-- Prove2me | solution 1 for HighDimProb.RandomMatrices.norm_of_subgaussian_matrix_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T18:17:07.674982+00:00
-- url     : https://prove2.me/submissions/d2ecdbeb-62c5-49cf-a7d1-91479ac18e8b

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real

lemma nsm_exp_le_add_exp_sq (x : ℝ) : exp x ≤ x + exp (x ^ 2) := by
  rcases le_or_gt |x| 1 with hx | hx
  · have h1 := Real.abs_exp_sub_one_sub_id_le hx
    have h2 := Real.add_one_le_exp (x ^ 2)
    have h3 := (abs_le.1 h1).2
    linarith
  · rcases le_or_gt 0 x with h0 | h0
    · have hx1 : 1 < x := by rwa [abs_of_nonneg h0] at hx
      have h4 : x ≤ x ^ 2 := by nlinarith
      have h5 := exp_le_exp.2 h4
      linarith
    · have hx1 : x < -1 := by
        rw [abs_of_neg h0] at hx; linarith
      have h4 : exp x ≤ 1 := Real.exp_le_one_iff.2 h0.le
      have h5 := Real.add_one_le_exp (x ^ 2)
      nlinarith

lemma nsm_pt1 (l b σ : ℝ) :
    exp (l * (σ * b)) ≤ exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (b ^ 2) / 2) := by
  have h1 : l * (σ * b) ≤ l ^ 2 * σ ^ 2 / 2 + b ^ 2 / 2 := by
    nlinarith [sq_nonneg (l * σ - b)]
  have h2 : exp (b ^ 2 / 2) ≤ 1 / 2 + exp (b ^ 2) / 2 := by
    have hz : exp (b ^ 2) = exp (b ^ 2 / 2) ^ 2 := by rw [sq (exp _), ← exp_add]; ring_nf
    nlinarith [sq_nonneg (exp (b ^ 2 / 2) - 1)]
  calc exp (l * (σ * b)) ≤ exp (l ^ 2 * σ ^ 2 / 2 + b ^ 2 / 2) := exp_le_exp.2 h1
    _ = exp (l ^ 2 * σ ^ 2 / 2) * exp (b ^ 2 / 2) := exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (exp_pos _).le

lemma nsm_pt2 (l b σ : ℝ) (hq : l ^ 2 * σ ^ 2 ≤ 1) :
    exp (l * (σ * b)) ≤ l * (σ * b) + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (b ^ 2) := by
  have h1 := nsm_exp_le_add_exp_sq (l * (σ * b))
  have h2 : (l * (σ * b)) ^ 2 = l ^ 2 * σ ^ 2 * b ^ 2 + (1 - l ^ 2 * σ ^ 2) * 0 := by ring
  have hq0 : 0 ≤ l ^ 2 * σ ^ 2 := by positivity
  have h3 := convexOn_exp.2 (Set.mem_univ (b ^ 2)) (Set.mem_univ (0 : ℝ)) hq0 (sub_nonneg.2 hq)
    (by ring : l ^ 2 * σ ^ 2 + (1 - l ^ 2 * σ ^ 2) = 1)
  simp only [smul_eq_mul] at h3
  rw [h2] at h1
  rw [exp_zero] at h3
  linarith

lemma nsm_subG {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hYint : Integrable Y P) (hmean : ∫ ω, Y ω ∂P = 0) (σ : ℝ) (hσ : 0 < σ)
    (hint : Integrable (fun ω => exp (Y ω ^ 2 / σ ^ 2)) P)
    (hle : ∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P ≤ 2) :
    HasSubgaussianMGF Y (2 * σ ^ 2).toNNReal P := by
  have hY : AEStronglyMeasurable Y P := hYint.aestronglyMeasurable
  have hYσ : ∀ ω, σ * (Y ω / σ) = Y ω := fun ω => by field_simp
  have hYσ2 : ∀ ω, (Y ω / σ) ^ 2 = Y ω ^ 2 / σ ^ 2 := fun ω => div_pow _ _ _
  have hpt1 : ∀ l ω, exp (l * Y ω) ≤
      exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (Y ω ^ 2 / σ ^ 2) / 2) := by
    intro l ω
    have h := nsm_pt1 l (Y ω / σ) σ
    rwa [hYσ, hYσ2] at h
  have hintE : ∀ l, Integrable (fun ω => exp (l * Y ω)) P := by
    intro l
    refine Integrable.mono' (((integrable_const (1 / 2 : ℝ)).add (hint.div_const 2)).const_mul
      (exp (l ^ 2 * σ ^ 2 / 2)))
      (Real.continuous_exp.comp_aestronglyMeasurable (hY.const_mul l))
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact hpt1 l ω
  refine ⟨hintE, fun l => ?_⟩
  have htarget : ((2 * σ ^ 2).toNNReal : ℝ) * l ^ 2 / 2 = l ^ 2 * σ ^ 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]; ring
  rw [htarget, mgf]
  rcases le_or_gt (l ^ 2 * σ ^ 2) 1 with hq | hq
  · have hpt2 : ∀ ω, exp (l * Y ω) ≤
        l * Y ω + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2) := by
      intro ω
      have h := nsm_pt2 l (Y ω / σ) σ hq
      rwa [hYσ, hYσ2] at h
    have hI1 : Integrable (fun ω => l * Y ω + (1 - l ^ 2 * σ ^ 2)) P :=
      (hYint.const_mul l).add (integrable_const _)
    have hI2 : Integrable (fun ω => l ^ 2 * σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2)) P := hint.const_mul _
    calc ∫ ω, exp (l * Y ω) ∂P
        ≤ ∫ ω, (l * Y ω + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2)) ∂P :=
          integral_mono (hintE l) (hI1.add hI2) hpt2
      _ = l * ∫ ω, Y ω ∂P + (1 - l ^ 2 * σ ^ 2) +
            l ^ 2 * σ ^ 2 * ∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P := by
          rw [integral_add hI1 hI2, integral_add (hYint.const_mul l) (integrable_const _),
            integral_const_mul, integral_const_mul, integral_const]
          simp
      _ ≤ 1 + l ^ 2 * σ ^ 2 := by
          rw [hmean]
          have hq0 : 0 ≤ l ^ 2 * σ ^ 2 := by positivity
          nlinarith
      _ ≤ exp (l ^ 2 * σ ^ 2) := by linarith [add_one_le_exp (l ^ 2 * σ ^ 2)]
  · have hI : Integrable
        (fun ω => exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (Y ω ^ 2 / σ ^ 2) / 2)) P :=
      ((integrable_const (1 / 2 : ℝ)).add (hint.div_const 2)).const_mul _
    calc ∫ ω, exp (l * Y ω) ∂P
        ≤ ∫ ω, exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (Y ω ^ 2 / σ ^ 2) / 2) ∂P :=
          integral_mono (hintE l) hI (hpt1 l)
      _ = exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + (∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P) / 2) := by
          rw [integral_const_mul, integral_add (integrable_const _) (hint.div_const 2),
            integral_const, integral_div]
          simp
      _ ≤ exp (l ^ 2 * σ ^ 2 / 2) * exp (l ^ 2 * σ ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
          have h1 := add_one_le_exp (1 / 2 : ℝ)
          have h2 : exp (1 / 2 : ℝ) ≤ exp (l ^ 2 * σ ^ 2 / 2) := exp_le_exp.2 (by linarith)
          linarith
      _ = exp (l ^ 2 * σ ^ 2) := by rw [← exp_add]; ring_nf

lemma nsm_mono {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {c c' : NNReal}
    (h : HasSubgaussianMGF X c P) (hc : c ≤ c') : HasSubgaussianMGF X c' P := by
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans (exp_le_exp.2 ?_)⟩
  have : (c : ℝ) ≤ c' := hc
  have h2 : (c : ℝ) * t ^ 2 ≤ c' * t ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg t)
  linarith

lemma nsm_subG_of_norm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hYint : Integrable Y P) (hmean : ∫ ω, Y ω ∂P = 0) (K : NNReal)
    (hK : HighDimProb.Concentration.subgaussianNorm P Y ≤ K) (K' : ℝ) (hK' : (K : ℝ) < K') :
    HasSubgaussianMGF Y (2 * K' ^ 2).toNNReal P := by
  have hK'0 : 0 < K' := lt_of_le_of_lt K.2 hK'
  have hlt : HighDimProb.Concentration.subgaussianNorm P Y < ENNReal.ofReal K' := by
    refine lt_of_le_of_lt hK ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hK'0).2 hK'
  unfold HighDimProb.Concentration.subgaussianNorm at hlt
  obtain ⟨σ, h1⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hσ, h2⟩ := iInf_lt_iff.1 h1
  obtain ⟨hint, h3⟩ := iInf_lt_iff.1 h2
  obtain ⟨hle, h4⟩ := iInf_lt_iff.1 h3
  have hσK : σ < K' := (ENNReal.ofReal_lt_ofReal_iff hK'0).1 h4
  refine nsm_mono (nsm_subG P Y hYint hmean σ hσ hint hle) ?_
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity),
    Real.coe_toNNReal _ (by positivity)]
  nlinarith

/-- packing bound: a 1/4-separated subset of the closed unit ball has at most 9^n points. -/
lemma nsm_card_le (n : ℕ) (S : Finset (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ x ∈ S, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (1 / 4 : ℝ) ≤ ‖x - y‖) :
    (S.card : ℝ) ≤ 9 ^ n := by
  set μ : Measure (EuclideanSpace ℝ (Fin n)) := volume
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hdisj : (S : Set (EuclideanSpace ℝ (Fin n))).PairwiseDisjoint
      (fun x => Metric.ball x (1 / 8 : ℝ)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.2 fun z hz1 hz2 => ?_
    have h1 := hsep x hx y hy hxy
    rw [Metric.mem_ball, dist_eq_norm] at hz1 hz2
    have : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
      calc ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; abel
        _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  have hsub : (⋃ x ∈ S, Metric.ball x (1 / 8 : ℝ)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (9 / 8) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    have := hS x hx
    calc ‖z - 0‖ = ‖(z - x) + x‖ := by simp
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < 9 / 8 := by linarith
  have hmeas := measure_biUnion_finset (μ := μ) hdisj (fun x _ => (measurableSet_ball :
    MeasurableSet (Metric.ball x (1 / 8 : ℝ))))
  have hle := measure_mono (μ := μ) hsub
  rw [hmeas] at hle
  simp only [μ, Measure.addHaar_ball_of_pos _ _ (by norm_num : (0 : ℝ) < 1 / 8),
    Measure.addHaar_ball_of_pos _ _ (by norm_num : (0 : ℝ) < 9 / 8), Finset.sum_const, hfin,
    nsmul_eq_mul] at hle
  set V := (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball 0 1)
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have h2 := (ENNReal.mul_le_mul_iff_left hV0 hVt).1 hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have h3 : ((9 : ℝ) / 8) ^ n = 9 ^ n * (1 / 8) ^ n := by rw [← mul_pow]; norm_num
  rw [h3] at h2
  have h4 : (0 : ℝ) < (1 / 8) ^ n := by positivity
  nlinarith

/-- existence of a 1/4-net of the closed unit ball of size at most 9^n. -/
lemma nsm_net (n : ℕ) : ∃ N : Finset (EuclideanSpace ℝ (Fin n)),
    (∀ x ∈ N, ‖x‖ ≤ 1) ∧ (N.card : ℝ) ≤ 9 ^ n ∧
    ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∃ y ∈ N, ‖x - y‖ < 1 / 4 := by
  by_contra hcon
  push Not at hcon
  have key : ∀ k : ℕ, ∃ S : Finset (EuclideanSpace ℝ (Fin n)), S.card = k ∧
      (∀ x ∈ S, ‖x‖ ≤ 1) ∧ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → (1 / 4 : ℝ) ≤ ‖x - y‖) := by
    intro k
    induction k with
    | zero => exact ⟨∅, by simp, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨S, hc, hS, hsep⟩ := ih
      obtain ⟨x, hx, hfar⟩ := hcon S hS (nsm_card_le n S hS hsep)
      have hxS : x ∉ S := by
        intro h
        have := hfar x h
        simp at this
        linarith
      refine ⟨insert x S, by rw [Finset.card_insert_of_notMem hxS, hc], ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.1 hy with h | h
        · rw [h]; exact hx
        · exact hS y h
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with h1 | h1 <;> rcases Finset.mem_insert.1 hb with h2 | h2
        · exact absurd (h1.trans h2.symm) hab
        · rw [h1]; exact hfar b h2
        · rw [h2, norm_sub_rev]; exact hfar a h1
        · exact hsep a h1 b h2 hab
  obtain ⟨S, hc, hS, hsep⟩ := key (9 ^ n + 1)
  have := nsm_card_le n S hS hsep
  rw [hc] at this
  push_cast at this
  linarith

/-- operator norm via nets. -/
lemma nsm_opNorm_le {n m : ℕ} (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (N : Finset (EuclideanSpace ℝ (Fin n))) (M : Finset (EuclideanSpace ℝ (Fin m)))
    (hN : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∃ y ∈ N, ‖x - y‖ < 1 / 4)
    (hM : ∀ x : EuclideanSpace ℝ (Fin m), ‖x‖ ≤ 1 → ∃ y ∈ M, ‖x - y‖ < 1 / 4)
    (u : ℝ) (hu : 0 ≤ u) (h : ∀ x ∈ N, ∀ y ∈ M, inner ℝ (T x) y < u) : ‖T‖ ≤ 2 * u := by
  have hv : ∀ x ∈ N, ‖T x‖ ≤ 4 / 3 * u := by
    intro x hx
    set v := T x
    by_cases hv0 : v = 0
    · rw [hv0, norm_zero]; positivity
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    set w := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by
      simp only [w, norm_smul, norm_inv, norm_norm]; field_simp
    obtain ⟨y, hy, hwy⟩ := hM w hw.le
    have h1 : inner ℝ v w = ‖v‖ := by
      simp only [w, inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
    have h2 : inner ℝ v w = inner ℝ v y + inner ℝ v (w - y) := by
      rw [← inner_add_right]; congr 1; abel
    have h3 : inner ℝ v (w - y) ≤ ‖v‖ * ‖w - y‖ := real_inner_le_norm _ _
    have h4 := h x hx y hy
    have h5 : ‖v‖ * ‖w - y‖ ≤ ‖v‖ * (1 / 4) := mul_le_mul_of_nonneg_left hwy.le hvpos.le
    linarith
  have hT : ‖T‖ ≤ 4 / 3 * u + ‖T‖ / 4 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hN x hx.le
    have h1 : ‖T x‖ ≤ ‖T y‖ + ‖T (x - y)‖ := by
      rw [map_sub]
      calc ‖T x‖ = ‖T y + (T x - T y)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖T (x - y)‖ ≤ ‖T‖ * ‖x - y‖ := T.le_opNorm _
    have h3 : ‖T‖ * ‖x - y‖ ≤ ‖T‖ * (1 / 4) := mul_le_mul_of_nonneg_left hxy.le (norm_nonneg _)
    have := hv y hy
    linarith
  linarith

/-- the bilinear form of a matrix. -/
lemma nsm_inner_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) x) y =
      ∑ p : Fin m × Fin n, (y p.1 * x p.2) * A p.1 p.2 := by
  rw [Fintype.sum_prod_type]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, PiLp.inner_apply,
    PiLp.toLp_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma nsm_const_mul {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : HasSubgaussianMGF Y c.toNNReal P) (r : ℝ) :
    HasSubgaussianMGF (fun ω => r * Y ω) (r ^ 2 * c).toNNReal P := by
  have h1 := h.const_mul r
  convert h1 using 1
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by positivity)]
  show r ^ 2 * c = r ^ 2 * (c.toNNReal : ℝ)
  rw [Real.coe_toNNReal _ hc]

lemma nsm_count (m n : ℕ) (t cN cM : ℝ) (hN : cN ≤ 9 ^ n) (hM : cM ≤ 9 ^ m) (hN0 : 0 ≤ cN)
    (hM0 : 0 ≤ cM) (ht : 0 < t) :
    cN * cM * exp (-(4 * (Real.sqrt m + Real.sqrt n + t) ^ 2)) ≤ exp (-(t ^ 2)) := by
  have h9 : (9 : ℝ) ≤ exp 3 := by
    have h1 := Real.exp_one_gt_d9
    have he : (2.7 : ℝ) ≤ exp 1 := by linarith
    have h3 : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    calc (9 : ℝ) ≤ 2.7 ^ 3 := by norm_num
      _ ≤ exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he 3
  have hpow : ∀ k : ℕ, (9 : ℝ) ^ k ≤ exp (3 * k) := by
    intro k
    calc (9 : ℝ) ^ k ≤ exp 3 ^ k := pow_le_pow_left₀ (by norm_num) h9 k
      _ = exp (3 * k) := by rw [← Real.exp_nat_mul]; ring_nf
  have hsm := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hsn := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hs0 := Real.sqrt_nonneg (m : ℝ)
  have hs1 := Real.sqrt_nonneg (n : ℝ)
  have hsq : (m : ℝ) + n + t ^ 2 ≤ (Real.sqrt m + Real.sqrt n + t) ^ 2 := by
    nlinarith [mul_nonneg hs0 hs1, mul_nonneg hs0 ht.le, mul_nonneg hs1 ht.le]
  calc cN * cM * exp (-(4 * (Real.sqrt m + Real.sqrt n + t) ^ 2))
      ≤ exp (3 * n) * exp (3 * m) * exp (-(4 * (Real.sqrt m + Real.sqrt n + t) ^ 2)) := by
        gcongr
        · exact hN.trans (hpow n)
        · exact hM.trans (hpow m)
    _ = exp (3 * n + 3 * m - 4 * (Real.sqrt m + Real.sqrt n + t) ^ 2) := by
        rw [← exp_add, ← exp_add]; ring_nf
    _ ≤ exp (-(t ^ 2)) := by
        apply exp_le_exp.2
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith

lemma nsm_key {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
    {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (hindep : iIndepFun (fun p : Fin m × Fin n => fun ω => A ω p.1 p.2) Prob)
    (hmean : ∀ i j, Integrable (fun ω => A ω i j) Prob ∧ ∫ ω, A ω i j ∂Prob = 0)
    (K : NNReal)
    (hK : ∀ i j, HighDimProb.Concentration.subgaussianNorm Prob (fun ω => A ω i j) ≤ K)
    (t : ℝ) (ht : 0 < t) (K' : ℝ) (hK' : (K : ℝ) < K') :
    Prob {ω | 8 * K' * (Real.sqrt m + Real.sqrt n + t) <
      HighDimProb.RandomMatrices.matrixOpNorm (A ω)} ≤ ENNReal.ofReal (exp (-(t ^ 2))) := by
  have hK'0 : 0 < K' := lt_of_le_of_lt K.2 hK'
  set s := Real.sqrt m + Real.sqrt n + t with hs_def
  have hs : 0 < s := by positivity
  set u := 4 * K' * s with hu_def
  have hu : 0 ≤ u := by positivity
  obtain ⟨N, hNb, hNc, hNn⟩ := nsm_net n
  obtain ⟨M, hMb, hMc, hMn⟩ := nsm_net m
  have hsubE : ∀ p : Fin m × Fin n,
      HasSubgaussianMGF (fun ω => A ω p.1 p.2) (2 * K' ^ 2).toNNReal Prob := fun p =>
    nsm_subG_of_norm Prob _ (hmean p.1 p.2).1 (hmean p.1 p.2).2 K (hK p.1 p.2) K' hK'
  have hZ : ∀ x ∈ N, ∀ y ∈ M,
      Prob {ω | u ≤ ∑ p : Fin m × Fin n, (y p.1 * x p.2) * A ω p.1 p.2} ≤
        ENNReal.ofReal (exp (-(4 * s ^ 2))) := by
    intro x hx y hy
    have hind : iIndepFun (fun (p : Fin m × Fin n) ω => (y p.1 * x p.2) * A ω p.1 p.2) Prob :=
      hindep.comp (fun p a => (y p.1 * x p.2) * a) (fun p => measurable_const.mul measurable_id)
    have hsub : ∀ p ∈ (Finset.univ : Finset (Fin m × Fin n)),
        HasSubgaussianMGF (fun ω => (y p.1 * x p.2) * A ω p.1 p.2)
          (Real.toNNReal ((y p.1 * x p.2 : ℝ) ^ 2 * (2 * K' ^ 2))) Prob :=
      fun p _ => nsm_const_mul (by positivity) (hsubE p) _
    have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind hsub
    have hc : (∑ p ∈ (Finset.univ : Finset (Fin m × Fin n)),
        (Real.toNNReal ((y p.1 * x p.2 : ℝ) ^ 2 * (2 * K' ^ 2)))) ≤
        (2 * K' ^ 2).toNNReal := by
      rw [← NNReal.coe_le_coe, NNReal.coe_sum, Finset.sum_congr rfl (fun p _ => Real.coe_toNNReal _
        (by positivity : (0 : ℝ) ≤ (y p.1 * x p.2) ^ 2 * (2 * K' ^ 2))),
        Real.coe_toNNReal _ (by positivity), ← Finset.sum_mul]
      have hx1 := hNb x hx
      have hy1 := hMb y hy
      have hxs : ∑ j, x j ^ 2 ≤ 1 := by
        rw [← EuclideanSpace.real_norm_sq_eq]; nlinarith [norm_nonneg x]
      have hys : ∑ i, y i ^ 2 ≤ 1 := by
        rw [← EuclideanSpace.real_norm_sq_eq]; nlinarith [norm_nonneg y]
      have hprod : ∑ p : Fin m × Fin n, (y p.1 * x p.2) ^ 2 = (∑ i, y i ^ 2) * ∑ j, x j ^ 2 := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hprod]
      have h0 : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      have h1 : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have h2 : (∑ i, y i ^ 2) * ∑ j, x j ^ 2 ≤ 1 := by nlinarith
      have h3 : 0 ≤ 2 * K' ^ 2 := by positivity
      nlinarith
    have htail := (nsm_mono hsum hc).measure_ge_le hu
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    refine htail.trans (le_of_eq ?_)
    rw [Real.coe_toNNReal _ (by positivity)]
    congr 1
    rw [hu_def]
    field_simp
    ring
  have hbad : {ω | 8 * K' * s < HighDimProb.RandomMatrices.matrixOpNorm (A ω)} ⊆
      ⋃ x ∈ N, ⋃ y ∈ M, {ω | u ≤ ∑ p : Fin m × Fin n, (y p.1 * x p.2) * A ω p.1 p.2} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hcon
    have hle := nsm_opNorm_le (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A ω)) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) N M hNn hMn u hu
      (fun x hx y hy => by rw [nsm_inner_eq]; exact hcon x hx y hy)
    simp only [Set.mem_setOf_eq] at hω
    unfold HighDimProb.RandomMatrices.matrixOpNorm at hω
    linarith
  calc Prob {ω | 8 * K' * s < HighDimProb.RandomMatrices.matrixOpNorm (A ω)}
      ≤ Prob (⋃ x ∈ N, ⋃ y ∈ M,
          {ω | u ≤ ∑ p : Fin m × Fin n, (y p.1 * x p.2) * A ω p.1 p.2}) := measure_mono hbad
    _ ≤ ∑ x ∈ N, Prob (⋃ y ∈ M,
          {ω | u ≤ ∑ p : Fin m × Fin n, (y p.1 * x p.2) * A ω p.1 p.2}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ N, ∑ y ∈ M,
          Prob {ω | u ≤ ∑ p : Fin m × Fin n, (y p.1 * x p.2) * A ω p.1 p.2} :=
        Finset.sum_le_sum fun x _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ N, ∑ y ∈ M, ENNReal.ofReal (exp (-(4 * s ^ 2))) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hZ x hx y hy
    _ = ENNReal.ofReal ((N.card : ℝ) * M.card * exp (-(4 * s ^ 2))) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal (exp (-(t ^ 2))) :=
        ENNReal.ofReal_le_ofReal (nsm_count m n t _ _ hNc hMc (by positivity) (by positivity) ht)

open MeasureTheory ProbabilityTheory NNReal ENNReal HighDimProb.RandomMatrices in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Ω → Matrix (Fin m) (Fin n) ℝ)
        (hindep : iIndepFun (fun p : Fin m × Fin n => fun ω => A ω p.1 p.2) Prob)
        (hmean : ∀ i j, Integrable (fun ω => A ω i j) Prob ∧ ∫ ω, A ω i j ∂Prob = 0)
        (K : ℝ≥0)
        (hK : ∀ i j, HighDimProb.Concentration.subgaussianNorm Prob (fun ω => A ω i j) ≤ K)
        (t : ℝ) (ht : 0 < t),
        1 - 2 * Real.exp (-(t ^ 2)) ≤
          Prob.real {ω | matrixOpNorm (A ω) ≤ C * K * (Real.sqrt m + Real.sqrt n + t)} := by
  refine ⟨8, by norm_num, ?_⟩
  intro Ω _ Prob _ m n hm hn A hindep hmean K hK t ht
  set s := Real.sqrt m + Real.sqrt n + t with hs_def
  have hs : 0 < s := by positivity
  set B : ℕ → Set Ω := fun k =>
    {ω | 8 * ((K : ℝ) + 1 / ((k : ℝ) + 1)) * s < matrixOpNorm (A ω)} with hB
  have hBmono : Monotone B := by
    intro k k' hkk' ω hω
    simp only [hB, Set.mem_setOf_eq] at hω ⊢
    refine lt_of_le_of_lt ?_ hω
    have : 1 / ((k' : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hkk' 1)
    have h8 : 0 ≤ 8 * s := by positivity
    nlinarith
  have hBle : ∀ k, Prob (B k) ≤ ENNReal.ofReal (exp (-(t ^ 2))) := fun k =>
    nsm_key Prob A hindep hmean K hK t ht _ (by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith)
  have hU : Prob (⋃ k, B k) ≤ ENNReal.ofReal (exp (-(t ^ 2))) :=
    le_of_tendsto' (tendsto_measure_iUnion_atTop hBmono) hBle
  have hsub : {ω | 8 * (K : ℝ) * s < matrixOpNorm (A ω)} ⊆ ⋃ k, B k := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    have hgap : 0 < (matrixOpNorm (A ω) - 8 * K * s) / (8 * s) := by
      apply div_pos (by linarith) (by positivity)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hgap
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simp only [hB, Set.mem_setOf_eq]
    rw [lt_div_iff₀ (by positivity)] at hk
    nlinarith
  have hbad : Prob.real {ω | 8 * (K : ℝ) * s < matrixOpNorm (A ω)} ≤ exp (-(t ^ 2)) :=
    ENNReal.toReal_le_of_le_ofReal (exp_pos _).le ((measure_mono hsub).trans hU)
  have hunion : (Set.univ : Set Ω) ⊆ {ω | matrixOpNorm (A ω) ≤ 8 * K * s} ∪
      {ω | 8 * (K : ℝ) * s < matrixOpNorm (A ω)} := by
    intro ω _
    rcases le_or_gt (matrixOpNorm (A ω)) (8 * K * s) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h1 : Prob.real (Set.univ : Set Ω) ≤ Prob.real {ω | matrixOpNorm (A ω) ≤ 8 * K * s} +
      Prob.real {ω | 8 * (K : ℝ) * s < matrixOpNorm (A ω)} :=
    (measureReal_mono hunion).trans (measureReal_union_le _ _)
  have hu1 : Prob.real (Set.univ : Set Ω) = 1 := by simp [Measure.real]
  rw [hu1] at h1
  have := (exp_pos (-(t ^ 2))).le
  linarith
