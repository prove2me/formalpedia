-- Prove2me | solution 1 for HighDimProb.Concentration.general_hoeffding
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T22:27:35.208897+00:00
-- url     : https://prove2.me/submissions/565f5a69-62e2-4ba5-b641-a7dcb105f2ee

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real

lemma hdpc_exp_le_add_exp_sq (x : ℝ) : exp x ≤ x + exp (x ^ 2) := by
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

lemma hdpc_pt1 (l b σ : ℝ) :
    exp (l * (σ * b)) ≤ exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (b ^ 2) / 2) := by
  have h1 : l * (σ * b) ≤ l ^ 2 * σ ^ 2 / 2 + b ^ 2 / 2 := by
    nlinarith [sq_nonneg (l * σ - b)]
  have h2 : exp (b ^ 2 / 2) ≤ 1 / 2 + exp (b ^ 2) / 2 := by
    have hz : exp (b ^ 2) = exp (b ^ 2 / 2) ^ 2 := by rw [sq (exp _), ← exp_add]; ring_nf
    nlinarith [sq_nonneg (exp (b ^ 2 / 2) - 1)]
  calc exp (l * (σ * b)) ≤ exp (l ^ 2 * σ ^ 2 / 2 + b ^ 2 / 2) := exp_le_exp.2 h1
    _ = exp (l ^ 2 * σ ^ 2 / 2) * exp (b ^ 2 / 2) := exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (exp_pos _).le

lemma hdpc_pt2 (l b σ : ℝ) (hq : l ^ 2 * σ ^ 2 ≤ 1) :
    exp (l * (σ * b)) ≤ l * (σ * b) + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (b ^ 2) := by
  have h1 := hdpc_exp_le_add_exp_sq (l * (σ * b))
  have h2 : (l * (σ * b)) ^ 2 = l ^ 2 * σ ^ 2 * b ^ 2 + (1 - l ^ 2 * σ ^ 2) * 0 := by ring
  have hq0 : 0 ≤ l ^ 2 * σ ^ 2 := by positivity
  have h3 := convexOn_exp.2 (Set.mem_univ (b ^ 2)) (Set.mem_univ (0 : ℝ)) hq0 (sub_nonneg.2 hq)
    (by ring : l ^ 2 * σ ^ 2 + (1 - l ^ 2 * σ ^ 2) = 1)
  simp only [smul_eq_mul] at h3
  rw [h2] at h1
  rw [exp_zero] at h3
  linarith

lemma hdpc_subG {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hmean : ∫ ω, Y ω ∂P = 0) (σ : ℝ) (hσ : 0 < σ)
    (hint : Integrable (fun ω => exp (Y ω ^ 2 / σ ^ 2)) P)
    (hle : ∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P ≤ 2) :
    HasSubgaussianMGF Y (2 * σ ^ 2).toNNReal P := by
  have hYσ : ∀ ω, σ * (Y ω / σ) = Y ω := fun ω => by field_simp
  have hYσ2 : ∀ ω, (Y ω / σ) ^ 2 = Y ω ^ 2 / σ ^ 2 := fun ω => div_pow _ _ _
  have hpt1 : ∀ l ω, exp (l * Y ω) ≤
      exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (Y ω ^ 2 / σ ^ 2) / 2) := by
    intro l ω
    have h := hdpc_pt1 l (Y ω / σ) σ
    rwa [hYσ, hYσ2] at h
  have hintE : ∀ l, Integrable (fun ω => exp (l * Y ω)) P := by
    intro l
    refine Integrable.mono' (((integrable_const (1 / 2 : ℝ)).add (hint.div_const 2)).const_mul
      (exp (l ^ 2 * σ ^ 2 / 2))) ((hY.const_mul l).exp.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact hpt1 l ω
  have hYint : Integrable Y P := by
    refine Integrable.mono' (hint.const_mul σ) hY.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |Y ω / σ| ≤ exp ((Y ω / σ) ^ 2) := by
      nlinarith [sq_nonneg (|Y ω / σ| - 1 / 2), sq_abs (Y ω / σ),
        add_one_le_exp ((Y ω / σ) ^ 2)]
    rw [hYσ2, abs_div, abs_of_pos hσ, div_le_iff₀ hσ] at h1
    linarith [mul_comm σ (exp (Y ω ^ 2 / σ ^ 2))]
  refine ⟨hintE, fun l => ?_⟩
  have htarget : ((2 * σ ^ 2).toNNReal : ℝ) * l ^ 2 / 2 = l ^ 2 * σ ^ 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]; ring
  rw [htarget, mgf]
  rcases le_or_gt (l ^ 2 * σ ^ 2) 1 with hq | hq
  · have hpt2 : ∀ ω, exp (l * Y ω) ≤
        l * Y ω + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2) := by
      intro ω
      have h := hdpc_pt2 l (Y ω / σ) σ hq
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

lemma hdpc_const_mul {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : HasSubgaussianMGF Y c.toNNReal P) (r : ℝ) :
    HasSubgaussianMGF (fun ω => r * Y ω) (r ^ 2 * c).toNNReal P := by
  have h1 := h.const_mul r
  convert h1 using 1
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by positivity)]
  show r ^ 2 * c = r ^ 2 * (c.toNNReal : ℝ)
  rw [Real.coe_toNNReal _ hc]

open MeasureTheory ProbabilityTheory Real HighDimProb.Concentration in
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {N : ℕ} (X : Fin N → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X P →
        (∀ i, ∫ ω, X i ω ∂P = 0) →
        (∀ i, ∃ s > 0, Integrable (fun ω => Real.exp ((X i ω) ^ 2 / s ^ 2)) P ∧
                       ∫ ω, Real.exp ((X i ω) ^ 2 / s ^ 2) ∂P ≤ 2) →
        ∀ (a : Fin N → ℝ) {t : ℝ}, 0 ≤ t →
        P.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
          2 * Real.exp (-(c * t ^ 2 /
            ((⨆ i, subgaussianNorm P (X i)) ^ 2 * ∑ i, (a i) ^ 2))) := by
  refine ⟨1 / 16, by norm_num, ?_⟩
  intro Ω _ P _ N X hX_meas hX_indep hmean hsg a t ht
  set K := ⨆ i, subgaussianNorm P (X i) with hK
  set A := ∑ i, (a i) ^ 2 with hA
  have hP1 : P.real {ω | t ≤ |∑ i, a i * X i ω|} ≤ 1 := measureReal_le_one
  by_cases hD : K ^ 2 * A = 0
  · rw [hD, div_zero, neg_zero, exp_zero]; linarith
  have hnn : ∀ i, 0 ≤ subgaussianNorm P (X i) := fun i => Real.sInf_nonneg (fun x hx => hx.1.le)
  have hbdd : BddAbove (Set.range fun i => subgaussianNorm P (X i)) :=
    (Set.finite_range _).bddAbove
  have hleK : ∀ i, subgaussianNorm P (X i) ≤ K := fun i => le_ciSup hbdd i
  have hK0 : 0 ≤ K := Real.iSup_nonneg hnn
  have hKne : K ≠ 0 := by
    intro h; apply hD; rw [h]; ring
  have hKpos : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hKne)
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hσ : ∀ i, Integrable (fun ω => exp (X i ω ^ 2 / (2 * K) ^ 2)) P ∧
      ∫ ω, exp (X i ω ^ 2 / (2 * K) ^ 2) ∂P ≤ 2 := by
    intro i
    obtain ⟨s0, hs0, hint0, hle0⟩ := hsg i
    have hne : ({s : ℝ | 0 < s ∧ Integrable (fun ω => Real.exp ((X i ω) ^ 2 / s ^ 2)) P ∧
        ∫ ω, Real.exp ((X i ω) ^ 2 / s ^ 2) ∂P ≤ 2}).Nonempty := ⟨s0, hs0, hint0, hle0⟩
    have hlt : subgaussianNorm P (X i) < 2 * K := by linarith [hleK i]
    unfold subgaussianNorm at hlt
    obtain ⟨s, ⟨hs, hints, hles⟩, hs2⟩ := exists_lt_of_csInf_lt hne hlt
    have hmono : ∀ ω, exp (X i ω ^ 2 / (2 * K) ^ 2) ≤ exp (X i ω ^ 2 / s ^ 2) := fun ω =>
      exp_le_exp.2 (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (pow_le_pow_left₀ hs.le hs2.le 2))
    have hint2 : Integrable (fun ω => exp (X i ω ^ 2 / (2 * K) ^ 2)) P :=
      hints.mono' (((hX_meas i).pow_const 2).div_const _).exp.aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact hmono ω)
    exact ⟨hint2, (integral_mono hint2 hints hmono).trans hles⟩
  have hc8 : (0 : ℝ) ≤ 2 * (2 * K) ^ 2 := by positivity
  have hsubX : ∀ i, HasSubgaussianMGF (X i) (2 * (2 * K) ^ 2).toNNReal P := fun i =>
    hdpc_subG P (X i) (hX_meas i) (hmean i) (2 * K) (by positivity) (hσ i).1 (hσ i).2
  have tail : ∀ b : Fin N → ℝ, (∀ i, b i ^ 2 = a i ^ 2) →
      P.real {ω | t ≤ ∑ i, b i * X i ω} ≤ exp (-(t ^ 2 / (16 * K ^ 2 * A))) := by
    intro b hb
    have hind : iIndepFun (fun i ω => b i * X i ω) P :=
      hX_indep.comp (fun i x => b i * x) (fun i => measurable_const.mul measurable_id)
    have hsub : ∀ i ∈ (Finset.univ : Finset (Fin N)),
        HasSubgaussianMGF (fun ω => b i * X i ω) (b i ^ 2 * (2 * (2 * K) ^ 2)).toNNReal P :=
      fun i _ => hdpc_const_mul hc8 (hsubX i) (b i)
    have key := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub ht
    refine key.trans (le_of_eq ?_)
    have hS : ((∑ i, (b i ^ 2 * (2 * (2 * K) ^ 2)).toNNReal : NNReal) : ℝ) = 8 * K ^ 2 * A := by
      rw [hA, NNReal.coe_sum, Finset.sum_congr rfl (fun i _ => Real.coe_toNNReal _
        (by positivity : (0 : ℝ) ≤ b i ^ 2 * (2 * (2 * K) ^ 2))), ← Finset.sum_mul]
      simp_rw [hb]
      ring
    rw [hS]
    congr 1
    ring
  have h1 := tail a (fun i => rfl)
  have h2 := tail (fun i => -a i) (fun i => by ring)
  have hsplit : {ω | t ≤ |∑ i, a i * X i ω|} ⊆
      {ω | t ≤ ∑ i, a i * X i ω} ∪ {ω | t ≤ ∑ i, (fun i => -a i) i * X i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases le_abs.1 hω with h | h
    · exact Or.inl h
    · right
      simp only [neg_mul, Finset.sum_neg_distrib]
      exact h
  have he : -(1 / 16 * t ^ 2 / (K ^ 2 * A)) = -(t ^ 2 / (16 * K ^ 2 * A)) := by ring
  rw [he]
  calc P.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ P.real ({ω | t ≤ ∑ i, a i * X i ω} ∪ {ω | t ≤ ∑ i, (fun i => -a i) i * X i ω}) :=
        measureReal_mono hsplit
    _ ≤ P.real {ω | t ≤ ∑ i, a i * X i ω} + P.real {ω | t ≤ ∑ i, (fun i => -a i) i * X i ω} :=
        measureReal_union_le _ _
    _ ≤ _ := by linarith
