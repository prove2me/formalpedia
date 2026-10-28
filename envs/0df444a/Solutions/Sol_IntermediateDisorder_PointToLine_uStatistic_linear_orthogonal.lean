-- Prove2me | solution 1 for IntermediateDisorder.PointToLine.uStatistic_linear_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T14:16:40.509629+00:00
-- url     : https://prove2.me/submissions/2a24304c-cd10-42ab-ac58-62a9ad68cc06

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos
import Definitions.Def_IntermediateDisorder_PointToLine_UStatistic


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace IDLind

lemma norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have h1 : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i
        = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [h1]
    have hbp : ‖∏ i ∈ s, b i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have haj := ha j (Finset.mem_insert_self _ _)
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    calc _ ≤ ‖a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)‖ + ‖(a j - b j) * ∏ i ∈ s, b i‖ :=
          norm_add_le _ _
      _ ≤ 1 * ∑ i ∈ s, ‖a i - b i‖ + ‖a j - b j‖ * 1 := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul haj ih' (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left hbp (norm_nonneg _))
      _ = _ := by ring

/-- `|1 - s²/2 - e^{-s²/2}| ≤ s⁴/4` for `s² ≤ 2`, in `ℂ`. -/
lemma norm_one_sub_sub_exp_le (s : ℝ) (hs : s ^ 2 ≤ 2) :
    ‖(1 - (s : ℂ) ^ 2 / 2) - ((Real.exp (-s ^ 2 / 2) : ℝ) : ℂ)‖ ≤ s ^ 2 * s ^ 2 / 4 := by
  have hc : (1 - (s : ℂ) ^ 2 / 2) - ((Real.exp (-s ^ 2 / 2) : ℝ) : ℂ)
      = (((1 - s ^ 2 / 2 - Real.exp (-s ^ 2 / 2)) : ℝ) : ℂ) := by push_cast; ring
  rw [hc, Complex.norm_real, Real.norm_eq_abs]
  have hx : |(-s ^ 2 / 2 : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg s]
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have he : 1 - s ^ 2 / 2 - Real.exp (-s ^ 2 / 2)
      = -(Real.exp (-s ^ 2 / 2) - 1 - (-s ^ 2 / 2)) := by ring
  rw [he, abs_neg]
  calc _ ≤ (-s ^ 2 / 2) ^ 2 := h
    _ = s ^ 2 * s ^ 2 / 4 := by ring

/-- Lindeberg-type CLT for weighted sums of an i.i.d. family, at the level of characteristic
functions: if the weights are uniformly small and their squares sum to `σ2` in the limit, the
characteristic function of `∑ c_{n,i} X_i` tends to that of `N(0, σ2)`. -/
theorem charFun_weighted_sum_tendsto {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ι → Ω → ℝ} (hmeas : ∀ i, AEMeasurable (X i) P)
    (hindep : iIndepFun X P) (i0 : ι) (hident : ∀ i, IdentDistrib (X i) (X i0) P P)
    (h0 : P[X i0] = 0) (h1 : P[X i0 ^ 2] = 1)
    (s : ℕ → Finset ι) (c : ℕ → ι → ℝ) (σ2 : ℝ)
    (hmax : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i ∈ s n, |c n i| ≤ ε)
    (hsum : Tendsto (fun n => ∑ i ∈ s n, c n i ^ 2) atTop (𝓝 σ2)) (t : ℝ) :
    Tendsto (fun n => charFun (P.map (fun a => ∑ i ∈ s n, c n i * X i a)) t) atTop
      (𝓝 ((Real.exp (-(σ2 * t ^ 2) / 2) : ℝ) : ℂ)) := by
  set φ : ℝ → ℂ := charFun (P.map (X i0)) with hφ
  -- the characteristic function factorises
  have hfac : ∀ n, charFun (P.map (fun a => ∑ i ∈ s n, c n i * X i a)) t
      = ∏ i ∈ s n, φ (c n i * t) := by
    intro n
    have hind : iIndepFun (fun i a => c n i * X i a) P :=
      hindep.comp (fun i x => c n i * x) (fun i => measurable_const.mul measurable_id)
    have h := (hind.restrict (s n)).charFun_map_fun_finsetSum_eq_prod
      (s := s n) (fun i _ => (hmeas i).const_mul (c n i))
    rw [h, Finset.prod_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [charFun_map_mul_comp (hmeas i), (hident i).map_eq]
  simp_rw [hfac]
  set b : ℕ → ι → ℂ := fun n i => ((Real.exp (-(c n i * t) ^ 2 / 2) : ℝ) : ℂ) with hb
  -- the Gaussian product
  have hprodb : ∀ n, ∏ i ∈ s n, b n i
      = ((Real.exp (-((∑ i ∈ s n, c n i ^ 2) * t ^ 2) / 2) : ℝ) : ℂ) := by
    intro n
    simp only [hb]
    rw [← Complex.ofReal_prod, ← Real.exp_sum]
    congr 2
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hlimb : Tendsto (fun n => ∏ i ∈ s n, b n i) atTop
      (𝓝 ((Real.exp (-(σ2 * t ^ 2) / 2) : ℝ) : ℂ)) := by
    simp_rw [hprodb]
    have hc : Continuous fun u : ℝ => ((Real.exp (-(u * t ^ 2) / 2) : ℝ) : ℂ) := by fun_prop
    exact (hc.tendsto σ2).comp hsum
  -- the difference tends to zero
  have hdiff : Tendsto (fun n => ∏ i ∈ s n, φ (c n i * t) - ∏ i ∈ s n, b n i) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set K : ℝ := (t ^ 2 + 1) * (|σ2| + 2) with hK
    have hKpos : 0 < K := by positivity
    set η : ℝ := ε / (4 * K) with hη
    have hηpos : 0 < η := by positivity
    have htay := (taylor_charFun_two (hident i0).aemeasurable_fst h0 h1).def hηpos
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp htay
    -- smallness radius for `c * t`
    set r : ℝ := min (min (δ / 2) 1) (Real.sqrt (4 * η)) with hr
    have hrpos : 0 < r := by
      simp only [hr]
      exact lt_min (lt_min (by positivity) one_pos) (Real.sqrt_pos.mpr (by positivity))
    have hev1 := hmax (r / (|t| + 1)) (by positivity)
    have hev2 : ∀ᶠ n in atTop, ∑ i ∈ s n, c n i ^ 2 ≤ |σ2| + 1 := by
      have := hsum.eventually (gt_mem_nhds (show σ2 < |σ2| + 1 by
        linarith [le_abs_self σ2]))
      exact this.mono fun n hn => hn.le
    filter_upwards [hev1, hev2] with n hn1 hn2
    rw [dist_zero_right]
    -- per-term bound
    have hsmall : ∀ i ∈ s n, |c n i * t| ≤ r := by
      intro i hi
      have h1' := hn1 i hi
      rw [abs_mul]
      have ht1 : 0 < |t| + 1 := by positivity
      calc |c n i| * |t| ≤ (r / (|t| + 1)) * (|t| + 1) := by
            apply mul_le_mul h1' (by linarith) (abs_nonneg _) (by positivity)
        _ = r := by field_simp
    have hterm : ∀ i ∈ s n, ‖φ (c n i * t) - b n i‖ ≤ 2 * η * (c n i * t) ^ 2 := by
      intro i hi
      have hsi := hsmall i hi
      set u : ℝ := c n i * t with hu
      have hu1 : |u| ≤ δ / 2 := hsi.trans ((min_le_left _ _).trans (min_le_left _ _))
      have hu2 : |u| ≤ 1 := hsi.trans ((min_le_left _ _).trans (min_le_right _ _))
      have hu3 : |u| ≤ Real.sqrt (4 * η) := hsi.trans (min_le_right _ _)
      have hu3' : u ^ 2 ≤ 4 * η := by
        have := sq_le_sq' (by linarith [abs_nonneg u, neg_abs_le u, le_abs_self u]) (le_abs_self u |>.trans hu3)
        calc u ^ 2 = |u| ^ 2 := (sq_abs u).symm
          _ ≤ Real.sqrt (4 * η) ^ 2 := by
              exact pow_le_pow_left₀ (abs_nonneg u) hu3 2
          _ = 4 * η := Real.sq_sqrt (by positivity)
      have hu2' : u ^ 2 ≤ 2 := by nlinarith [abs_nonneg u, sq_abs u]
      have hT := hδ (show dist u 0 < δ by
        rw [Real.dist_eq, sub_zero]; linarith)
      have hE := norm_one_sub_sub_exp_le u hu2'
      have hsplit : φ u - b n i = (φ u - (1 - (u : ℂ) ^ 2 / 2))
          + ((1 - (u : ℂ) ^ 2 / 2) - ((Real.exp (-u ^ 2 / 2) : ℝ) : ℂ)) := by
        simp only [hb, hu]; ring
      rw [hsplit]
      have hT' : ‖φ u - (1 - (u : ℂ) ^ 2 / 2)‖ ≤ η * u ^ 2 := by
        have := hT
        simp only [hφ] at this ⊢
        convert this using 2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg u)]
      calc _ ≤ ‖φ u - (1 - (u : ℂ) ^ 2 / 2)‖
            + ‖(1 - (u : ℂ) ^ 2 / 2) - ((Real.exp (-u ^ 2 / 2) : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ η * u ^ 2 + u ^ 2 * u ^ 2 / 4 := add_le_add hT' hE
        _ ≤ η * u ^ 2 + u ^ 2 * (4 * η) / 4 := by
            gcongr
        _ = 2 * η * u ^ 2 := by ring
    have hnormφ : ∀ i ∈ s n, ‖φ (c n i * t)‖ ≤ 1 := fun i _ => by
      simp only [hφ]
      have : IsProbabilityMeasure (P.map (X i0)) :=
        Measure.isProbabilityMeasure_map (hident i0).aemeasurable_fst
      exact norm_charFun_le_one _
    have hnormb : ∀ i ∈ s n, ‖b n i‖ ≤ 1 := fun i _ => by
      simp only [hb]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have := sq_nonneg (c n i * t)
      linarith
    calc ‖∏ i ∈ s n, φ (c n i * t) - ∏ i ∈ s n, b n i‖
        ≤ ∑ i ∈ s n, ‖φ (c n i * t) - b n i‖ :=
          norm_prod_sub_prod_le _ _ _ hnormφ hnormb
      _ ≤ ∑ i ∈ s n, 2 * η * (c n i * t) ^ 2 := Finset.sum_le_sum hterm
      _ = 2 * η * t ^ 2 * ∑ i ∈ s n, c n i ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ ≤ 2 * η * t ^ 2 * (|σ2| + 1) := by gcongr
      _ < ε := by
          have : 2 * η * t ^ 2 * (|σ2| + 1) ≤ ε / 2 := by
            rw [hη, hK]
            have hA : 0 ≤ |σ2| := abs_nonneg _
            rw [div_eq_mul_inv]
            have hpos : 0 < 4 * ((t ^ 2 + 1) * (|σ2| + 2)) := by positivity
            rw [show 2 * (ε * (4 * ((t ^ 2 + 1) * (|σ2| + 2)))⁻¹) * t ^ 2 * (|σ2| + 1)
                = ε * (2 * t ^ 2 * (|σ2| + 1)) / (4 * ((t ^ 2 + 1) * (|σ2| + 2))) by
                  field_simp]
            rw [div_le_div_iff₀ hpos (by norm_num)]
            nlinarith [sq_nonneg t, hε.le, mul_nonneg hε.le (sq_nonneg t),
              mul_nonneg (mul_nonneg hε.le (sq_nonneg t)) hA]
          linarith
  have := hdiff.add hlimb
  simpa using this

/-- Cramér–Wold / Lévy bridge: convergence of the characteristic functions of all linear
combinations gives convergence in distribution of `Fin m → ℝ`-valued random vectors. -/
theorem tendstoInDistribution_of_charFun_linear {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {m : ℕ}
    (V : ℕ → Ω → (Fin m → ℝ)) (Z : Ω' → (Fin m → ℝ))
    (hV : ∀ n, AEMeasurable (V n) P) (hZ : AEMeasurable Z Q)
    (h : ∀ t : Fin m → ℝ, Tendsto
      (fun n => ∫ a, Complex.exp (((∑ j, t j * V n a j : ℝ) : ℂ) * Complex.I) ∂P) atTop
        (𝓝 (∫ b, Complex.exp (((∑ j, t j * Z b j : ℝ) : ℂ) * Complex.I) ∂Q))) :
    TendstoInDistribution V atTop Z (fun _ => P) Q := by
  let e : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m) := WithLp.toLp 2
  have he : Measurable e := WithLp.measurable_toLp 2 _
  have hinner : ∀ (v : Fin m → ℝ) (t : EuclideanSpace ℝ (Fin m)),
      (inner ℝ (e v) t : ℝ) = ∑ j, (WithLp.ofLp t) j * v j := by
    intro v t
    simp only [e, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  have hE : TendstoInDistribution (fun n a => e (V n a)) atTop (fun b => e (Z b))
      (fun _ => P) Q :=
    { forall_aemeasurable := fun n => he.comp_aemeasurable (hV n)
      aemeasurable_limit := he.comp_aemeasurable hZ
      tendsto := by
        refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
        simp only [ProbabilityMeasure.coe_mk]
        rw [charFun_apply, integral_map (φ := fun b => e (Z b)) (he.comp_aemeasurable hZ)
          (by fun_prop)]
        have hn : ∀ n, charFun (P.map (fun a => e (V n a))) t
            = ∫ a, Complex.exp (((∑ j, (WithLp.ofLp t) j * V n a j : ℝ) : ℂ) * Complex.I) ∂P := by
          intro n
          rw [charFun_apply, integral_map (φ := fun a => e (V n a)) (he.comp_aemeasurable (hV n))
            (by fun_prop)]
          simp_rw [hinner]
        simp_rw [hn, hinner]
        exact h (WithLp.ofLp t) }
  have hc : Continuous (WithLp.ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ)) :=
    PiLp.continuous_ofLp 2 _
  exact hE.continuous_comp hc

/-- Multivariate weighted CLT: jointly, the weighted sums `∑ c_{j,n,i} X_i` converge in law to
any random vector `Z` with characteristic function `exp(-tᵀΣt/2)`, where `Σ` is the limit of
the empirical covariances `∑_i c_{j,n,i} c_{j',n,i}`. -/
theorem tendstoInDistribution_weighted_vec {Ω Ω' ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {X : ι → Ω → ℝ} (hmeas : ∀ i, AEMeasurable (X i) P)
    (hindep : iIndepFun X P) (i0 : ι) (hident : ∀ i, IdentDistrib (X i) (X i0) P P)
    (h0 : P[X i0] = 0) (h1 : P[X i0 ^ 2] = 1) {m : ℕ}
    (s : ℕ → Finset ι) (c : Fin m → ℕ → ι → ℝ) (S : Fin m → Fin m → ℝ)
    (hmax : ∀ j, ∀ ε > 0, ∀ᶠ n in atTop, ∀ i ∈ s n, |c j n i| ≤ ε)
    (hcov : ∀ j j', Tendsto (fun n => ∑ i ∈ s n, c j n i * c j' n i) atTop (𝓝 (S j j')))
    (Z : Ω' → Fin m → ℝ) (hZ : AEMeasurable Z Q)
    (hZlaw : ∀ t : Fin m → ℝ,
      ∫ b, Complex.exp (((∑ j, t j * Z b j : ℝ) : ℂ) * Complex.I) ∂Q
        = ((Real.exp (-(∑ j, ∑ j', t j * t j' * S j j') / 2) : ℝ) : ℂ)) :
    TendstoInDistribution (fun n a j => ∑ i ∈ s n, c j n i * X i a) atTop Z
      (fun _ => P) Q := by
  have hVm : ∀ n, AEMeasurable (fun a j => ∑ i ∈ s n, c j n i * X i a) P := by
    intro n
    exact aemeasurable_pi_lambda _ fun j =>
      Finset.aemeasurable_fun_sum _ fun i _ => (hmeas i).const_mul _
  refine tendstoInDistribution_of_charFun_linear _ Z hVm hZ fun t => ?_
  rw [hZlaw t]
  set d : ℕ → ι → ℝ := fun n i => ∑ j, t j * c j n i with hd
  have hrw : ∀ n a, (∑ j, t j * ∑ i ∈ s n, c j n i * X i a) = ∑ i ∈ s n, d n i * X i a := by
    intro n a
    simp only [hd, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hchar : ∀ n, ∫ a, Complex.exp (((∑ j, t j * ∑ i ∈ s n, c j n i * X i a : ℝ) : ℂ)
      * Complex.I) ∂P = charFun (P.map (fun a => ∑ i ∈ s n, d n i * X i a)) 1 := by
    intro n
    rw [charFun_apply_real, integral_map (Finset.aemeasurable_fun_sum _ fun i _ =>
      (hmeas i).const_mul _) (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hrw]
    push_cast
    ring_nf
  simp_rw [hchar]
  have hmaxd : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i ∈ s n, |d n i| ≤ ε := by
    intro ε hε
    set T : ℝ := ∑ j, |t j| + 1 with hT
    have hTpos : 0 < T := by positivity
    have hall : ∀ᶠ n in atTop, ∀ j, ∀ i ∈ s n, |c j n i| ≤ ε / T :=
      Filter.eventually_all.2 fun j => hmax j (ε / T) (by positivity)
    filter_upwards [hall] with n hn i hi
    calc |d n i| ≤ ∑ j, |t j * c j n i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |t j| * (ε / T) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hn j i hi) (abs_nonneg _)
      _ = (∑ j, |t j|) * (ε / T) := by rw [Finset.sum_mul]
      _ ≤ T * (ε / T) := by
          apply mul_le_mul_of_nonneg_right (by rw [hT]; linarith) (by positivity)
      _ = ε := by field_simp
  have hsumd : Tendsto (fun n => ∑ i ∈ s n, d n i ^ 2) atTop
      (𝓝 (∑ j, ∑ j', t j * t j' * S j j')) := by
    have hexp : ∀ n, ∑ i ∈ s n, d n i ^ 2
        = ∑ j, ∑ j', t j * t j' * ∑ i ∈ s n, c j n i * c j' n i := by
      intro n
      simp only [hd, sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    simp_rw [hexp]
    exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun j' _ =>
      (hcov j j').const_mul _
  have := charFun_weighted_sum_tendsto hmeas hindep i0 hident h0 h1 s d _ hmaxd hsumd 1
  simpa using this

open IntermediateDisorder.PointToLine in
/-- The white noise on finitely many strip sets is a centred Gaussian vector with covariance
`|A_j ∩ A_j'|`: closed form of the characteristic function of a linear combination. -/
theorem whiteNoise_charFun {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    [IsProbabilityMeasure Q] {W : Set (ℝ × ℝ) → Ω' → ℝ} (hW : IsWhiteNoise W Q) {m : ℕ}
    (A : Fin m → FiniteStripSet) (t : Fin m → ℝ) :
    ∫ b, Complex.exp (((∑ j, t j * W (A j).1 b : ℝ) : ℂ) * Complex.I) ∂Q
      = ((Real.exp (-(∑ j, ∑ j', t j * t j' * (volume ((A j).1 ∩ (A j').1)).toReal) / 2) : ℝ)
          : ℂ) := by
  set Y : Ω' → ℝ := fun b => ∑ j, t j * W (A j).1 b with hY
  have hG : HasGaussianLaw Y Q := by
    have h := ((hW.gaussian.comp_right A).smul t).hasGaussianLaw_fun_sum (I := Finset.univ)
    have e : Y = fun ω => ∑ i, t i • ((fun A : FiniteStripSet => W A.1) ∘ A) i ω := by
      funext b; simp [hY, smul_eq_mul]
    rw [e]; exact h
  have hL : ∀ j, MemLp (W (A j).1) 2 Q := fun j =>
    (hW.gaussian.hasGaussianLaw_eval (A j)).memLp_two
  have hYm : AEMeasurable Y Q := hG.aemeasurable
  have hmean : Q[Y] = 0 := by
    simp only [hY]
    rw [integral_finsetSum _ fun j _ => ((hL j).integrable one_le_two).const_mul _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, hW.mean_zero (A j), mul_zero]
  have hsq : ∫ b, Y b ^ 2 ∂Q
      = ∑ j, ∑ j', t j * t j' * (volume ((A j).1 ∩ (A j').1)).toReal := by
    have hexp : ∀ b, Y b ^ 2 = ∑ j, ∑ j', t j * t j' * (W (A j).1 b * W (A j').1 b) := by
      intro b
      simp only [hY, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      ring
    simp_rw [hexp]
    have hint : ∀ j j', Integrable (fun b => t j * t j' * (W (A j).1 b * W (A j').1 b)) Q :=
      fun j j' => ((hL j).integrable_mul (hL j')).const_mul _
    have hint2 : ∀ j, Integrable (fun b => ∑ j', t j * t j' * (W (A j).1 b * W (A j').1 b)) Q :=
      fun j => integrable_finsetSum _ fun j' _ => hint j j'
    rw [integral_finsetSum _ fun j _ => hint2 j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun j' _ => hint j j']
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [integral_const_mul, hW.covariance (A j) (A j')]
  have hvar : Var[Y; Q] = ∑ j, ∑ j', t j * t j' * (volume ((A j).1 ∩ (A j').1)).toReal := by
    rw [variance_of_integral_eq_zero hYm hmean, hsq]
  have hchar : ∫ b, Complex.exp (((Y b : ℝ) : ℂ) * Complex.I) ∂Q = charFun (Q.map Y) 1 := by
    rw [charFun_apply_real, integral_map hYm (by fun_prop)]
    simp
  rw [show (fun b => Complex.exp (((∑ j, t j * W (A j).1 b : ℝ) : ℂ) * Complex.I))
      = fun b => Complex.exp (((Y b : ℝ) : ℂ) * Complex.I) from rfl, hchar,
    hG.map_eq_gaussianReal, charFun_gaussianReal, hmean]
  have hv0 : 0 ≤ Var[Y; Q] := variance_nonneg _ _
  rw [Real.coe_toNNReal _ hv0, hvar, Complex.ofReal_exp]
  push_cast
  ring_nf

open IntermediateDisorder.PointToLine in
/-- Weighted sums of a standard environment converge jointly to the white noise on finitely
many strip sets, as soon as the weights are uniformly small and their empirical covariances
converge to `|A_j ∩ A_j'|`. (The CLT core of AKQ Theorem 4.3.) -/
theorem env_tendstoInDistribution_whiteNoise {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {W : Set (ℝ × ℝ) → Ω' → ℝ} (hW : IsWhiteNoise W Q') {m : ℕ}
    (A : Fin m → FiniteStripSet) (s : ℕ → Finset (ℕ × ℤ)) (c : Fin m → ℕ → ℕ × ℤ → ℝ)
    (hmax : ∀ j, ∀ ε > 0, ∀ᶠ n in atTop, ∀ i ∈ s n, |c j n i| ≤ ε)
    (hcov : ∀ j j', Tendsto (fun n => ∑ i ∈ s n, c j n i * c j' n i) atTop
      (𝓝 (volume ((A j).1 ∩ (A j').1)).toReal)) :
    TendstoInDistribution (fun n a j => ∑ i ∈ s n, c j n i * ω i a) atTop
      (fun b j => W (A j).1 b) (fun _ => Q) Q' := by
  have hZ : AEMeasurable (fun b j => W (A j).1 b) Q' :=
    aemeasurable_pi_lambda _ fun j => hW.gaussian.aemeasurable (A j)
  have h1 : Q[ω (1, 0) ^ 2] = 1 := by
    have := hω.second_moment
    simpa [Pi.pow_apply] using this
  exact tendstoInDistribution_weighted_vec (fun i => (hω.measurable i).aemeasurable) hω.indep
    (1, 0) hω.identDistrib hω.mean_zero h1 s c
    (fun j j' => (volume ((A j).1 ∩ (A j').1)).toReal) hmax hcov _ hZ
    (fun t => whiteNoise_charFun hW A t)

end IDLind



/-! L1a for ead56ca5: first-order cell weights of a strip box have vanishing maximum and
empirical covariances converging to the Lebesgue measure of the box intersection. -/

namespace IDL1a

open MeasureTheory Set Filter Topology

lemma vol_Ioc_add (u h : ℝ) (hh : 0 ≤ h) : volume.real (Ioc u (u + h)) = h := by
  rw [Real.volume_real_Ioc_of_le (by linarith)]; ring

lemma cell_err_abs_le (h u a b c d : ℝ) (hh : 0 < h) :
    |volume.real (Ioc a b ∩ Ioc u (u + h)) * volume.real (Ioc c d ∩ Ioc u (u + h)) / h
      - volume.real (Ioc a b ∩ Ioc c d ∩ Ioc u (u + h))| ≤ h := by
  have hT := vol_Ioc_add u h hh.le
  have hfin : volume (Ioc u (u + h)) ≠ ⊤ := measure_Ioc_lt_top.ne
  have h1 : volume.real (Ioc a b ∩ Ioc u (u + h)) ≤ h :=
    (measureReal_mono inter_subset_right hfin).trans hT.le
  have h2 : volume.real (Ioc c d ∩ Ioc u (u + h)) ≤ h :=
    (measureReal_mono inter_subset_right hfin).trans hT.le
  have h3 : volume.real (Ioc a b ∩ Ioc c d ∩ Ioc u (u + h)) ≤ h :=
    (measureReal_mono inter_subset_right hfin).trans hT.le
  have p1 : 0 ≤ volume.real (Ioc a b ∩ Ioc u (u + h)) := measureReal_nonneg
  have p2 : 0 ≤ volume.real (Ioc c d ∩ Ioc u (u + h)) := measureReal_nonneg
  have p3 : 0 ≤ volume.real (Ioc a b ∩ Ioc c d ∩ Ioc u (u + h)) := measureReal_nonneg
  have q1 : 0 ≤ volume.real (Ioc a b ∩ Ioc u (u + h)) *
      volume.real (Ioc c d ∩ Ioc u (u + h)) / h := by positivity
  have q2 : volume.real (Ioc a b ∩ Ioc u (u + h)) *
      volume.real (Ioc c d ∩ Ioc u (u + h)) / h ≤ h := by
    rw [div_le_iff₀ hh]; nlinarith
  rw [abs_le]; constructor <;> linarith

lemma cell_err_eq_zero (h u a b c d : ℝ) (hh : 0 < h) (ha : a ∉ Ioc u (u + h))
    (hb : b ∉ Ioc u (u + h)) :
    volume.real (Ioc a b ∩ Ioc u (u + h)) * volume.real (Ioc c d ∩ Ioc u (u + h)) / h
      - volume.real (Ioc a b ∩ Ioc c d ∩ Ioc u (u + h)) = 0 := by
  by_cases hI : Ioc u (u + h) ⊆ Ioc a b
  · rw [inter_eq_right.mpr hI, inter_right_comm, inter_eq_right.mpr hI, vol_Ioc_add u h hh.le,
      inter_comm (Ioc u (u + h)), mul_div_cancel_left₀ _ hh.ne', sub_self]
  · have hE : Ioc a b ∩ Ioc u (u + h) = ∅ := by
      rw [Ioc_subset_Ioc_iff (by linarith)] at hI
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at ha hb
      rw [Ioc_inter_Ioc, Ioc_eq_empty_iff, not_lt]
      rcases ha with ha | ha
      · rcases hb with hb | hb
        · exact (min_le_left _ _).trans (hb.trans (le_max_right _ _))
        · exact absurd ⟨hb.le, ha⟩ hI
      · exact ((min_le_right _ _).trans ha.le).trans (le_max_left _ _)
    have hE' : Ioc a b ∩ Ioc c d ∩ Ioc u (u + h) = ∅ := by
      rw [inter_right_comm, hE, empty_inter]
    rw [hE, hE']; simp

/-- One-dimensional tiling estimate: for pairwise disjoint cells of length `h` covering
`I ∩ J`, the normalised sum of products of overlaps is `|I ∩ J|` up to `2h`. -/
theorem tiling_sum_bound {ι : Type*} (S : Finset ι) (u : ι → ℝ) (h a b c d : ℝ) (hh : 0 < h)
    (hdisj : (S : Set ι).PairwiseDisjoint (fun x => Ioc (u x) (u x + h)))
    (hcov : Ioc a b ∩ Ioc c d ⊆ ⋃ x ∈ S, Ioc (u x) (u x + h)) :
    |∑ x ∈ S, volume.real (Ioc a b ∩ Ioc (u x) (u x + h)) *
        volume.real (Ioc c d ∩ Ioc (u x) (u x + h)) / h
      - volume.real (Ioc a b ∩ Ioc c d)| ≤ 2 * h := by
  classical
  have htile : volume.real (Ioc a b ∩ Ioc c d) =
      ∑ x ∈ S, volume.real (Ioc a b ∩ Ioc c d ∩ Ioc (u x) (u x + h)) := by
    rw [← measureReal_biUnion_finset
      (fun x hx y hy hxy => (hdisj hx hy hxy).mono inter_subset_right inter_subset_right)
      (fun x _ => (measurableSet_Ioc.inter measurableSet_Ioc).inter measurableSet_Ioc)
      (fun x _ => ((measure_mono inter_subset_right).trans_lt measure_Ioc_lt_top).ne)]
    congr 1; rw [← inter_iUnion₂]; exact (inter_eq_left.mpr hcov).symm
  rw [htile, ← Finset.sum_sub_distrib]
  have hcard : ∀ p : ℝ, (S.filter (fun x => p ∈ Ioc (u x) (u x + h))).card ≤ 1 := by
    intro p; rw [Finset.card_le_one]; intro x hx y hy
    simp only [Finset.mem_filter] at hx hy
    by_contra hxy
    exact (Set.disjoint_left.mp (hdisj hx.1 hy.1 hxy)) hx.2 hy.2
  have hcard2 : (S.filter (fun x => a ∈ Ioc (u x) (u x + h) ∨ b ∈ Ioc (u x) (u x + h))).card
      ≤ 2 := by
    rw [Finset.filter_or]
    exact (Finset.card_union_le _ _).trans (by have := hcard a; have := hcard b; omega)
  calc _ ≤ ∑ x ∈ S, |volume.real (Ioc a b ∩ Ioc (u x) (u x + h)) *
          volume.real (Ioc c d ∩ Ioc (u x) (u x + h)) / h
          - volume.real (Ioc a b ∩ Ioc c d ∩ Ioc (u x) (u x + h))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ S.filter (fun x => a ∈ Ioc (u x) (u x + h) ∨ b ∈ Ioc (u x) (u x + h)),
          |volume.real (Ioc a b ∩ Ioc (u x) (u x + h)) *
          volume.real (Ioc c d ∩ Ioc (u x) (u x + h)) / h
          - volume.real (Ioc a b ∩ Ioc c d ∩ Ioc (u x) (u x + h))| := by
        refine (Finset.sum_filter_of_ne ?_).symm
        intro x _ hx
        by_contra hn
        push Not at hn
        exact hx (by rw [cell_err_eq_zero h (u x) a b c d hh hn.1 hn.2, abs_zero])
    _ ≤ ∑ x ∈ S.filter (fun x => a ∈ Ioc (u x) (u x + h) ∨ b ∈ Ioc (u x) (u x + h)), h :=
        Finset.sum_le_sum (fun x _ => cell_err_abs_le h (u x) a b c d hh)
    _ = (S.filter (fun x => a ∈ Ioc (u x) (u x + h) ∨ b ∈ Ioc (u x) (u x + h))).card * h := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * h := by
        gcongr
        exact_mod_cast hcard2

/-- Time cell `((i-1)/n, i/n]` and space cell `((x-1)/√n, (x+1)/√n]` (the factors of `cell`). -/
noncomputable def tCell (n i : ℕ) : Set ℝ := Ioc (((i : ℝ) - 1) / n) ((i : ℝ) / n)

noncomputable def xCell (n : ℕ) (x : ℤ) : Set ℝ :=
  Ioc (((x : ℝ) - 1) / Real.sqrt n) (((x : ℝ) + 1) / Real.sqrt n)

lemma tCell_eq (n i : ℕ) :
    tCell n i = Ioc (((i : ℝ) - 1) / n) (((i : ℝ) - 1) / n + 1 / n) := by
  unfold tCell; congr 1; ring

lemma xCell_eq (n : ℕ) (x : ℤ) :
    xCell n x = Ioc (((x : ℝ) - 1) / Real.sqrt n) (((x : ℝ) - 1) / Real.sqrt n + 2 / Real.sqrt n) := by
  unfold xCell; congr 1; ring

/-- First-order weight of the box `(a,b] × (c,d]` at site `(i,x)`:
`√2 n^{-3/4} · cellAverage = n^{3/4}/√2 · |A ∩ cell(i,x)|`, with the parity constraint. -/
noncomputable def wt (n : ℕ) (a b c d : ℝ) (p : ℕ × ℤ) : ℝ :=
  if Even ((p.1 : ℤ) - p.2) then
    (n : ℝ) ^ (3 / 4 : ℝ) / Real.sqrt 2 *
      (volume.real (Ioc a b ∩ tCell n p.1) * volume.real (Ioc c d ∩ xCell n p.2))
  else 0

/-- The finite set of sites carrying the weights of boxes inside `[0,1] × [-L, L]`. -/
noncomputable def supp (n : ℕ) (L : ℝ) : Finset (ℕ × ℤ) :=
  Finset.Icc 1 n ×ˢ Finset.Icc (-((⌈L * Real.sqrt n⌉₊ : ℤ) + 1)) ((⌈L * Real.sqrt n⌉₊ : ℤ) + 1)

lemma rpow34_mul_self (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) = n * Real.sqrt n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_add hpos, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hpos.le (by norm_num)]
  norm_num

lemma rpow34_div (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (3 / 4 : ℝ) / (n * Real.sqrt n) = (n : ℝ) ^ (-(3 / 4) : ℝ) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hpos.le (by norm_num), ← Real.rpow_sub hpos]
  norm_num

lemma wt_nonneg (n : ℕ) (a b c d : ℝ) (p : ℕ × ℤ) : 0 ≤ wt n a b c d p := by
  unfold wt; split_ifs
  · have : 0 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have : 0 ≤ volume.real (Ioc a b ∩ tCell n p.1) := measureReal_nonneg
    have : 0 ≤ volume.real (Ioc c d ∩ xCell n p.2) := measureReal_nonneg
    positivity
  · exact le_refl 0

lemma wt_le (n : ℕ) (hn : 0 < n) (a b c d : ℝ) (p : ℕ × ℤ) :
    wt n a b c d p ≤ Real.sqrt 2 * (n : ℝ) ^ (-(3 / 4) : ℝ) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hpos
  have h2 : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hT : volume.real (Ioc a b ∩ tCell n p.1) ≤ 1 / n := by
    rw [tCell_eq]
    exact (measureReal_mono inter_subset_right measure_Ioc_lt_top.ne).trans
      (vol_Ioc_add _ _ (by positivity)).le
  have hX : volume.real (Ioc c d ∩ xCell n p.2) ≤ 2 / Real.sqrt n := by
    rw [xCell_eq]
    exact (measureReal_mono inter_subset_right measure_Ioc_lt_top.ne).trans
      (vol_Ioc_add _ _ (by positivity)).le
  have hT0 : 0 ≤ volume.real (Ioc a b ∩ tCell n p.1) := measureReal_nonneg
  have hX0 : 0 ≤ volume.real (Ioc c d ∩ xCell n p.2) := measureReal_nonneg
  have hr : 0 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg hpos.le _
  have key : Real.sqrt 2 * (n : ℝ) ^ (-(3 / 4) : ℝ) =
      (n : ℝ) ^ (3 / 4 : ℝ) / Real.sqrt 2 * (1 / n * (2 / Real.sqrt n)) := by
    rw [← rpow34_div n hn]
    have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    linarith [this]
  rw [key]
  unfold wt; split_ifs
  · gcongr
  · positivity

theorem wt_max (L a b c d : ℝ) : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ p ∈ supp n L,
    |wt n a b c d p| ≤ ε := by
  intro ε hε
  have ht : Tendsto (fun n : ℕ => Real.sqrt 2 * (n : ℝ) ^ (-(3 / 4) : ℝ)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
      tendsto_natCast_atTop_atTop).const_mul (Real.sqrt 2)
    simpa using this
  filter_upwards [ht.eventually (ge_mem_nhds hε), eventually_ge_atTop 1] with n hn hn1 p _
  rw [abs_of_nonneg (wt_nonneg n a b c d p)]
  exact (wt_le n hn1 a b c d p).trans hn

lemma t_disj (n : ℕ) : ((Finset.Icc 1 n : Finset ℕ) : Set ℕ).PairwiseDisjoint
    (fun i : ℕ => Ioc (((i : ℝ) - 1) / n) (((i : ℝ) - 1) / n + 1 / n)) := by
  intro i _ j _ hij
  show Disjoint _ _
  have key : ∀ i j : ℕ, i < j → ((i : ℝ) - 1) / n + 1 / n ≤ ((j : ℝ) - 1) / n := by
    intro i j h
    have h' : ((i + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast h
    push_cast at h'
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  rcases lt_or_gt_of_ne hij with h | h
  · exact Ioc_disjoint_Ioc_of_le (key i j h)
  · exact (Ioc_disjoint_Ioc_of_le (key j i h)).symm

lemma t_cov (n : ℕ) (hn : 1 ≤ n) (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    Ioc a b ∩ Ioc a' b' ⊆
      ⋃ i ∈ Finset.Icc 1 n, Ioc (((i : ℝ) - 1) / n) (((i : ℝ) - 1) / n + 1 / n) := by
  rintro t ⟨⟨ht1, ht2⟩, _⟩
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 < t := by linarith
  simp only [mem_iUnion, Finset.mem_Icc, mem_Ioc, exists_prop]
  refine ⟨⌈(n : ℝ) * t⌉₊, ⟨Nat.ceil_pos.mpr (by positivity), Nat.ceil_le.mpr (by nlinarith)⟩,
    ?_, ?_⟩
  · rw [div_lt_iff₀ hpos]
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) * t)
    linarith
  · rw [← add_div, le_div_iff₀ hpos]
    have := Nat.le_ceil ((n : ℝ) * t)
    linarith

lemma x_disj (n i : ℕ) (X : Finset ℤ) :
    ((X.filter (fun x : ℤ => Even ((i : ℤ) - x)) : Finset ℤ) : Set ℤ).PairwiseDisjoint
      (fun x : ℤ => Ioc (((x : ℝ) - 1) / Real.sqrt n)
        (((x : ℝ) - 1) / Real.sqrt n + 2 / Real.sqrt n)) := by
  intro x hx y hy hxy
  show Disjoint _ _
  simp only [Finset.coe_filter, mem_setOf_eq] at hx hy
  have key : ∀ x y : ℤ, x < y → Even (y - x) →
      ((x : ℝ) - 1) / Real.sqrt n + 2 / Real.sqrt n ≤ ((y : ℝ) - 1) / Real.sqrt n := by
    intro x y h hev
    obtain ⟨r, hr⟩ := hev
    have h2 : x + 2 ≤ y := by omega
    have h2' : ((x + 2 : ℤ) : ℝ) ≤ y := by exact_mod_cast h2
    push_cast at h2'
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have hev : Even (y - x) := by
    have := hx.2.sub hy.2
    rwa [show ((i : ℤ) - x) - (i - y) = y - x by ring] at this
  rcases lt_or_gt_of_ne hxy with h | h
  · exact Ioc_disjoint_Ioc_of_le (key x y h hev)
  · refine (Ioc_disjoint_Ioc_of_le (key y x h ?_)).symm
    have := hev.neg; rwa [neg_sub] at this

lemma x_cov (n : ℕ) (hn : 1 ≤ n) (i : ℕ) (L c d c' d' : ℝ) (hc : -L ≤ c) (hd : d ≤ L) :
    Ioc c d ∩ Ioc c' d' ⊆
      ⋃ x ∈ (Finset.Icc (-((⌈L * Real.sqrt n⌉₊ : ℤ) + 1)) ((⌈L * Real.sqrt n⌉₊ : ℤ) + 1)).filter
          (fun x : ℤ => Even ((i : ℤ) - x)),
        Ioc (((x : ℝ) - 1) / Real.sqrt n) (((x : ℝ) - 1) / Real.sqrt n + 2 / Real.sqrt n) := by
  rintro y ⟨⟨hy1, hy2⟩, _⟩
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hm1 := Int.le_ceil ((y * Real.sqrt n - i - 1) / 2)
  have hm2 := Int.ceil_lt_add_one ((y * Real.sqrt n - i - 1) / 2)
  have hL := Nat.le_ceil (L * Real.sqrt n)
  have hyL : y * Real.sqrt n ≤ L * Real.sqrt n := mul_le_mul_of_nonneg_right (by linarith) hs.le
  have hyL' : -(L * Real.sqrt n) < y * Real.sqrt n := by nlinarith
  simp only [mem_iUnion, Finset.mem_filter, Finset.mem_Icc, mem_Ioc, exists_prop]
  refine ⟨2 * ⌈(y * Real.sqrt n - i - 1) / 2⌉ + i, ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · have : ((-((⌈L * Real.sqrt n⌉₊ : ℤ) + 1) : ℤ) : ℝ) ≤
        ((2 * ⌈(y * Real.sqrt n - i - 1) / 2⌉ + i : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  · have : ((2 * ⌈(y * Real.sqrt n - i - 1) / 2⌉ + i : ℤ) : ℝ) ≤
        (((⌈L * Real.sqrt n⌉₊ : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  · exact ⟨-⌈(y * Real.sqrt n - i - 1) / 2⌉, by ring⟩
  · rw [div_lt_iff₀ hs]; push_cast; linarith
  · rw [← add_div, le_div_iff₀ hs]; push_cast; linarith

lemma wt_mul_sum (n : ℕ) (hn : 0 < n) (i : ℕ) (X : Finset ℤ) (a b c d a' b' c' d' : ℝ) :
    ∑ x ∈ X, wt n a b c d (i, x) * wt n a' b' c' d' (i, x) =
      (volume.real (Ioc a b ∩ Ioc (((i : ℝ) - 1) / n) (((i : ℝ) - 1) / n + 1 / n)) *
        volume.real (Ioc a' b' ∩ Ioc (((i : ℝ) - 1) / n) (((i : ℝ) - 1) / n + 1 / n)) / (1 / n)) *
      ∑ x ∈ X.filter (fun x : ℤ => Even ((i : ℤ) - x)),
        volume.real (Ioc c d ∩ Ioc (((x : ℝ) - 1) / Real.sqrt n)
            (((x : ℝ) - 1) / Real.sqrt n + 2 / Real.sqrt n)) *
          volume.real (Ioc c' d' ∩ Ioc (((x : ℝ) - 1) / Real.sqrt n)
            (((x : ℝ) - 1) / Real.sqrt n + 2 / Real.sqrt n)) / (2 / Real.sqrt n) := by
  classical
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [wt, tCell_eq, xCell_eq]
  split_ifs with hE
  · have hs := rpow34_mul_self n hn
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [div_div_eq_mul_div, div_div_eq_mul_div, div_one]
    calc _ = ((n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) / (Real.sqrt 2 * Real.sqrt 2) *
          ((volume.real (Ioc a b ∩ Ioc (((i : ℝ) - 1) / n) (((i : ℝ) - 1) / n + 1 / n)) *
            volume.real (Ioc a' b' ∩ Ioc (((i : ℝ) - 1) / n) (((i : ℝ) - 1) / n + 1 / n))) *
          (volume.real (Ioc c d ∩ Ioc (((x : ℝ) - 1) / Real.sqrt n)
            (((x : ℝ) - 1) / Real.sqrt n + 2 / Real.sqrt n)) *
          volume.real (Ioc c' d' ∩ Ioc (((x : ℝ) - 1) / Real.sqrt n)
            (((x : ℝ) - 1) / Real.sqrt n + 2 / Real.sqrt n)))) := by ring
      _ = _ := by rw [hs, h2]; ring
  · simp

theorem wt_cov (L a b c d a' b' c' d' : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hc : -L ≤ c)
    (hd : d ≤ L) :
    Tendsto (fun n : ℕ => ∑ p ∈ supp n L, wt n a b c d p * wt n a' b' c' d' p) atTop
      (𝓝 (volume.real ((Ioc a b ×ˢ Ioc c d) ∩ (Ioc a' b' ×ˢ Ioc c' d')))) := by
  classical
  have htarget : volume.real ((Ioc a b ×ˢ Ioc c d) ∩ (Ioc a' b' ×ˢ Ioc c' d')) =
      volume.real (Ioc a b ∩ Ioc a' b') * volume.real (Ioc c d ∩ Ioc c' d') := by
    rw [prod_inter_prod, Measure.volume_eq_prod, measureReal_prod_prod]
  rw [htarget]
  have hφ0 : 0 ≤ volume.real (Ioc c d ∩ Ioc c' d') := measureReal_nonneg
  have hbound : ∀ n : ℕ, 1 ≤ n →
      ‖∑ p ∈ supp n L, wt n a b c d p * wt n a' b' c' d' p -
          volume.real (Ioc a b ∩ Ioc a' b') * volume.real (Ioc c d ∩ Ioc c' d')‖ ≤
        (volume.real (Ioc a b ∩ Ioc a' b') + 2 * (1 / n)) * (2 * (2 / Real.sqrt n)) +
          volume.real (Ioc c d ∩ Ioc c' d') * (2 * (1 / n)) := by
    intro n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
    rw [Real.norm_eq_abs, supp, Finset.sum_product]
    rw [Finset.sum_congr rfl fun i _ => wt_mul_sum n hn i _ a b c d a' b' c' d']
    set P : ℕ → ℝ := fun i =>
      volume.real (Ioc a b ∩ Ioc (((i : ℝ) - 1) / n) (((i : ℝ) - 1) / n + 1 / n)) *
        volume.real (Ioc a' b' ∩ Ioc (((i : ℝ) - 1) / n) (((i : ℝ) - 1) / n + 1 / n)) / (1 / n)
      with hPdef
    set G : ℕ → ℝ := fun i =>
      ∑ x ∈ (Finset.Icc (-((⌈L * Real.sqrt n⌉₊ : ℤ) + 1)) ((⌈L * Real.sqrt n⌉₊ : ℤ) + 1)).filter
          (fun x : ℤ => Even ((i : ℤ) - x)),
        volume.real (Ioc c d ∩ Ioc (((x : ℝ) - 1) / Real.sqrt n)
            (((x : ℝ) - 1) / Real.sqrt n + 2 / Real.sqrt n)) *
          volume.real (Ioc c' d' ∩ Ioc (((x : ℝ) - 1) / Real.sqrt n)
            (((x : ℝ) - 1) / Real.sqrt n + 2 / Real.sqrt n)) / (2 / Real.sqrt n) with hGdef
    have hPt : |∑ i ∈ Finset.Icc 1 n, P i - volume.real (Ioc a b ∩ Ioc a' b')| ≤ 2 * (1 / n) :=
      tiling_sum_bound (Finset.Icc 1 n) (fun i : ℕ => ((i : ℝ) - 1) / n) (1 / n) a b a' b'
        (by positivity) (t_disj n) (t_cov n hn a b a' b' ha hb)
    have hGt : ∀ i : ℕ, |G i - volume.real (Ioc c d ∩ Ioc c' d')| ≤ 2 * (2 / Real.sqrt n) :=
      fun i => tiling_sum_bound _ (fun x : ℤ => ((x : ℝ) - 1) / Real.sqrt n) (2 / Real.sqrt n)
        c d c' d' (by positivity) (x_disj n i _) (x_cov n hn i L c d c' d' hc hd)
    have hP0 : ∀ i, 0 ≤ P i := fun i =>
      div_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) (by positivity)
    have e1 : ∑ i ∈ Finset.Icc 1 n, P i * G i -
        volume.real (Ioc a b ∩ Ioc a' b') * volume.real (Ioc c d ∩ Ioc c' d') =
        ∑ i ∈ Finset.Icc 1 n, P i * (G i - volume.real (Ioc c d ∩ Ioc c' d')) +
          volume.real (Ioc c d ∩ Ioc c' d') *
            (∑ i ∈ Finset.Icc 1 n, P i - volume.real (Ioc a b ∩ Ioc a' b')) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]; ring
    have e2 : |∑ i ∈ Finset.Icc 1 n, P i * (G i - volume.real (Ioc c d ∩ Ioc c' d'))| ≤
        (∑ i ∈ Finset.Icc 1 n, P i) * (2 * (2 / Real.sqrt n)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, abs_of_nonneg (hP0 i)]
      exact mul_le_mul_of_nonneg_left (hGt i) (hP0 i)
    have e3 : ∑ i ∈ Finset.Icc 1 n, P i ≤ volume.real (Ioc a b ∩ Ioc a' b') + 2 * (1 / n) := by
      have := (abs_le.mp hPt).2; linarith
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hφ0]
    have h4 : 0 ≤ 2 * (2 / Real.sqrt n) := by positivity
    have := mul_le_mul_of_nonneg_right e3 h4
    have := mul_le_mul_of_nonneg_left hPt hφ0
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun n : ℕ =>
      (volume.real (Ioc a b ∩ Ioc a' b') + 2 * (1 / (n : ℝ))) * (2 * (2 / Real.sqrt n)) +
        volume.real (Ioc c d ∩ Ioc c' d') * (2 * (1 / (n : ℝ))))
    (Eventually.of_forall fun n => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact hbound n hn
  · have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => 2 / Real.sqrt n) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have := ((tendsto_const_nhds (x := volume.real (Ioc a b ∩ Ioc a' b'))).add
      (h1.const_mul 2)).mul (h2.const_mul 2) |>.add
        ((h1.const_mul 2).const_mul (volume.real (Ioc c d ∩ Ioc c' d')))
    simpa using this

end IDL1a

/-! L1b: factorisation of the k-th U-statistic on products of time-separated boxes. -/

namespace IDL1b

open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory Set Filter Topology IDL1a

instance : SigmaFinite stripMeasure := by unfold stripMeasure; infer_instance

/-- The strip box `(a,b] × (c,d]`. -/
def box (a b c d : ℝ) : Set (ℝ × ℝ) := Ioc a b ×ˢ Ioc c d

lemma stripMeasure_prod (s t : Set ℝ) (hs : MeasurableSet s) :
    stripMeasure (s ×ˢ t) = volume (s ∩ Icc 0 1) * volume t := by
  rw [stripMeasure, Measure.prod_prod, Measure.restrict_apply hs]

lemma measurableSet_tCell (n i : ℕ) : MeasurableSet (tCell n i) := measurableSet_Ioc

lemma cell_eq_pi {k : ℕ} (n : ℕ) (I : Fin k → ℕ) (x : Fin k → ℤ) :
    cell n I x = univ.pi (fun j => tCell n (I j) ×ˢ xCell n (x j)) := rfl

lemma measurableSet_cell {k : ℕ} (n : ℕ) (I : Fin k → ℕ) (x : Fin k → ℤ) :
    MeasurableSet (cell n I x) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc.prod measurableSet_Ioc

lemma tCell_sub (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) : tCell n i ⊆ Icc 0 1 := by
  intro t ⟨h1, h2⟩
  have hpos : (0 : ℝ) < n := by exact_mod_cast (hi.trans hin)
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hin' : (i : ℝ) ≤ n := by exact_mod_cast hin
  constructor
  · exact le_trans (div_nonneg (by linarith) hpos.le) h1.le
  · exact h2.trans ((div_le_one hpos).mpr hin')

lemma kernelMeasure_cell {k : ℕ} (n : ℕ) (hn : 1 ≤ n) (I : Fin k → ℕ)
    (hI : ∀ j, 1 ≤ I j ∧ I j ≤ n) (x : Fin k → ℤ) :
    (kernelMeasure k (cell n I x)).toReal = ((1 / n) * (2 / Real.sqrt n)) ^ k := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
  rw [kernelMeasure, cell_eq_pi, Measure.pi_pi, ENNReal.toReal_prod]
  refine (Finset.prod_congr rfl fun j _ => ?_).trans
    (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  rw [stripMeasure_prod (tCell n (I j)) (xCell n (x j)) (measurableSet_tCell n (I j)),
    ENNReal.toReal_mul,
    inter_eq_left.mpr (tCell_sub n (I j) (hI j).1 (hI j).2), ← measureReal_def,
    ← measureReal_def, tCell_eq, xCell_eq, vol_Ioc_add _ _ (by positivity),
    vol_Ioc_add _ _ (by positivity)]

lemma cellAverage_box {k : ℕ} (n : ℕ) (hn : 1 ≤ n) (a b c d : Fin k → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, b j ≤ 1)
    (hB : MeasurableSet (univ.pi fun j => box (a j) (b j) (c j) (d j)))
    (hfin : kernelMeasure k (univ.pi fun j => box (a j) (b j) (c j) (d j)) ≠ ⊤)
    (I : Fin k → ℕ) (hI : ∀ j, 1 ≤ I j ∧ I j ≤ n) (x : Fin k → ℤ) :
    cellAverage (indicatorConstLp 2 hB hfin (1 : ℝ)) n I x =
      ∏ j, volume.real (Ioc (a j) (b j) ∩ tCell n (I j)) *
        volume.real (Ioc (c j) (d j) ∩ xCell n (x j)) / ((1 / n) * (2 / Real.sqrt n)) := by
  unfold cellAverage
  have hstrip : ∀ j, (stripMeasure (box (a j) (b j) (c j) (d j) ∩
      (tCell n (I j) ×ˢ xCell n (x j)))).toReal = volume.real (Ioc (a j) (b j) ∩ tCell n (I j)) *
        volume.real (Ioc (c j) (d j) ∩ xCell n (x j)) := by
    intro j
    have hsub : Ioc (a j) (b j) ∩ tCell n (I j) ⊆ Icc 0 1 := fun t ht =>
      ⟨(ha j).trans ht.1.1.le, ht.1.2.trans (hb j)⟩
    rw [box, prod_inter_prod, stripMeasure_prod (Ioc (a j) (b j) ∩ tCell n (I j)) _
      (measurableSet_Ioc.inter (measurableSet_tCell n (I j))),
      ENNReal.toReal_mul, inter_eq_left.mpr hsub]
    rfl
  have hBcell : (kernelMeasure k).real ((univ.pi fun j => box (a j) (b j) (c j) (d j)) ∩
      cell n I x) = ∏ j, volume.real (Ioc (a j) (b j) ∩ tCell n (I j)) *
        volume.real (Ioc (c j) (d j) ∩ xCell n (x j)) := by
    rw [measureReal_def, kernelMeasure, cell_eq_pi, ← pi_inter_distrib, Measure.pi_pi,
      ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact hstrip j
  rw [setIntegral_indicatorConstLp (measurableSet_cell n I x) hB hfin, smul_eq_mul, mul_one,
    kernelMeasure_cell n hn I hI x, hBcell, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, inv_mul_eq_div]

open scoped Classical in
lemma coeff_eq {k : ℕ} (n : ℕ) (hn : 1 ≤ n) (a b c d : Fin k → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, b j ≤ 1)
    (hB : MeasurableSet (univ.pi fun j => box (a j) (b j) (c j) (d j)))
    (hfin : kernelMeasure k (univ.pi fun j => box (a j) (b j) (c j) (d j)) ≠ ⊤)
    (I : Fin k → ℕ) (hI : ∀ j, 1 ≤ I j ∧ I j ≤ n) (x : Fin k → ℤ) :
    (n : ℝ) ^ (-(3 * (k : ℝ) / 4)) * (Real.sqrt 2 ^ k *
      cellAverage (indicatorConstLp 2 hB hfin (1 : ℝ)) n I x *
        (if ParityMatch I x then 1 else 0)) =
      ∏ j, wt n (a j) (b j) (c j) (d j) (I j, x j) := by
  classical
  rw [cellAverage_box n hn a b c d ha hb hB hfin I hI x]
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
  have hpow : (n : ℝ) ^ (-(3 * (k : ℝ) / 4)) = ∏ _j : Fin k, (n : ℝ) ^ (-(3 / 4) : ℝ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
      ← Real.rpow_mul hpos.le]
    ring_nf
  have hpar : (if ParityMatch I x then (1 : ℝ) else 0) =
      ∏ j, (if Even ((I j : ℤ) - x j) then (1 : ℝ) else 0) := by
    by_cases h : ParityMatch I x
    · rw [if_pos h]; exact (Finset.prod_eq_one fun j _ => if_pos (h j)).symm
    · rw [if_neg h]
      unfold ParityMatch at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)).symm
  have h2 : Real.sqrt 2 ^ k = ∏ _j : Fin k, Real.sqrt 2 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow, hpar, h2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqn : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hpos.le
  have h34 := rpow34_div n (by omega)
  unfold wt
  split_ifs with hE
  · rw [← h34]
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · simp

lemma prod_integrable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {k : ℕ}
    (Y : Fin k → Ω → ℝ) (hY : iIndepFun Y Q) (hm : ∀ j, Measurable (Y j))
    (hi : ∀ j, Integrable (Y j) Q) (s : Finset (Fin k)) : Integrable (∏ j ∈ s, Y j) Q := by
  have := hY.isProbabilityMeasure
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty]; exact integrable_const (1 : ℝ)
  | cons j s hj ih =>
    rw [Finset.prod_cons]
    exact IndepFun.integrable_mul (iIndepFun.indepFun_finsetProd_of_notMem hY hm hj).symm (hi j) ih

lemma envProduct_memLp {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) {k : ℕ} (I : Fin k → ℕ)
    (hI : Function.Injective I) (x : Fin k → ℤ) : MemLp (envProduct ω I x) 2 Q := by
  have hinj : Function.Injective (fun j => (I j, x j)) := fun j j' h => hI (congrArg Prod.fst h)
  have hmeas : Measurable (envProduct ω I x) := by
    unfold envProduct
    exact Finset.measurable_prod _ fun j _ => hω.measurable _
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  have hind : iIndepFun (fun j => fun z => ω (I j, x j) z ^ 2) Q :=
    (hω.indep.precomp hinj).comp (fun _ y => y ^ 2) (fun _ => measurable_id.pow_const 2)
  have := prod_integrable (fun j => fun z => ω (I j, x j) z ^ 2) hind
    (fun j => (hω.measurable _).pow_const 2)
    (fun j => ((hω.identDistrib (I j, x j)).memLp_iff.mpr hω.memLp_two).integrable_sq) Finset.univ
  convert this using 1
  funext z
  simp [envProduct, Finset.prod_pow]

lemma smul_envProductLp_ae {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) {k : ℕ} (C : ℝ) (I : Fin k → ℕ)
    (hI : Function.Injective I) (x : Fin k → ℤ) :
    ((C • envProductLp ω Q I x : Lp ℝ 2 Q) : Ω → ℝ) =ᵐ[Q] fun z => C * envProduct ω I x z := by
  have hm := envProduct_memLp hω I hI x
  unfold envProductLp
  rw [dif_pos hm]
  filter_upwards [Lp.coeFn_smul C (hm.toLp _), hm.coeFn_toLp] with z h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]

lemma vol_inter_Ioc_ne_zero {a b u v : ℝ} (h : volume.real (Ioc a b ∩ Ioc u v) ≠ 0) :
    a < v ∧ u < b := by
  by_contra hc
  apply h
  rw [Ioc_inter_Ioc, Ioc_eq_empty, measureReal_empty]
  rw [not_and_or, not_lt, not_lt] at hc
  rw [not_lt]
  rcases hc with hc | hc
  · exact (min_le_right _ _).trans (hc.trans (le_max_left _ _))
  · exact (min_le_left _ _).trans (hc.trans (le_max_right _ _))

lemma wt_ne_zero {n : ℕ} {a b c d : ℝ} {p : ℕ × ℤ} (h : wt n a b c d p ≠ 0) :
    ((p.1 : ℝ) - 1) / n < b ∧ a < (p.1 : ℝ) / n ∧
      c < ((p.2 : ℝ) + 1) / Real.sqrt n ∧ ((p.2 : ℝ) - 1) / Real.sqrt n < d := by
  unfold wt at h
  split_ifs at h with hE
  · have h1 : volume.real (Ioc a b ∩ tCell n p.1) ≠ 0 := fun h0 => h (by rw [h0]; ring)
    have h2 : volume.real (Ioc c d ∩ xCell n p.2) ≠ 0 := fun h0 => h (by rw [h0]; ring)
    obtain ⟨t1, t2⟩ := vol_inter_Ioc_ne_zero h1
    obtain ⟨x1, x2⟩ := vol_inter_Ioc_ne_zero h2
    exact ⟨t2, t1, x1, x2⟩
  · exact absurd rfl h

lemma mem_supp_of_wt {n : ℕ} (hn : 1 ≤ n) {L a b c d : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hc : -L ≤ c) (hd : d ≤ L) {p : ℕ × ℤ} (h : wt n a b c d p ≠ 0) : p ∈ supp n L := by
  obtain ⟨t1, t2, x1, x2⟩ := wt_ne_zero h
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
  have hL := Nat.le_ceil (L * Real.sqrt n)
  rw [div_lt_iff₀ hpos] at t1
  rw [lt_div_iff₀ hpos] at t2
  rw [lt_div_iff₀ hs] at x1
  rw [div_lt_iff₀ hs] at x2
  have hxL : d * Real.sqrt n ≤ L * Real.sqrt n := mul_le_mul_of_nonneg_right hd hs.le
  have hxL' : -L * Real.sqrt n ≤ c * Real.sqrt n := mul_le_mul_of_nonneg_right hc hs.le
  simp only [supp, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have : (0 : ℝ) < p.1 := by nlinarith
    exact_mod_cast this
  · have : (p.1 : ℝ) < n + 1 := by nlinarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  · have : ((-((⌈L * Real.sqrt n⌉₊ : ℤ) + 1) : ℤ) : ℝ) < p.2 := by push_cast; nlinarith
    exact_mod_cast this.le
  · have : (p.2 : ℝ) < (((⌈L * Real.sqrt n⌉₊ : ℤ) + 1 : ℤ) : ℝ) + 1 := by push_cast; nlinarith
    have h' : p.2 < ((⌈L * Real.sqrt n⌉₊ : ℤ) + 1) + 1 := by exact_mod_cast this
    omega

lemma wt_collision {n : ℕ} (hn : 1 ≤ n) {a b c d a' b' c' d' : ℝ}
    (hsep : b < a' ∨ b' < a) (hgap : ∀ u v : ℝ, (u = b ∧ v = a' ∨ u = b' ∧ v = a) → u < v →
      1 / (n : ℝ) < v - u)
    {p p' : ℕ × ℤ} (h : wt n a b c d p ≠ 0) (h' : wt n a' b' c' d' p' ≠ 0) (he : p.1 = p'.1) :
    False := by
  obtain ⟨t1, t2, -, -⟩ := wt_ne_zero h
  obtain ⟨t1', t2', -, -⟩ := wt_ne_zero h'
  rw [he] at t1 t2
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (p'.1 : ℝ) / n - ((p'.1 : ℝ) - 1) / n = 1 / n := by ring
  rcases hsep with hs | hs
  · have := hgap b a' (Or.inl ⟨rfl, rfl⟩) hs; linarith
  · have := hgap b' a (Or.inr ⟨rfl, rfl⟩) hs; linarith

open scoped Classical in
/-- L1b: on a product of time-separated strip boxes, the rescaled `k`-th U-statistic is, for `n`
large, the product of the first-order weighted environment sums of the boxes. -/
theorem uStatistic_box_factor {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) {k : ℕ} (L : ℝ) (a b c d : Fin k → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, b j ≤ 1) (hc : ∀ j, -L ≤ c j) (hd : ∀ j, d j ≤ L)
    (hsep : ∀ j j', j ≠ j' → b j < a j' ∨ b j' < a j)
    (hB : MeasurableSet (univ.pi fun j => box (a j) (b j) (c j) (d j)))
    (hfin : kernelMeasure k (univ.pi fun j => box (a j) (b j) (c j) (d j)) ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop,
      (((n : ℝ) ^ (-(3 * (k : ℝ) / 4)) •
          uStatistic ω Q n k (indicatorConstLp 2 hB hfin (1 : ℝ)) : Lp ℝ 2 Q) : Ω → ℝ)
        =ᵐ[Q] fun z => ∏ j, ∑ p ∈ supp n L, wt n (a j) (b j) (c j) (d j) p * ω p z := by
  have hev : ∀ᶠ n : ℕ in atTop, ∀ j j' : Fin k, b j < a j' → 1 / (n : ℝ) < a j' - b j := by
    rw [Filter.eventually_all]; intro j
    rw [Filter.eventually_all]; intro j'
    by_cases h : b j < a j'
    · filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat).eventually
        (gt_mem_nhds (sub_pos.mpr h))] with n hn _ using hn
    · exact Eventually.of_forall fun n h' => absurd h' h
  filter_upwards [eventually_ge_atTop 1, hev] with n hn hgapn
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hgap : ∀ j j' : Fin k, j ≠ j' → ∀ u v : ℝ,
      (u = b j ∧ v = a j' ∨ u = b j' ∧ v = a j) → u < v → 1 / (n : ℝ) < v - u := by
    intro j j' _ u v huv h
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hgapn j j' h
    · exact hgapn j' j h
  set X : Finset ℤ :=
    Finset.Icc (-((⌈L * Real.sqrt n⌉₊ : ℤ) + 1)) ((⌈L * Real.sqrt n⌉₊ : ℤ) + 1) with hX
  have hsupp : supp n L = Finset.Icc 1 n ×ˢ X := rfl
  have hterm : ∀ (i : Fin k → Fin n) (x : Fin k → ℤ),
      (n : ℝ) ^ (-(3 * (k : ℝ) / 4)) •
          uStatisticTerm ω Q n k (indicatorConstLp 2 hB hfin (1 : ℝ)) i x =
        (∏ j, wt n (a j) (b j) (c j) (d j) ((i j : ℕ) + 1, x j)) •
          envProductLp ω Q (timesOf i) x := by
    intro i x
    unfold uStatisticTerm
    rw [smul_smul, coeff_eq n hn a b c d ha hb hB hfin (timesOf i)
      (fun j => ⟨by simp [timesOf], (i j).isLt⟩) x]
    rfl
  have hnz : (n : ℝ) ^ (-(3 * (k : ℝ) / 4)) ≠ 0 := (Real.rpow_pos_of_pos hpos _).ne'
  have hzero : ∀ (i : Fin k → Fin n) (x : Fin k → ℤ), x ∉ Fintype.piFinset (fun _ => X) →
      uStatisticTerm ω Q n k (indicatorConstLp 2 hB hfin (1 : ℝ)) i x = 0 := by
    intro i x hx
    have hprod : ∏ j, wt n (a j) (b j) (c j) (d j) ((i j : ℕ) + 1, x j) = 0 := by
      rw [Fintype.mem_piFinset, not_forall] at hx
      obtain ⟨j, hj⟩ := hx
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      by_contra hne
      have := mem_supp_of_wt hn (ha j) (hb j) (hc j) (hd j) hne
      rw [hsupp, Finset.mem_product] at this
      exact hj this.2
    have h1 := hterm i x
    rw [hprod, zero_smul] at h1
    exact (smul_eq_zero.mp h1).resolve_left hnz
  have hLHS : (n : ℝ) ^ (-(3 * (k : ℝ) / 4)) •
      uStatistic ω Q n k (indicatorConstLp 2 hB hfin (1 : ℝ)) =
      ∑ p ∈ (Finset.univ.filter (fun i : Fin k → Fin n => Function.Injective i)) ×ˢ
          Fintype.piFinset (fun _ => X),
        (∏ j, wt n (a j) (b j) (c j) (d j) ((p.1 j : ℕ) + 1, p.2 j)) •
          envProductLp ω Q (timesOf p.1) p.2 := by
    unfold uStatistic
    rw [Finset.smul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tsum_eq_sum (s := Fintype.piFinset fun _ => X) (fun x hx => hzero i x hx),
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => hterm i x
  rw [hLHS]
  have hae : ∀ p ∈ (Finset.univ.filter (fun i : Fin k → Fin n => Function.Injective i)) ×ˢ
      Fintype.piFinset (fun _ => X),
      (((∏ j, wt n (a j) (b j) (c j) (d j) ((p.1 j : ℕ) + 1, p.2 j)) •
          envProductLp ω Q (timesOf p.1) p.2 : Lp ℝ 2 Q) : Ω → ℝ) =ᵐ[Q]
        fun z => (∏ j, wt n (a j) (b j) (c j) (d j) ((p.1 j : ℕ) + 1, p.2 j)) *
          envProduct ω (timesOf p.1) p.2 z := by
    intro p hp
    have hinj : Function.Injective p.1 := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    refine smul_envProductLp_ae hω _ (timesOf p.1) (fun j j' h => hinj (Fin.ext ?_)) p.2
    simpa [timesOf] using h
  filter_upwards [Lp.coeFn_finsetSum (E := ℝ) (p := 2) (μ := Q) _ _,
    (Filter.eventually_all_finset _).2 hae] with z hz hz'
  rw [hz, Finset.sum_apply]
  refine (Finset.sum_congr rfl hz').trans ?_
  rw [Finset.prod_univ_sum]
  have hfg : ∀ p : (Fin k → Fin n) × (Fin k → ℤ),
      (∏ j, wt n (a j) (b j) (c j) (d j) ((p.1 j : ℕ) + 1, p.2 j)) *
          envProduct ω (timesOf p.1) p.2 z =
        ∏ j, (wt n (a j) (b j) (c j) (d j) ((p.1 j : ℕ) + 1, p.2 j) *
          ω ((p.1 j : ℕ) + 1, p.2 j) z) := by
    intro p
    rw [Finset.prod_mul_distrib]
    rfl
  refine Finset.sum_bij_ne_zero (fun p _ _ => fun j => ((p.1 j : ℕ) + 1, p.2 j)) ?_ ?_ ?_ ?_
  · intro p hp _
    rw [Fintype.mem_piFinset]
    intro j
    rw [hsupp, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by omega, (p.1 j).isLt⟩, (Fintype.mem_piFinset.mp (Finset.mem_product.mp hp).2) j⟩
  · intro p _ _ p' _ _ h
    have h1 : ∀ j, (p.1 j : ℕ) + 1 = (p'.1 j : ℕ) + 1 ∧ p.2 j = p'.2 j :=
      fun j => Prod.ext_iff.mp (congrFun h j)
    exact Prod.ext (funext fun j => Fin.ext (by have := (h1 j).1; omega))
      (funext fun j => (h1 j).2)
  · intro q hq hne
    have hq' := Fintype.mem_piFinset.mp hq
    have hw : ∀ j, wt n (a j) (b j) (c j) (d j) (q j) ≠ 0 := by
      intro j hj
      apply hne
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, zero_mul])
    have hb1 : ∀ j, 1 ≤ (q j).1 ∧ (q j).1 ≤ n := fun j => by
      have := hq' j
      rw [hsupp, Finset.mem_product, Finset.mem_Icc] at this
      exact this.1
    have hxX : ∀ j, (q j).2 ∈ X := fun j => by
      have := hq' j
      rw [hsupp, Finset.mem_product] at this
      exact this.2
    obtain ⟨i, hi⟩ : ∃ i : Fin k → Fin n, ∀ j, (i j : ℕ) + 1 = (q j).1 :=
      ⟨fun j => ⟨(q j).1 - 1, by have := hb1 j; omega⟩, fun j => by
        have := hb1 j; simp only; omega⟩
    have hinj : Function.Injective i := by
      intro j j' h
      by_contra hjj
      have he : (q j).1 = (q j').1 := by rw [← hi j, ← hi j', h]
      exact wt_collision hn (hsep j j' hjj) (hgap j j' hjj) (hw j) (hw j') he
    have hq_eq : (fun j => (((i j : ℕ) + 1, (q j).2) : ℕ × ℤ)) = q :=
      funext fun j => Prod.ext (hi j) rfl
    refine ⟨(i, fun j => (q j).2), Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj⟩, Fintype.mem_piFinset.mpr hxX⟩, ?_, hq_eq⟩
    intro h0
    apply hne
    have e := hfg (i, fun j => (q j).2)
    rw [← hq_eq]
    exact e.symm.trans h0
  · intro p _ _
    exact hfg p

end IDL1b

namespace IDL2a
open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory Set Filter Topology

/-- The set of sites `{(I j, x j)}` of an environment product. -/
def sites {k : ℕ} (I : Fin k → ℕ) (x : Fin k → ℤ) : Finset (ℕ × ℤ) :=
  Finset.univ.image fun j => (I j, x j)

lemma envProduct_eq_prod_sites {Ω : Type*} (ω : ℕ × ℤ → Ω → ℝ) {k : ℕ} (I : Fin k → ℕ)
    (hI : Function.Injective I) (x : Fin k → ℤ) (z : Ω) :
    envProduct ω I x z = ∏ p ∈ sites I x, ω p z := by
  classical
  unfold envProduct sites
  rw [Finset.prod_image (fun j _ j' _ h => hI (congrArg Prod.fst h))]

lemma integral_ite_factor {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    (p : ℕ × ℤ) (P1 P2 : Prop) [Decidable P1] [Decidable P2] :
    ∫ z, (if P1 then ω p z else 1) * (if P2 then ω p z else 1) ∂Q
      = if P1 ↔ P2 then 1 else 0 := by
  have h1 : ∫ z, ω p z ∂Q = 0 := by
    rw [(hω.identDistrib p).integral_eq]; exact hω.mean_zero
  have h2 : ∫ z, ω p z * ω p z ∂Q = 1 := by
    have := ((hω.identDistrib p).comp (measurable_id.pow_const 2)).integral_eq
    simp only [Function.comp_def, id] at this
    rw [← hω.second_moment, ← this]
    congr 1; funext z; ring
  by_cases a : P1 <;> by_cases b : P2 <;> simp [a, b, h1, h2]

lemma integral_prod_mul_prod {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    (S T : Finset (ℕ × ℤ)) :
    ∫ z, (∏ p ∈ S, ω p z) * (∏ p ∈ T, ω p z) ∂Q = if S = T then 1 else 0 := by
  classical
  set U := S ∪ T with hU
  let f : U → ℝ → ℝ := fun p y => (if p.1 ∈ S then y else 1) * (if p.1 ∈ T then y else 1)
  have hprod : ∀ z, (∏ p ∈ S, ω p z) * (∏ p ∈ T, ω p z) = ∏ p : U, f p (ω p.1 z) := by
    intro z
    rw [Finset.prod_coe_sort U (fun p => (if p ∈ S then ω p z else 1) *
      (if p ∈ T then ω p z else 1)), Finset.prod_mul_distrib, Finset.prod_ite_mem,
      Finset.prod_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_left,
      Finset.inter_eq_right.mpr Finset.subset_union_right]
  simp_rw [hprod]
  have hind : iIndepFun (fun p : U => ω p.1) Q := hω.indep.precomp Subtype.val_injective
  have hfc : ∀ p, Continuous (f p) := fun p =>
    (continuous_if_const _ (fun _ => continuous_id) (fun _ => continuous_const)).mul
      (continuous_if_const _ (fun _ => continuous_id) (fun _ => continuous_const))
  rw [hind.integral_fun_prod_comp (f := f) (fun p => (hω.measurable _).aemeasurable)
    (fun p => (hfc p).measurable.aestronglyMeasurable)]
  simp only [f, integral_ite_factor hω]
  by_cases hST : S = T
  · rw [if_pos hST]
    exact Finset.prod_eq_one fun p _ => by rw [if_pos (by rw [hST])]
  · rw [if_neg hST]
    obtain ⟨p, hp⟩ : ∃ p ∈ U, ¬ (p ∈ S ↔ p ∈ T) := by
      by_contra h
      push_neg at h
      apply hST
      ext p
      by_cases hp : p ∈ U
      · exact h p hp
      · simp only [hU, Finset.mem_union, not_or] at hp
        simp [hp.1, hp.2]
    exact Finset.prod_eq_zero (i := ⟨p, hp.1⟩) (Finset.mem_univ _) (if_neg hp.2)

lemma inner_envProductLp {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {k k' : ℕ} (I : Fin k → ℕ) (hI : Function.Injective I) (x : Fin k → ℤ)
    (I' : Fin k' → ℕ) (hI' : Function.Injective I') (x' : Fin k' → ℤ) :
    inner ℝ (envProductLp ω Q I x) (envProductLp ω Q I' x')
      = if sites I x = sites I' x' then 1 else 0 := by
  have hm := IDL1b.envProduct_memLp hω I hI x
  have hm' := IDL1b.envProduct_memLp hω I' hI' x'
  unfold envProductLp
  rw [dif_pos hm, dif_pos hm', L2.inner_def, ← integral_prod_mul_prod hω]
  refine integral_congr_ae ?_
  filter_upwards [hm.coeFn_toLp, hm'.coeFn_toLp] with z h1 h2
  rw [h1, h2, envProduct_eq_prod_sites ω I hI x z, envProduct_eq_prod_sites ω I' hI' x' z,
    real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp [mul_comm]

lemma sites_inj {k : ℕ} {I : Fin k → ℕ} (hI : Function.Injective I) {x x' : Fin k → ℤ}
    (h : sites I x = sites I x') : x = x' := by
  classical
  funext j
  have hj : (I j, x j) ∈ sites I x' := h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)
  obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hj
  have := hI (congrArg Prod.fst hj')
  subst this
  exact (congrArg Prod.snd hj').symm

lemma orthonormal_envProductLp {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {k : ℕ} (I : Fin k → ℕ) (hI : Function.Injective I) :
    Orthonormal ℝ (fun x : Fin k → ℤ => envProductLp ω Q I x) := by
  rw [orthonormal_iff_ite]
  intro x x'
  rw [inner_envProductLp hω I hI x I hI x']
  by_cases h : x = x'
  · simp [h]
  · rw [if_neg h, if_neg (fun h' => h (sites_inj hI h'))]

/-- Cauchy-Schwarz for averages: `(avg f)^2 * μ(univ) ≤ ∫ f^2`. -/
lemma sq_avg_mul_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : MemLp f 2 μ) :
    ((μ.real univ)⁻¹ * ∫ a, f a ∂μ) ^ 2 * μ.real univ ≤ ∫ a, f a ^ 2 ∂μ := by
  have hi1 : Integrable f μ := hf.integrable one_le_two
  have hi2 : Integrable (fun a => f a ^ 2) μ := hf.integrable_sq
  by_cases hm : μ.real univ = 0
  · rw [hm, mul_zero]; exact integral_nonneg fun a => sq_nonneg _
  set c := (μ.real univ)⁻¹ * ∫ a, f a ∂μ with hc
  have h0 : 0 ≤ ∫ a, (f a - c) ^ 2 ∂μ := integral_nonneg fun a => sq_nonneg _
  have hexp : ∫ a, (f a - c) ^ 2 ∂μ = ∫ a, f a ^ 2 ∂μ - 2 * c * ∫ a, f a ∂μ + c ^ 2 * μ.real univ := by
    have : (fun a => (f a - c) ^ 2) = fun a => (f a ^ 2 - 2 * c * f a) + c ^ 2 := by
      funext a; ring
    rw [this, integral_add (f := fun a => f a ^ 2 - 2 * c * f a) (g := fun _ => c ^ 2)
        (hi2.sub (hi1.const_mul _)) (integrable_const _),
      integral_sub (f := fun a => f a ^ 2) (g := fun a => 2 * c * f a) hi2 (hi1.const_mul _),
      integral_const_mul, integral_const, smul_eq_mul, mul_comm (μ.real univ)]
  have hint : ∫ a, f a ∂μ = c * μ.real univ := by
    rw [hc, mul_comm, ← mul_assoc, mul_inv_cancel₀ hm, one_mul]
  rw [hexp, hint] at h0
  nlinarith


lemma kernelMeasure_cell_ne_top {k : ℕ} (n : ℕ) (I : Fin k → ℕ) (x : Fin k → ℤ) :
    kernelMeasure k (cell n I x) ≠ ⊤ := by
  rw [kernelMeasure, IDL1b.cell_eq_pi, Measure.pi_pi]
  refine ENNReal.prod_ne_top fun j _ => ?_
  rw [IDL1b.stripMeasure_prod _ _ (IDL1b.measurableSet_tCell n (I j))]
  refine ENNReal.mul_ne_top ?_ (by simp [IDL1a.xCell, Real.volume_Ioc])
  exact ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono inter_subset_right)

lemma integrableOn_cell {k : ℕ} (f : Lp ℝ 2 (kernelMeasure k)) (n : ℕ) (I : Fin k → ℕ)
    (x : Fin k → ℤ) : IntegrableOn (fun z => f z) (cell n I x) (kernelMeasure k) := by
  have := isFiniteMeasure_restrict.mpr (kernelMeasure_cell_ne_top n I x)
  exact ((Lp.memLp f).restrict _).integrable one_le_two

lemma cellAverage_sq_mul_le {k : ℕ} (g : Lp ℝ 2 (kernelMeasure k)) (n : ℕ) (I : Fin k → ℕ)
    (x : Fin k → ℤ) :
    cellAverage g n I x ^ 2 * (kernelMeasure k (cell n I x)).toReal ≤
      ∫ z in cell n I x, g z ^ 2 ∂kernelMeasure k := by
  haveI : IsFiniteMeasure ((kernelMeasure k).restrict (cell n I x)) :=
    isFiniteMeasure_restrict.mpr (kernelMeasure_cell_ne_top n I x)
  have h := sq_avg_mul_le ((kernelMeasure k).restrict (cell n I x)) (fun z => g z)
    ((Lp.memLp g).restrict _)
  have hr : ((kernelMeasure k).restrict (cell n I x)).real univ =
      (kernelMeasure k (cell n I x)).toReal := by
    rw [measureReal_def, Measure.restrict_apply_univ]
  rw [hr] at h
  unfold cellAverage
  exact h

lemma Ioc_t_disj {n : ℕ} (hn : 1 ≤ n) {a b : ℕ} (h : a ≠ b) :
    Disjoint (Ioc (((a : ℝ) - 1) / n) ((a : ℝ) / n))
      (Ioc (((b : ℝ) - 1) / n) ((b : ℝ) / n)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Set.disjoint_left]
  rintro t ⟨h1, h2⟩ ⟨h3, h4⟩
  rcases Nat.lt_or_gt_of_ne h with hab | hab
  · have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast Nat.succ_le_of_lt hab
    have := lt_of_lt_of_le h3 h2
    rw [div_lt_div_iff_of_pos_right hpos] at this
    linarith
  · have hab' : (b : ℝ) + 1 ≤ a := by exact_mod_cast Nat.succ_le_of_lt hab
    have := lt_of_lt_of_le h1 h4
    rw [div_lt_div_iff_of_pos_right hpos] at this
    linarith

lemma Ioc_x_disj {s : ℝ} (hs : 0 < s) {a b : ℤ} (h : a + 2 ≤ b ∨ b + 2 ≤ a) :
    Disjoint (Ioc (((a : ℝ) - 1) / s) (((a : ℝ) + 1) / s))
      (Ioc (((b : ℝ) - 1) / s) (((b : ℝ) + 1) / s)) := by
  rw [Set.disjoint_left]
  rintro t ⟨h1, h2⟩ ⟨h3, h4⟩
  rcases h with hab | hab
  · have hab' : (a : ℝ) + 2 ≤ b := by exact_mod_cast hab
    have := lt_of_lt_of_le h3 h2
    rw [div_lt_div_iff_of_pos_right hs] at this
    linarith
  · have hab' : (b : ℝ) + 2 ≤ a := by exact_mod_cast hab
    have := lt_of_lt_of_le h1 h4
    rw [div_lt_div_iff_of_pos_right hs] at this
    linarith

lemma cell_disjoint {k : ℕ} {n : ℕ} (hn : 1 ≤ n) {I I' : Fin k → ℕ} {x x' : Fin k → ℤ}
    (hp : ParityMatch I x) (hp' : ParityMatch I' x') (hne : ¬ (I = I' ∧ x = x')) :
    Disjoint (cell n I x) (cell n I' x') := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  unfold cell
  rw [Set.disjoint_univ_pi]
  by_cases hI : I = I'
  · subst hI
    have hx : x ≠ x' := fun h => hne ⟨rfl, h⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    refine ⟨j, Set.disjoint_prod.mpr (Or.inr (Ioc_x_disj hs ?_))⟩
    obtain ⟨m, hm⟩ := (hp j).sub (hp' j)
    omega
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hI
    exact ⟨j, Set.disjoint_prod.mpr (Or.inl (Ioc_t_disj hn hj))⟩

/-- Bessel-type bound: the squared cell averages over pairwise distinct parity cells, weighted by
the cell volumes, are bounded by `‖g‖²`. -/
lemma cellAvg_sum_le {k : ℕ} (g : Lp ℝ 2 (kernelMeasure k)) {n : ℕ} (hnk : 1 ≤ n ∨ k = 0)
    (P : Finset ((Fin k → ℕ) × (Fin k → ℤ))) (hP : ∀ p ∈ P, ParityMatch p.1 p.2) :
    ∑ p ∈ P, cellAverage g n p.1 p.2 ^ 2 * (kernelMeasure k (cell n p.1 p.2)).toReal ≤
      ∫ z, g z ^ 2 ∂kernelMeasure k := by
  have hint : Integrable (fun z => g z ^ 2) (kernelMeasure k) := (Lp.memLp g).integrable_sq
  calc _ ≤ ∑ p ∈ P, ∫ z in cell n p.1 p.2, g z ^ 2 ∂kernelMeasure k :=
        Finset.sum_le_sum fun p _ => cellAverage_sq_mul_le g n p.1 p.2
    _ = ∫ z in ⋃ p ∈ P, cell n p.1 p.2, g z ^ 2 ∂kernelMeasure k :=
        (integral_biUnion_finset P (fun p _ => IDL1b.measurableSet_cell n p.1 p.2)
          (fun p hp q hq hpq => by
            rcases hnk with hn | hk
            · exact cell_disjoint hn (hP p hp) (hP q hq) (fun h => hpq (Prod.ext h.1 h.2))
            · subst hk; exact absurd (Subsingleton.elim p q) hpq)
          (fun p _ => hint.integrableOn)).symm
    _ ≤ _ := setIntegral_le_integral hint (Eventually.of_forall fun z => sq_nonneg _)

lemma timesOf_injective {k n : ℕ} {i : Fin k → Fin n} (hi : Function.Injective i) :
    Function.Injective (timesOf i) := fun a b h => hi (Fin.ext (by simpa [timesOf] using h))

lemma timesOf_bounds {k n : ℕ} (i : Fin k → Fin n) (j : Fin k) :
    1 ≤ timesOf i j ∧ timesOf i j ≤ n := by
  unfold timesOf; exact ⟨by omega, (i j).isLt⟩

open scoped Classical in
lemma summable_sq_coeff {k : ℕ} (g : Lp ℝ 2 (kernelMeasure k)) {n : ℕ} (hn : 1 ≤ n)
    (T : Fin k → ℕ) (hT : ∀ j, 1 ≤ T j ∧ T j ≤ n) :
    Summable fun x : Fin k → ℤ =>
      (cellAverage g n T x * (if ParityMatch T x then 1 else 0)) ^ 2 := by
  set M : ℝ := ((1 / n) * (2 / Real.sqrt n)) ^ k with hM
  have hMpos : 0 < M := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  refine summable_of_sum_le (c := (∫ z, g z ^ 2 ∂kernelMeasure k) / M)
    (fun x => sq_nonneg _) fun s => ?_
  rw [le_div_iff₀ hMpos, Finset.sum_mul]
  have h1 : ∀ x ∈ s, (cellAverage g n T x * (if ParityMatch T x then 1 else 0)) ^ 2 * M =
      if ParityMatch T x then cellAverage g n T x ^ 2 *
        (kernelMeasure k (cell n T x)).toReal else 0 := by
    intro x _
    rw [IDL1b.kernelMeasure_cell n hn T hT x]
    split_ifs <;> simp [hM]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have h2 := cellAvg_sum_le g (Or.inl hn) ((s.filter fun x => ParityMatch T x).image fun x => (T, x))
    (by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact (Finset.mem_filter.mp hx).2)
  rwa [Finset.sum_image (fun x _ y _ h => (Prod.ext_iff.mp h).2)] at h2

open scoped Classical in
/-- Part 1 of Lemma 4.1: the series over `x` defining `𝒮_k^n(g)` converge in `L²(Q)`. -/
theorem summable_uStatisticTerm {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (n k : ℕ)
    (g : Lp ℝ 2 (kernelMeasure k)) (i : Fin k → Fin n) (hi : Function.Injective i) :
    Summable (fun x : Fin k → ℤ => uStatisticTerm ω Q n k g i x) := by
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · haveI : Unique (Fin k → ℤ) := Pi.uniqueOfIsEmpty _
    exact Summable.of_finite
  · have hn : 1 ≤ n := by
      obtain ⟨j⟩ := hk
      exact Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact (i j).elim0)
    have hv := orthonormal_envProductLp hω (timesOf i) (timesOf_injective hi)
    have key := hv.orthogonalFamily.summable_iff_norm_sq_summable (fun x =>
      Real.sqrt 2 ^ k * cellAverage g n (timesOf i) x *
        (if ParityMatch (timesOf i) x then 1 else 0))
    simp only [LinearIsometry.toSpanSingleton_apply] at key
    unfold uStatisticTerm
    rw [key]
    have := (summable_sq_coeff g hn (timesOf i) (timesOf_bounds i)).mul_left
      ((Real.sqrt 2 ^ k) ^ 2)
    refine this.congr fun x => ?_
    rw [Real.norm_eq_abs, sq_abs]
    ring

lemma cellAverage_add {k : ℕ} (f g : Lp ℝ 2 (kernelMeasure k)) (n : ℕ) (I : Fin k → ℕ)
    (x : Fin k → ℤ) :
    cellAverage (f + g) n I x = cellAverage f n I x + cellAverage g n I x := by
  unfold cellAverage
  have h : ∫ z in cell n I x, (f + g) z ∂kernelMeasure k =
      ∫ z in cell n I x, (f z + g z) ∂kernelMeasure k :=
    integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))
  rw [h, integral_add (integrableOn_cell f n I x) (integrableOn_cell g n I x)]
  ring

lemma cellAverage_smul {k : ℕ} (c : ℝ) (f : Lp ℝ 2 (kernelMeasure k)) (n : ℕ)
    (I : Fin k → ℕ) (x : Fin k → ℤ) :
    cellAverage (c • f) n I x = c * cellAverage f n I x := by
  unfold cellAverage
  have h : ∫ z in cell n I x, (c • f) z ∂kernelMeasure k =
      ∫ z in cell n I x, c * f z ∂kernelMeasure k := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [Lp.coeFn_smul c f] with z hz
    rw [hz, Pi.smul_apply, smul_eq_mul]
  rw [h, integral_const_mul]
  ring

open scoped Classical in
lemma uStatisticTerm_add {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    (ω : ℕ × ℤ → Ω → ℝ) (n k : ℕ) (f g : Lp ℝ 2 (kernelMeasure k)) (i : Fin k → Fin n)
    (x : Fin k → ℤ) :
    uStatisticTerm ω Q n k (f + g) i x = uStatisticTerm ω Q n k f i x + uStatisticTerm ω Q n k g i x := by
  unfold uStatisticTerm
  rw [cellAverage_add, ← add_smul]
  congr 1; ring

open scoped Classical in
lemma uStatisticTerm_smul {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    (ω : ℕ × ℤ → Ω → ℝ) (n k : ℕ) (c : ℝ) (f : Lp ℝ 2 (kernelMeasure k)) (i : Fin k → Fin n)
    (x : Fin k → ℤ) :
    uStatisticTerm ω Q n k (c • f) i x = c • uStatisticTerm ω Q n k f i x := by
  unfold uStatisticTerm
  rw [cellAverage_smul, smul_smul]
  congr 1; ring

/-- `𝒮_k^n` as a linear map. -/
noncomputable def uStatL {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (n k : ℕ) :
    Lp ℝ 2 (kernelMeasure k) →ₗ[ℝ] Lp ℝ 2 Q where
  toFun := uStatistic ω Q n k
  map_add' f g := by
    unfold uStatistic
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hinj := (Finset.mem_filter.mp hi).2
    simp_rw [uStatisticTerm_add]
    exact (summable_uStatisticTerm hω n k f i hinj).tsum_add
      (summable_uStatisticTerm hω n k g i hinj)
  map_smul' c f := by
    unfold uStatistic
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hinj := (Finset.mem_filter.mp hi).2
    simp_rw [uStatisticTerm_smul]
    exact (summable_uStatisticTerm hω n k f i hinj).tsum_const_smul c

/-- Part 2 of Lemma 4.1: linearity. -/
theorem uStatistic_linear {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (n k m : ℕ)
    (α : Fin m → ℝ) (g : Fin m → Lp ℝ 2 (kernelMeasure k)) :
    ∑ l, α l • uStatistic ω Q n k (g l) = uStatistic ω Q n k (∑ l, α l • g l) := by
  have h := map_sum (uStatL hω n k) (fun l => α l • g l) Finset.univ
  simp only [map_smul] at h
  exact h.symm

lemma inner_tsum_right {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E) (f : ι → E) (hs : Summable f) :
    inner ℝ w (∑' i, f i) = ∑' i, inner ℝ w (f i) := by
  have := (innerSL ℝ w).map_tsum hs
  simpa only [innerSL_apply_apply] using this

lemma norm_sq_tsum_orthonormal {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : ι → E} (hv : Orthonormal ℝ v) (c : ι → ℝ) (hs : Summable fun i => c i • v i) :
    ‖∑' i, c i • v i‖ ^ 2 = ∑' i, c i ^ 2 := by
  classical
  have hcoef : ∀ j, inner ℝ (v j) (∑' i, c i • v i) = c j := by
    intro j
    rw [inner_tsum_right _ _ hs, tsum_eq_single j]
    · rw [real_inner_smul_right, hv.1 j |> fun h => (real_inner_self_eq_norm_sq (v j)).trans
        (by rw [h, one_pow]), mul_one]
    · intro i hij
      rw [real_inner_smul_right, hv.2 (Ne.symm hij), mul_zero]
  rw [← real_inner_self_eq_norm_sq, real_inner_comm, inner_tsum_right _ _ hs]
  congr 1; funext i
  rw [real_inner_smul_right, real_inner_comm, hcoef i, sq]

lemma card_sites {k : ℕ} {I : Fin k → ℕ} (hI : Function.Injective I) (x : Fin k → ℤ) :
    (sites I x).card = k := by
  unfold sites
  rw [Finset.card_image_of_injective _ (fun j j' h => hI (congrArg Prod.fst h)),
    Finset.card_univ, Fintype.card_fin]

open scoped Classical in
lemma inner_uStatisticTerm_env {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (n k : ℕ)
    (g : Lp ℝ 2 (kernelMeasure k)) (i : Fin k → Fin n) (hi : Function.Injective i)
    (x : Fin k → ℤ) {k' : ℕ} (I' : Fin k' → ℕ) (hI' : Function.Injective I') (x' : Fin k' → ℤ)
    (h : k' ≠ k) :
    inner ℝ (uStatisticTerm ω Q n k g i x) (envProductLp ω Q I' x') = 0 := by
  unfold uStatisticTerm
  rw [real_inner_smul_left, inner_envProductLp hω _ (timesOf_injective hi) x I' hI' x',
    if_neg (show ¬ sites (timesOf i) x = sites I' x' from fun hs => h (by
      rw [← card_sites hI' x', ← hs, card_sites (timesOf_injective hi) x])), mul_zero]

open scoped Classical in
lemma inner_uStatistic_env {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (n k : ℕ)
    (g : Lp ℝ 2 (kernelMeasure k)) {k' : ℕ} (I' : Fin k' → ℕ) (hI' : Function.Injective I')
    (x' : Fin k' → ℤ) (h : k' ≠ k) :
    inner ℝ (uStatistic ω Q n k g) (envProductLp ω Q I' x') = 0 := by
  unfold uStatistic
  rw [sum_inner]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hinj := (Finset.mem_filter.mp hi).2
  rw [real_inner_comm, inner_tsum_right _ _ (summable_uStatisticTerm hω n k g i hinj)]
  have : ∀ x, inner ℝ (envProductLp ω Q I' x') (uStatisticTerm ω Q n k g i x) = 0 := fun x => by
    rw [real_inner_comm]; exact inner_uStatisticTerm_env hω n k g i hinj x I' hI' x' h
  simp only [this, tsum_zero]

/-- Part 3 of Lemma 4.1: `𝒮_k^n(g)` has mean zero for `k ≥ 1`. -/
theorem uStatistic_integral_zero {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (n k : ℕ)
    (hk : 1 ≤ k) (g : Lp ℝ 2 (kernelMeasure k)) :
    ∫ a, (uStatistic ω Q n k g : Ω → ℝ) a ∂Q = 0 := by
  have hI0 : Function.Injective (Fin.elim0 : Fin 0 → ℕ) := fun a => a.elim0
  have h0 := inner_uStatistic_env hω n k g (Fin.elim0 : Fin 0 → ℕ) hI0 Fin.elim0 (by omega)
  have hm := IDL1b.envProduct_memLp hω (Fin.elim0 : Fin 0 → ℕ) hI0 Fin.elim0
  unfold envProductLp at h0
  rw [dif_pos hm, L2.inner_def] at h0
  refine Eq.trans (integral_congr_ae ?_) h0
  filter_upwards [hm.coeFn_toLp] with z hz
  rw [hz, Real.inner_apply]
  simp [envProduct]

/-- Part 4 of Lemma 4.1: orthogonality across orders. -/
theorem uStatistic_orthogonal {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (n k₁ k₂ : ℕ)
    (h : k₁ ≠ k₂) (g₁ : Lp ℝ 2 (kernelMeasure k₁)) (g₂ : Lp ℝ 2 (kernelMeasure k₂)) :
    ∫ a, (uStatistic ω Q n k₁ g₁ : Ω → ℝ) a * (uStatistic ω Q n k₂ g₂ : Ω → ℝ) a ∂Q = 0 := by
  classical
  have key : inner ℝ (uStatistic ω Q n k₁ g₁) (uStatistic ω Q n k₂ g₂) = 0 := by
    rw [show uStatistic ω Q n k₂ g₂ = ∑ i ∈ Finset.univ.filter
        (fun i : Fin k₂ → Fin n => Function.Injective i),
        ∑' x, uStatisticTerm ω Q n k₂ g₂ i x from rfl, inner_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hinj := (Finset.mem_filter.mp hi).2
    rw [inner_tsum_right _ _ (summable_uStatisticTerm hω n k₂ g₂ i hinj)]
    have : ∀ x, inner ℝ (uStatistic ω Q n k₁ g₁) (uStatisticTerm ω Q n k₂ g₂ i x) = 0 :=
      fun x => by
        unfold uStatisticTerm
        rw [real_inner_smul_right, inner_uStatistic_env hω n k₁ g₁ _ (timesOf_injective hinj) x
          (Ne.symm h), mul_zero]
    simp only [this, tsum_zero]
  rw [L2.inner_def] at key
  refine Eq.trans (integral_congr_ae (Eventually.of_forall fun a => ?_)) key
  simp only [Real.inner_apply]

lemma timesOf_inj {k n : ℕ} {i i' : Fin k → Fin n} (h : timesOf i = timesOf i') : i = i' := by
  funext j
  have h1 := congrFun h j
  unfold timesOf at h1
  exact Fin.ext (by omega)

lemma timesOf_strictMono {k n : ℕ} {i : Fin k → Fin n} (hs : StrictMono i) :
    StrictMono (timesOf i) := fun a b hab => by
  unfold timesOf
  have := Fin.lt_iff_val_lt_val.mp (hs hab)
  omega

lemma range_subset_of_sites {k : ℕ} {I I' : Fin k → ℕ} {y y' : Fin k → ℤ}
    (h : sites I y = sites I' y') : Set.range I ⊆ Set.range I' := by
  rintro t ⟨j, rfl⟩
  have : (I j, y j) ∈ sites I' y' := h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)
  obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp this
  exact ⟨j', congrArg Prod.fst hj'⟩

lemma sites_ne_of_strictMono {k n : ℕ} {i i' : Fin k → Fin n} (hs : StrictMono i)
    (hs' : StrictMono i') (hne : i ≠ i') (x x' : Fin k → ℤ) :
    sites (timesOf i) x ≠ sites (timesOf i') x' := by
  intro h
  apply hne
  have hrange := (range_subset_of_sites h).antisymm (range_subset_of_sites h.symm)
  exact timesOf_inj (((timesOf_strictMono hs).range_inj (timesOf_strictMono hs')).mp hrange)

lemma strictMono_of_mem_cell_simplex {k n : ℕ} {i : Fin k → Fin n} (hi : Function.Injective i)
    {x : Fin k → ℤ} {z : Fin k → ℝ × ℝ} (hz : z ∈ cell n (timesOf i) x) (hs : z ∈ simplex k) :
    StrictMono i := by
  cases k with
  | zero => exact fun a => a.elim0
  | succ m =>
    rw [Fin.strictMono_iff_lt_succ]
    intro j
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Fin.pos (i 0)
    have h1 := (hs j.succ).1
    have he : (j.succ).castSucc = (j.castSucc).succ := Fin.ext (by simp)
    rw [he, withOrigin, Fin.cons_succ] at h1
    unfold cell at hz
    have ha := Set.mem_univ_pi.mp hz j.castSucc
    have hb := Set.mem_univ_pi.mp hz j.succ
    simp only [Set.mem_prod, Set.mem_Ioc, timesOf] at ha hb
    push_cast at ha hb
    have h2 := lt_of_lt_of_le (ha.1.1.trans h1) hb.1.2
    rw [div_lt_div_iff_of_pos_right hnpos] at h2
    have h3 : (i j.castSucc : ℕ) < (i j.succ : ℕ) + 1 := by
      have : ((i j.castSucc : ℕ) : ℝ) < ((i j.succ : ℕ) : ℝ) + 1 := by linarith
      exact_mod_cast this
    have hne : i j.castSucc ≠ i j.succ := fun h => (Fin.castSucc_lt_succ : j.castSucc < j.succ).ne (hi h)
    exact lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr (by omega)) hne

lemma cellAverage_eq_zero_of_not_strictMono {k n : ℕ} (g : Lp ℝ 2 (kernelMeasure k))
    (hg : SimplexSupported g) {i : Fin k → Fin n} (hi : Function.Injective i)
    (hns : ¬ StrictMono i) (x : Fin k → ℤ) : cellAverage g n (timesOf i) x = 0 := by
  unfold cellAverage
  rw [integral_eq_zero_of_ae, mul_zero]
  rw [EventuallyEq, ae_restrict_iff' (IDL1b.measurableSet_cell n _ x)]
  filter_upwards [hg] with z hz hzc
  exact hz (fun hs => hns (strictMono_of_mem_cell_simplex hi hzc hs))

open scoped Classical in
/-- The coefficient of `ω(i, x)` in `𝒮_k^n(g)`. -/
noncomputable def coef (n k : ℕ) (g : Lp ℝ 2 (kernelMeasure k)) (i : Fin k → Fin n)
    (x : Fin k → ℤ) : ℝ :=
  Real.sqrt 2 ^ k * cellAverage g n (timesOf i) x * (if ParityMatch (timesOf i) x then 1 else 0)

lemma two_pow_eq {k n : ℕ} (i : Fin k → Fin n) (x : Fin k → ℤ) :
    (2 : ℝ) ^ k = (n : ℝ) ^ (3 * (k : ℝ) / 2) * (kernelMeasure k (cell n (timesOf i) x)).toReal := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [kernelMeasure, IDL1b.cell_eq_pi, Measure.pi_pi]
  · have hn : 1 ≤ n := Fin.pos (i ⟨0, hk⟩)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [IDL1b.kernelMeasure_cell n hn (timesOf i) (timesOf_bounds i) x,
      show 3 * (k : ℝ) / 2 = (3 / 2 : ℝ) * (k : ℝ) by ring,
      Real.rpow_mul_natCast (Nat.cast_nonneg _), ← mul_pow]
    congr 1
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hnpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    field_simp

open scoped Classical in
lemma ofReal_coef_sq {k n : ℕ} (g : Lp ℝ 2 (kernelMeasure k)) (i : Fin k → Fin n)
    (x : Fin k → ℤ) :
    ENNReal.ofReal (coef n k g i x ^ 2) =
      ENNReal.ofReal ((n : ℝ) ^ (3 * (k : ℝ) / 2)) *
        (if ParityMatch (timesOf i) x then kernelMeasure k (cell n (timesOf i) x) *
          ENNReal.ofReal (cellAverage g n (timesOf i) x ^ 2) else 0) := by
  unfold coef
  split_ifs with hp
  · have hsq : (Real.sqrt 2 ^ k) ^ 2 = 2 ^ k := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
    rw [mul_one, mul_pow, hsq, two_pow_eq i x, ← ENNReal.ofReal_toReal
      (kernelMeasure_cell_ne_top n (timesOf i) x), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal ENNReal.toReal_nonneg, mul_assoc]
  · simp

lemma eLpNorm_sq_eq_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) : eLpNorm (f : α → ℝ) 2 μ ^ 2 = ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]

lemma norm_sq_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ a, f a ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1; funext a; rw [Real.inner_apply, sq]

open scoped Classical in
/-- Part 5b: `‖ḡ_n‖² ≤ ‖g‖²`. -/
theorem cellAverageNormSq_le {k : ℕ} (g : Lp ℝ 2 (kernelMeasure k)) (n : ℕ) :
    cellAverageNormSq g n ≤ eLpNorm (g : (Fin k → ℝ × ℝ) → ℝ) 2 (kernelMeasure k) ^ 2 := by
  rw [eLpNorm_sq_eq_ofReal, norm_sq_eq_integral, cellAverageNormSq, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  by_cases hnk : 1 ≤ n ∨ k = 0
  · rw [← Finset.sum_filter]
    have h1 : ∀ p ∈ s.filter (fun p : (Fin k → Fin n) × (Fin k → ℤ) =>
        ParityMatch (timesOf p.1) p.2),
        kernelMeasure k (cell n (timesOf p.1) p.2) *
          ENNReal.ofReal (cellAverage g n (timesOf p.1) p.2 ^ 2) =
        ENNReal.ofReal (cellAverage g n (timesOf p.1) p.2 ^ 2 *
          (kernelMeasure k (cell n (timesOf p.1) p.2)).toReal) := by
      intro p _
      rw [ENNReal.ofReal_mul (sq_nonneg _),
        ENNReal.ofReal_toReal (kernelMeasure_cell_ne_top _ _ _), mul_comm]
    rw [Finset.sum_congr rfl h1, ← ENNReal.ofReal_sum_of_nonneg
      (fun _ _ => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)]
    apply ENNReal.ofReal_le_ofReal
    have h2 := cellAvg_sum_le g hnk
      ((s.filter fun p : (Fin k → Fin n) × (Fin k → ℤ) => ParityMatch (timesOf p.1) p.2).image
        fun p => (timesOf p.1, p.2))
      (by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
        exact (Finset.mem_filter.mp hp).2)
    rwa [Finset.sum_image (g := fun p : (Fin k → Fin n) × (Fin k → ℤ) => (timesOf p.1, p.2))
      (fun p _ q _ h => Prod.ext (timesOf_inj (Prod.ext_iff.mp h).1)
      (Prod.ext_iff.mp h).2)] at h2
  · push_neg at hnk
    have hn : n = 0 := by omega
    subst hn
    haveI : IsEmpty (Fin k → Fin 0) := ⟨fun f => (f ⟨0, by omega⟩).elim0⟩
    rw [Finset.eq_empty_of_isEmpty s]
    simp

open scoped Classical in
/-- Part 5a: `Q[𝒮_k^n(g)²] ≤ n^{3k/2} ‖ḡ_n‖²` for simplex-supported `g`. -/
theorem uStatistic_norm_bound {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (n k : ℕ)
    (g : Lp ℝ 2 (kernelMeasure k)) (hg : SimplexSupported g) :
    eLpNorm (uStatistic ω Q n k g : Ω → ℝ) 2 Q ^ 2 ≤
      ENNReal.ofReal ((n : ℝ) ^ (3 * (k : ℝ) / 2)) * cellAverageNormSq g n := by
  have hterm : ∀ i x, uStatisticTerm ω Q n k g i x =
      coef n k g i x • envProductLp ω Q (timesOf i) x := fun _ _ => rfl
  have hzero : ∀ i, Function.Injective i → ¬ StrictMono i →
      (∑' x, uStatisticTerm ω Q n k g i x) = 0 := by
    intro i hi hns
    have : ∀ x, uStatisticTerm ω Q n k g i x = 0 := fun x => by
      rw [hterm, coef, cellAverage_eq_zero_of_not_strictMono g hg hi hns x]; simp
    simp only [this, tsum_zero]
  have horth : ∀ i, Function.Injective i → ∀ i', Function.Injective i' → i ≠ i' →
      inner ℝ (∑' x, uStatisticTerm ω Q n k g i x) (∑' x, uStatisticTerm ω Q n k g i' x) = 0 := by
    intro i hinj i' hinj' hne
    by_cases hs : StrictMono i
    · by_cases hs' : StrictMono i'
      · have h1 : ∀ x', inner ℝ (∑' x, uStatisticTerm ω Q n k g i x)
            (envProductLp ω Q (timesOf i') x') = 0 := by
          intro x'
          rw [real_inner_comm, inner_tsum_right _ _ (summable_uStatisticTerm hω n k g i hinj)]
          have : ∀ x, inner ℝ (envProductLp ω Q (timesOf i') x')
              (uStatisticTerm ω Q n k g i x) = 0 := by
            intro x
            rw [hterm, real_inner_smul_right, inner_envProductLp hω _ (timesOf_injective hinj') x'
              _ (timesOf_injective hinj) x,
              if_neg (sites_ne_of_strictMono hs' hs (Ne.symm hne) x' x), mul_zero]
          simp only [this, tsum_zero]
        rw [inner_tsum_right _ _ (summable_uStatisticTerm hω n k g i' hinj')]
        have h2 : ∀ x', inner ℝ (∑' x, uStatisticTerm ω Q n k g i x)
            (uStatisticTerm ω Q n k g i' x') = 0 := fun x' => by
          rw [hterm i' x', real_inner_smul_right, h1, mul_zero]
        simp only [h2, tsum_zero]
      · rw [hzero i' hinj' hs', inner_zero_right]
    · rw [hzero i hinj hs, inner_zero_left]
  have hnormS : ‖uStatistic ω Q n k g‖ ^ 2 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin k → Fin n => Function.Injective i),
        ‖∑' x, uStatisticTerm ω Q n k g i x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold uStatistic
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [inner_sum, Finset.sum_eq_single i (fun i' hi' hne => horth i (Finset.mem_filter.mp hi).2
      i' (Finset.mem_filter.mp hi').2 (Ne.symm hne)) (fun h => absurd hi h),
      real_inner_self_eq_norm_sq]
  have hnormSi : ∀ i, Function.Injective i →
      ‖∑' x, uStatisticTerm ω Q n k g i x‖ ^ 2 = ∑' x, coef n k g i x ^ 2 ∧
        Summable (fun x => coef n k g i x ^ 2) := by
    intro i hinj
    have hsum := summable_uStatisticTerm hω n k g i hinj
    have hv := orthonormal_envProductLp hω (timesOf i) (timesOf_injective hinj)
    refine ⟨norm_sq_tsum_orthonormal hv (coef n k g i) hsum, ?_⟩
    have key := hv.orthogonalFamily.summable_iff_norm_sq_summable (coef n k g i)
    simp only [LinearIsometry.toSpanSingleton_apply] at key
    have h2 := key.mp hsum
    simpa only [Real.norm_eq_abs, sq_abs] using h2
  rw [eLpNorm_sq_eq_ofReal, hnormS, ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  calc _ = ∑ i ∈ Finset.univ.filter (fun i : Fin k → Fin n => Function.Injective i),
        ∑' x, ENNReal.ofReal (coef n k g i x ^ 2) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        obtain ⟨h1, h2⟩ := hnormSi i (Finset.mem_filter.mp hi).2
        rw [h1, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h2]
    _ ≤ ∑ i : Fin k → Fin n, ∑' x, ENNReal.ofReal (coef n k g i x ^ 2) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ∑' p : (Fin k → Fin n) × (Fin k → ℤ), ENNReal.ofReal (coef n k g p.1 p.2 ^ 2) := by
        rw [ENNReal.tsum_prod (f := fun i x => ENNReal.ofReal (coef n k g i x ^ 2)),
          tsum_fintype (f := fun i => ∑' x, ENNReal.ofReal (coef n k g i x ^ 2))]
    _ = _ := by
        rw [cellAverageNormSq, ← ENNReal.tsum_mul_left]
        congr 1; funext p
        exact ofReal_coef_sq g p.1 p.2

end IDL2a

open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (n : ℕ) :
    (∀ (k : ℕ) (g : Lp ℝ 2 (kernelMeasure k)) (i : Fin k → Fin n), Function.Injective i →
      Summable (fun x : Fin k → ℤ => uStatisticTerm ω Q n k g i x)) ∧
    (∀ (k m : ℕ) (α : Fin m → ℝ) (g : Fin m → Lp ℝ 2 (kernelMeasure k)),
      ∑ l, α l • uStatistic ω Q n k (g l) = uStatistic ω Q n k (∑ l, α l • g l)) ∧
    (∀ (k : ℕ), 1 ≤ k → ∀ g : Lp ℝ 2 (kernelMeasure k),
      ∫ a, (uStatistic ω Q n k g : Ω → ℝ) a ∂Q = 0) ∧
    (∀ (k₁ k₂ : ℕ), k₁ ≠ k₂ → ∀ (g₁ : Lp ℝ 2 (kernelMeasure k₁))
      (g₂ : Lp ℝ 2 (kernelMeasure k₂)),
      ∫ a, (uStatistic ω Q n k₁ g₁ : Ω → ℝ) a * (uStatistic ω Q n k₂ g₂ : Ω → ℝ) a ∂Q = 0) ∧
    (∀ (k : ℕ) (g : Lp ℝ 2 (kernelMeasure k)), SimplexSupported g →
      eLpNorm (uStatistic ω Q n k g : Ω → ℝ) 2 Q ^ 2 ≤
          ENNReal.ofReal ((n : ℝ) ^ (3 * (k : ℝ) / 2)) * cellAverageNormSq g n ∧
        ENNReal.ofReal ((n : ℝ) ^ (3 * (k : ℝ) / 2)) * cellAverageNormSq g n ≤
          ENNReal.ofReal ((n : ℝ) ^ (3 * (k : ℝ) / 2)) *
            eLpNorm (g : (Fin k → ℝ × ℝ) → ℝ) 2 (kernelMeasure k) ^ 2) := by
  exact ⟨fun k g i hi => IDL2a.summable_uStatisticTerm hω n k g i hi,
   fun k m α g => IDL2a.uStatistic_linear hω n k m α g,
   fun k hk g => IDL2a.uStatistic_integral_zero hω n k hk g,
   fun k₁ k₂ h g₁ g₂ => IDL2a.uStatistic_orthogonal hω n k₁ k₂ h g₁ g₂,
   fun k g hg => ⟨IDL2a.uStatistic_norm_bound hω n k g hg,
     by gcongr; exact IDL2a.cellAverageNormSq_le g n⟩⟩
