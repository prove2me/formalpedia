-- Prove2me | solution 1 for IntermediateDisorder.PointToLine.modifiedPartitionFunction_tendstoInDistribution_chaos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T16:45:45.958007+00:00
-- url     : https://prove2.me/submissions/56f11984-9af1-4d5c-905c-dac1b77a090d

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos
import Definitions.Def_IntermediateDisorder_PointToLine_UStatistic


set_option autoImplicit false
set_option maxHeartbeats 1000000

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
/-- Lemma 4.1 (014f3eb1), assembled. -/
theorem IDL2a.uStatistic_linear_orthogonal' {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
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
            eLpNorm (g : (Fin k → ℝ × ℝ) → ℝ) 2 (kernelMeasure k) ^ 2) :=
  ⟨fun k g i hi => IDL2a.summable_uStatisticTerm hω n k g i hi,
   fun k m α g => IDL2a.uStatistic_linear hω n k m α g,
   fun k hk g => IDL2a.uStatistic_integral_zero hω n k hk g,
   fun k₁ k₂ h g₁ g₂ => IDL2a.uStatistic_orthogonal hω n k₁ k₂ h g₁ g₂,
   fun k g hg => ⟨IDL2a.uStatistic_norm_bound hω n k g hg,
     by gcongr; exact IDL2a.cellAverageNormSq_le g n⟩⟩

namespace IDL1c

open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory Set Filter Topology IDL1a IDL1b

/-- Convergence in distribution is unchanged by eventually a.e.-equal modifications. -/
lemma tendstoInDistribution_congr_eventually {Ω Ω' E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    {X Y : ℕ → Ω → E} {Z : Ω' → E} (h : TendstoInDistribution X atTop Z (fun _ => Q) Q')
    (hXY : ∀ᶠ n in atTop, X n =ᵐ[Q] Y n) (hY : ∀ n, AEMeasurable (Y n) Q) :
    TendstoInDistribution Y atTop Z (fun _ => Q) Q' where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := by
    refine h.tendsto.congr' ?_
    filter_upwards [hXY] with n hn
    exact Subtype.ext (Measure.map_congr hn)

lemma measurableSet_box (a b c d : ℝ) : MeasurableSet (box a b c d) :=
  measurableSet_Ioc.prod measurableSet_Ioc

lemma volume_box_ne_top (a b c d : ℝ) : volume (box a b c d) ≠ ⊤ := by
  rw [box, Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top (by simp) (by simp)

lemma box_sub (a b c d : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    box a b c d ⊆ Icc (0 : ℝ) 1 ×ˢ univ := by
  rintro ⟨t, x⟩ ⟨⟨h1, h2⟩, -⟩
  exact ⟨⟨ha.trans h1.le, h2.trans hb⟩, trivial⟩

/-- A strip box as an index of the white noise. -/
def boxFS (a b c d : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) : FiniteStripSet :=
  ⟨box a b c d, measurableSet_box a b c d, box_sub a b c d ha hb, volume_box_ne_top a b c d⟩

/-- L1c(a): the first-order box sums converge jointly to the white noise on the boxes. -/
theorem box_vec_tendsto {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {W : Set (ℝ × ℝ) → Ω' → ℝ} (hW : IsWhiteNoise W Q') {m : ℕ} (L : ℝ)
    (a b c d : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1) (hc : ∀ i, -L ≤ c i)
    (hd : ∀ i, d i ≤ L) :
    TendstoInDistribution
      (fun n z i => ∑ p ∈ supp n L, wt n (a i) (b i) (c i) (d i) p * ω p z) atTop
      (fun z i => W (box (a i) (b i) (c i) (d i)) z) (fun _ => Q) Q' :=
  IDLind.env_tendstoInDistribution_whiteNoise hω hW
    (fun i => boxFS (a i) (b i) (c i) (d i) (ha i) (hb i)) (fun n => supp n L)
    (fun i n p => wt n (a i) (b i) (c i) (d i) p) (fun i => wt_max L _ _ _ _)
    (fun i i' => wt_cov L _ _ _ _ _ _ _ _ (ha i) (hb i) (hc i) (hd i))

lemma measurableSet_boxPi {k : ℕ} (a b c d : Fin k → ℝ) :
    MeasurableSet (univ.pi fun j => box (a j) (b j) (c j) (d j)) :=
  MeasurableSet.univ_pi fun j => measurableSet_box _ _ _ _

lemma kernelMeasure_boxPi_ne_top {k : ℕ} (a b c d : Fin k → ℝ) :
    kernelMeasure k (univ.pi fun j => box (a j) (b j) (c j) (d j)) ≠ ⊤ := by
  rw [kernelMeasure, Measure.pi_pi]
  refine ENNReal.prod_ne_top fun j _ => ?_
  rw [box, stripMeasure_prod _ _ measurableSet_Ioc]
  exact ENNReal.mul_ne_top (measure_ne_top_of_subset inter_subset_right (by simp))
    (by simp)

/-- The indicator of a product of strip boxes, as an `L²` kernel. -/
noncomputable def boxInd {k : ℕ} (a b c d : Fin k → ℝ) : Lp ℝ 2 (kernelMeasure k) :=
  indicatorConstLp 2 (measurableSet_boxPi a b c d) (kernelMeasure_boxPi_ne_top a b c d) (1 : ℝ)

/-- A simple chaos: order-`k` kernels are finite combinations of box products drawn from one
finite list of boxes. -/
noncomputable def simpleG {m : ℕ} (a b c d : Fin m → ℝ) (T : (k : ℕ) → Finset (Fin k → Fin m))
    (r : (k : ℕ) → (Fin k → Fin m) → ℝ) (k : ℕ) : Lp ℝ 2 (kernelMeasure k) :=
  ∑ σ ∈ T k, r k σ • boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)

/-- The polynomial in the box variables representing a simple chaos. -/
noncomputable def simplePoly {m : ℕ} (K : ℕ) (T : (k : ℕ) → Finset (Fin k → Fin m))
    (r : (k : ℕ) → (Fin k → Fin m) → ℝ) (v : Fin m → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), ∑ σ ∈ T k, r k σ * ∏ j, v (σ j)

lemma continuous_simplePoly {m : ℕ} (K : ℕ) (T : (k : ℕ) → Finset (Fin k → Fin m))
    (r : (k : ℕ) → (Fin k → Fin m) → ℝ) : Continuous (simplePoly K T r) := by
  unfold simplePoly
  refine continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun σ _ => ?_
  exact continuous_const.mul (continuous_finset_prod _ fun j _ => continuous_apply _)

lemma simpleG_eq_zero {m : ℕ} (a b c d : Fin m → ℝ) (T : (k : ℕ) → Finset (Fin k → Fin m))
    (r : (k : ℕ) → (Fin k → Fin m) → ℝ) {K : ℕ} (hT : ∀ k, K < k → T k = ∅) {k : ℕ}
    (hk : K < k) : simpleG a b c d T r k = 0 := by
  simp [simpleG, hT k hk]

/-- Discrete side of a simple chaos: eventually a.e. the polynomial of the box sums. -/
theorem discreteChaos_simple_ae {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) {m : ℕ} (L : ℝ)
    (a b c d : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1) (hc : ∀ i, -L ≤ c i)
    (hd : ∀ i, d i ≤ L) (K : ℕ) (T : (k : ℕ) → Finset (Fin k → Fin m))
    (r : (k : ℕ) → (Fin k → Fin m) → ℝ) (hT : ∀ k, K < k → T k = ∅)
    (hsep : ∀ k, ∀ σ ∈ T k, ∀ j j', j ≠ j' → b (σ j) < a (σ j') ∨ b (σ j') < a (σ j)) :
    ∀ᶠ n : ℕ in atTop, (discreteChaos ω Q n (simpleG a b c d T r) : Ω → ℝ) =ᵐ[Q]
      fun z => simplePoly K T r
        (fun i => ∑ p ∈ supp n L, wt n (a i) (b i) (c i) (d i) p * ω p z) := by
  have hev : ∀ k ∈ Finset.range (K + 1), ∀ σ ∈ T k, ∀ᶠ n : ℕ in atTop,
      (((n : ℝ) ^ (-(3 * (k : ℝ) / 4)) •
          uStatistic ω Q n k (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)) : Lp ℝ 2 Q) : Ω → ℝ)
        =ᵐ[Q] fun z => ∏ j, ∑ p ∈ supp n L, wt n (a (σ j)) (b (σ j)) (c (σ j)) (d (σ j)) p
          * ω p z :=
    fun k _ σ hσ => uStatistic_box_factor hω L (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)
      (fun j => ha _) (fun j => hb _) (fun j => hc _) (fun j => hd _) (hsep k σ hσ)
      (measurableSet_boxPi _ _ _ _) (kernelMeasure_boxPi_ne_top _ _ _ _)
  have hev' : ∀ᶠ n : ℕ in atTop, ∀ k ∈ Finset.range (K + 1), ∀ σ ∈ T k,
      (((n : ℝ) ^ (-(3 * (k : ℝ) / 4)) •
          uStatistic ω Q n k (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)) : Lp ℝ 2 Q) : Ω → ℝ)
        =ᵐ[Q] fun z => ∏ j, ∑ p ∈ supp n L, wt n (a (σ j)) (b (σ j)) (c (σ j)) (d (σ j)) p
          * ω p z := by
    rw [Filter.eventually_all_finset]
    intro k hk
    rw [Filter.eventually_all_finset]
    exact hev k hk
  filter_upwards [hev', eventually_ge_atTop K] with n hn hKn
  -- reduce the range to `K + 1`
  have hsplit : discreteChaos ω Q n (simpleG a b c d T r) =
      ∑ k ∈ Finset.range (K + 1), ∑ σ ∈ T k, r k σ •
        ((n : ℝ) ^ (-(3 * (k : ℝ) / 4)) •
          uStatistic ω Q n k (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ))) := by
    unfold discreteChaos
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hKn))]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hlin := map_sum (IDL2a.uStatL hω n k)
        (fun σ => r k σ • boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)) (T k)
      simp only [map_smul] at hlin
      change (n : ℝ) ^ (-(3 * (k : ℝ) / 4)) • IDL2a.uStatL hω n k (simpleG a b c d T r k) = _
      rw [simpleG, hlin, Finset.smul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [smul_comm]
      rfl
    · intro k _ hk
      have hk' : K < k := by simpa using hk
      rw [simpleG_eq_zero a b c d T r hT hk']
      change (n : ℝ) ^ (-(3 * (k : ℝ) / 4)) • IDL2a.uStatL hω n k 0 = 0
      rw [map_zero, smul_zero]
  rw [hsplit]
  refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
  have hk_ae : ∀ k ∈ Finset.range (K + 1),
      (((∑ σ ∈ T k, r k σ • ((n : ℝ) ^ (-(3 * (k : ℝ) / 4)) •
          uStatistic ω Q n k (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)))) : Lp ℝ 2 Q) : Ω → ℝ)
        =ᵐ[Q] fun z => ∑ σ ∈ T k, r k σ * ∏ j, ∑ p ∈ supp n L,
          wt n (a (σ j)) (b (σ j)) (c (σ j)) (d (σ j)) p * ω p z := by
    intro k hk
    refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
    have hσ : ∀ σ ∈ T k, (((r k σ • ((n : ℝ) ^ (-(3 * (k : ℝ) / 4)) •
          uStatistic ω Q n k (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)))) : Lp ℝ 2 Q) : Ω → ℝ)
        =ᵐ[Q] fun z => r k σ * ∏ j, ∑ p ∈ supp n L,
          wt n (a (σ j)) (b (σ j)) (c (σ j)) (d (σ j)) p * ω p z := by
      intro σ hσ'
      filter_upwards [Lp.coeFn_smul (r k σ) ((n : ℝ) ^ (-(3 * (k : ℝ) / 4)) •
          uStatistic ω Q n k (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ))), hn k hk σ hσ']
        with z h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    have hall := (ae_all_iff.mpr fun σ : T k => hσ σ.1 σ.2 :
      ∀ᵐ z ∂Q, ∀ σ : T k, _)
    filter_upwards [hall] with z hz
    exact Finset.sum_congr rfl fun σ hσ' => hz ⟨σ, hσ'⟩
  have hall := (ae_all_iff.mpr fun k : Finset.range (K + 1) => hk_ae k.1 k.2 :
    ∀ᵐ z ∂Q, ∀ k : Finset.range (K + 1), _)
  filter_upwards [hall] with z hz
  simp only [simplePoly]
  exact Finset.sum_congr rfl fun k hk => hz ⟨k, hk⟩

/-- Continuous side of a simple chaos: a.e. the polynomial of the white noise on the boxes. -/
theorem fockIntegral_simple_ae {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'}
    [IsProbabilityMeasure Q'] {W : Set (ℝ × ℝ) → Ω' → ℝ}
    {I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q'} (hI : IsMultipleIntegral W Q' I)
    {m : ℕ} (a b c d : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1) (K : ℕ)
    (T : (k : ℕ) → Finset (Fin k → Fin m)) (r : (k : ℕ) → (Fin k → Fin m) → ℝ)
    (hT : ∀ k, K < k → T k = ∅)
    (hsep : ∀ k, ∀ σ ∈ T k, ∀ j j', j ≠ j' → b (σ j) < a (σ j') ∨ b (σ j') < a (σ j)) :
    (fockIntegral I (simpleG a b c d T r) : Ω' → ℝ) =ᵐ[Q']
      fun z => simplePoly K T r (fun i => W (box (a i) (b i) (c i) (d i)) z) := by
  have hsum : fockIntegral I (simpleG a b c d T r) =
      ∑ k ∈ Finset.range (K + 1), ∑ σ ∈ T k, r k σ •
        I k (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)) := by
    unfold fockIntegral
    rw [tsum_eq_sum (s := Finset.range (K + 1))]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [simpleG, map_sum]
      simp only [map_smul]
    · intro k hk
      have hk' : K < k := by simpa using hk
      rw [simpleG_eq_zero a b c d T r hT hk', map_zero]
  rw [hsum]
  refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
  have hk_ae : ∀ k ∈ Finset.range (K + 1),
      (((∑ σ ∈ T k, r k σ • I k (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ))) : Lp ℝ 2 Q') :
          Ω' → ℝ)
        =ᵐ[Q'] fun z => ∑ σ ∈ T k, r k σ * ∏ j, W (box (a (σ j)) (b (σ j)) (c (σ j))
          (d (σ j))) z := by
    intro k _
    refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
    have hσ : ∀ σ ∈ T k, (((r k σ • I k (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ))) :
          Lp ℝ 2 Q') : Ω' → ℝ)
        =ᵐ[Q'] fun z => r k σ * ∏ j, W (box (a (σ j)) (b (σ j)) (c (σ j)) (d (σ j))) z := by
      intro σ hσ'
      have hdisj : Pairwise fun i j =>
          Disjoint (boxFS (a (σ i)) (b (σ i)) (c (σ i)) (d (σ i)) (ha _) (hb _)).1
            (boxFS (a (σ j)) (b (σ j)) (c (σ j)) (d (σ j)) (ha _) (hb _)).1 := by
        intro i j hij
        change Disjoint (box _ _ _ _) (box _ _ _ _)
        refine Set.disjoint_left.mpr ?_
        rintro ⟨t, x⟩ ⟨⟨h1, h2⟩, -⟩ ⟨⟨h3, h4⟩, -⟩
        rcases hsep k σ hσ' i j hij with h | h
        · simp only at h1 h2 h3 h4; linarith
        · simp only at h1 h2 h3 h4; linarith
      have hIk := hI k (fun j => boxFS (a (σ j)) (b (σ j)) (c (σ j)) (d (σ j)) (ha _) (hb _))
        hdisj (measurableSet_boxPi (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ))
        (kernelMeasure_boxPi_ne_top (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ))
      filter_upwards [Lp.coeFn_smul (r k σ) (I k (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ))),
        hIk] with z h1 h2
      rw [h1, Pi.smul_apply, smul_eq_mul]
      congr 1
    have hall := (ae_all_iff.mpr fun σ : T k => hσ σ.1 σ.2 :
      ∀ᵐ z ∂Q', ∀ σ : T k, _)
    filter_upwards [hall] with z hz
    exact Finset.sum_congr rfl fun σ hσ' => hz ⟨σ, hσ'⟩
  have hall := (ae_all_iff.mpr fun k : Finset.range (K + 1) => hk_ae k.1 k.2 :
    ∀ᵐ z ∂Q', ∀ k : Finset.range (K + 1), _)
  filter_upwards [hall] with z hz
  simp only [simplePoly]
  exact Finset.sum_congr rfl fun k hk => hz ⟨k, hk⟩

/-- L1c: Lemma 4.4 for simple chaoses built on time-separated strip boxes. -/
theorem simple_chaos_tendsto {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {W : Set (ℝ × ℝ) → Ω' → ℝ} (hW : IsWhiteNoise W Q')
    {I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q'} (hI : IsMultipleIntegral W Q' I)
    {m : ℕ} (L : ℝ) (a b c d : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1)
    (hc : ∀ i, -L ≤ c i) (hd : ∀ i, d i ≤ L) (K : ℕ) (T : (k : ℕ) → Finset (Fin k → Fin m))
    (r : (k : ℕ) → (Fin k → Fin m) → ℝ) (hT : ∀ k, K < k → T k = ∅)
    (hsep : ∀ k, ∀ σ ∈ T k, ∀ j j', j ≠ j' → b (σ j) < a (σ j') ∨ b (σ j') < a (σ j)) :
    TendstoInDistribution (fun n => (discreteChaos ω Q n (simpleG a b c d T r) : Ω → ℝ))
      atTop (fockIntegral I (simpleG a b c d T r) : Ω' → ℝ) (fun _ => Q) Q' := by
  have h1 := (box_vec_tendsto hω hW L a b c d ha hb hc hd).continuous_comp
    (continuous_simplePoly K T r)
  have h2 := h1.congr (Y := fun n z => simplePoly K T r
      (fun i => ∑ p ∈ supp n L, wt n (a i) (b i) (c i) (d i) p * ω p z))
    (fun n => EventuallyEq.rfl)
    (fockIntegral_simple_ae hI a b c d ha hb K T r hT hsep).symm
  refine tendstoInDistribution_congr_eventually h2 ?_
    (fun n => (Lp.aestronglyMeasurable _).aemeasurable)
  filter_upwards [discreteChaos_simple_ae hω L a b c d ha hb hc hd K T r hT hsep] with n hn
  exact hn.symm

end IDL1c

namespace IDL2b

open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory Set Filter Topology IDL1a IDL1b IDL1c

/-- `∫⁻ x², d(law Z) = ‖Z‖²` for `Z ∈ L²`. -/
lemma lintegral_map_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} (Z : Lp ℝ 2 μ) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(μ.map (Z : α → ℝ)) = ENNReal.ofReal (‖Z‖ ^ 2) := by
  have hf : Measurable fun x : ℝ => ENNReal.ofReal (x ^ 2) := by fun_prop
  rw [lintegral_map' hf.aemeasurable (Lp.aestronglyMeasurable Z).aemeasurable,
    IDL2a.norm_sq_eq_integral, ofReal_integral_eq_lintegral_ofReal]
  · exact (Lp.memLp Z).integrable_sq
  · exact Eventually.of_forall fun x => sq_nonneg _

/-- Fatou for convergence in law: an eventual `L²` bound passes to the limit. -/
theorem norm_le_of_tendstoInDistribution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    {X : ℕ → Lp ℝ 2 Q} {Y : Lp ℝ 2 Q'}
    (h : TendstoInDistribution (fun n => (X n : Ω → ℝ)) atTop (Y : Ω' → ℝ) (fun _ => Q) Q')
    {C : ℝ} (hC : ∀ᶠ n in atTop, ‖X n‖ ≤ C) : ‖Y‖ ≤ C := by
  have hlim := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := Q'.map (Y : Ω' → ℝ)) (μs := fun n => Q.map (X n : Ω → ℝ)) (f := fun x : ℝ => x ^ 2)
    (continuous_pow 2) (fun x => sq_nonneg x)
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto hG)
  rw [lintegral_map_sq Y] at hlim
  simp only [lintegral_map_sq] at hlim
  obtain ⟨n0, hn0⟩ := hC.exists
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hn0
  have hle : atTop.liminf (fun n => ENNReal.ofReal (‖X n‖ ^ 2)) ≤ ENNReal.ofReal (C ^ 2) := by
    refine liminf_le_of_frequently_le' (hC.mono fun n hn => ?_).frequently
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hn 2)
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hlim.trans hle)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC0 two_ne_zero).mp h2

/-- Scaled discrete contraction: `‖n^{-3k/4} 𝒮_k^n f‖ ≤ ‖f‖` for simplex-supported `f`. -/
theorem norm_scaled_uStatistic_le {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) {n : ℕ}
    (hn : 1 ≤ n) (k : ℕ) (f : Lp ℝ 2 (kernelMeasure k)) (hf : SimplexSupported f) :
    ‖((n : ℝ) ^ (-(3 * (k : ℝ) / 4))) • uStatistic ω Q n k f‖ ≤ ‖f‖ := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : eLpNorm (uStatistic ω Q n k f : Ω → ℝ) 2 Q ^ 2 ≤
      ENNReal.ofReal ((n : ℝ) ^ (3 * (k : ℝ) / 2)) *
        eLpNorm (f : (Fin k → ℝ × ℝ) → ℝ) 2 (kernelMeasure k) ^ 2 :=
    (IDL2a.uStatistic_norm_bound hω n k f hf).trans
      (by gcongr; exact IDL2a.cellAverageNormSq_le f n)
  rw [IDL2a.eLpNorm_sq_eq_ofReal, IDL2a.eLpNorm_sq_eq_ofReal,
    ← ENNReal.ofReal_mul (by positivity)] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hc : ((n : ℝ) ^ (-(3 * (k : ℝ) / 4))) ^ 2 * (n : ℝ) ^ (3 * (k : ℝ) / 2) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos]
    norm_num
    ring_nf
    simp
  have hsq : ‖((n : ℝ) ^ (-(3 * (k : ℝ) / 4))) • uStatistic ω Q n k f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc ((n : ℝ) ^ (-(3 * (k : ℝ) / 4))) ^ 2 * ‖uStatistic ω Q n k f‖ ^ 2
        ≤ ((n : ℝ) ^ (-(3 * (k : ℝ) / 4))) ^ 2 * ((n : ℝ) ^ (3 * (k : ℝ) / 2) * ‖f‖ ^ 2) := by
          gcongr
      _ = ‖f‖ ^ 2 := by rw [← mul_assoc, hc, one_mul]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- Time-ordered box products lie in the simplex. -/
lemma boxPi_sub_simplex {k : ℕ} (a b c d : Fin k → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, b j ≤ 1)
    (hord : ∀ j j' : Fin k, j < j' → b j < a j') :
    (univ.pi fun j => box (a j) (b j) (c j) (d j)) ⊆ simplex k := by
  obtain _ | k := k
  · intro z _ j; exact j.elim0
  intro z hz j
  have hzj : ∀ j, a j < (z j).1 ∧ (z j).1 ≤ b j := fun j => ((hz j (mem_univ _)).1)
  refine ⟨?_, (hzj j).2.trans (hb j)⟩
  induction j using Fin.cases with
  | zero => simpa [withOrigin] using (ha 0).trans_lt (hzj 0).1
  | succ i =>
    have : (withOrigin z (Fin.succ i).castSucc) = z i.castSucc := by
      simp [withOrigin]
    rw [this]
    exact ((hzj _).2.trans_lt (hord _ _ (Fin.castSucc_lt_succ (i := i)))).trans (hzj _).1

/-- Simple single-order kernels on time-ordered boxes are simplex supported. -/
lemma simplexSupported_simple {m k : ℕ} (a b c d : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, b i ≤ 1) (S : Finset (Fin k → Fin m)) (r : (Fin k → Fin m) → ℝ)
    (hord : ∀ σ ∈ S, ∀ j j' : Fin k, j < j' → b (σ j) < a (σ j')) :
    SimplexSupported (∑ σ ∈ S, r σ • boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)) := by
  have hσ : ∀ σ ∈ S, ∀ᵐ z ∂(kernelMeasure k), z ∉ simplex k →
      ((r σ • boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ) : Lp ℝ 2 (kernelMeasure k)) :
        (Fin k → ℝ × ℝ) → ℝ) z = 0 := by
    intro σ hσS
    filter_upwards [Lp.coeFn_smul (r σ) (boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)),
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_boxPi (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ))
        (hμs := kernelMeasure_boxPi_ne_top (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)) (c := (1 : ℝ))]
      with z h1 h2 hz
    rw [h1, Pi.smul_apply, boxInd, h2, Set.indicator_of_notMem, smul_zero]
    exact fun hz' => hz (boxPi_sub_simplex (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ) (fun j => ha _)
      (fun j => hb _) (hord σ hσS) hz')
  have hall := (ae_all_iff.mpr fun σ : S => hσ σ.1 σ.2 :
    ∀ᵐ z ∂(kernelMeasure k), ∀ σ : S, _)
  filter_upwards [Lp.coeFn_fun_finsetSum S
    (fun σ => r σ • boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)), hall] with z h1 h2 hz
  rw [h1]
  exact Finset.sum_eq_zero fun σ hσS => h2 ⟨σ, hσS⟩ hz

/-- The single-order index data of a simple kernel. -/
def singleT {m : ℕ} (k : ℕ) (S : Finset (Fin k → Fin m)) (k' : ℕ) : Finset (Fin k' → Fin m) :=
  if h : k = k' then h ▸ S else ∅

/-- The single-order coefficients of a simple kernel. -/
noncomputable def singleR {m : ℕ} (k : ℕ) (r : (Fin k → Fin m) → ℝ) (k' : ℕ) :
    (Fin k' → Fin m) → ℝ :=
  if h : k = k' then h ▸ r else 0

lemma simpleG_single_self {m : ℕ} (a b c d : Fin m → ℝ) (k : ℕ) (S : Finset (Fin k → Fin m))
    (r : (Fin k → Fin m) → ℝ) :
    simpleG a b c d (singleT k S) (singleR k r) k =
      ∑ σ ∈ S, r σ • boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ) := by
  simp [simpleG, singleT, singleR]

lemma simpleG_single_ne {m : ℕ} (a b c d : Fin m → ℝ) (k : ℕ) (S : Finset (Fin k → Fin m))
    (r : (Fin k → Fin m) → ℝ) {k' : ℕ} (h : k ≠ k') :
    simpleG a b c d (singleT k S) (singleR k r) k' = 0 := by
  simp [simpleG, singleT, h]

/-- L2b': the multiple integral is a contraction on simple time-ordered box kernels. -/
theorem norm_I_simple_le {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {W : Set (ℝ × ℝ) → Ω' → ℝ} (hW : IsWhiteNoise W Q')
    {I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q'} (hI : IsMultipleIntegral W Q' I)
    {m : ℕ} (L : ℝ) (a b c d : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1)
    (hc : ∀ i, -L ≤ c i) (hd : ∀ i, d i ≤ L) (k : ℕ) (S : Finset (Fin k → Fin m))
    (r : (Fin k → Fin m) → ℝ) (hord : ∀ σ ∈ S, ∀ j j' : Fin k, j < j' → b (σ j) < a (σ j')) :
    ‖I k (∑ σ ∈ S, r σ • boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ))‖ ≤
      ‖∑ σ ∈ S, r σ • boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ)‖ := by
  set f := ∑ σ ∈ S, r σ • boxInd (a ∘ σ) (b ∘ σ) (c ∘ σ) (d ∘ σ) with hfdef
  have hT : ∀ k', k < k' → singleT k S k' = ∅ := fun k' hk => by
    simp [singleT, hk.ne]
  have hsep : ∀ k', ∀ σ ∈ singleT k S k', ∀ j j', j ≠ j' →
      b (σ j) < a (σ j') ∨ b (σ j') < a (σ j) := by
    intro k' σ hσ j j' hjj
    by_cases h : k = k'
    · subst h
      have hσ' : σ ∈ S := by simpa [singleT] using hσ
      rcases lt_or_gt_of_ne hjj with h' | h'
      · exact Or.inl (hord σ hσ' j j' h')
      · exact Or.inr (hord σ hσ' j' j h')
    · simp [singleT, h] at hσ
  have hconv := simple_chaos_tendsto hω hW hI L a b c d ha hb hc hd k (singleT k S)
    (singleR k r) hT hsep
  have hfock : fockIntegral I (simpleG a b c d (singleT k S) (singleR k r)) = I k f := by
    unfold fockIntegral
    rw [tsum_eq_single k, simpleG_single_self]
    intro k' hk'
    rw [simpleG_single_ne a b c d k S r (Ne.symm hk'), map_zero]
  have hdisc : ∀ n, k ≤ n → discreteChaos ω Q n (simpleG a b c d (singleT k S) (singleR k r)) =
      ((n : ℝ) ^ (-(3 * (k : ℝ) / 4))) • uStatistic ω Q n k f := by
    intro n hkn
    unfold discreteChaos
    rw [Finset.sum_eq_single k, simpleG_single_self]
    · intro k' _ hk'
      rw [simpleG_single_ne a b c d k S r (Ne.symm hk')]
      change (n : ℝ) ^ (-(3 * (k' : ℝ) / 4)) • IDL2a.uStatL hω n k' 0 = 0
      rw [map_zero, smul_zero]
    · intro hk; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn)) hk
  rw [hfock] at hconv
  refine norm_le_of_tendstoInDistribution hconv ?_
  filter_upwards [eventually_ge_atTop (max k 1)] with n hn
  rw [hdisc n (le_of_max_le_left hn)]
  exact norm_scaled_uStatistic_le hω (le_of_max_le_right hn) k f
    (simplexSupported_simple a b c d ha hb S r hord)

end IDL2b

namespace IDL3a

open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory Set Filter Topology
  IDL1a IDL1b IDL1c MeasurableSpace

/-- Time-ordered, separated box tuples inside `[0,1]`. -/
def Good {k : ℕ} (a b : Fin k → ℝ) : Prop :=
  (∀ j, 0 ≤ a j) ∧ (∀ j, b j ≤ 1) ∧ ∀ j j' : Fin k, j < j' → b j < a j'

/-- Indicators of good box products. -/
def boxSet (k : ℕ) : Set (Lp ℝ 2 (kernelMeasure k)) :=
  {f | ∃ a b c d : Fin k → ℝ, Good a b ∧ f = boxInd a b c d}

def CR : Set (Set ℝ) := {S | ∃ l u : ℝ, l < u ∧ Ioc l u = S}

lemma isPiSystem_CR : IsPiSystem CR := isPiSystem_Ioc id id

lemma gen_CR : generateFrom CR = (inferInstance : MeasurableSpace ℝ) :=
  (borel_eq_generateFrom_Ioc ℝ).symm.trans BorelSpace.measurable_eq.symm

lemma span_CR : IsCountablySpanning CR := by
  refine ⟨fun n : ℕ => Ioc (-((n : ℝ) + 1)) ((n : ℝ) + 1), fun n => ⟨_, _, by linarith, rfl⟩, ?_⟩
  refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌈|x|⌉₊, ?_⟩
  have h1 := Nat.le_ceil |x|
  constructor
  · linarith [neg_abs_le x]
  · linarith [le_abs_self x]

def C2 : Set (Set (ℝ × ℝ)) := image2 (· ×ˢ ·) CR CR

def Cpi (k : ℕ) : Set (Set (Fin k → ℝ × ℝ)) := pi univ '' pi univ fun _ => C2

lemma gen_Cpi (k : ℕ) : generateFrom (Cpi k) = (inferInstance : MeasurableSpace (Fin k → ℝ × ℝ)) :=
  generateFrom_eq_pi (fun _ => generateFrom_eq_prod gen_CR gen_CR span_CR span_CR)
    (fun _ => span_CR.prod span_CR)

lemma isPiSystem_Cpi (k : ℕ) : IsPiSystem (Cpi k) :=
  IsPiSystem.pi fun _ => isPiSystem_CR.prod isPiSystem_CR

lemma mem_Cpi {k : ℕ} {t : Set (Fin k → ℝ × ℝ)} (ht : t ∈ Cpi k) :
    ∃ l u l' u' : Fin k → ℝ, t = univ.pi fun j => box (l j) (u j) (l' j) (u' j) := by
  obtain ⟨S, hS, rfl⟩ := ht
  have : ∀ j, ∃ l u l' u' : ℝ, S j = box l u l' u' := by
    intro j
    obtain ⟨A, ⟨l, u, -, rfl⟩, B, ⟨l', u', -, rfl⟩, hAB⟩ := hS j (mem_univ j)
    exact ⟨l, u, l', u', hAB.symm⟩
  choose l u l' u' h using this
  exact ⟨l, u, l', u', by simp only [← h]⟩

lemma box_inter (a b c d a' b' c' d' : ℝ) :
    box a b c d ∩ box a' b' c' d' = box (max a a') (min b b') (max c c') (min d d') := by
  simp only [box, prod_inter_prod, Ioc_inter_Ioc]

lemma boxPi_inter {k : ℕ} (a b c d a' b' c' d' : Fin k → ℝ) :
    (univ.pi fun j => box (a j) (b j) (c j) (d j)) ∩ (univ.pi fun j => box (a' j) (b' j) (c' j) (d' j))
      = univ.pi fun j => box (max (a j) (a' j)) (min (b j) (b' j)) (max (c j) (c' j))
          (min (d j) (d' j)) := by
  rw [← pi_inter_distrib]
  simp only [box_inter]

lemma good_inter {k : ℕ} {a b : Fin k → ℝ} (l u : Fin k → ℝ) (h : Good a b) :
    Good (fun j => max (l j) (a j)) (fun j => min (u j) (b j)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j => (h1 j).trans (le_max_right _ _), fun j => (min_le_right _ _).trans (h2 j),
    fun j j' hjj => ?_⟩
  exact ((min_le_right _ _).trans_lt (h3 j j' hjj)).trans_le (le_max_right _ _)

/-- An `L²` function orthogonal to all good box products vanishes a.e. on every good box product. -/
theorem ae_zero_on_good {k : ℕ} (u : Lp ℝ 2 (kernelMeasure k))
    (hu : ∀ a b c d : Fin k → ℝ, Good a b →
      ∫ z in univ.pi (fun j => box (a j) (b j) (c j) (d j)), u z ∂(kernelMeasure k) = 0)
    (a b c d : Fin k → ℝ) (hg : Good a b) :
    ∀ᵐ z ∂((kernelMeasure k).restrict (univ.pi fun j => box (a j) (b j) (c j) (d j))), u z = 0 := by
  set D := univ.pi fun j => box (a j) (b j) (c j) (d j) with hD
  have hDm : MeasurableSet D := measurableSet_boxPi a b c d
  haveI : IsFiniteMeasure ((kernelMeasure k).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (kernelMeasure_boxPi_ne_top a b c d)⟩
  have hint : Integrable (u : (Fin k → ℝ × ℝ) → ℝ) ((kernelMeasure k).restrict D) :=
    ((Lp.memLp u).restrict D).integrable one_le_two
  have hclaim : ∀ t (ht : MeasurableSet t), ∫ z in t ∩ D, u z ∂(kernelMeasure k) = 0 := by
    refine induction_on_inter (gen_Cpi k).symm (isPiSystem_Cpi k) ?_ ?_ ?_ ?_
    · simp
    · intro t ht
      obtain ⟨l, u', l', u'', rfl⟩ := mem_Cpi ht
      rw [hD, boxPi_inter]
      exact hu _ _ _ _ (good_inter l u' hg)
    · intro t htm ht
      have h1 := integral_inter_add_sdiff (μ := kernelMeasure k) (f := (u : (Fin k → ℝ × ℝ) → ℝ))
        htm hint
      have e1 : D ∩ t = t ∩ D := inter_comm _ _
      have e2 : D \ t = tᶜ ∩ D := by rw [diff_eq, inter_comm]
      rw [e1, e2, ht, zero_add] at h1
      rw [h1]
      exact hu a b c d hg
    · intro f hdisj hfm hf
      rw [iUnion_inter, integral_iUnion (fun i => (hfm i).inter hDm)
        (fun i j hij => (hdisj hij).mono inter_subset_left inter_subset_left)
        ((show IntegrableOn (u : (Fin k → ℝ × ℝ) → ℝ) D (kernelMeasure k) from hint).mono_set
          (iUnion_subset fun i => inter_subset_right))]
      · simp [hf]
  have := hint.ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _ => by
    rw [Measure.restrict_restrict hs]
    exact hclaim s hs
  filter_upwards [this] with z hz using hz

/-- The countable family of rational good regions. -/
def Dset {k : ℕ} (i : (Fin k → ℚ × ℚ) × ℕ) : Set (Fin k → ℝ × ℝ) :=
  open scoped Classical in
  if Good (fun j => ((i.1 j).1 : ℝ)) (fun j => ((i.1 j).2 : ℝ)) then
    univ.pi fun j => box ((i.1 j).1 : ℝ) ((i.1 j).2 : ℝ) (-(i.2 : ℝ)) (i.2 : ℝ)
  else ∅

lemma measurableSet_Dset {k : ℕ} (i : (Fin k → ℚ × ℚ) × ℕ) : MeasurableSet (Dset i) := by
  unfold Dset; split_ifs
  · exact measurableSet_boxPi _ _ _ _
  · exact MeasurableSet.empty

/-- Gap bound along the simplex. -/
lemma simplex_gap {k : ℕ} {z : Fin k → ℝ × ℝ} (hz : z ∈ simplex k) :
    ∃ δ > 0, (∀ j, δ ≤ (z j).1) ∧ ∀ j j' : Fin k, j < j' → (z j).1 + δ ≤ (z j').1 := by
  set gap : Fin k → ℝ := fun j => (z j).1 - (withOrigin z j.castSucc).1 with hgap
  have hgpos : ∀ j, 0 < gap j := fun j => sub_pos.mpr (hz j).1
  set δ : ℝ := 1 / (1 + ∑ j, 1 / gap j) with hδ
  have hsum : 0 ≤ ∑ j, 1 / gap j := Finset.sum_nonneg fun j _ => (one_div_pos.mpr (hgpos j)).le
  have hδpos : 0 < δ := by positivity
  have hδle : ∀ j, δ ≤ gap j := by
    intro j
    have h1 : 1 / gap j ≤ 1 + ∑ j, 1 / gap j := by
      have := Finset.single_le_sum (f := fun j => 1 / gap j)
        (fun j _ => (one_div_pos.mpr (hgpos j)).le) (Finset.mem_univ j)
      linarith
    rw [hδ, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (hgpos j)] at h1
    linarith
  set s : Fin (k + 1) → ℝ := fun i => (withOrigin z i).1 with hs
  have hmono : Monotone fun i : Fin (k + 1) => s i - δ * (i : ℕ) := by
    rw [Fin.monotone_iff_le_succ]
    intro j
    have h := hδle j
    simp only [hs, hgap, withOrigin, Fin.cons_succ, Fin.coe_castSucc, Fin.val_succ] at h ⊢
    push_cast
    linarith
  have hstep : ∀ i i' : Fin (k + 1), i ≤ i' → s i + δ * ((i' : ℕ) - (i : ℕ) : ℝ) ≤ s i' := by
    intro i i' hii
    have := hmono hii
    simp only at this
    linarith
  have hsucc : ∀ j : Fin k, s j.succ = (z j).1 := fun j => by simp [hs, withOrigin]
  have hs0 : s 0 = 0 := by simp [hs, withOrigin]
  refine ⟨δ, hδpos, fun j => ?_, fun j j' hjj => ?_⟩
  · have := hstep 0 j.succ (Fin.zero_le _)
    rw [hs0, hsucc] at this
    have hj : (1 : ℝ) ≤ ((j.succ : ℕ) : ℝ) - ((0 : Fin (k + 1)) : ℕ) := by simp
    nlinarith
  · have := hstep j.succ j'.succ (Fin.succ_le_succ_iff.mpr hjj.le)
    rw [hsucc, hsucc] at this
    have hj : (1 : ℝ) ≤ ((j'.succ : ℕ) : ℝ) - ((j.succ : ℕ) : ℝ) := by
      have : (j : ℕ) < j' := hjj
      simp only [Fin.val_succ]; push_cast
      have : ((j : ℕ) : ℝ) + 1 ≤ (j' : ℕ) := by exact_mod_cast this
      linarith
    nlinarith

lemma simplex_sub_iUnion (k : ℕ) : simplex k ⊆ ⋃ i, Dset (k := k) i := by
  intro z hz
  obtain ⟨δ, hδ, hpos, hsep⟩ := simplex_gap hz
  have ha : ∀ j, ∃ q : ℚ, (z j).1 - δ / 2 < q ∧ (q : ℝ) < (z j).1 := fun j =>
    exists_rat_btwn (by linarith)
  have hb : ∀ j, ∃ q : ℚ, (z j).1 < q ∧ (q : ℝ) < (z j).1 + δ / 2 := fun j =>
    exists_rat_btwn (by linarith)
  choose qa hqa using ha
  choose qb hqb using hb
  set R : ℕ := ⌈∑ j, |(z j).2|⌉₊ + 1 with hR
  refine mem_iUnion.2 ⟨(fun j => (qa j, min (qb j) 1), R), ?_⟩
  have hgood : Good (fun j => (((qa j, min (qb j) 1) : ℚ × ℚ).1 : ℝ))
      (fun j => (((qa j, min (qb j) 1) : ℚ × ℚ).2 : ℝ)) := by
    refine ⟨fun j => ?_, fun j => ?_, fun j j' hjj => ?_⟩
    · simp only; linarith [hqa j, hpos j]
    · simp only [Rat.cast_min, Rat.cast_one]; exact min_le_right _ _
    · simp only [Rat.cast_min, Rat.cast_one]
      linarith [min_le_left ((qb j : ℝ)) 1, hqb j, hqa j', hsep j j' hjj]
  unfold Dset
  rw [if_pos hgood]
  intro j _
  have h1 : (z j).1 ≤ 1 := (hz j).2
  have hx : |(z j).2| ≤ ∑ j, |(z j).2| :=
    Finset.single_le_sum (f := fun j => |(z j).2|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  have hR' : ∑ j, |(z j).2| < (R : ℝ) := by
    rw [hR]; push_cast; linarith [Nat.le_ceil (∑ j, |(z j).2|)]
  refine ⟨⟨(hqa j).2, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [Rat.cast_min, Rat.cast_one]; exact le_min (hqb j).1.le h1
  · simp only; linarith [neg_abs_le (z j).2]
  · simp only; linarith [le_abs_self (z j).2]

/-- An `L²` function orthogonal to all good box products vanishes a.e. on the simplex. -/
theorem ae_zero_on_simplex {k : ℕ} (u : Lp ℝ 2 (kernelMeasure k))
    (hu : ∀ a b c d : Fin k → ℝ, Good a b →
      ∫ z in univ.pi (fun j => box (a j) (b j) (c j) (d j)), u z ∂(kernelMeasure k) = 0) :
    ∀ᵐ z ∂(kernelMeasure k), z ∈ simplex k → u z = 0 := by
  have hi : ∀ i : (Fin k → ℚ × ℚ) × ℕ, ∀ᵐ z ∂((kernelMeasure k).restrict (Dset i)), u z = 0 := by
    intro i
    unfold Dset
    split_ifs with hg
    · exact ae_zero_on_good u hu _ _ _ _ hg
    · simp
  have hU := (ae_restrict_iUnion_iff (μ := kernelMeasure k) Dset (fun z => u z = 0)).2 hi
  rw [ae_restrict_iff' (MeasurableSet.iUnion measurableSet_Dset)] at hU
  filter_upwards [hU] with z hz hzs using hz (simplex_sub_iUnion k hzs)

/-- L3a: good box products span a dense subspace of the simplex-supported kernels. -/
theorem mem_closure_span {k : ℕ} (h : Lp ℝ 2 (kernelMeasure k)) (hh : SimplexSupported h) :
    h ∈ (Submodule.span ℝ (boxSet k)).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro u hu
  have hu' : ∀ a b c d : Fin k → ℝ, Good a b →
      ∫ z in univ.pi (fun j => box (a j) (b j) (c j) (d j)), u z ∂(kernelMeasure k) = 0 := by
    intro a b c d hg
    have hmem : boxInd a b c d ∈ Submodule.span ℝ (boxSet k) :=
      Submodule.subset_span ⟨a, b, c, d, hg, rfl⟩
    have := (Submodule.mem_orthogonal _ _).1 hu _ hmem
    rwa [boxInd, L2.inner_indicatorConstLp_one] at this
  have hz := ae_zero_on_simplex u hu'
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hz, hh] with z h1 h2
  by_cases hzs : z ∈ simplex k
  · simp [h1 hzs]
  · simp [h2 hzs]

end IDL3a

namespace IDL2c

open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory Set Filter Topology
  IDL1a IDL1b IDL1c

/-- Contraction on the span of good box products. -/
theorem norm_I_span_le {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {W : Set (ℝ × ℝ) → Ω' → ℝ} (hW : IsWhiteNoise W Q')
    {I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q'} (hI : IsMultipleIntegral W Q' I)
    {k : ℕ} (v : Lp ℝ 2 (kernelMeasure k)) (hv : v ∈ Submodule.span ℝ (IDL3a.boxSet k)) :
    ‖I k v‖ ≤ ‖v‖ := by
  classical
  obtain ⟨n, r, g, rfl⟩ := Submodule.mem_span_set'.1 hv
  have hg : ∀ i, ∃ A B C D : Fin k → ℝ, IDL3a.Good A B ∧
      (g i : Lp ℝ 2 (kernelMeasure k)) = boxInd A B C D := fun i => (g i).2
  choose A B C D hgood heq using hg
  let e : Fin n × Fin k ≃ Fin (n * k) := finProdFinEquiv
  let a : Fin (n * k) → ℝ := fun p => A (e.symm p).1 (e.symm p).2
  let b : Fin (n * k) → ℝ := fun p => B (e.symm p).1 (e.symm p).2
  let c : Fin (n * k) → ℝ := fun p => C (e.symm p).1 (e.symm p).2
  let d : Fin (n * k) → ℝ := fun p => D (e.symm p).1 (e.symm p).2
  let σ : Fin n → Fin k → Fin (n * k) := fun i j => e (i, j)
  have ha' : ∀ i, a ∘ σ i = A i := fun i => funext fun j => by simp [a, σ]
  have hb' : ∀ i, b ∘ σ i = B i := fun i => funext fun j => by simp [b, σ]
  have hc' : ∀ i, c ∘ σ i = C i := fun i => funext fun j => by simp [c, σ]
  have hd' : ∀ i, d ∘ σ i = D i := fun i => funext fun j => by simp [d, σ]
  have hsum : ∑ i, r i • (g i : Lp ℝ 2 (kernelMeasure k)) =
      ∑ τ ∈ Finset.univ.image σ, (∑ i ∈ Finset.univ.filter (fun i => σ i = τ), r i) •
        boxInd (a ∘ τ) (b ∘ τ) (c ∘ τ) (d ∘ τ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := σ) (t := Finset.univ.image σ)
      (fun i _ => Finset.mem_image_of_mem σ (Finset.mem_univ i))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hστ : σ i = τ := (Finset.mem_filter.1 hi).2
    rw [heq i, ← hστ, ha', hb', hc', hd']
  rw [hsum]
  set L : ℝ := ∑ p, (|c p| + |d p|) with hL
  have hcd : ∀ p, |c p| + |d p| ≤ L := fun p =>
    Finset.single_le_sum (f := fun p => |c p| + |d p|) (fun p _ => by positivity)
      (Finset.mem_univ p)
  refine IDL2b.norm_I_simple_le hω hW hI L a b c d (fun p => (hgood _).1 _)
    (fun p => (hgood _).2.1 _) (fun p => ?_) (fun p => ?_) k _ _ ?_
  · linarith [hcd p, neg_abs_le (c p), abs_nonneg (d p)]
  · linarith [hcd p, le_abs_self (d p), abs_nonneg (c p)]
  · intro τ hτ j j' hjj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hτ
    have h1 := (hgood i).2.2 j j' hjj
    simpa [a, b, σ] using h1

/-- L2b: the multiple integral is a contraction on simplex-supported kernels. -/
theorem norm_I_le {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {W : Set (ℝ × ℝ) → Ω' → ℝ} (hW : IsWhiteNoise W Q')
    {I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q'} (hI : IsMultipleIntegral W Q' I)
    {k : ℕ} (h : Lp ℝ 2 (kernelMeasure k)) (hh : SimplexSupported h) : ‖I k h‖ ≤ ‖h‖ := by
  have hcl : IsClosed {v : Lp ℝ 2 (kernelMeasure k) | ‖I k v‖ ≤ ‖v‖} :=
    isClosed_le (I k).continuous.norm continuous_norm
  have hsub : (Submodule.span ℝ (IDL3a.boxSet k) : Set (Lp ℝ 2 (kernelMeasure k))) ⊆
      {v | ‖I k v‖ ≤ ‖v‖} := fun v hv => norm_I_span_le hω hW hI v hv
  have hmem : h ∈ closure (Submodule.span ℝ (IDL3a.boxSet k) : Set (Lp ℝ 2 (kernelMeasure k))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact IDL3a.mem_closure_span h hh
  exact closure_minimal hsub hcl hmem

end IDL2c

namespace IDL4

open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory Set Filter Topology
  IDL1a IDL1b IDL1c

lemma key {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (F : ℝ → ℝ) (M : ℝ)
    (hFb : ∀ x y, dist (F x) (F y) ≤ M) (L : NNReal) (hFl : LipschitzWith L F)
    (δ : ℝ) (hδ : 0 < δ) :
    |∫ ω, F ω ∂(μ.map Y) - ∫ ω, F ω ∂(μ.map X)|
      ≤ L * δ + M * μ.real {a | δ < |X a - Y a|} := by
  have hFc : Continuous F := hFl.continuous
  have hM : 0 ≤ M := by simpa using hFb 0 0
  have hS : NullMeasurableSet {a | δ < |X a - Y a|} μ :=
    nullMeasurableSet_lt (by fun_prop) (by fun_prop)
  have h_int_Y : Integrable (fun x ↦ F (Y x)) μ := by
    refine Integrable.of_bound (by fun_prop) (‖F 0‖ + M) (ae_of_all _ fun a ↦ ?_)
    specialize hFb (Y a) 0
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (F (Y a)) (F 0)).trans hFb
  have h_int_X : Integrable (fun x ↦ F (X x)) μ := by
    refine Integrable.of_bound (by fun_prop) (‖F 0‖ + M) (ae_of_all _ fun a ↦ ?_)
    specialize hFb (X a) 0
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (F (X a)) (F 0)).trans hFb
  have h_int_ind : Integrable (fun a ↦ (L : ℝ) * δ + M * {a | δ < |X a - Y a|}.indicator 1 a) μ :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).indicator₀ hS).const_mul M)
  rw [integral_map hY (by fun_prop), integral_map hX (by fun_prop),
    ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
  calc ‖∫ a, F (Y a) - F (X a) ∂μ‖
      ≤ ∫ a, ‖F (Y a) - F (X a)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ a, ((L : ℝ) * δ + M * {a | δ < |X a - Y a|}.indicator 1 a) ∂μ := by
        refine integral_mono (h_int_Y.sub h_int_X).norm h_int_ind fun a ↦ ?_
        by_cases ha : δ < |X a - Y a|
        · have : {a | δ < |X a - Y a|}.indicator (1 : Ω → ℝ) a = 1 :=
            Set.indicator_of_mem (show a ∈ {a | δ < |X a - Y a|} from ha) _
          rw [this, mul_one, ← dist_eq_norm]
          have := hFb (Y a) (X a)
          have : 0 ≤ (L : ℝ) * δ := by positivity
          linarith
        · have : {a | δ < |X a - Y a|}.indicator (1 : Ω → ℝ) a = 0 :=
            Set.indicator_of_notMem (show a ∉ {a | δ < |X a - Y a|} from ha) _
          rw [this, mul_zero, add_zero, ← dist_eq_norm]
          refine (hFl.dist_le_mul _ _).trans ?_
          gcongr
          rw [Real.dist_eq, abs_sub_comm]
          exact not_lt.1 ha
    _ = L * δ + M * μ.real {a | δ < |X a - Y a|} := by
        have h2 : Integrable (fun a ↦ M * {a | δ < |X a - Y a|}.indicator (1 : Ω → ℝ) a) μ :=
          ((integrable_const (1 : ℝ)).indicator₀ hS).const_mul M
        rw [integral_add (integrable_const _) h2, integral_const_mul M, integral_indicator₀ hS]
        simp

lemma lip_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : ∀ i, Ω i → ℝ} {Z : Ω' → ℝ} (h : TendstoInDistribution X l Z μ μ')
    (F : ℝ → ℝ) (hb : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C) (hl : ∃ L, LipschitzWith L F) :
    Tendsto (fun i ↦ ∫ ω, F ω ∂((μ i).map (X i))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z))) := by
  have := (tendsto_iff_forall_lipschitz_integral_tendsto.1 h.tendsto) F hb hl
  simpa using this

set_option backward.isDefEq.respectTransparency.types false in
lemma of_lip {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : ∀ i, Ω i → ℝ} {Z : Ω' → ℝ} (hX : ∀ i, AEMeasurable (X i) (μ i))
    (hZ : AEMeasurable Z μ')
    (h : ∀ F : ℝ → ℝ, (∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C) → (∃ L, LipschitzWith L F) →
      Tendsto (fun i ↦ ∫ ω, F ω ∂((μ i).map (X i))) l (𝓝 (∫ ω, F ω ∂(μ'.map Z)))) :
    TendstoInDistribution X l Z μ μ' := by
  refine ⟨hX, hZ, ?_⟩
  rwa [tendsto_iff_forall_lipschitz_integral_tendsto]


/-- Uniform approximation (Billingsley Thm 3.2) with an eventual uniform condition. -/
theorem approx
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    {Ωk : ℕ → Type*} [∀ k, MeasurableSpace (Ωk k)] (Pk : ∀ k, Measure (Ωk k))
    [∀ k, IsProbabilityMeasure (Pk k)]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Ykn : ℕ → ∀ n, Ω n → ℝ) (Yk : ∀ k, Ωk k → ℝ) (Yn : ∀ n, Ω n → ℝ) (Y : Ω' → ℝ)
    (hYn : ∀ n, AEMeasurable (Yn n) (P n))
    (h_row : ∀ k, TendstoInDistribution (Ykn k) atTop (Yk k) P (Pk k))
    (h_unif : ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, 0 < θ → ∀ᶠ k in atTop, ∀ᶠ n in atTop,
      P n {a | ε < |Ykn k n a - Yn n a|} ≤ ENNReal.ofReal θ)
    (h_col : TendstoInDistribution Yk atTop Y Pk P') :
    TendstoInDistribution Yn atTop Y P P' := by
  refine of_lip hYn h_col.aemeasurable_limit ?_
  rintro F ⟨M, hb⟩ ⟨L, hl⟩
  rw [Metric.tendsto_nhds]
  intro η hη
  have hM : 0 ≤ M := by simpa using hb 0 0
  set δ : ℝ := η / (4 * ((L : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hLδ : (L : ℝ) * δ ≤ η / 4 := by
    have h1 : ((L : ℝ) + 1) * δ = η / 4 := by rw [hδdef]; field_simp
    have h2 : (L : ℝ) * δ ≤ ((L : ℝ) + 1) * δ := by nlinarith
    linarith
  set θ : ℝ := η / (4 * (M + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  have hMθ : M * θ ≤ η / 4 := by
    have h1 : (M + 1) * θ = η / 4 := by rw [hθdef]; field_simp
    have h2 : M * θ ≤ (M + 1) * θ := by nlinarith
    linarith
  have hA := h_unif δ hδ θ hθ
  have hB := Metric.tendsto_nhds.1 (lip_tendsto h_col F ⟨M, hb⟩ ⟨L, hl⟩) (η / 4)
    (by positivity)
  obtain ⟨k, hk1, hk2⟩ := (hA.and hB).exists
  have hC := Metric.tendsto_nhds.1 (lip_tendsto (h_row k) F ⟨M, hb⟩ ⟨L, hl⟩) (η / 4)
    (by positivity)
  filter_upwards [hC, hk1] with n hn hk1n
  have hK := key (P n) (Ykn k n) (Yn n) ((h_row k).forall_aemeasurable n) (hYn n)
    F M hb L hl δ hδ
  have hS : (P n).real {a | δ < |Ykn k n a - Yn n a|} ≤ θ :=
    ENNReal.toReal_le_of_le_ofReal hθ.le hk1n
  have hMS : M * (P n).real {a | δ < |Ykn k n a - Yn n a|} ≤ η / 4 :=
    (mul_le_mul_of_nonneg_left hS hM).trans hMθ
  rw [Real.dist_eq] at hn hk2 ⊢
  have tri := abs_sub_le (∫ ω, F ω ∂((P n).map (Yn n))) (∫ ω, F ω ∂((P n).map (Ykn k n)))
    (∫ ω, F ω ∂(P'.map Y))
  have tri2 := abs_sub_le (∫ ω, F ω ∂((P n).map (Ykn k n))) (∫ ω, F ω ∂((Pk k).map (Yk k)))
    (∫ ω, F ω ∂(P'.map Y))
  linarith

/-- Chebyshev for an `L²` element. -/
lemma cheb {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    (X : Lp ℝ 2 Q) {ε : ℝ} (hε : 0 < ε) :
    Q {a | ε < |(X : Ω → ℝ) a|} ≤ ENNReal.ofReal ((‖X‖ / ε) ^ 2) := by
  have h := mul_meas_ge_le_pow_eLpNorm' (μ := Q) (p := 2) two_ne_zero ENNReal.ofNat_ne_top
    (Lp.aestronglyMeasurable X) (ENNReal.ofReal ε)
  have hsub : {a | ε < |(X : Ω → ℝ) a|} ⊆ {x | ENNReal.ofReal ε ≤ ‖(X : Ω → ℝ) x‖ₑ} := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal ha.le
  have hE : eLpNorm (X : Ω → ℝ) 2 Q = ENNReal.ofReal ‖X‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top X)]
  rw [hE] at h
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  rw [← ENNReal.ofReal_pow hε.le, ← ENNReal.ofReal_pow (norm_nonneg _)] at h
  have hne : ENNReal.ofReal (ε ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have key : ENNReal.ofReal (ε ^ 2) * Q {x | ENNReal.ofReal ε ≤ ‖(X : Ω → ℝ) x‖ₑ} ≤
      ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal ((‖X‖ / ε) ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have : ε ^ 2 * (‖X‖ / ε) ^ 2 = ‖X‖ ^ 2 := by field_simp
    rw [this]; exact h
  exact (measure_mono hsub).trans
    ((ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top).1 key)

/-- Finitely many span elements (one per order `k ≤ K`) as one simple chaos. -/
lemma exists_simple {K : ℕ} (v : (k : Fin (K + 1)) → Lp ℝ 2 (kernelMeasure k))
    (hv : ∀ k : Fin (K + 1), v k ∈ Submodule.span ℝ (IDL3a.boxSet (k : ℕ))) :
    ∃ (m : ℕ) (a b c d : Fin m → ℝ) (T : (k : ℕ) → Finset (Fin k → Fin m))
      (r : (k : ℕ) → (Fin k → Fin m) → ℝ), (∀ i, 0 ≤ a i) ∧ (∀ i, b i ≤ 1) ∧
      (∀ k, K < k → T k = ∅) ∧
      (∀ k, ∀ σ ∈ T k, ∀ j j' : Fin k, j < j' → b (σ j) < a (σ j')) ∧
      ∀ k (h : k < K + 1), simpleG a b c d T r k = v ⟨k, h⟩ := by
  classical
  have hrep := fun k => Submodule.mem_span_set'.1 (hv k)
  choose N R gen hgen using hrep
  have hg : ∀ (k : Fin (K + 1)) (i : Fin (N k)), ∃ A B C D : Fin (k : ℕ) → ℝ, IDL3a.Good A B ∧
      (gen k i : Lp ℝ 2 (kernelMeasure k)) = boxInd A B C D := fun k i => (gen k i).2
  choose A B C D hgood heq using hg
  let P := Σ k : Fin (K + 1), Fin (N k) × Fin (k : ℕ)
  let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let a : Fin (Fintype.card P) → ℝ := fun p => A (e.symm p).1 (e.symm p).2.1 (e.symm p).2.2
  let b : Fin (Fintype.card P) → ℝ := fun p => B (e.symm p).1 (e.symm p).2.1 (e.symm p).2.2
  let c : Fin (Fintype.card P) → ℝ := fun p => C (e.symm p).1 (e.symm p).2.1 (e.symm p).2.2
  let d : Fin (Fintype.card P) → ℝ := fun p => D (e.symm p).1 (e.symm p).2.1 (e.symm p).2.2
  let σ : (k : Fin (K + 1)) → Fin (N k) → Fin (k : ℕ) → Fin (Fintype.card P) :=
    fun k i j => e ⟨k, (i, j)⟩
  have hF : ∀ (F : (k : Fin (K + 1)) → Fin (N k) → Fin (k : ℕ) → ℝ) (k : Fin (K + 1))
      (i : Fin (N k)), (fun p => F (e.symm p).1 (e.symm p).2.1 (e.symm p).2.2) ∘ σ k i = F k i := by
    intro F k i
    funext j
    change F (e.symm (e ⟨k, (i, j)⟩)).1 (e.symm (e ⟨k, (i, j)⟩)).2.1
      (e.symm (e ⟨k, (i, j)⟩)).2.2 = F k i j
    rw [Equiv.symm_apply_apply]
  have ha' : ∀ k i, a ∘ σ k i = A k i := hF A
  have hb' : ∀ k i, b ∘ σ k i = B k i := hF B
  have hc' : ∀ k i, c ∘ σ k i = C k i := hF C
  have hd' : ∀ k i, d ∘ σ k i = D k i := hF D
  refine ⟨Fintype.card P, a, b, c, d,
    fun k => if h : k < K + 1 then Finset.univ.image (σ ⟨k, h⟩) else ∅,
    fun k τ => if h : k < K + 1 then
      ∑ i ∈ Finset.univ.filter (fun i => σ ⟨k, h⟩ i = τ), R ⟨k, h⟩ i else 0,
    fun p => (hgood _ _).1 _, fun p => (hgood _ _).2.1 _, ?_, ?_, ?_⟩
  · intro k hk
    simp [show ¬ k < K + 1 by omega]
  · intro k τ hτ j j' hjj
    have h : k < K + 1 := by
      by_contra h
      simp [h] at hτ
    simp only [dif_pos h] at hτ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hτ
    have h1 := (hgood ⟨k, h⟩ i).2.2 j j' hjj
    rw [← hb' ⟨k, h⟩ i, ← ha' ⟨k, h⟩ i] at h1
    exact h1
  · intro k h
    simp only [simpleG, dif_pos h]
    rw [← hgen ⟨k, h⟩]
    rw [← Finset.sum_fiberwise_of_maps_to (g := σ ⟨k, h⟩) (t := Finset.univ.image (σ ⟨k, h⟩))
      (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hστ : σ ⟨k, h⟩ i = τ := (Finset.mem_filter.1 hi).2
    rw [heq, ← hστ, ha', hb', hc', hd']

lemma simplexSupported_sub {k : ℕ} (f h : Lp ℝ 2 (kernelMeasure k)) (hf : SimplexSupported f)
    (hh : SimplexSupported h) : SimplexSupported (f - h) := by
  unfold SimplexSupported at *
  filter_upwards [Lp.coeFn_sub f h, hf, hh] with z h1 h2 h3 hz
  rw [h1, Pi.sub_apply, h2 hz, h3 hz, sub_zero]

lemma eLpNorm_sub_eq {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} (X Y : Lp ℝ 2 Q) :
    eLpNorm ((X : Ω → ℝ) - (Y : Ω → ℝ)) 2 Q = ENNReal.ofReal ‖X - Y‖ := by
  rw [← eLpNorm_congr_ae (Lp.coeFn_sub X Y), Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

/-- L4 (scalar Lemma 4.4 for absolutely summable simplex-supported kernels):
`I^n(g) → I(g)` in law. -/
theorem chaos_tendsto {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Q : Measure Ω} [IsProbabilityMeasure Q] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q)
    {W : Set (ℝ × ℝ) → Ω' → ℝ} (hW : IsWhiteNoise W Q')
    {I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q'} (hI : IsMultipleIntegral W Q' I)
    (g : (k : ℕ) → Lp ℝ 2 (kernelMeasure k)) (hg : ∀ k, SimplexSupported (g k))
    (hs : Summable fun k => ‖g k‖) :
    TendstoInDistribution (fun n => (discreteChaos ω Q n g : Ω → ℝ)) atTop
      (fockIntegral I g : Ω' → ℝ) (fun _ => Q) Q' := by
  have happ : ∀ K : ℕ, ∀ k : Fin (K + 1), ∃ v ∈ Submodule.span ℝ (IDL3a.boxSet (k : ℕ)),
      dist (g k) v < 1 / ((K : ℝ) + 1) ^ 2 := by
    intro K k
    have hmem : g k ∈ closure (Submodule.span ℝ (IDL3a.boxSet (k : ℕ)) :
        Set (Lp ℝ 2 (kernelMeasure k))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact IDL3a.mem_closure_span (g k) (hg k)
    exact Metric.mem_closure_iff.1 hmem _ (by positivity)
  choose v hv hvd using happ
  have hsimp := fun K => exists_simple (v K) (hv K)
  choose m a b c d T r ha hb hT hord hG using hsimp
  set G : ℕ → (k : ℕ) → Lp ℝ 2 (kernelMeasure k) :=
    fun K => simpleG (a K) (b K) (c K) (d K) (T K) (r K) with hGdef
  have hGlow : ∀ K k, k ≤ K → ‖G K k - g k‖ ≤ 1 / ((K : ℝ) + 1) ^ 2 := by
    intro K k hk
    have h : k < K + 1 := by omega
    simp only [hGdef]
    rw [hG K k h, norm_sub_rev, ← dist_eq_norm]
    exact (hvd K ⟨k, h⟩).le
  have hGhigh : ∀ K k, K < k → G K k = 0 := fun K k hk =>
    simpleG_eq_zero _ _ _ _ _ _ (hT K) hk
  have hGss : ∀ K k, SimplexSupported (G K k) := fun K k =>
    IDL2b.simplexSupported_simple (a K) (b K) (c K) (d K) (ha K) (hb K) (T K k) (r K k)
      (hord K k)
  set err : ℕ → ℝ := fun K => ∑' k, ‖G K k - g k‖ with herrdef
  have hsumm : ∀ K, Summable fun k => ‖G K k - g k‖ := by
    intro K
    refine (summable_nat_add_iff (K + 1)).1 ?_
    have : (fun k => ‖G K (k + (K + 1)) - g (k + (K + 1))‖) = fun k => ‖g (k + (K + 1))‖ := by
      funext k
      rw [hGhigh K _ (by omega), zero_sub, norm_neg]
    rw [this]
    exact (summable_nat_add_iff (K + 1)).2 hs
  have herr_le : ∀ K, err K ≤ 1 / ((K : ℝ) + 1) + ∑' k, ‖g (k + (K + 1))‖ := by
    intro K
    simp only [herrdef]
    rw [← (hsumm K).sum_add_tsum_nat_add (K + 1)]
    have h1 : ∑ i ∈ Finset.range (K + 1), ‖G K i - g i‖ ≤ 1 / ((K : ℝ) + 1) := by
      calc ∑ i ∈ Finset.range (K + 1), ‖G K i - g i‖
          ≤ ∑ i ∈ Finset.range (K + 1), 1 / ((K : ℝ) + 1) ^ 2 :=
            Finset.sum_le_sum fun i hi => hGlow K i (by simp at hi; omega)
        _ = 1 / ((K : ℝ) + 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            field_simp
    have h2 : ∑' i, ‖G K (i + (K + 1)) - g (i + (K + 1))‖ = ∑' k, ‖g (k + (K + 1))‖ := by
      refine tsum_congr fun k => ?_
      rw [hGhigh K _ (by omega), zero_sub, norm_neg]
    rw [h2]
    linarith
  have herr0 : Tendsto err atTop (𝓝 0) := by
    have hu : Tendsto (fun K : ℕ => 1 / ((K : ℝ) + 1) + ∑' k, ‖g (k + (K + 1))‖) atTop
        (𝓝 0) := by
      have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := (tendsto_sum_nat_add (fun k => ‖g k‖)).comp (tendsto_add_atTop_nat 1)
      simpa using h1.add h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun K => tsum_nonneg fun k => norm_nonneg _) herr_le
  have hdisc : ∀ K n, 1 ≤ n →
      ‖discreteChaos ω Q n (G K) - discreteChaos ω Q n g‖ ≤ err K := by
    intro K n hn
    have heq : discreteChaos ω Q n (G K) - discreteChaos ω Q n g =
        ∑ k ∈ Finset.range (n + 1),
          ((n : ℝ) ^ (-(3 * (k : ℝ) / 4))) • uStatistic ω Q n k (G K k - g k) := by
      unfold discreteChaos
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← smul_sub]
      congr 1
      exact ((IDL2a.uStatL hω n k).map_sub (G K k) (g k)).symm
    rw [heq]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => IDL2b.norm_scaled_uStatistic_le hω hn k _
      (simplexSupported_sub _ _ (hGss K k) (hg k))).trans ?_
    exact (hsumm K).sum_le_tsum _ (fun k _ => norm_nonneg _)
  have hfock : ∀ K, ‖fockIntegral I (G K) - fockIntegral I g‖ ≤ err K := by
    intro K
    have hsI : Summable fun k => I k (g k) :=
      Summable.of_norm_bounded hs (fun k => IDL2c.norm_I_le hω hW hI (g k) (hg k))
    have hsG : Summable fun k => I k (G K k) := by
      refine Summable.of_norm_bounded ((hsumm K).add hs) (fun k => ?_)
      refine (IDL2c.norm_I_le hω hW hI _ (hGss K k)).trans ?_
      calc ‖G K k‖ = ‖(G K k - g k) + g k‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    unfold fockIntegral
    rw [← hsG.tsum_sub hsI]
    refine tsum_of_norm_bounded (hsumm K).hasSum fun k => ?_
    rw [← map_sub]
    exact IDL2c.norm_I_le hω hW hI _ (simplexSupported_sub _ _ (hGss K k) (hg k))
  have hcol : TendstoInDistribution (fun K => (fockIntegral I (G K) : Ω' → ℝ)) atTop
      (fockIntegral I g : Ω' → ℝ) (fun _ => Q') Q' := by
    refine TendstoInMeasure.tendstoInDistribution ?_
      (fun K => (Lp.aestronglyMeasurable _).aemeasurable)
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero
      (fun K => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
    have hup : Tendsto (fun K => ENNReal.ofReal (err K)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal herr0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun _ => bot_le) (fun K => ?_)
    rw [eLpNorm_sub_eq]
    exact ENNReal.ofReal_le_ofReal (hfock K)
  have hunif : ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, 0 < θ → ∀ᶠ K in atTop, ∀ᶠ n in atTop,
      (fun _ => Q) n {x | ε < |(fun K n => (discreteChaos ω Q n (G K) : Ω → ℝ)) K n x -
        (fun n => (discreteChaos ω Q n g : Ω → ℝ)) n x|} ≤ ENNReal.ofReal θ := by
    intro ε hε θ hθ
    have ht : Tendsto (fun K => (err K / ε) ^ 2) atTop (𝓝 0) := by
      simpa using (herr0.div_const ε).pow 2
    filter_upwards [ht.eventually (gt_mem_nhds hθ)] with K hK
    filter_upwards [eventually_ge_atTop 1] with n hn
    set D := discreteChaos ω Q n (G K) - discreteChaos ω Q n g with hD
    have hset : {x | ε < |(discreteChaos ω Q n (G K) : Ω → ℝ) x -
        (discreteChaos ω Q n g : Ω → ℝ) x|} =ᵐ[Q] {x | ε < |(D : Ω → ℝ) x|} := by
      filter_upwards [Lp.coeFn_sub (discreteChaos ω Q n (G K)) (discreteChaos ω Q n g)]
        with x hx
      change (ε < |_ - _|) = (ε < |(D : Ω → ℝ) x|)
      rw [hD, hx, Pi.sub_apply]
    calc Q {x | ε < |(discreteChaos ω Q n (G K) : Ω → ℝ) x -
          (discreteChaos ω Q n g : Ω → ℝ) x|}
        = Q {x | ε < |(D : Ω → ℝ) x|} := measure_congr hset
      _ ≤ ENNReal.ofReal ((‖D‖ / ε) ^ 2) := cheb D hε
      _ ≤ ENNReal.ofReal ((err K / ε) ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := hdisc K n hn
          gcongr
      _ ≤ ENNReal.ofReal θ := ENNReal.ofReal_le_ofReal hK.le
  have hrow : ∀ K, TendstoInDistribution (fun n => (discreteChaos ω Q n (G K) : Ω → ℝ)) atTop
      (fockIntegral I (G K) : Ω' → ℝ) (fun _ => Q) Q' := by
    intro K
    set L : ℝ := ∑ p, (|c K p| + |d K p|) with hL
    have hcd : ∀ p, |c K p| + |d K p| ≤ L := fun p =>
      Finset.single_le_sum (f := fun p => |c K p| + |d K p|) (fun p _ => by positivity)
        (Finset.mem_univ p)
    refine simple_chaos_tendsto hω hW hI L (a K) (b K) (c K) (d K) (ha K) (hb K)
      (fun p => ?_) (fun p => ?_) K (T K) (r K) (hT K) ?_
    · linarith [hcd p, neg_abs_le (c K p), abs_nonneg (d K p)]
    · linarith [hcd p, le_abs_self (d K p), abs_nonneg (c K p)]
    · intro k σ hσ j j' hjj
      rcases lt_or_gt_of_ne hjj with h | h
      · exact Or.inl (hord K k σ hσ j j' h)
      · exact Or.inr (hord K k σ hσ j' j h)
  exact approx (fun _ => Q) (fun _ => Q') Q' (fun K n => (discreteChaos ω Q n (G K) : Ω → ℝ))
    (fun K => (fockIntegral I (G K) : Ω' → ℝ)) (fun n => (discreteChaos ω Q n g : Ω → ℝ))
    (fockIntegral I g : Ω' → ℝ) (fun n => (Lp.aestronglyMeasurable _).aemeasurable)
    hrow hunif hcol

end IDL4

namespace IDL5

open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory Set Filter Topology
  IDL1a IDL1b

lemma abs_walkPos_le {m : ℕ} (s : Fin m → Bool) : |walkPos s m| ≤ m := by
  unfold walkPos
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin m, |(if (j : ℕ) < m then stepZ (s j) else 0)| ≤ ∑ _j : Fin m, (1 : ℤ) :=
        Finset.sum_le_sum fun j _ => by
          unfold stepZ
          split_ifs <;> simp
    _ = m := by simp

lemma srwProb_eq_zero {m : ℕ} {y : ℤ} (hy : (m : ℤ) < |y|) : srwProb m y = 0 := by
  unfold srwProb
  rw [Finset.filter_false_of_mem fun s _ hs => by
    have := abs_walkPos_le s
    rw [hs] at this
    omega]
  simp

/-- Support of the path kernel: `|x_j| ≤ i_j` when `p_k(i,x) ≠ 0`, `i` monotone. -/
lemma abs_le_of_pathKernel_ne_zero {k : ℕ} {i : Fin k → ℕ} {x : Fin k → ℤ} (hi : Monotone i)
    (h : pathKernel i x ≠ 0) : ∀ j, |x j| ≤ i j := by
  have hf : ∀ j : Fin k, |x j - (Fin.cons 0 x : Fin (k + 1) → ℤ) j.castSucc| ≤
      ((i j - (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc : ℕ) : ℤ) := by
    intro j
    by_contra hc
    push_neg at hc
    exact h (Finset.prod_eq_zero (Finset.mem_univ j) (srwProb_eq_zero hc))
  intro j
  obtain ⟨j, hj⟩ := j
  induction j with
  | zero =>
    have h1 := hf ⟨0, hj⟩
    have hcs0 : Fin.castSucc (⟨0, hj⟩ : Fin k) = 0 := by ext; simp
    rw [hcs0, Fin.cons_zero, Fin.cons_zero] at h1
    simpa using h1
  | succ j ih =>
    have h1 := hf ⟨j + 1, hj⟩
    have h2 := ih (by omega)
    have hcs : Fin.castSucc (⟨j + 1, hj⟩ : Fin k) = Fin.succ ⟨j, by omega⟩ := by ext; simp
    rw [hcs, Fin.cons_succ, Fin.cons_succ] at h1
    have hmono : i ⟨j, by omega⟩ ≤ i ⟨j + 1, hj⟩ := hi (Fin.mk_le_mk.2 (by omega))
    rw [Nat.cast_sub hmono] at h1
    have h3 := abs_sub_abs_le_abs_sub (x ⟨j + 1, hj⟩) (x ⟨j, by omega⟩)
    linarith

lemma parityMatch_parityRound (i : ℕ) (y : ℝ) : Even ((i : ℤ) - parityRound i y) := by
  unfold parityRound
  refine ⟨((i / 2 : ℕ) : ℤ) - round ((y - ((i % 2 : ℕ) : ℝ)) / 2), ?_⟩
  have h : (i : ℤ) = 2 * ((i / 2 : ℕ) : ℤ) + ((i % 2 : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod i 2).symm
  linear_combination h

lemma abs_sub_parityRound_le (i : ℕ) (y : ℝ) : |y - parityRound i y| ≤ 1 := by
  set w : ℝ := (y - ((i % 2 : ℕ) : ℝ)) / 2 with hw
  have e : ((parityRound i y : ℤ) : ℝ) = 2 * (round w : ℝ) + ((i % 2 : ℕ) : ℝ) := by
    simp only [parityRound, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, hw]
  have h := abs_sub_round w
  rw [e]
  have : y - (2 * (round w : ℝ) + ((i % 2 : ℕ) : ℝ)) = 2 * (w - round w) := by
    rw [hw]; ring
  rw [this, abs_mul]
  norm_num
  linarith

lemma parityRound_eq {i : ℕ} {x : ℤ} {y : ℝ} (hx : Even ((i : ℤ) - x)) (h1 : (x : ℝ) - 1 < y)
    (h2 : y < x + 1) : parityRound i y = x := by
  have hr := abs_le.1 (abs_sub_parityRound_le i y)
  obtain ⟨m, hm⟩ := hx.sub (parityMatch_parityRound i y)
  have h3 : ((parityRound i y : ℤ) : ℝ) < x + 2 := by linarith
  have h4 : (x : ℝ) - 2 < ((parityRound i y : ℤ) : ℝ) := by linarith
  have h3' : parityRound i y < x + 2 := by exact_mod_cast h3
  have h4' : x - 2 < parityRound i y := by exact_mod_cast h4
  omega

lemma ceil_eq_of_mem_tCell {n i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) {t : ℝ} (ht : t ∈ tCell n i) :
    ⌈(n : ℝ) * t⌉₊ = i := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := ht
  rw [div_lt_iff₀ hpos] at h1
  rw [le_div_iff₀ hpos] at h2
  rw [Nat.ceil_eq_iff (by omega), Nat.cast_sub hi]
  push_cast
  constructor <;> linarith

lemma mem_tCell_of_ceil_eq {n i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) {t : ℝ}
    (h : ⌈(n : ℝ) * t⌉₊ = i) : t ∈ tCell n i := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.ceil_eq_iff (by omega), Nat.cast_sub hi] at h
  push_cast at h
  exact ⟨by rw [div_lt_iff₀ hpos]; linarith, by rw [le_div_iff₀ hpos]; linarith⟩

/-- Points whose scaled space coordinate is an integer (a null set): the parity-rounding ties. -/
def tieSet (n k : ℕ) : Set (Fin k → ℝ × ℝ) :=
  {z | ∃ j, ∃ m : ℤ, (z j).2 * Real.sqrt n = m}

lemma ae_not_tie (n k : ℕ) (hn : 1 ≤ n) : ∀ᵐ z ∂(kernelMeasure k), z ∉ tieSet n k := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hE : tieSet n k = ⋃ j, ⋃ m : ℤ,
      Function.eval j ⁻¹' (univ ×ˢ {(m : ℝ) / Real.sqrt n}) := by
    ext z
    simp only [tieSet, mem_setOf_eq, mem_iUnion, mem_preimage, Function.eval, mem_prod,
      mem_univ, true_and, mem_singleton_iff]
    refine exists_congr fun j => exists_congr fun m => ?_
    rw [eq_div_iff hs.ne']
  rw [ae_iff]
  simp only [not_not, setOf_mem_eq]
  rw [hE, measure_iUnion_null_iff]
  intro j
  rw [measure_iUnion_null_iff]
  intro m
  refine Measure.pi_eval_preimage_null _ ?_
  simp [stripMeasure, Measure.prod_prod]

open scoped Classical in
/-- Times in `D_k^n`. -/
noncomputable def Dn (n k : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ => Finset.Icc 1 n).filter fun i => InDiscreteSimplex n i

open scoped Classical in
/-- Sites with `|x_j| ≤ n` matching the parity of `i`. -/
noncomputable def Xn (n k : ℕ) (i : Fin k → ℕ) : Finset (Fin k → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n).filter fun x => ParityMatch i x

/-- The cell-constant form of `p_k^n`. -/
noncomputable def Kfun (n k : ℕ) (z : Fin k → ℝ × ℝ) : ℝ :=
  ∑ i ∈ Dn n k, ∑ x ∈ Xn n k i,
    ((2 : ℝ) ^ k)⁻¹ * pathKernel i x * (cell n i x).indicator (fun _ => (1 : ℝ)) z

theorem discreteKernel_eq_Kfun {n k : ℕ} (hn : 1 ≤ n) {z : Fin k → ℝ × ℝ}
    (hz : z ∉ tieSet n k) : discreteKernel n k z = Kfun n k z := by
  classical
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  unfold Kfun discreteKernel pathKernelBar
  set ic : Fin k → ℕ := fun j => ⌈(n : ℝ) * (z j).1⌉₊ with hic
  set xc : Fin k → ℤ := fun j => parityRound (ic j) ((z j).2 * Real.sqrt n) with hxc
  have hpc : ParityMatch ic xc := fun j => parityMatch_parityRound _ _
  have huniq : ∀ i x, (∀ j, 1 ≤ i j) → ParityMatch i x → z ∈ cell n i x →
      i = ic ∧ x = xc := by
    intro i x hi hp hz'
    have hij : ∀ j, ic j = i j := fun j =>
      ceil_eq_of_mem_tCell hn (hi j) (hz' j (mem_univ j)).1
    have hieq : i = ic := funext fun j => (hij j).symm
    refine ⟨hieq, funext fun j => ?_⟩
    obtain ⟨h1, h2⟩ := (hz' j (mem_univ j)).2
    have hy1 : (x j : ℝ) - 1 < (z j).2 * Real.sqrt n := by
      rw [div_lt_iff₀ hs] at h1; exact h1
    have hy2 : (z j).2 * Real.sqrt n ≤ (x j : ℝ) + 1 := by
      rw [le_div_iff₀ hs] at h2; exact h2
    have hy2' : (z j).2 * Real.sqrt n < (x j : ℝ) + 1 := by
      refine lt_of_le_of_ne hy2 fun heq => hz ⟨j, x j + 1, ?_⟩
      rw [heq]; push_cast; ring
    show x j = parityRound (ic j) ((z j).2 * Real.sqrt n)
    rw [hij j]
    exact (parityRound_eq (hp j) hy1 hy2').symm
  have hzero : ∀ i ∈ Dn n k, ∀ x ∈ Xn n k i, ¬ (i = ic ∧ x = xc) →
      ((2 : ℝ) ^ k)⁻¹ * pathKernel i x * (cell n i x).indicator (fun _ => (1 : ℝ)) z = 0 := by
    intro i hi x hx hne
    rw [indicator_of_notMem, mul_zero]
    intro hm
    exact hne (huniq i x (fun j => ((Finset.mem_filter.1 hi).2.1 j).1)
      (Finset.mem_filter.1 hx).2 hm)
  by_cases hD : InDiscreteSimplex n ic
  · rw [if_pos hD]
    have hic1 : ∀ j, 1 ≤ ic j := fun j => (hD.1 j).1
    have hzc : z ∈ cell n ic xc := by
      intro j _
      refine ⟨mem_tCell_of_ceil_eq hn (hic1 j) rfl, ?_⟩
      have hr := abs_le.1 (abs_sub_parityRound_le (ic j) ((z j).2 * Real.sqrt n))
      have hne : (z j).2 * Real.sqrt n ≠ (xc j : ℝ) - 1 := fun h =>
        hz ⟨j, xc j - 1, by rw [h]; push_cast; ring⟩
      have hxj : ((xc j : ℤ) : ℝ) = ((parityRound (ic j) ((z j).2 * Real.sqrt n) : ℤ) : ℝ) := rfl
      constructor
      · rw [div_lt_iff₀ hs]
        refine lt_of_le_of_ne (by rw [hxj]; linarith) (Ne.symm hne)
      · rw [le_div_iff₀ hs, hxj]; linarith
    have hicD : ic ∈ Dn n k :=
      Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun j => Finset.mem_Icc.2 (hD.1 j), hD⟩
    by_cases hX : xc ∈ Xn n k ic
    · rw [Finset.sum_eq_single ic, Finset.sum_eq_single xc]
      · rw [indicator_of_mem hzc, mul_one]
      · intro x hx hne
        exact hzero ic hicD x hx (fun h => hne h.2)
      · intro h; exact absurd hX h
      · intro i hi hne
        exact Finset.sum_eq_zero fun x hx => hzero i hi x hx (fun h => hne h.1)
      · intro h; exact absurd hicD h
    · have hpk : pathKernel ic xc = 0 := by
        by_contra hne
        apply hX
        have hb := abs_le_of_pathKernel_ne_zero hD.2.monotone hne
        refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun j => ?_, hpc⟩
        have h1 := abs_le.1 (hb j)
        have h2 : ((ic j : ℕ) : ℤ) ≤ n := by exact_mod_cast (hD.1 j).2
        exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
      rw [hpk, mul_zero]
      symm
      refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun x hx => ?_
      refine hzero i hi x hx ?_
      rintro ⟨rfl, rfl⟩
      exact hX hx
  · rw [if_neg hD]
    symm
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun x hx => ?_
    refine hzero i hi x hx ?_
    rintro ⟨rfl, -⟩
    exact hD (Finset.mem_filter.1 hi).2

lemma memLp_Kfun (n k : ℕ) : MemLp (Kfun n k) 2 (kernelMeasure k) := by
  unfold Kfun
  refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun x _ => ?_
  exact (memLp_indicator_const 2 (measurableSet_cell n i x) (1 : ℝ)
    (Or.inr (IDL2a.kernelMeasure_cell_ne_top n i x))).const_mul _

lemma discreteKernel_ae_eq (n k : ℕ) (hn : 1 ≤ n) :
    discreteKernel n k =ᵐ[kernelMeasure k] Kfun n k := by
  filter_upwards [ae_not_tie n k hn] with z hz using discreteKernel_eq_Kfun hn hz

lemma memLp_discreteKernel (n k : ℕ) (hn : 1 ≤ n) :
    MemLp (discreteKernel n k) 2 (kernelMeasure k) :=
  (memLp_Kfun n k).ae_eq (discreteKernel_ae_eq n k hn).symm

lemma coeFn_discreteKernelLp (n k : ℕ) (hn : 1 ≤ n) :
    (discreteKernelLp n k : (Fin k → ℝ × ℝ) → ℝ) =ᵐ[kernelMeasure k] Kfun n k := by
  rw [discreteKernelLp, dif_pos (memLp_discreteKernel n k hn)]
  exact (MemLp.coeFn_toLp _).trans (discreteKernel_ae_eq n k hn)

lemma discreteKernel_supp {n k : ℕ} {z : Fin k → ℝ × ℝ} (h : z ∉ simplex k) :
    discreteKernel n k z = 0 := by
  unfold discreteKernel
  rw [if_neg]
  intro hD
  apply h
  obtain _ | k := k
  · intro j; exact j.elim0
  have hn : (0 : ℝ) < n := by
    have := (hD.1 0).1.trans (hD.1 0).2
    exact_mod_cast this
  intro j
  have hle : (z j).1 ≤ 1 := by
    have h2 := Nat.ceil_le.1 (hD.1 j).2
    have : (n : ℝ) * (z j).1 ≤ n * 1 := by simpa using h2
    exact le_of_mul_le_mul_left this hn
  refine ⟨?_, hle⟩
  induction j using Fin.cases with
  | zero =>
    have h1 := Nat.ceil_pos.1 (hD.1 0).1
    simp only [withOrigin, Fin.castSucc_zero, Fin.cons_zero]
    exact pos_of_mul_pos_right h1 hn.le
  | succ i =>
    have hwo : withOrigin z (Fin.succ i).castSucc = z i.castSucc := by simp [withOrigin]
    rw [hwo]
    have hlt := hD.2 (Fin.castSucc_lt_succ (i := i))
    by_contra hc
    push_neg at hc
    have := Nat.ceil_mono (mul_le_mul_of_nonneg_left hc hn.le)
    exact absurd hlt (not_lt.2 this)

lemma simplexSupported_discreteKernelLp (n k : ℕ) :
    SimplexSupported (discreteKernelLp n k) := by
  unfold SimplexSupported discreteKernelLp
  split_ifs with h
  · filter_upwards [MemLp.coeFn_toLp h] with z hz hzs
    rw [hz]
    exact discreteKernel_supp hzs
  · filter_upwards [Lp.coeFn_zero ℝ 2 (kernelMeasure k)] with z hz _
    rw [hz]; rfl

end IDL5

namespace IDL5

open IntermediateDisorder.PointToLine MeasureTheory Finset

lemma walkPos_eq {n : ℕ} (s : Fin n → Bool) :
    walkPos s n = 2 * ((univ.filter fun j => s j = true).card : ℤ) - n := by
  have h1 : walkPos s n = ∑ j : Fin n, (if s j = true then (1 : ℤ) else -1) := by
    unfold walkPos stepZ
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos j.is_lt]
  rw [h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun j => s j = true)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

lemma card_walkPos_zero (m : ℕ) :
    (univ.filter fun s : Fin (2 * m) → Bool => walkPos s (2 * m) = 0).card =
      (2 * m).choose m := by
  have hE : (univ.filter fun s : Fin (2 * m) → Bool => walkPos s (2 * m) = 0) =
      univ.filter fun s : Fin (2 * m) → Bool => (univ.filter fun j => s j = true).card = m := by
    ext s
    simp only [mem_filter, mem_univ, true_and, walkPos_eq]
    push_cast
    omega
  rw [hE, show (2 * m).choose m = ((univ : Finset (Fin (2 * m))).card).choose m by simp,
    ← Finset.card_powersetCard]
  refine Finset.card_nbij' (fun s => univ.filter fun j => s j = true)
    (fun t j => decide (j ∈ t)) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hs
    simp [mem_powersetCard, hs]
  · intro t ht
    simp only [mem_coe, mem_powersetCard] at ht
    simp [ht.2]
  · intro s _
    funext j
    simp
  · intro t _
    ext j
    simp

lemma srwProb_two_mul_zero (m : ℕ) :
    srwProb (2 * m) 0 = (Nat.centralBinom m : ℝ) / 4 ^ m := by
  unfold srwProb
  rw [card_walkPos_zero, ← Nat.centralBinom_eq_two_mul_choose, pow_mul]
  norm_num
  ring

lemma centralBinom_sq_mul_le (m : ℕ) : Nat.centralBinom m ^ 2 * (2 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    have hpos : 0 < (m + 1) ^ 2 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc (m + 1) ^ 2 * (Nat.centralBinom (m + 1) ^ 2 * (2 * (m + 1) + 1))
        = ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 * (2 * m + 3) := by ring
      _ = 4 * (2 * m + 1) * (2 * m + 3) * (Nat.centralBinom m ^ 2 * (2 * m + 1)) := by
          rw [h]; ring
      _ ≤ 4 * (2 * m + 1) * (2 * m + 3) * 16 ^ m := Nat.mul_le_mul_left _ ih
      _ ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by
          rw [pow_succ]
          have : 4 * (2 * m + 1) * (2 * m + 3) ≤ (m + 1) ^ 2 * 16 := by nlinarith
          calc 4 * (2 * m + 1) * (2 * m + 3) * 16 ^ m ≤ (m + 1) ^ 2 * 16 * 16 ^ m :=
                Nat.mul_le_mul_right _ this
            _ = (m + 1) ^ 2 * (16 ^ m * 16) := by ring

/-- `p(2m,0)² (2m+1) ≤ 1`. -/
lemma srwProb_two_mul_zero_sq_le (m : ℕ) : srwProb (2 * m) 0 ^ 2 * (2 * m + 1) ≤ 1 := by
  rw [srwProb_two_mul_zero]
  have h : ((Nat.centralBinom m ^ 2 * (2 * m + 1) : ℕ) : ℝ) ≤ ((16 ^ m : ℕ) : ℝ) := by
    exact_mod_cast centralBinom_sq_mul_le m
  push_cast at h
  have h16 : (16 : ℝ) ^ m = (4 ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity), ← h16]
  linarith

end IDL5

namespace IDL5

open IntermediateDisorder.PointToLine MeasureTheory Finset

lemma srwProb_nonneg (m : ℕ) (y : ℤ) : 0 ≤ srwProb m y := by
  unfold srwProb; positivity

lemma card_walkPos (m c : ℕ) :
    (univ.filter fun s : Fin m → Bool => walkPos s m = 2 * (c : ℤ) - m).card = m.choose c := by
  have hE : (univ.filter fun s : Fin m → Bool => walkPos s m = 2 * (c : ℤ) - m) =
      univ.filter fun s : Fin m → Bool => (univ.filter fun j => s j = true).card = c := by
    ext s
    simp only [mem_filter, mem_univ, true_and, walkPos_eq]
    omega
  rw [hE, show m.choose c = ((univ : Finset (Fin m)).card).choose c by simp,
    ← Finset.card_powersetCard]
  refine Finset.card_nbij' (fun s => univ.filter fun j => s j = true)
    (fun t j => decide (j ∈ t)) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hs
    simp [mem_powersetCard, hs]
  · intro t ht
    simp only [mem_coe, mem_powersetCard] at ht
    simp [ht.2]
  · intro s _
    funext j
    simp
  · intro t _
    ext j
    simp

lemma srwProb_eq_choose (m c : ℕ) :
    srwProb m (2 * (c : ℤ) - m) = (m.choose c : ℝ) / 2 ^ m := by
  unfold srwProb
  rw [card_walkPos, inv_mul_eq_div]

lemma mem_image_of_srwProb_ne_zero {m : ℕ} {y : ℤ} (h : srwProb m y ≠ 0) :
    y ∈ (range (m + 1)).image (fun c : ℕ => 2 * (c : ℤ) - m) := by
  unfold srwProb at h
  have hne : (univ.filter fun s : Fin m → Bool => walkPos s m = y).Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    push_neg at h0
    apply h
    simp [Nat.le_zero.1 h0]
  obtain ⟨s, hs⟩ := hne
  rw [mem_filter] at hs
  rw [mem_image]
  refine ⟨(univ.filter fun j => s j = true).card, ?_, ?_⟩
  · rw [mem_range, Nat.lt_succ_iff]
    exact (card_filter_le _ _).trans (by simp)
  · rw [← hs.2, walkPos_eq]

/-- Collision bound: `∑_{y ∈ S} p(m,y)² ≤ p(2m,0)` for every finite `S`. -/
lemma sum_sq_le (m : ℕ) (S : Finset ℤ) :
    ∑ y ∈ S, srwProb m y ^ 2 ≤ srwProb (2 * m) 0 := by
  classical
  set T := (range (m + 1)).image (fun c : ℕ => 2 * (c : ℤ) - m) with hTdef
  have hT : ∑ y ∈ T, srwProb m y ^ 2 = srwProb (2 * m) 0 := by
    rw [hTdef, Finset.sum_image (fun a _ b _ h => by
      have : (a : ℤ) = b := by simpa using h
      exact_mod_cast this)]
    simp_rw [srwProb_eq_choose]
    rw [srwProb_two_mul_zero, Nat.centralBinom_eq_two_mul_choose, ← Nat.sum_range_choose_sq m]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [div_pow, ← pow_mul, mul_comm m 2, pow_mul]
    norm_num
  calc ∑ y ∈ S, srwProb m y ^ 2 ≤ ∑ y ∈ S ∪ T, srwProb m y ^ 2 :=
        sum_le_sum_of_subset_of_nonneg subset_union_left (fun _ _ _ => sq_nonneg _)
    _ = ∑ y ∈ T, srwProb m y ^ 2 := by
        refine (sum_subset subset_union_right fun y _ hy => ?_).symm
        have : srwProb m y = 0 := by
          by_contra h0
          exact hy (mem_image_of_srwProb_ne_zero h0)
        rw [this]; ring
    _ = srwProb (2 * m) 0 := hT

lemma cons_castSucc_zero {α : Type*} {k : ℕ} (a : α) (x : Fin k → α) (h : 0 < k) :
    (Fin.cons a x : Fin (k + 1) → α) (Fin.castSucc ⟨0, h⟩) = a := by
  have : (Fin.castSucc ⟨0, h⟩ : Fin (k + 1)) = 0 := Fin.ext rfl
  rw [this, Fin.cons_zero]

lemma cons_castSucc_succ {α : Type*} {k : ℕ} (a : α) (x : Fin k → α) (j : ℕ)
    (h : j + 1 < k) :
    (Fin.cons a x : Fin (k + 1) → α) (Fin.castSucc ⟨j + 1, h⟩) = x ⟨j, by omega⟩ := by
  have : (Fin.castSucc ⟨j + 1, h⟩ : Fin (k + 1)) = Fin.succ ⟨j, by omega⟩ := Fin.ext rfl
  rw [this, Fin.cons_succ]

/-- Increments `Δx_j = x_j - x_{j-1}` (`x_0 = 0`). -/
def incr {k : ℕ} (x : Fin k → ℤ) : Fin k → ℤ :=
  fun j => x j - (Fin.cons 0 x : Fin (k + 1) → ℤ) j.castSucc

lemma incr_injective {k : ℕ} : Function.Injective (incr (k := k)) := by
  intro x x' h
  have key : ∀ j : ℕ, ∀ hj : j < k, x ⟨j, hj⟩ = x' ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h0 := congrFun h ⟨0, hj⟩
      simp only [incr, cons_castSucc_zero] at h0
      linarith
    | succ j ih =>
      intro hj
      have h1 := congrFun h ⟨j + 1, hj⟩
      simp only [incr, cons_castSucc_succ] at h1
      have := ih (by omega)
      linarith
  funext j
  exact key j.1 j.2

/-- Collision bound for `p_k`: `∑_{x ∈ A} p_k(i,x)² ≤ ∏_j p(2Δi_j, 0)`. -/
lemma sum_pathKernel_sq_le {k : ℕ} (i : Fin k → ℕ) (A : Finset (Fin k → ℤ)) :
    ∑ x ∈ A, pathKernel i x ^ 2 ≤
      ∏ j : Fin k, srwProb (2 * (i j - (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc)) 0 := by
  classical
  set di : Fin k → ℕ := fun j => i j - (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc
  set F : (Fin k → ℤ) → ℝ := fun d => ∏ j : Fin k, srwProb (di j) (d j) ^ 2 with hF
  have h1 : ∀ x, pathKernel i x ^ 2 = F (incr x) := by
    intro x
    rw [hF, pathKernel, ← Finset.prod_pow]
    rfl
  set B : Finset ℤ := (A.image incr).biUnion fun d => univ.image d
  have hsub : A.image incr ⊆ Fintype.piFinset fun _ => B := by
    intro d hd
    rw [Fintype.mem_piFinset]
    intro j
    exact mem_biUnion.2 ⟨d, hd, mem_image.2 ⟨j, mem_univ _, rfl⟩⟩
  have hFn : ∀ d, 0 ≤ F d := fun d => prod_nonneg fun _ _ => sq_nonneg _
  calc ∑ x ∈ A, pathKernel i x ^ 2 = ∑ x ∈ A, F (incr x) := sum_congr rfl fun x _ => h1 x
    _ = ∑ d ∈ A.image incr, F d := (sum_image fun a _ b _ h => incr_injective h).symm
    _ ≤ ∑ d ∈ Fintype.piFinset (fun _ => B), F d :=
        sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => hFn d
    _ = ∏ j : Fin k, ∑ y ∈ B, srwProb (di j) y ^ 2 := by
        rw [hF, Finset.prod_univ_sum]
    _ ≤ ∏ j : Fin k, srwProb (2 * di j) 0 :=
        prod_le_prod (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) fun j _ => sum_sq_le _ _

end IDL5

namespace IDL5

open IntermediateDisorder.PointToLine MeasureTheory Finset

lemma sq_sum_mul_indicator {α ι : Type*} (P : Finset ι) (C : ι → Set α)
    (hd : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (C p) (C q)) (a : ι → ℝ) (z : α) :
    (∑ p ∈ P, a p * (C p).indicator (fun _ => (1 : ℝ)) z) ^ 2 =
      ∑ p ∈ P, a p ^ 2 * (C p).indicator (fun _ => (1 : ℝ)) z := by
  classical
  by_cases h : ∃ p ∈ P, z ∈ C p
  · obtain ⟨p, hp, hz⟩ := h
    have hq : ∀ q ∈ P, q ≠ p → z ∉ C q := fun q hq hqp hzq =>
      Set.disjoint_left.1 (hd q hq p hp hqp) hzq hz
    rw [Finset.sum_eq_single_of_mem p hp (fun q hq' hqp => by
          rw [Set.indicator_of_notMem (hq q hq' hqp), mul_zero]),
      Finset.sum_eq_single_of_mem p hp (fun q hq' hqp => by
          rw [Set.indicator_of_notMem (hq q hq' hqp), mul_zero]),
      Set.indicator_of_mem hz]
    ring
  · push_neg at h
    rw [Finset.sum_eq_zero (fun q hq => by rw [Set.indicator_of_notMem (h q hq), mul_zero]),
      Finset.sum_eq_zero (fun q hq => by rw [Set.indicator_of_notMem (h q hq), mul_zero])]
    ring

open scoped Classical in
lemma Kfun_eq_sigma (n k : ℕ) (z : Fin k → ℝ × ℝ) :
    Kfun n k z = ∑ p ∈ (Dn n k).sigma (Xn n k),
      ((2 : ℝ) ^ k)⁻¹ * pathKernel p.1 p.2 * (cell n p.1 p.2).indicator (fun _ => (1 : ℝ)) z := by
  unfold Kfun
  rw [Finset.sum_sigma]

open scoped Classical in
lemma integral_Kfun_sq (n k : ℕ) (hn : 1 ≤ n) :
    ∫ z, Kfun n k z ^ 2 ∂(kernelMeasure k) = ∑ p ∈ (Dn n k).sigma (Xn n k),
      (((2 : ℝ) ^ k)⁻¹ * pathKernel p.1 p.2) ^ 2 * ((1 / n) * (2 / Real.sqrt n)) ^ k := by
  have hd : ∀ p ∈ (Dn n k).sigma (Xn n k), ∀ q ∈ (Dn n k).sigma (Xn n k), p ≠ q →
      Disjoint (cell n p.1 p.2) (cell n q.1 q.2) := by
    intro p hp q hq hpq
    rw [Finset.mem_sigma] at hp hq
    refine IDL2a.cell_disjoint hn (Finset.mem_filter.1 hp.2).2 (Finset.mem_filter.1 hq.2).2 ?_
    intro h
    exact hpq (Sigma.ext h.1 (heq_of_eq h.2))
  have hpt : ∀ z, Kfun n k z ^ 2 = ∑ p ∈ (Dn n k).sigma (Xn n k),
      (((2 : ℝ) ^ k)⁻¹ * pathKernel p.1 p.2) ^ 2 *
        (cell n p.1 p.2).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    rw [Kfun_eq_sigma]
    exact sq_sum_mul_indicator ((Dn n k).sigma (Xn n k))
      (fun p : (Σ _ : Fin k → ℕ, Fin k → ℤ) => cell n p.1 p.2) hd
      (fun p : (Σ _ : Fin k → ℕ, Fin k → ℤ) => ((2 : ℝ) ^ k)⁻¹ * pathKernel p.1 p.2) z
  simp_rw [hpt]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_sigma] at hp
    have hb : ∀ j, 1 ≤ p.1 j ∧ p.1 j ≤ n := by
      intro j
      have := Fintype.mem_piFinset.1 (Finset.mem_filter.1 hp.1).1 j
      exact Finset.mem_Icc.1 this
    rw [integral_const_mul, integral_indicator_const _ (IDL1b.measurableSet_cell n p.1 p.2),
      smul_eq_mul, mul_one, Measure.real, IDL1b.kernelMeasure_cell n hn p.1 hb p.2]
  · intro p _
    exact (memLp_one_iff_integrable.1 (memLp_indicator_const 1 (IDL1b.measurableSet_cell n p.1 p.2)
      (1 : ℝ) (Or.inr (IDL2a.kernelMeasure_cell_ne_top n _ _)))).const_mul _

lemma norm_sq_discreteKernelLp (n k : ℕ) (hn : 1 ≤ n) :
    ‖discreteKernelLp n k‖ ^ 2 = ∫ z, Kfun n k z ^ 2 ∂(kernelMeasure k) := by
  rw [IDL2a.norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_discreteKernelLp n k hn] with z hz
  rw [hz]

open scoped Classical in
/-- `‖n^{k/2} p_k^n‖² ≤ ∑_{i ∈ D_k^n} (2√n)^{-k} ∏_j p(2Δi_j, 0)`. -/
theorem norm_sq_scaled_le (n k : ℕ) (hn : 1 ≤ n) :
    ‖((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k‖ ^ 2 ≤
      ∑ i ∈ Dn n k, (1 / (2 * Real.sqrt n)) ^ k *
        ∏ j : Fin k, srwProb (2 * (i j - (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc)) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hpow : ‖(n : ℝ) ^ ((k : ℝ) / 2)‖ ^ 2 = (n : ℝ) ^ k := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.rpow_mul_natCast hn0.le,
      show (k : ℝ) / 2 * ((2 : ℕ) : ℝ) = (k : ℕ) by push_cast; ring, Real.rpow_natCast]
  rw [norm_smul, mul_pow, hpow, norm_sq_discreteKernelLp n k hn, integral_Kfun_sq n k hn,
    Finset.sum_sigma, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsum : ∑ x ∈ Xn n k i, (((2 : ℝ) ^ k)⁻¹ * pathKernel i x) ^ 2 *
      ((1 / n) * (2 / Real.sqrt n)) ^ k =
      ((4 : ℝ) ^ k)⁻¹ * ((1 / n) * (2 / Real.sqrt n)) ^ k * ∑ x ∈ Xn n k i, pathKernel i x ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_pow, inv_pow, ← pow_mul, show (4 : ℝ) ^ k = ((2 : ℝ) ^ 2) ^ k by norm_num, ← pow_mul,
      mul_comm 2 k]
    ring
  rw [hsum]
  calc (n : ℝ) ^ k * (((4 : ℝ) ^ k)⁻¹ * ((1 / n) * (2 / Real.sqrt n)) ^ k *
        ∑ x ∈ Xn n k i, pathKernel i x ^ 2)
      ≤ (n : ℝ) ^ k * (((4 : ℝ) ^ k)⁻¹ * ((1 / n) * (2 / Real.sqrt n)) ^ k *
        ∏ j : Fin k, srwProb (2 * (i j - (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc)) 0) := by
        gcongr
        exact sum_pathKernel_sq_le i _
    _ = (1 / (2 * Real.sqrt n)) ^ k *
        ∏ j : Fin k, srwProb (2 * (i j - (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc)) 0 := by
        rw [← mul_assoc, ← mul_assoc, ← inv_pow, ← mul_pow, ← mul_pow]
        congr 2
        field_simp
        ring

end IDL5

namespace IDL5

open IntermediateDisorder.PointToLine MeasureTheory Finset

/-- `∑_{m=1}^M m^{-1/2} ≤ 2√M`. -/
lemma sum_inv_sqrt_le (M : ℕ) : ∑ m ∈ Icc 1 M, 1 / Real.sqrt m ≤ 2 * Real.sqrt M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hb : 0 < Real.sqrt ((M + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have ha2 := Real.sq_sqrt hM
    have hb2 : Real.sqrt ((M + 1 : ℕ) : ℝ) ^ 2 = M + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have ha0 := Real.sqrt_nonneg (M : ℝ)
    have key : 1 / Real.sqrt ((M + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((M + 1 : ℕ) : ℝ) - 2 * Real.sqrt M := by
      rw [div_le_iff₀ hb]
      nlinarith [sq_nonneg (Real.sqrt (M : ℝ) - Real.sqrt ((M + 1 : ℕ) : ℝ))]
    linarith

/-- `∑_{m=1}^N e^{-rm} ≤ 1/r`. -/
lemma sum_exp_neg_le {r : ℝ} (hr : 0 < r) (N : ℕ) :
    ∑ m ∈ Icc 1 N, Real.exp (-r * m) ≤ 1 / r := by
  set q := Real.exp (-r) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    have := Real.exp_lt_exp.2 (show -r < 0 by linarith)
    rwa [Real.exp_zero] at this
  have h1 : ∀ m : ℕ, Real.exp (-r * m) = q ^ m := by
    intro m; rw [hq, ← Real.exp_nat_mul]; ring_nf
  simp_rw [h1]
  have h2 : Icc 1 N = Ico 1 (N + 1) := rfl
  rw [h2]
  refine (geom_sum_Ico_le_of_lt_one hq0 hq1).trans ?_
  rw [pow_one, div_le_div_iff₀ (by linarith) hr]
  have he := Real.add_one_le_exp r
  have hqe : q * Real.exp r = 1 := by rw [hq, ← Real.exp_add]; simp
  nlinarith [Real.exp_pos r]

/-- `∑_{m=1}^N e^{-rm}/√m ≤ 3/√r` for `0 < r ≤ 1`. -/
lemma sum_exp_div_sqrt_le {r : ℝ} (hr0 : 0 < r) (N : ℕ) :
    ∑ m ∈ Icc 1 N, Real.exp (-r * m) / Real.sqrt m ≤ 3 / Real.sqrt r := by
  classical
  set M := ⌊1 / r⌋₊ with hMdef
  have hM1 : (M : ℝ) ≤ 1 / r := Nat.floor_le (by positivity)
  have hM2 : 1 / r < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun m => m ≤ M)]
  have hA : ∑ m ∈ (Icc 1 N).filter (fun m => m ≤ M), Real.exp (-r * m) / Real.sqrt m ≤
      2 / Real.sqrt r := by
    calc ∑ m ∈ (Icc 1 N).filter (fun m => m ≤ M), Real.exp (-r * m) / Real.sqrt m
        ≤ ∑ m ∈ (Icc 1 N).filter (fun m => m ≤ M), 1 / Real.sqrt m := by
          refine Finset.sum_le_sum fun m _ => ?_
          refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          nlinarith
      _ ≤ ∑ m ∈ Icc 1 M, 1 / Real.sqrt m := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
          intro m hm
          rw [Finset.mem_filter, Finset.mem_Icc] at hm
          rw [Finset.mem_Icc]; omega
      _ ≤ 2 * Real.sqrt M := sum_inv_sqrt_le M
      _ ≤ 2 / Real.sqrt r := by
          have h := Real.sqrt_le_sqrt hM1
          rw [one_div, Real.sqrt_inv, ← one_div] at h
          calc 2 * Real.sqrt M ≤ 2 * (1 / Real.sqrt r) := by linarith
            _ = 2 / Real.sqrt r := by ring
  have hB : ∑ m ∈ (Icc 1 N).filter (fun m => ¬ m ≤ M), Real.exp (-r * m) / Real.sqrt m ≤
      1 / Real.sqrt r := by
    calc ∑ m ∈ (Icc 1 N).filter (fun m => ¬ m ≤ M), Real.exp (-r * m) / Real.sqrt m
        ≤ ∑ m ∈ (Icc 1 N).filter (fun m => ¬ m ≤ M), Real.sqrt r * Real.exp (-r * m) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [Finset.mem_filter] at hm
          have hm' : (M : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : M + 1 ≤ m)
          have hrm : 1 ≤ r * m := by
            have := lt_of_lt_of_le hM2 hm'
            rw [div_lt_iff₀ hr0] at this
            linarith
          have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 (by linarith)
          have hprod : 1 ≤ Real.sqrt r * Real.sqrt m := by
            rw [← Real.sqrt_mul hr0.le]
            exact Real.one_le_sqrt.2 hrm
          rw [div_le_iff₀ hsm]
          have he := (Real.exp_pos (-r * m)).le
          nlinarith
      _ ≤ ∑ m ∈ Icc 1 N, Real.sqrt r * Real.exp (-r * m) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity
      _ = Real.sqrt r * ∑ m ∈ Icc 1 N, Real.exp (-r * m) := by rw [Finset.mul_sum]
      _ ≤ Real.sqrt r * (1 / r) := by gcongr; exact sum_exp_neg_le hr0 N
      _ = 1 / Real.sqrt r := by
          have h2 := Real.sq_sqrt hr0.le
          field_simp
          nlinarith
  calc _ ≤ 2 / Real.sqrt r + 1 / Real.sqrt r := add_le_add hA hB
    _ = 3 / Real.sqrt r := by ring

/-- `Δi_j` in `ℕ`. -/
def dinc {k : ℕ} (i : Fin k → ℕ) : Fin k → ℕ :=
  fun j => i j - (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc

lemma mem_Dn_iff {n k : ℕ} {i : Fin k → ℕ} :
    i ∈ Dn n k ↔ (∀ j, 1 ≤ i j ∧ i j ≤ n) ∧ StrictMono i := by
  classical
  unfold Dn
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Finset.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma cons_lt_of_mem_Dn {n k : ℕ} {i : Fin k → ℕ} (hi : i ∈ Dn n k) (j : Fin k) :
    (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc < i j := by
  rw [mem_Dn_iff] at hi
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => rw [cons_castSucc_zero]; exact (hi.1 _).1
  | succ j =>
    rw [cons_castSucc_succ]
    exact hi.2 (Fin.mk_lt_mk.2 (Nat.lt_succ_self j))

lemma dinc_mem {n k : ℕ} {i : Fin k → ℕ} (hi : i ∈ Dn n k) (j : Fin k) :
    dinc i j ∈ Icc 1 n := by
  have h1 := cons_lt_of_mem_Dn hi j
  have h2 := ((mem_Dn_iff.1 hi).1 j).2
  rw [Finset.mem_Icc]
  unfold dinc
  omega

lemma dinc_injOn {n k : ℕ} : Set.InjOn (dinc (k := k)) (Dn n k : Set (Fin k → ℕ)) := by
  intro i hi i' hi' h
  have key : ∀ j : ℕ, ∀ hj : j < k, i ⟨j, hj⟩ = i' ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h0 := congrFun h ⟨0, hj⟩
      simp only [dinc, cons_castSucc_zero] at h0
      omega
    | succ j ih =>
      intro hj
      have h1 := congrFun h ⟨j + 1, hj⟩
      have c1 := cons_lt_of_mem_Dn hi ⟨j + 1, hj⟩
      have c2 := cons_lt_of_mem_Dn hi' ⟨j + 1, hj⟩
      simp only [dinc, cons_castSucc_succ] at h1 c1 c2
      have := ih (by omega)
      omega
  funext j
  exact key j.1 j.2

/-- Telescoping: `∑_j Δi_j ≤ n` on `D_k^n`. -/
lemma sum_dinc_le {n k : ℕ} {i : Fin k → ℕ} (hi : i ∈ Dn n k) : ∑ j, dinc i j ≤ n := by
  have hD := mem_Dn_iff.1 hi
  set I : ℕ → ℕ := fun l => if l = 0 then 0 else if h : l - 1 < k then i ⟨l - 1, h⟩ else n
    with hIdef
  have hI1 : ∀ j : Fin k, i j = I (j + 1) := by
    intro j; simp [hIdef, j.2]
  have hI0 : ∀ j : Fin k, (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc = I j := by
    intro j
    obtain ⟨j, hj⟩ := j
    cases j with
    | zero => rw [cons_castSucc_zero]; simp [hIdef]
    | succ j =>
      rw [cons_castSucc_succ]
      simp [hIdef, show j < k by omega]
  have hmono : Monotone I := by
    refine monotone_nat_of_le_succ fun l => ?_
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [hIdef]
    · simp only [hIdef]
      rw [if_neg (by omega), if_neg (by omega)]
      by_cases h1 : l - 1 < k
      · by_cases h2 : l + 1 - 1 < k
        · rw [dif_pos h1, dif_pos h2]
          exact (hD.2 (Fin.mk_lt_mk.2 (by omega))).le
        · rw [dif_pos h1, dif_neg h2]; exact (hD.1 _).2
      · rw [dif_neg h1, dif_neg (by omega)]
  have hsum : ∑ j, dinc i j = ∑ l ∈ range k, (I (l + 1) - I l) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold dinc
    rw [hI1, hI0]
  rw [hsum, Finset.sum_range_tsub hmono]
  have : I k ≤ n := by
    simp only [hIdef]
    split_ifs with h0 h1
    · omega
    · exact (hD.1 _).2
    · exact le_refl _
  omega

/-- Generating-function bound on `D_k^n`. -/
lemma gen_bound {n k : ℕ} (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) {r : ℝ} (hr : 0 ≤ r) :
    ∑ i ∈ Dn n k, ∏ j, f (dinc i j) ≤
      Real.exp (r * n) * (∑ m ∈ Icc 1 n, f m * Real.exp (-r * m)) ^ k := by
  classical
  calc ∑ i ∈ Dn n k, ∏ j, f (dinc i j)
      ≤ ∑ i ∈ Dn n k, Real.exp (r * n) * ∏ j, (f (dinc i j) * Real.exp (-r * dinc i j)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.prod_mul_distrib, ← Real.exp_sum]
        have hs : ((∑ j, dinc i j : ℕ) : ℝ) ≤ n := by exact_mod_cast sum_dinc_le hi
        have hP : 0 ≤ ∏ j, f (dinc i j) := Finset.prod_nonneg fun _ _ => hf _
        have he : 1 ≤ Real.exp (r * n) * Real.exp (∑ j, -r * (dinc i j : ℝ)) := by
          rw [← Real.exp_add, Real.one_le_exp_iff]
          rw [← Finset.mul_sum]
          push_cast at hs
          nlinarith
        nlinarith
    _ = Real.exp (r * n) * ∑ d ∈ (Dn n k).image dinc, ∏ j, (f (d j) * Real.exp (-r * d j)) := by
        rw [← Finset.mul_sum, Finset.sum_image dinc_injOn]
    _ ≤ Real.exp (r * n) * ∑ d ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 n),
          ∏ j, (f (d j) * Real.exp (-r * d j)) := by
        gcongr
        · exact fun d _ _ => Finset.prod_nonneg fun j _ => mul_nonneg (hf _) (Real.exp_pos _).le
        · intro d hd
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
          exact Fintype.mem_piFinset.2 fun j => dinc_mem hi j
    _ = Real.exp (r * n) * (∑ m ∈ Icc 1 n, f m * Real.exp (-r * m)) ^ k := by
        congr 1
        rw [show (∑ m ∈ Icc 1 n, f m * Real.exp (-r * m)) ^ k =
          ∏ _j : Fin k, ∑ m ∈ Icc 1 n, f m * Real.exp (-r * m) by simp]
        exact (Finset.prod_univ_sum (fun _ : Fin k => Icc 1 n)
          (fun _ m => f m * Real.exp (-r * m))).symm

end IDL5

namespace IDL5

open IntermediateDisorder.PointToLine MeasureTheory Finset Filter

lemma srwProb_two_mul_zero_le {m : ℕ} (hm : 1 ≤ m) :
    srwProb (2 * m) 0 ≤ 1 / Real.sqrt m := by
  have h := srwProb_two_mul_zero_sq_le m
  have hp := srwProb_nonneg (2 * m) 0
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
  have hs2 := Real.sq_sqrt hm0.le
  rw [le_div_iff₀ hs]
  by_contra hc
  push_neg at hc
  have h1 : 1 < (srwProb (2 * m) 0 * Real.sqrt m) ^ 2 := by nlinarith
  rw [mul_pow, hs2] at h1
  have h2 : srwProb (2 * m) 0 ^ 2 * (m : ℝ) ≤ srwProb (2 * m) 0 ^ 2 * (2 * m + 1) := by
    have := sq_nonneg (srwProb (2 * m) 0)
    nlinarith
  linarith

lemma Dn_eq_empty {n k : ℕ} (h : n < k) : Dn n k = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  have hD := mem_Dn_iff.1 hi
  have hc := Finset.card_le_card_of_injOn i (s := (univ : Finset (Fin k))) (t := Icc 1 n)
    (fun j _ => Finset.mem_Icc.2 (hD.1 j)) (hD.2.injective.injOn)
  simp at hc
  omega

/-- Uniform superexponential bound: `‖n^{k/2} p_k^n‖² ≤ (5/√k)^k` for all `n ≥ 1`. -/
theorem norm_sq_scaled_le_pow (n k : ℕ) (hn : 1 ≤ n) :
    ‖((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k‖ ^ 2 ≤ (5 / Real.sqrt k) ^ k := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  set f : ℕ → ℝ := fun m => 1 / (2 * Real.sqrt n) * srwProb (2 * m) 0 with hfdef
  have hf : ∀ m, 0 ≤ f m := fun m => mul_nonneg (by positivity) (srwProb_nonneg _ _)
  have hrw : ∑ i ∈ Dn n k, (1 / (2 * Real.sqrt n)) ^ k *
      ∏ j : Fin k, srwProb (2 * (i j - (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc)) 0 =
      ∑ i ∈ Dn n k, ∏ j, f (dinc i j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  refine (norm_sq_scaled_le n k hn).trans ?_
  rw [hrw]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_const, nsmul_eq_mul, mul_one,
      pow_zero]
    exact_mod_cast Finset.card_le_one_of_subsingleton _
  by_cases hkn : k ≤ n
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    set r : ℝ := k / n with hr
    have hr0 : 0 < r := by positivity
    refine (gen_bound f hf hr0.le).trans ?_
    have hrn : r * n = k := by rw [hr]; field_simp
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
    have hinner : ∑ m ∈ Icc 1 n, f m * Real.exp (-r * m) ≤ 3 / (2 * Real.sqrt k) := by
      calc ∑ m ∈ Icc 1 n, f m * Real.exp (-r * m)
          ≤ ∑ m ∈ Icc 1 n, 1 / (2 * Real.sqrt n) * (Real.exp (-r * m) / Real.sqrt m) := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
            have := srwProb_two_mul_zero_le hm1
            have h' : srwProb (2 * m) 0 * Real.exp (-r * m) ≤ Real.exp (-r * m) / Real.sqrt m := by
              rw [div_eq_mul_one_div, mul_comm (Real.exp _)]
              exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
            show 1 / (2 * Real.sqrt n) * srwProb (2 * m) 0 * Real.exp (-r * m) ≤ _
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left h' (by positivity)
        _ = 1 / (2 * Real.sqrt n) * ∑ m ∈ Icc 1 n, Real.exp (-r * m) / Real.sqrt m := by
            rw [Finset.mul_sum]
        _ ≤ 1 / (2 * Real.sqrt n) * (3 / Real.sqrt r) := by
            gcongr; exact sum_exp_div_sqrt_le hr0 n
        _ = 3 / (2 * Real.sqrt k) := by
            rw [hr, Real.sqrt_div hk0.le]
            field_simp
    calc Real.exp (r * n) * (∑ m ∈ Icc 1 n, f m * Real.exp (-r * m)) ^ k
        ≤ Real.exp (r * n) * (3 / (2 * Real.sqrt k)) ^ k := by
          gcongr
          exact Finset.sum_nonneg fun m _ => mul_nonneg (hf m) (Real.exp_pos _).le
      _ = (Real.exp 1 * (3 / (2 * Real.sqrt k))) ^ k := by
          rw [hrn, mul_pow, ← Real.exp_nat_mul, mul_one]
      _ ≤ (5 / Real.sqrt k) ^ k := by
          gcongr
          have he := Real.exp_one_lt_d9
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hsk]
          nlinarith
  · rw [Dn_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- The uniform bound in norm form. -/
noncomputable def Bsup (k : ℕ) : ℝ := Real.sqrt ((5 / Real.sqrt k) ^ k)

lemma Bsup_nonneg (k : ℕ) : 0 ≤ Bsup k := Real.sqrt_nonneg _

theorem norm_scaled_le_Bsup (n k : ℕ) (hn : 1 ≤ n) :
    ‖((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k‖ ≤ Bsup k := by
  rw [Bsup, ← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt (norm_sq_scaled_le_pow n k hn)

lemma summable_pow_mul_Bsup (a : ℝ) : Summable fun k : ℕ => a ^ k * Bsup k := by
  refine (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).of_norm_bounded_eventually_nat ?_
  rw [Filter.eventually_atTop]
  refine ⟨max 1 ⌈(20 * a ^ 2) ^ 2⌉₊, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_of_max_le_left hk
  have hk2 : ⌈(20 * a ^ 2) ^ 2⌉₊ ≤ k := le_of_max_le_right hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hge : 20 * a ^ 2 ≤ Real.sqrt k := by
    have h1 : (20 * a ^ 2) ^ 2 ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk2)
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at this
  have hq : a ^ 2 * (5 / Real.sqrt k) ≤ 1 / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ hsk (by norm_num)]
    nlinarith
  have hq0 : 0 ≤ a ^ 2 * (5 / Real.sqrt k) := by positivity
  have e1 : |a| ^ k = Real.sqrt ((a ^ 2) ^ k) := by
    rw [show (a ^ 2) ^ k = (|a| ^ k) ^ 2 by rw [← sq_abs a]; ring, Real.sqrt_sq (by positivity)]
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Bsup_nonneg k), Bsup,
    e1, ← Real.sqrt_mul (by positivity), ← mul_pow]
  calc Real.sqrt ((a ^ 2 * (5 / Real.sqrt k)) ^ k) ≤ Real.sqrt ((1 / 4) ^ k) :=
        Real.sqrt_le_sqrt (pow_le_pow_left₀ hq0 hq k)
    _ = (1 / 2) ^ k := by
        rw [show (1 / 4 : ℝ) ^ k = ((1 / 2) ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
          Real.sqrt_sq (by positivity)]

end IDL5

namespace IDL5

open IntermediateDisorder.PointToLine MeasureTheory Finset

lemma choose_mono_left {m c c' : ℕ} (h : c ≤ c') (h' : c' ≤ m / 2) :
    m.choose c ≤ m.choose c' := by
  revert h'
  induction c', h using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ c' hc ih =>
    intro h'
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma choose_le_of_between {m c c' : ℕ} (h1 : c ≤ c') (h2 : c' ≤ m - c) (hcm : 2 * c ≤ m) :
    m.choose c ≤ m.choose c' := by
  by_cases hc' : c' ≤ m / 2
  · exact choose_mono_left h1 hc'
  · rw [← Nat.choose_symm (show c' ≤ m by omega)]
    exact choose_mono_left (by omega) (by omega)

lemma card_mul_choose_le {m a : ℕ} (ha : 2 * a ≤ m) : (m - 2 * a + 1) * m.choose a ≤ 2 ^ m := by
  have hcard : (Icc a (m - a)).card = m - 2 * a + 1 := by rw [Nat.card_Icc]; omega
  calc (m - 2 * a + 1) * m.choose a = ∑ _c' ∈ Icc a (m - a), m.choose a := by
        rw [sum_const, hcard, smul_eq_mul]
    _ ≤ ∑ c' ∈ Icc a (m - a), m.choose c' := sum_le_sum fun c' hc' => by
        rw [mem_Icc] at hc'; exact choose_le_of_between hc'.1 hc'.2 ha
    _ ≤ ∑ c' ∈ range (m + 1), m.choose c' := sum_le_sum_of_subset (by
        intro c' hc'; rw [mem_Icc] at hc'; rw [mem_range]; omega)
    _ = 2 ^ m := Nat.sum_range_choose m

/-- Unimodality bound: `p(m,y) (|y|+1) ≤ 1`. -/
lemma srwProb_mul_abs_le (m : ℕ) (y : ℤ) : srwProb m y * (|(y : ℝ)| + 1) ≤ 1 := by
  by_cases h0 : srwProb m y = 0
  · rw [h0, zero_mul]; norm_num
  obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_image_of_srwProb_ne_zero h0)
  rw [mem_range] at hc
  rw [srwProb_eq_choose]
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_mul_eq_mul_div, div_le_one h2]
  by_cases hcm : 2 * c ≤ m
  · have hz : ((m - 2 * c + 1 : ℕ) : ℤ) = |(2 * (c : ℤ) - m)| + 1 := by
      rw [abs_of_nonpos (by omega)]; omega
    have habs : |((2 * (c : ℤ) - m : ℤ) : ℝ)| + 1 = ((m - 2 * c + 1 : ℕ) : ℝ) := by
      rw [show ((m - 2 * c + 1 : ℕ) : ℝ) = (((m - 2 * c + 1 : ℕ) : ℤ) : ℝ) by norm_cast, hz]
      push_cast; ring
    rw [habs]
    have := card_mul_choose_le hcm
    rw [mul_comm] at this
    exact_mod_cast this
  · have ha : 2 * (m - c) ≤ m := by omega
    have hz : ((m - 2 * (m - c) + 1 : ℕ) : ℤ) = |(2 * (c : ℤ) - m)| + 1 := by
      rw [abs_of_nonneg (by omega)]; omega
    have habs : |((2 * (c : ℤ) - m : ℤ) : ℝ)| + 1 = ((m - 2 * (m - c) + 1 : ℕ) : ℝ) := by
      rw [show ((m - 2 * (m - c) + 1 : ℕ) : ℝ) = (((m - 2 * (m - c) + 1 : ℕ) : ℤ) : ℝ) by
        norm_cast, hz]
      push_cast; ring
    rw [habs, ← Nat.choose_symm (by omega : c ≤ m)]
    have := card_mul_choose_le ha
    rw [mul_comm] at this
    exact_mod_cast this

lemma le_inv_sqrt_of_sq_mul_le {X A B : ℝ} (hX : 0 ≤ X) (hA : 0 < A) (hAB : A ≤ B)
    (h : X ^ 2 * B ≤ 1) : X ≤ 1 / Real.sqrt A := by
  have hs := Real.sqrt_pos.2 hA
  rw [le_div_iff₀ hs]
  by_contra hc
  push_neg at hc
  have h1 : 1 < (X * Real.sqrt A) ^ 2 := by nlinarith
  rw [mul_pow, Real.sq_sqrt hA.le] at h1
  nlinarith [mul_le_mul_of_nonneg_left hAB (sq_nonneg X)]

/-- `p(m,y) ≤ 1/√m`. -/
lemma srwProb_le_inv_sqrt {m : ℕ} (hm : 1 ≤ m) (y : ℤ) : srwProb m y ≤ 1 / Real.sqrt m := by
  by_cases h0 : srwProb m y = 0
  · rw [h0]; positivity
  obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_image_of_srwProb_ne_zero h0)
  rw [srwProb_eq_choose]
  have hmid : (m.choose c : ℝ) / 2 ^ m ≤ (m.choose (m / 2) : ℝ) / 2 ^ m := by
    gcongr; exact_mod_cast Nat.choose_le_middle c m
  refine hmid.trans ?_
  obtain ⟨N, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [show 2 * N / 2 = N by omega]
    have hp : ((2 * N).choose N : ℝ) / 2 ^ (2 * N) = srwProb (2 * N) 0 := by
      rw [srwProb_two_mul_zero, Nat.centralBinom_eq_two_mul_choose, pow_mul]; norm_num
    rw [hp]
    exact le_inv_sqrt_of_sq_mul_le (srwProb_nonneg _ _) (by exact_mod_cast (by omega : 0 < 2 * N))
      (by push_cast; linarith) (srwProb_two_mul_zero_sq_le N)
  · rw [show (2 * N + 1) / 2 = N by omega]
    have hc2 : (2 * (N + 1)).choose (N + 1) = 2 * (2 * N + 1).choose N := by
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by ring, Nat.choose_succ_succ, Nat.choose_symm_half]
      ring
    have hp : ((2 * N + 1).choose N : ℝ) / 2 ^ (2 * N + 1) = srwProb (2 * (N + 1)) 0 := by
      rw [srwProb_two_mul_zero, Nat.centralBinom_eq_two_mul_choose, hc2]
      have h4 : (4 : ℝ) ^ (N + 1) = 2 * 2 ^ (2 * N + 1) := by
        rw [pow_succ, pow_succ, pow_mul]; ring
      rw [h4]
      push_cast
      field_simp
    rw [hp]
    exact le_inv_sqrt_of_sq_mul_le (srwProb_nonneg _ _) (by positivity)
      (by push_cast; linarith) (srwProb_two_mul_zero_sq_le (N + 1))

/-- `p(m,y)² (m + y²) ≤ 2`. -/
lemma srwProb_sq_mul_le {m : ℕ} (hm : 1 ≤ m) (y : ℤ) :
    srwProb m y ^ 2 * ((m : ℝ) + (y : ℝ) ^ 2) ≤ 2 := by
  have h1 := srwProb_le_inv_sqrt hm y
  have h2 := srwProb_mul_abs_le m y
  have hp := srwProb_nonneg m y
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := Real.sqrt_pos.2 hm0
  have a1 : srwProb m y ^ 2 * m ≤ 1 := by
    have h3 : srwProb m y * Real.sqrt m ≤ 1 := by rwa [le_div_iff₀ hs] at h1
    have h' : (srwProb m y * Real.sqrt m) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hp hs.le]
    rwa [mul_pow, Real.sq_sqrt hm0.le] at h'
  have a2 : srwProb m y ^ 2 * (y : ℝ) ^ 2 ≤ 1 := by
    have h3 : srwProb m y * |(y : ℝ)| ≤ 1 := by nlinarith [abs_nonneg (y : ℝ)]
    have h' : (srwProb m y * |(y : ℝ)|) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hp (abs_nonneg (y : ℝ))]
    rw [mul_pow, sq_abs] at h'
    exact h'
  nlinarith

end IDL5

namespace IDL5

open IntermediateDisorder.PointToLine MeasureTheory Finset

/-- One factor of the domination: `(√n/2) p(m,y) ≤ √5/√(Δt + Δx²)`. -/
lemma factor_le {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {y : ℤ} {dt dx : ℝ} (hdt : 0 < dt)
    (h1 : (n : ℝ) * dt < m + 1) (h2 : |(y : ℝ) - dx * Real.sqrt n| ≤ 2) :
    Real.sqrt n / 2 * srwProb m y ≤ Real.sqrt 5 / Real.sqrt (dt + dx ^ 2) := by
  have hp := srwProb_nonneg m y
  have hq := srwProb_sq_mul_le hm y
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := Real.sq_sqrt hn0.le
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hA : (dx * Real.sqrt n) ^ 2 ≤ (|(y : ℝ)| + 2) ^ 2 := by
    have := abs_le.1 h2
    apply sq_le_sq' <;> linarith [le_abs_self (y : ℝ), neg_abs_le (y : ℝ)]
  have hA' : (n : ℝ) * dx ^ 2 ≤ 2 * (y : ℝ) ^ 2 + 8 := by
    have e : (dx * Real.sqrt n) ^ 2 = n * dx ^ 2 := by rw [mul_pow, hsq]; ring
    rw [e] at hA
    nlinarith [sq_abs (y : ℝ), sq_nonneg (|(y : ℝ)| - 2)]
  have hB : (n : ℝ) * (dt + dx ^ 2) ≤ 10 * (m + (y : ℝ) ^ 2) := by nlinarith
  have hS : 0 < dt + dx ^ 2 := by positivity
  have hX : 0 ≤ Real.sqrt n / 2 * srwProb m y := by positivity
  have hXS : (Real.sqrt n / 2 * srwProb m y) ^ 2 * (dt + dx ^ 2) ≤ 5 := by
    have e : (Real.sqrt n / 2 * srwProb m y) ^ 2 = n / 4 * srwProb m y ^ 2 := by
      rw [mul_pow, div_pow, hsq]; ring
    rw [e]
    have h3 : srwProb m y ^ 2 * ((n : ℝ) * (dt + dx ^ 2)) ≤
        srwProb m y ^ 2 * (10 * (m + (y : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
    nlinarith
  rw [le_div_iff₀ (Real.sqrt_pos.2 hS)]
  rw [show Real.sqrt n / 2 * srwProb m y * Real.sqrt (dt + dx ^ 2) =
      Real.sqrt ((Real.sqrt n / 2 * srwProb m y) ^ 2 * (dt + dx ^ 2)) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hX]]
  exact Real.sqrt_le_sqrt hXS

lemma heat_sq_mul_le {t x : ℝ} (ht : 0 < t) : heatKernel t x ^ 2 * (t + x ^ 2) ≤ 5 := by
  unfold heatKernel
  have h2pt : 0 < 2 * Real.pi * t := by positivity
  rw [div_pow, Real.sq_sqrt h2pt.le, sq, ← Real.exp_add]
  set u := x ^ 2 / t with hu
  have hu0 : 0 ≤ u := by positivity
  have he : Real.exp (-x ^ 2 / (2 * t) + -x ^ 2 / (2 * t)) = Real.exp (-u) := by
    congr 1; rw [hu]; field_simp; ring
  rw [he]
  have h1 : (1 + u) * Real.exp (-u) ≤ 1 := by
    have := Real.add_one_le_exp u
    have h' : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-u)]
  have htx : t + x ^ 2 = t * (1 + u) := by rw [hu]; field_simp
  rw [htx, div_mul_eq_mul_div, div_le_iff₀ h2pt]
  have hpi := Real.pi_gt_three
  nlinarith [Real.exp_pos (-u), mul_le_mul_of_nonneg_left h1 ht.le]

lemma heat_le {t x : ℝ} (ht : 0 < t) : heatKernel t x ≤ Real.sqrt 5 / Real.sqrt (t + x ^ 2) := by
  have hS : 0 < t + x ^ 2 := by positivity
  have hX : 0 ≤ heatKernel t x := by unfold heatKernel; positivity
  rw [le_div_iff₀ (Real.sqrt_pos.2 hS)]
  rw [show heatKernel t x * Real.sqrt (t + x ^ 2) =
      Real.sqrt (heatKernel t x ^ 2 * (t + x ^ 2)) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hX]]
  exact Real.sqrt_le_sqrt (heat_sq_mul_le ht)

/-- Time increment. -/
def dtz {k : ℕ} (z : Fin k → ℝ × ℝ) (j : Fin k) : ℝ := (z j).1 - (withOrigin z j.castSucc).1
/-- Space increment. -/
def dxz {k : ℕ} (z : Fin k → ℝ × ℝ) (j : Fin k) : ℝ := (z j).2 - (withOrigin z j.castSucc).2

/-- The dominating function. -/
noncomputable def Gk (k : ℕ) : (Fin k → ℝ × ℝ) → ℝ :=
  (simplex k).indicator fun z => ∏ j, Real.sqrt 5 / Real.sqrt (dtz z j + dxz z j ^ 2)

lemma Gk_nonneg (k : ℕ) (z : Fin k → ℝ × ℝ) : 0 ≤ Gk k z :=
  Set.indicator_nonneg (fun _ _ => prod_nonneg fun _ _ => by positivity) z

lemma abs_rhoK_le (k : ℕ) (z : Fin k → ℝ × ℝ) : |rhoK k z| ≤ Gk k z := by
  by_cases hs : z ∈ simplex k
  · rw [rhoK, Gk, Set.indicator_of_mem hs, Set.indicator_of_mem hs, Finset.abs_prod]
    refine prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => ?_
    have hdt : 0 < dtz z j := by unfold dtz; linarith [(hs j).1]
    rw [abs_of_nonneg (by unfold heatKernel; positivity)]
    exact heat_le hdt
  · rw [rhoK, Set.indicator_of_notMem hs, abs_zero]
    exact Gk_nonneg k z

/-- Domination of the rescaled discrete kernel. -/
theorem abs_scaled_discreteKernel_le (n k : ℕ) (hn : 1 ≤ n) (z : Fin k → ℝ × ℝ) :
    |(n : ℝ) ^ ((k : ℝ) / 2) * discreteKernel n k z| ≤ Gk k z := by
  have hG0 := Gk_nonneg k z
  by_cases hs : z ∈ simplex k
  swap
  · rw [discreteKernel_supp hs, mul_zero, abs_zero]; exact hG0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold discreteKernel
  split_ifs with hD
  swap
  · rw [mul_zero, abs_zero]; exact hG0
  rw [Gk, Set.indicator_of_mem hs, pathKernelBar, pathKernel]
  have hpow : (n : ℝ) ^ ((k : ℝ) / 2) = Real.sqrt n ^ k := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  rw [hpow]
  set I : Fin k → ℕ := fun j => ⌈(n : ℝ) * (z j).1⌉₊ with hI
  set X : Fin k → ℤ := fun j => parityRound (I j) ((z j).2 * Real.sqrt n) with hX
  have heq : Real.sqrt n ^ k * (((2 : ℝ) ^ k)⁻¹ * ∏ j : Fin k,
      srwProb (I j - (Fin.cons 0 I : Fin (k + 1) → ℕ) j.castSucc)
        (X j - (Fin.cons 0 X : Fin (k + 1) → ℤ) j.castSucc)) =
      ∏ j : Fin k, (Real.sqrt n / 2 * srwProb (I j - (Fin.cons 0 I : Fin (k + 1) → ℕ) j.castSucc)
        (X j - (Fin.cons 0 X : Fin (k + 1) → ℤ) j.castSucc)) := by
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, div_pow]; ring
  rw [heq, Finset.abs_prod]
  refine prod_le_prod (fun _ _ => abs_nonneg _) fun j _ => ?_
  rw [abs_of_nonneg (mul_nonneg (by positivity) (srwProb_nonneg _ _))]
  have hsj := hs j
  have hDj := hD.1 j
  have hR : ∀ j : Fin k, |(X j : ℝ) - (z j).2 * Real.sqrt n| ≤ 1 := by
    intro j
    rw [abs_sub_comm]
    exact abs_sub_parityRound_le _ _
  have hceil : ∀ j : Fin k, (n : ℝ) * (z j).1 ≤ I j := fun j => Nat.le_ceil _
  have hceil2 : ∀ j : Fin k, (I j : ℝ) < (n : ℝ) * (z j).1 + 1 := by
    intro j
    have h1 : 1 ≤ I j := (hD.1 j).1
    have hpos : 0 < (n : ℝ) * (z j).1 := Nat.ceil_pos.1 (show 0 < ⌈(n : ℝ) * (z j).1⌉₊ from h1)
    exact Nat.ceil_lt_add_one hpos.le
  have hRj := hR j
  have hcj := hceil j
  obtain ⟨l, hl⟩ := j
  cases l with
  | zero =>
    simp only [dtz, dxz, withOrigin, cons_castSucc_zero, Nat.sub_zero, sub_zero] at hsj ⊢
    refine factor_le hn hDj.1 hsj.1 (by linarith) ?_
    exact hRj.trans (by norm_num)
  | succ l =>
    have hRl := hR ⟨l, by omega⟩
    have hc2 := hceil2 ⟨l, by omega⟩
    have hmono : I ⟨l, by omega⟩ < I ⟨l + 1, hl⟩ := hD.2 (Fin.mk_lt_mk.2 (Nat.lt_succ_self l))
    simp only [dtz, dxz, withOrigin, cons_castSucc_succ] at hsj ⊢
    refine factor_le hn (by omega) (by linarith [hsj.1]) ?_ ?_
    · rw [Nat.cast_sub hmono.le]
      linarith
    · push_cast
      have a1 := abs_le.1 hRj
      have a2 := abs_le.1 hRl
      rw [abs_le, sub_mul]
      constructor <;> linarith

end IDL5

namespace IDL6

open MeasureTheory Set

lemma inv_add_sq_eq {s : ℝ} (hs : 0 < s) (y : ℝ) :
    (s + y ^ 2)⁻¹ = s⁻¹ * (1 + ((Real.sqrt s)⁻¹ * y) ^ 2)⁻¹ := by
  have h := Real.sq_sqrt hs.le
  rw [mul_pow, inv_pow, h]
  field_simp

lemma integrable_inv_add_sq {s : ℝ} (hs : 0 < s) :
    Integrable (fun y : ℝ => (s + y ^ 2)⁻¹) := by
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have := (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hss.ne')).const_mul s⁻¹
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [inv_add_sq_eq hs y]

lemma integral_inv_add_sq {s : ℝ} (hs : 0 < s) :
    ∫ y : ℝ, (s + y ^ 2)⁻¹ = Real.pi / Real.sqrt s := by
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have h2 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  simp_rw [inv_add_sq_eq hs]
  rw [integral_const_mul]
  have := Measure.integral_comp_mul_left (fun u : ℝ => (1 + u ^ 2)⁻¹) (Real.sqrt s)⁻¹
  rw [this, integral_univ_inv_one_add_sq, inv_inv, abs_of_pos hss, smul_eq_mul,
    eq_div_iff hss.ne']
  rw [show s⁻¹ * (Real.sqrt s * Real.pi) * Real.sqrt s =
    s⁻¹ * (Real.sqrt s * Real.sqrt s) * Real.pi by ring, h2, inv_mul_cancel₀ hs.ne', one_mul]

lemma lintegral_inv_add_sq {s : ℝ} (hs : 0 < s) :
    ∫⁻ y : ℝ, ENNReal.ofReal ((s + y ^ 2)⁻¹) = ENNReal.ofReal (Real.pi / Real.sqrt s) := by
  rw [← integral_inv_add_sq hs, ofReal_integral_eq_lintegral_ofReal (integrable_inv_add_sq hs)]
  exact Filter.Eventually.of_forall fun y => by simp only [Pi.zero_apply]; positivity

/-- The one-step dominating density `H(s,y) = 1_{0<s≤1} 5/(s+y²)`. -/
noncomputable def H : ℝ × ℝ → ENNReal :=
  (Ioc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)).indicator fun p => ENNReal.ofReal (5 * (p.1 + p.2 ^ 2)⁻¹)

lemma measurable_H : Measurable H := by
  unfold H
  refine Measurable.indicator ?_ (measurableSet_Ioc.prod MeasurableSet.univ)
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

lemma lintegral_H_lt_top : ∫⁻ p, H p < ⊤ := by
  unfold H
  rw [lintegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ), Measure.volume_eq_prod,
    ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (5 * (p.1 + p.2 ^ 2)⁻¹))
      (ENNReal.measurable_ofReal.comp
        (by fun_prop : Measurable fun p : ℝ × ℝ => 5 * (p.1 + p.2 ^ 2)⁻¹)).aemeasurable]
  have hin : ∀ s ∈ Ioc (0 : ℝ) 1, ∫⁻ y : ℝ, ENNReal.ofReal (5 * ((s, y).1 + (s, y).2 ^ 2)⁻¹) =
      ENNReal.ofReal (5 * (Real.pi * s ^ (-(1 / 2 : ℝ)))) := by
    intro s hs
    simp only
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_inv_add_sq hs.1, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  rw [setLIntegral_congr_fun measurableSet_Ioc hin]
  have hint : IntegrableOn (fun s : ℝ => 5 * (Real.pi * s ^ (-(1 / 2 : ℝ)))) (Ioc 0 1) := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (5 * Real.pi)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    refine h.congr_fun (fun s _ => by ring) measurableSet_Ioc
  exact hint.lintegral_lt_top

end IDL6

namespace IDL6

open IntermediateDisorder.PointToLine MeasureTheory Set Finset IDL5

lemma stripMeasure_eq_restrict :
    stripMeasure = (volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  rw [stripMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

lemma lintegral_H_strip_le (a : ℝ × ℝ) : ∫⁻ p, H (p - a) ∂stripMeasure ≤ ∫⁻ p, H p := by
  rw [stripMeasure_eq_restrict]
  calc ∫⁻ p, H (p - a) ∂((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)))
      ≤ ∫⁻ p, H (p - a) := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ p, H p := lintegral_sub_right_eq_self H a

/-- Product of one-step dominating densities along a path started at `a`. -/
noncomputable def F (k : ℕ) (a : ℝ × ℝ) (z : Fin k → ℝ × ℝ) : ENNReal :=
  ∏ j : Fin k, H (z j - (Fin.cons a z : Fin (k + 1) → ℝ × ℝ) j.castSucc)

lemma measurable_cons_pair (k : ℕ) :
    Measurable fun p : (ℝ × ℝ) × (Fin k → ℝ × ℝ) => (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ × ℝ) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]; exact measurable_fst
  · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd

lemma measurable_F_uncurry (k : ℕ) :
    Measurable fun p : (ℝ × ℝ) × (Fin k → ℝ × ℝ) => F k p.1 p.2 := by
  unfold F
  refine Finset.measurable_prod _ fun j _ => measurable_H.comp ?_
  exact ((measurable_pi_apply j).comp measurable_snd).sub
    ((measurable_pi_apply j.castSucc).comp (measurable_cons_pair k))

lemma F_succ (k : ℕ) (a b : ℝ × ℝ) (z : Fin k → ℝ × ℝ) :
    F (k + 1) a (Fin.cons b z) = H (b - a) * F k b z := by
  unfold F
  rw [Fin.prod_univ_succ]
  congr 1

lemma lintegral_F_le (k : ℕ) : ∀ a : ℝ × ℝ,
    ∫⁻ z, F k a z ∂(Measure.pi fun _ : Fin k => stripMeasure) ≤ (∫⁻ p, H p) ^ k := by
  induction k with
  | zero => intro a; simp [F]
  | succ k ih =>
    intro a
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => stripMeasure) 0
    rw [← (MeasurePreserving.symm _ hmp).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    have hsymm : ∀ p : (ℝ × ℝ) × (Fin k → ℝ × ℝ),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ × ℝ) 0).symm p =
          Fin.cons p.1 p.2 := by
      intro p
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    simp_rw [hsymm, F_succ]
    have hmeas : Measurable fun p : (ℝ × ℝ) × (Fin k → ℝ × ℝ) => H (p.1 - a) * F k p.1 p.2 :=
      (measurable_H.comp (measurable_fst.sub_const a)).mul (measurable_F_uncurry k)
    rw [lintegral_prod _ hmeas.aemeasurable]
    calc ∫⁻ b, ∫⁻ z, H ((b, z).1 - a) * F k (b, z).1 (b, z).2
          ∂(Measure.pi fun _ : Fin k => stripMeasure) ∂stripMeasure
        = ∫⁻ b, H (b - a) * ∫⁻ z, F k b z ∂(Measure.pi fun _ : Fin k => stripMeasure)
            ∂stripMeasure := by
          refine lintegral_congr fun b => ?_
          exact lintegral_const_mul (H (b - a)) (f := fun z => F k b z)
            ((measurable_F_uncurry k).comp measurable_prodMk_left)
      _ ≤ ∫⁻ b, H (b - a) * (∫⁻ p, H p) ^ k ∂stripMeasure :=
          lintegral_mono fun b => by gcongr; exact ih b
      _ = (∫⁻ b, H (b - a) ∂stripMeasure) * (∫⁻ p, H p) ^ k :=
          lintegral_mul_const _ (measurable_H.comp (measurable_id.sub_const a))
      _ ≤ (∫⁻ p, H p) * (∫⁻ p, H p) ^ k := by gcongr ?_ * _; exact lintegral_H_strip_le a
      _ = (∫⁻ p, H p) ^ (k + 1) := (pow_succ' _ _).symm

lemma withOrigin_fst_nonneg {k : ℕ} {z : Fin k → ℝ × ℝ} (hz : z ∈ simplex k) :
    ∀ i : Fin (k + 1), 0 ≤ (withOrigin z i).1 := by
  intro i
  induction i using Fin.induction with
  | zero => simp [withOrigin]
  | succ j ih =>
    have h := (hz j).1
    have : withOrigin z j.succ = z j := by simp [withOrigin]
    rw [this]; linarith

lemma ofReal_Gk_sq_le (k : ℕ) (z : Fin k → ℝ × ℝ) :
    ENNReal.ofReal (Gk k z ^ 2) ≤ F k 0 z := by
  by_cases hs : z ∈ simplex k
  · rw [Gk, Set.indicator_of_mem hs, ← Finset.prod_pow,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => sq_nonneg _), F]
    refine Finset.prod_le_prod' fun j _ => le_of_eq ?_
    have hdt : 0 < dtz z j := by unfold dtz; linarith [(hs j).1]
    have hdt1 : dtz z j ≤ 1 := by
      unfold dtz; linarith [(hs j).2, withOrigin_fst_nonneg hs j.castSucc]
    have hpos : 0 < dtz z j + dxz z j ^ 2 := by positivity
    have hw : (Fin.cons (0 : ℝ × ℝ) z : Fin (k + 1) → ℝ × ℝ) = withOrigin z := by
      rw [withOrigin, Prod.mk_zero_zero]
    rw [hw, H, Set.indicator_of_mem]
    · rw [div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hpos.le, div_eq_mul_inv]
      rfl
    · exact ⟨⟨hdt, hdt1⟩, Set.mem_univ _⟩
  · rw [Gk, Set.indicator_of_notMem hs]
    simp

lemma measurable_withOrigin (k : ℕ) (i : Fin (k + 1)) :
    Measurable fun z : Fin k → ℝ × ℝ => withOrigin z i := by
  have h : (fun z : Fin k → ℝ × ℝ => withOrigin z i) =
      (fun p : (ℝ × ℝ) × (Fin k → ℝ × ℝ) => (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ × ℝ) i) ∘
        fun z => (((0 : ℝ), (0 : ℝ)), z) := by
    ext z <;> rfl
  rw [h]
  exact ((measurable_pi_apply i).comp (measurable_cons_pair k)).comp
    (measurable_const.prodMk measurable_id)

lemma measurableSet_simplex (k : ℕ) : MeasurableSet (simplex k) := by
  have h : simplex k = ⋂ j : Fin k, ({z : Fin k → ℝ × ℝ | (withOrigin z j.castSucc).1 < (z j).1} ∩
      {z | (z j).1 ≤ 1}) := by
    ext z; simp [simplex]
  rw [h]
  refine MeasurableSet.iInter fun j => (measurableSet_lt ?_ ?_).inter (measurableSet_le ?_ ?_)
  · exact (measurable_withOrigin k j.castSucc).fst
  · exact (measurable_pi_apply j).fst
  · exact (measurable_pi_apply j).fst
  · exact measurable_const

lemma measurable_dtz {k : ℕ} (j : Fin k) : Measurable fun z : Fin k → ℝ × ℝ => dtz z j :=
  (measurable_pi_apply j).fst.sub (measurable_withOrigin k j.castSucc).fst

lemma measurable_dxz {k : ℕ} (j : Fin k) : Measurable fun z : Fin k → ℝ × ℝ => dxz z j :=
  (measurable_pi_apply j).snd.sub (measurable_withOrigin k j.castSucc).snd

lemma measurable_Gk (k : ℕ) : Measurable (Gk k) := by
  unfold Gk
  refine Measurable.indicator ?_ (measurableSet_simplex k)
  refine Finset.measurable_prod _ fun j _ => measurable_const.div ?_
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_dtz j).add ((measurable_dxz j).pow_const 2))

theorem memLp_Gk (k : ℕ) : MemLp (Gk k) 2 (kernelMeasure k) := by
  rw [memLp_two_iff_integrable_sq (measurable_Gk k).aestronglyMeasurable]
  refine ⟨((measurable_Gk k).pow_const 2).aestronglyMeasurable, ?_⟩
  show ∫⁻ z, ‖Gk k z ^ 2‖ₑ ∂kernelMeasure k < ⊤
  calc ∫⁻ z, ‖Gk k z ^ 2‖ₑ ∂kernelMeasure k
      = ∫⁻ z, ENNReal.ofReal (Gk k z ^ 2) ∂kernelMeasure k := by
        refine lintegral_congr fun z => ?_
        rw [Real.enorm_eq_ofReal (sq_nonneg _)]
    _ ≤ ∫⁻ z, F k 0 z ∂kernelMeasure k := lintegral_mono fun z => ofReal_Gk_sq_le k z
    _ ≤ (∫⁻ p, H p) ^ k := lintegral_F_le k 0
    _ < ⊤ := (ENNReal.pow_ne_top lintegral_H_lt_top.ne).lt_top

end IDL6

namespace IDL6

open MeasureTheory Set Filter Topology

/-- Dominated convergence in `L²`: an `L²` dominating function, a.e. convergence. -/
theorem tendsto_eLpNorm_two_of_dominated {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℝ) (g G : α → ℝ) (hG : MemLp G 2 μ)
    (hmeas : ∀ n, 1 ≤ n → AEStronglyMeasurable (f n) μ) (hgm : AEStronglyMeasurable g μ)
    (hbd : ∀ n, 1 ≤ n → ∀ a, |f n a| ≤ G a) (hgb : ∀ a, |g a| ≤ G a)
    (hae : ∀ᵐ a ∂μ, Tendsto (fun n => f n a) atTop (𝓝 (g a))) :
    Tendsto (fun n => eLpNorm (fun a => f n a - g a) 2 μ) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hG2 : Integrable (fun a => (2 * G a) ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hG.const_mul 2).aestronglyMeasurable).1 (hG.const_mul 2)
  have hfin : ∫⁻ a, ‖2 * G a‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have h := hG2.2
    unfold HasFiniteIntegral at h
    simp_rw [enorm_pow] at h
    exact h.ne
  have key : Tendsto (fun n => ∫⁻ a, ‖f (n + 1) a - g a‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun n a => ‖f (n + 1) a - g a‖ₑ ^ 2) (f := fun _ => 0)
      (fun a => ‖2 * G a‖ₑ ^ 2)
      (fun n => (((hmeas (n + 1) (by omega)).sub hgm).enorm.pow_const 2))
      (fun n => Eventually.of_forall fun a => by
        have h : ‖f (n + 1) a - g a‖ₑ ≤ ‖2 * G a‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm]
          apply ENNReal.ofReal_le_ofReal
          have hG0 : 0 ≤ G a := (abs_nonneg _).trans (hgb a)
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 2 * G a by positivity)]
          calc |f (n + 1) a - g a| ≤ |f (n + 1) a| + |g a| := abs_sub _ _
            _ ≤ G a + G a := add_le_add (hbd (n + 1) (by omega) a) (hgb a)
            _ = 2 * G a := by ring
        simp only
        gcongr)
      hfin
      (by
        filter_upwards [hae] with a ha
        have h1 : Tendsto (fun n => f (n + 1) a - g a) atTop (𝓝 0) := by
          have := (ha.comp (tendsto_add_atTop_nat 1)).sub_const (g a)
          simpa using this
        have h2 := ((ENNReal.continuous_pow 2).tendsto _).comp
          ((continuous_enorm.tendsto (0 : ℝ)).comp h1)
        simp only [enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
        exact h2)
    simpa using this
  have hcont := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp key
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hcont
  refine hcont.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp

end IDL6

namespace IDL6

open IntermediateDisorder.PointToLine MeasureTheory Set Filter Topology IDL5

lemma measurable_heat : Measurable fun p : ℝ × ℝ => heatKernel p.1 p.2 := by
  unfold heatKernel; fun_prop

lemma measurable_rhoK (k : ℕ) : Measurable (rhoK k) := by
  unfold rhoK
  refine Measurable.indicator ?_ (measurableSet_simplex k)
  have h : ∀ j : Fin k, Measurable fun z : Fin k → ℝ × ℝ => heatKernel (dtz z j) (dxz z j) :=
    fun j => by
      have h1 := measurable_heat.comp ((measurable_dtz j).prodMk (measurable_dxz j))
      exact h1
  show Measurable fun z : Fin k → ℝ × ℝ => ∏ j : Fin k, heatKernel (dtz z j) (dxz z j)
  exact Finset.measurable_prod _ fun j _ => h j

/-- D3: the `L²` local limit theorem follows from a.e. convergence (domination by `Gk`). -/
theorem LLT_of_ae (k : ℕ) (hae : ∀ᵐ z ∂(kernelMeasure k),
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((k : ℝ) / 2) * discreteKernel n k z) atTop (𝓝 (rhoK k z))) :
    Tendsto (fun n : ℕ => eLpNorm (fun z => (n : ℝ) ^ ((k : ℝ) / 2) * discreteKernel n k z -
      rhoK k z) 2 (kernelMeasure k)) atTop (𝓝 0) :=
  tendsto_eLpNorm_two_of_dominated (fun n z => (n : ℝ) ^ ((k : ℝ) / 2) * discreteKernel n k z)
    (rhoK k) (Gk k) (memLp_Gk k)
    (fun n hn => (memLp_discreteKernel n k hn).aestronglyMeasurable.const_mul _)
    (measurable_rhoK k).aestronglyMeasurable
    (fun n hn z => abs_scaled_discreteKernel_le n k hn z) (abs_rhoK_le k) hae

end IDL6

namespace IDL7

open Filter Topology Real Finset

/-- `f(v) = (1+v) log(1+v) + (1-v) log(1-v)`, the binomial large-deviation exponent. -/
noncomputable def fH (v : ℝ) : ℝ := (1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v)

lemma fH_sub_sq_le {v : ℝ} (hv : |v| < 1) : |fH v - v ^ 2| ≤ 4 * (|v| ^ 3 / (1 - |v|)) := by
  have h1 := Real.abs_log_sub_add_sum_range_le (x := -v) (by rwa [abs_neg]) 2
  have h2 := Real.abs_log_sub_add_sum_range_le (x := v) hv 2
  rw [abs_neg] at h1
  have e1 : (∑ i ∈ range 2, (-v) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -v) =
      -v + v ^ 2 / 2 + Real.log (1 + v) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      sub_neg_eq_add]
    ring
  have e2 : (∑ i ∈ range 2, v ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - v) =
      v + v ^ 2 / 2 + Real.log (1 - v) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one]
    ring
  rw [e1] at h1
  rw [e2] at h2
  have key : fH v - v ^ 2 = (1 + v) * (-v + v ^ 2 / 2 + Real.log (1 + v)) +
      (1 - v) * (v + v ^ 2 / 2 + Real.log (1 - v)) := by unfold fH; ring
  rw [key]
  have hv' := abs_lt.1 hv
  have ha : |1 + v| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hb : |1 - v| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  calc _ ≤ |(1 + v) * (-v + v ^ 2 / 2 + Real.log (1 + v))| +
        |(1 - v) * (v + v ^ 2 / 2 + Real.log (1 - v))| := abs_add_le _ _
    _ = |1 + v| * |-v + v ^ 2 / 2 + Real.log (1 + v)| +
        |1 - v| * |v + v ^ 2 / 2 + Real.log (1 - v)| := by rw [abs_mul, abs_mul]
    _ ≤ 2 * (|v| ^ (2 + 1) / (1 - |v|)) + 2 * (|v| ^ (2 + 1) / (1 - |v|)) :=
        add_le_add (mul_le_mul ha h1 (abs_nonneg _) (by norm_num))
          (mul_le_mul hb h2 (abs_nonneg _) (by norm_num))
    _ = 4 * (|v| ^ 3 / (1 - |v|)) := by ring

lemma tendsto_aux (r w : ℕ → ℝ) (u : ℝ) (hr : Tendsto r atTop atTop)
    (hw : Tendsto w atTop (𝓝 u)) :
    Tendsto (fun n => -(r n ^ 2 / 2) * fH (w n / r n)) atTop (𝓝 (-(u ^ 2 / 2))) := by
  have hinv : Tendsto (fun n => (r n)⁻¹) atTop (𝓝 0) := hr.inv_tendsto_atTop
  have hv : Tendsto (fun n => w n / r n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hw.mul hinv
  have hvabs : Tendsto (fun n => |w n / r n|) atTop (𝓝 0) := by simpa using hv.abs
  have hbound : Tendsto (fun n => 2 * (|w n| ^ 3 * (r n)⁻¹ / (1 - |w n / r n|))) atTop (𝓝 0) := by
    have := ((hw.abs.pow 3).mul hinv).div (tendsto_const_nhds.sub hvabs)
      (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa using this.const_mul 2
  have hev : ∀ᶠ n in atTop, 1 < r n := hr.eventually_gt_atTop 1
  have hsmall : ∀ᶠ n in atTop, |w n / r n| < 1 / 2 :=
    hvabs.eventually (gt_mem_nhds (by norm_num))
  have herr : Tendsto (fun n => -(r n ^ 2 / 2) * (fH (w n / r n) - (w n / r n) ^ 2)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hev, hsmall] with n hn hs
    have hr0 : 0 < r n := by linarith
    have h := fH_sub_sq_le (v := w n / r n) (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < r n ^ 2 / 2)]
    have hD : 0 < 1 - |w n / r n| := by linarith
    calc r n ^ 2 / 2 * |fH (w n / r n) - (w n / r n) ^ 2|
        ≤ r n ^ 2 / 2 * (4 * (|w n / r n| ^ 3 / (1 - |w n / r n|))) := by gcongr
      _ = 2 * (|w n| ^ 3 * (r n)⁻¹ / (1 - |w n / r n|)) := by
        generalize 1 - |w n / r n| = D at hD ⊢
        rw [abs_div, abs_of_pos hr0, div_pow]
        field_simp
        ring
  have hmain : Tendsto (fun n => -(w n ^ 2 / 2)) atTop (𝓝 (-(u ^ 2 / 2))) :=
    ((hw.pow 2).div_const 2).neg
  have := hmain.add herr
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hev] with n hn
  have hr0 : r n ≠ 0 := by positivity
  field_simp
  ring

lemma fact_eq (p : ℕ) (hp : 1 ≤ p) :
    (p.factorial : ℝ) = Stirling.stirlingSeq p * (Real.sqrt (2 * p) * (p / Real.exp 1) ^ p) := by
  have h : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Stirling.stirlingSeq, div_mul_cancel₀]
  exact mul_ne_zero (Real.sqrt_ne_zero'.2 (by positivity))
    (pow_ne_zero _ (div_ne_zero h.ne' (Real.exp_pos 1).ne'))

lemma alg_id (sm sc sb A B : ℝ) (c b : ℕ) (hA : 0 < A) (hB : 0 < B) (hsc : sc ≠ 0)
    (hsb : sb ≠ 0) :
    Real.sqrt (A + B) * (sm * (Real.sqrt (2 * (A + B)) * ((A + B) / Real.exp 1) ^ (c + b)) /
      ((sc * (Real.sqrt (2 * A) * (A / Real.exp 1) ^ c)) *
        (sb * (Real.sqrt (2 * B) * (B / Real.exp 1) ^ b))) / 2 ^ (c + b))
    = sm / (sc * sb) *
      (Real.sqrt (A + B) * Real.sqrt (2 * (A + B)) / (Real.sqrt (2 * A) * Real.sqrt (2 * B))) *
      ((A + B) ^ (c + b) / (A ^ c * B ^ b * 2 ^ (c + b))) := by
  have h1 : Real.sqrt (2 * A) ≠ 0 := Real.sqrt_ne_zero'.2 (by positivity)
  have h2 : Real.sqrt (2 * B) ≠ 0 := Real.sqrt_ne_zero'.2 (by positivity)
  have h3 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  rw [div_pow, div_pow, div_pow, pow_add (Real.exp 1)]
  field_simp

lemma term_eq (c b : ℕ) (hc : 1 ≤ c) (hb : 1 ≤ b) :
    Real.sqrt ((c + b : ℕ) : ℝ) * (((c + b).choose c : ℝ) / 2 ^ (c + b)) =
      Stirling.stirlingSeq (c + b) / (Stirling.stirlingSeq c * Stirling.stirlingSeq b) *
      (Real.sqrt ((c + b : ℕ) : ℝ) * Real.sqrt (2 * ((c + b : ℕ) : ℝ)) /
        (Real.sqrt (2 * (c : ℝ)) * Real.sqrt (2 * (b : ℝ)))) *
      Real.exp (-(Real.sqrt ((c + b : ℕ) : ℝ) ^ 2 / 2) *
        fH ((2 * (c : ℝ) - ((c + b : ℕ) : ℝ)) / Real.sqrt ((c + b : ℕ) : ℝ) /
          Real.sqrt ((c + b : ℕ) : ℝ))) := by
  have hA : (0 : ℝ) < c := by exact_mod_cast hc
  have hB : (0 : ℝ) < b := by exact_mod_cast hb
  have hcb : (((c + b : ℕ)) : ℝ) = c + b := by push_cast; ring
  have hsc : Stirling.stirlingSeq c ≠ 0 := by
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    exact (Stirling.stirlingSeq'_pos c').ne'
  have hsb : Stirling.stirlingSeq b ≠ 0 := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact (Stirling.stirlingSeq'_pos b').ne'
  rw [Nat.cast_choose ℝ (Nat.le_add_right c b), Nat.add_sub_cancel_left,
    fact_eq (c + b) (by omega), fact_eq c hc, fact_eq b hb, hcb]
  rw [alg_id _ _ _ _ _ c b hA hB hsc hsb]
  congr 1
  have hM : (0 : ℝ) < c + b := by positivity
  rw [Real.sq_sqrt hM.le, div_div, Real.mul_self_sqrt hM.le]
  have hE : 0 < ((c : ℝ) + b) ^ (c + b) / ((c : ℝ) ^ c * (b : ℝ) ^ b * 2 ^ (c + b)) := by
    positivity
  rw [← Real.exp_log hE]
  congr 1
  unfold fH
  have h1 : 1 + (2 * (c : ℝ) - (c + b)) / (c + b) = 2 * c / (c + b) := by field_simp; ring
  have h2 : 1 - (2 * (c : ℝ) - (c + b)) / (c + b) = 2 * b / (c + b) := by field_simp; ring
  rw [h1, h2, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_div (by positivity) hM.ne', Real.log_mul (by norm_num) hA.ne',
    Real.log_div (by positivity) hM.ne', Real.log_mul (by norm_num) hB.ne']
  push_cast
  field_simp
  ring

/-- de Moivre-Laplace local limit for the binomial coefficients. -/
theorem binom_llt (m c : ℕ → ℕ) (u : ℝ) (hm : Tendsto (fun n => (m n : ℝ)) atTop atTop)
    (hc : ∀ n, c n ≤ m n)
    (hu : Tendsto (fun n => (2 * (c n : ℝ) - m n) / Real.sqrt (m n)) atTop (𝓝 u)) :
    Tendsto (fun n => Real.sqrt (m n) * (((m n).choose (c n) : ℝ) / 2 ^ (m n))) atTop
      (𝓝 (Real.sqrt 2 / Real.sqrt π * Real.exp (-(u ^ 2 / 2)))) := by
  set r : ℕ → ℝ := fun n => Real.sqrt (m n) with hr_def
  set w : ℕ → ℝ := fun n => (2 * (c n : ℝ) - m n) / Real.sqrt (m n) with hw_def
  have hr : Tendsto r atTop atTop := Real.tendsto_sqrt_atTop.comp hm
  have hv : Tendsto (fun n => w n / r n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hu.mul hr.inv_tendsto_atTop
  have hpos : ∀ᶠ n in atTop, (1 : ℝ) < m n := hm.eventually_gt_atTop 1
  have hAM : Tendsto (fun n => (c n : ℝ) / m n) atTop (𝓝 (1 / 2)) := by
    have : Tendsto (fun n => (1 + w n / r n) / 2) atTop (𝓝 (1 / 2)) := by
      simpa using (hv.const_add 1).div_const 2
    refine this.congr' ?_
    filter_upwards [hpos] with n hn
    simp only [hr_def, hw_def]
    rw [div_div, Real.mul_self_sqrt (by linarith)]
    field_simp
    ring
  have hBM : Tendsto (fun n => ((m n - c n : ℕ) : ℝ) / m n) atTop (𝓝 (1 / 2)) := by
    have : Tendsto (fun n => 1 - (c n : ℝ) / m n) atTop (𝓝 (1 - 1 / 2)) :=
      tendsto_const_nhds.sub hAM
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this
    refine this.congr' ?_
    filter_upwards [hpos] with n hn
    rw [Nat.cast_sub (hc n)]
    field_simp
  have hA : Tendsto (fun n => (c n : ℝ)) atTop atTop := by
    have := hm.atTop_mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hAM
    refine this.congr' ?_
    filter_upwards [hpos] with n hn
    field_simp
  have hB : Tendsto (fun n => ((m n - c n : ℕ) : ℝ)) atTop atTop := by
    have := hm.atTop_mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hBM
    refine this.congr' ?_
    filter_upwards [hpos] with n hn
    field_simp
  have hAn : Tendsto c atTop atTop := tendsto_natCast_atTop_iff.1 hA
  have hBn : Tendsto (fun n => m n - c n) atTop atTop := tendsto_natCast_atTop_iff.1 hB
  have hmn : Tendsto m atTop atTop := tendsto_natCast_atTop_iff.1 hm
  have hS := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hpi : Real.sqrt π ≠ 0 := Real.sqrt_ne_zero'.2 Real.pi_pos
  have hF1 : Tendsto (fun n => Stirling.stirlingSeq (m n) /
      (Stirling.stirlingSeq (c n) * Stirling.stirlingSeq (m n - c n))) atTop
      (𝓝 (Real.sqrt π / (Real.sqrt π * Real.sqrt π))) :=
    (hS.comp hmn).div ((hS.comp hAn).mul (hS.comp hBn)) (mul_ne_zero hpi hpi)
  have hF2 : Tendsto (fun n => Real.sqrt (m n) * Real.sqrt (2 * (m n : ℝ)) /
      (Real.sqrt (2 * (c n : ℝ)) * Real.sqrt (2 * ((m n - c n : ℕ) : ℝ)))) atTop
      (𝓝 (Real.sqrt 2)) := by
    have : Tendsto (fun n => Real.sqrt (1 / (2 * ((c n : ℝ) / m n *
        (((m n - c n : ℕ) : ℝ) / m n))))) atTop
        (𝓝 (Real.sqrt (1 / (2 * (1 / 2 * (1 / 2)))))) :=
      (tendsto_const_nhds.div (tendsto_const_nhds.mul (hAM.mul hBM)) (by norm_num)).sqrt
    rw [show (1 : ℝ) / (2 * (1 / 2 * (1 / 2))) = 2 by norm_num] at this
    refine this.congr' ?_
    filter_upwards [hpos, hA.eventually_gt_atTop 0, hB.eventually_gt_atTop 0] with n hn ha hb
    have hm0 : (0 : ℝ) < m n := by linarith
    rw [← Real.sqrt_mul hm0.le, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * c n),
      ← Real.sqrt_div' _ (by positivity)]
    congr 1
    field_simp
  have hF3 := (Real.continuous_exp.tendsto _).comp (tendsto_aux r w u hr hu)
  have hall := (hF1.mul hF2).mul hF3
  have hlim : Real.sqrt π / (Real.sqrt π * Real.sqrt π) * Real.sqrt 2 *
      Real.exp (-(u ^ 2 / 2)) = Real.sqrt 2 / Real.sqrt π * Real.exp (-(u ^ 2 / 2)) := by
    field_simp
  rw [hlim] at hall
  refine hall.congr' ?_
  filter_upwards [hAn.eventually_ge_atTop 1, hBn.eventually_ge_atTop 1] with n h1 h2
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (hc n)
  simp only [Function.comp_apply, hr_def, hw_def]
  rw [hb, Nat.add_sub_cancel_left] at h2 ⊢
  exact (term_eq (c n) b h1 h2).symm

end IDL7

namespace IDL7

open Filter Topology Real Finset

/-- Local limit theorem for a kernel given by binomial coefficients (the SRW kernel). -/
theorem srw_llt_gen (P : ℕ → ℤ → ℝ)
    (hP : ∀ m c : ℕ, P m (2 * (c : ℤ) - m) = (m.choose c : ℝ) / 2 ^ m)
    (m : ℕ → ℕ) (y : ℕ → ℤ) (u : ℝ) (hm : Tendsto (fun n => (m n : ℝ)) atTop atTop)
    (hpar : ∀ n, Even ((m n : ℤ) + y n))
    (hu : Tendsto (fun n => (y n : ℝ) / Real.sqrt (m n)) atTop (𝓝 u)) :
    Tendsto (fun n => Real.sqrt (m n) * P (m n) (y n)) atTop
      (𝓝 (Real.sqrt 2 / Real.sqrt π * Real.exp (-(u ^ 2 / 2)))) := by
  classical
  have hr : Tendsto (fun n => Real.sqrt (m n)) atTop atTop := Real.tendsto_sqrt_atTop.comp hm
  have hym : Tendsto (fun n => (y n : ℝ) / m n) atTop (𝓝 0) := by
    have := hu.mul hr.inv_tendsto_atTop
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [hm.eventually_gt_atTop 0] with n hn
    simp only [Pi.inv_apply]
    rw [← div_eq_mul_inv, div_div, Real.mul_self_sqrt hn.le]
  have hle : ∀ᶠ n in atTop, |y n| ≤ (m n : ℤ) := by
    filter_upwards [hym.abs.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1)), hm.eventually_gt_atTop 0]
      with n h1 hn
    have : |(y n : ℝ)| < m n := by rwa [abs_div, abs_of_pos hn, div_lt_one hn] at h1
    have h2 : ((|y n| : ℤ) : ℝ) < ((m n : ℤ) : ℝ) := by push_cast; exact this
    exact (Int.cast_lt.1 h2).le
  let c : ℕ → ℕ := fun n => if |y n| ≤ (m n : ℤ) then (((m n : ℤ) + y n) / 2).toNat else 0
  have hc : ∀ n, c n ≤ m n := by
    intro n
    simp only [c]
    split_ifs with h
    · have := abs_le.1 h
      rw [Int.toNat_le]
      omega
    · exact Nat.zero_le _
  have hcy : ∀ᶠ n in atTop, 2 * (c n : ℤ) - m n = y n := by
    filter_upwards [hle] with n h
    simp only [c, if_pos h]
    obtain ⟨t, ht⟩ := hpar n
    have := abs_le.1 h
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hu' : Tendsto (fun n => (2 * (c n : ℝ) - m n) / Real.sqrt (m n)) atTop (𝓝 u) := by
    refine hu.congr' ?_
    filter_upwards [hcy] with n h
    rw [← h]
    push_cast
    ring
  have := binom_llt m c u hm hc hu'
  refine this.congr' ?_
  filter_upwards [hcy] with n h
  rw [← h, hP]

lemma ceil_div_tendsto {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌈(n : ℝ) * a⌉₊ : ℝ) / n) atTop (𝓝 a) := by
  have hup : Tendsto (fun n : ℕ => a + 1 / (n : ℝ)) atTop (𝓝 a) := by
    have := (tendsto_const_nhds (x := a)).add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn', mul_comm]
    exact Nat.le_ceil _
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn', add_mul, one_div_mul_cancel hn'.ne', mul_comm a]
    exact (Nat.ceil_lt_add_one (by positivity)).le

/-- One factor of the rescaled discrete kernel converges to the heat kernel factor. -/
theorem factor_tendsto (P : ℕ → ℤ → ℝ)
    (hP : ∀ m c : ℕ, P m (2 * (c : ℤ) - m) = (m.choose c : ℝ) / 2 ^ m)
    (R : ℕ → ℝ → ℤ) (hR1 : ∀ (i : ℕ) (y : ℝ), |y - R i y| ≤ 1) (hR2 : ∀ (i : ℕ) (y : ℝ), Even ((i : ℤ) - R i y))
    {s t x x' : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    Tendsto (fun n : ℕ => Real.sqrt n / 2 *
      P (⌈(n : ℝ) * t⌉₊ - ⌈(n : ℝ) * s⌉₊)
        (R ⌈(n : ℝ) * t⌉₊ (x * Real.sqrt n) - R ⌈(n : ℝ) * s⌉₊ (x' * Real.sqrt n))) atTop
      (𝓝 (Real.exp (-(x - x') ^ 2 / (2 * (t - s))) / Real.sqrt (2 * π * (t - s)))) := by
  have hT : 0 < t - s := sub_pos.2 hst
  set M : ℕ → ℕ := fun n => ⌈(n : ℝ) * t⌉₊ - ⌈(n : ℝ) * s⌉₊ with hM_def
  set Y : ℕ → ℤ := fun n => R ⌈(n : ℝ) * t⌉₊ (x * Real.sqrt n) - R ⌈(n : ℝ) * s⌉₊ (x' * Real.sqrt n)
    with hY_def
  have hmono : ∀ n : ℕ, ⌈(n : ℝ) * s⌉₊ ≤ ⌈(n : ℝ) * t⌉₊ := fun n =>
    Nat.ceil_mono (mul_le_mul_of_nonneg_left hst.le n.cast_nonneg)
  have hMcast : ∀ n, (M n : ℝ) = ⌈(n : ℝ) * t⌉₊ - ⌈(n : ℝ) * s⌉₊ := fun n => by
    simp only [hM_def]; rw [Nat.cast_sub (hmono n)]
  have hMn : Tendsto (fun n : ℕ => (M n : ℝ) / n) atTop (𝓝 (t - s)) := by
    have := (ceil_div_tendsto (hs.trans hst.le)).sub (ceil_div_tendsto hs)
    refine this.congr' (Eventually.of_forall fun n => ?_)
    show _ = (M n : ℝ) / n
    rw [hMcast, sub_div]
  have hM : Tendsto (fun n => (M n : ℝ)) atTop atTop := by
    have := tendsto_natCast_atTop_atTop.atTop_mul_pos hT hMn
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hsq : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hYn : Tendsto (fun n : ℕ => (Y n : ℝ) / Real.sqrt n) atTop (𝓝 (x - x')) := by
    have h0 : Tendsto (fun n : ℕ => (Y n : ℝ) / Real.sqrt n - (x - x')) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop hsq)
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
      rw [Real.norm_eq_abs, show (Y n : ℝ) / Real.sqrt n - (x - x') =
        ((R ⌈(n : ℝ) * t⌉₊ (x * Real.sqrt n) - x * Real.sqrt n) -
          (R ⌈(n : ℝ) * s⌉₊ (x' * Real.sqrt n) - x' * Real.sqrt n)) / Real.sqrt n by
        simp only [hY_def]; push_cast; field_simp; ring]
      rw [abs_div, abs_of_pos hn']
      gcongr
      have a1 := hR1 ⌈(n : ℝ) * t⌉₊ (x * Real.sqrt n)
      have a2 := hR1 ⌈(n : ℝ) * s⌉₊ (x' * Real.sqrt n)
      rw [abs_sub_comm] at a1 a2
      calc _ ≤ |(R ⌈(n : ℝ) * t⌉₊ (x * Real.sqrt n) : ℝ) - x * Real.sqrt n| +
            |(R ⌈(n : ℝ) * s⌉₊ (x' * Real.sqrt n) : ℝ) - x' * Real.sqrt n| := abs_sub _ _
        _ ≤ 2 := by linarith
    simpa using h0.add_const (x - x')
  have hpar : ∀ n, Even ((M n : ℤ) + Y n) := by
    intro n
    obtain ⟨a, ha⟩ := hR2 ⌈(n : ℝ) * t⌉₊ (x * Real.sqrt n)
    obtain ⟨b, hb⟩ := hR2 ⌈(n : ℝ) * s⌉₊ (x' * Real.sqrt n)
    have hm := hmono n
    refine ⟨a - b + R ⌈(n : ℝ) * t⌉₊ (x * Real.sqrt n) - R ⌈(n : ℝ) * s⌉₊ (x' * Real.sqrt n), ?_⟩
    simp only [hM_def, hY_def]
    omega
  set u : ℝ := (x - x') / Real.sqrt (t - s) with hu_def
  have hsT : Real.sqrt (t - s) ≠ 0 := Real.sqrt_ne_zero'.2 hT
  have hu : Tendsto (fun n => (Y n : ℝ) / Real.sqrt (M n)) atTop (𝓝 u) := by
    have := hYn.div hMn.sqrt hsT
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0, hM.eventually_gt_atTop 0] with n hn hMp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Pi.div_apply]
    rw [Real.sqrt_div' _ hn'.le]
    have h1 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn').ne'
    have h2 : Real.sqrt (M n) ≠ 0 := (Real.sqrt_pos.2 hMp).ne'
    field_simp
  have hsrw := srw_llt_gen P hP M Y u hM hpar hu
  have hlim := ((tendsto_const_nhds (x := (1 / 2 : ℝ))).mul (hMn.sqrt.inv₀ hsT)).mul hsrw
  have hval : 1 / 2 * (Real.sqrt (t - s))⁻¹ *
      (Real.sqrt 2 / Real.sqrt π * Real.exp (-(u ^ 2 / 2))) =
      Real.exp (-(x - x') ^ 2 / (2 * (t - s))) / Real.sqrt (2 * π * (t - s)) := by
    have he : -(u ^ 2 / 2) = -(x - x') ^ 2 / (2 * (t - s)) := by
      rw [hu_def, div_pow, Real.sq_sqrt hT.le, neg_div, div_div, mul_comm (t - s) 2]
    rw [he, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hpi : Real.sqrt π ≠ 0 := Real.sqrt_ne_zero'.2 Real.pi_pos
    have h2' : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    exact Real.sq_sqrt (by norm_num)
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hM.eventually_gt_atTop 0] with n hn hMp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_div' _ hn'.le]
  have h1 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn').ne'
  have h2 : Real.sqrt (M n) ≠ 0 := (Real.sqrt_pos.2 hMp).ne'
  simp only [hM_def, hY_def] at h2 ⊢
  field_simp

end IDL7

namespace IDL7

open IntermediateDisorder.PointToLine MeasureTheory Filter Topology Finset IDL5 IDL6

lemma parityRound_zero_zero : parityRound 0 0 = 0 := by simp [parityRound]

lemma cons_eq_withOrigin {α : Type*} {k : ℕ} (g : ℝ × ℝ → α) (z : Fin k → ℝ × ℝ)
    (i : Fin (k + 1)) :
    (Fin.cons (g ((0 : ℝ), (0 : ℝ))) (fun j => g (z j)) : Fin (k + 1) → α) i =
      g (withOrigin z i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [withOrigin]
  · simp [withOrigin]

/-- A3: pointwise convergence of the rescaled discrete kernel (everywhere, not only a.e.). -/
theorem A3_pointwise (k : ℕ) (z : Fin k → ℝ × ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((k : ℝ) / 2) * discreteKernel n k z) atTop
      (𝓝 (rhoK k z)) := by
  by_cases hs : z ∈ simplex k
  swap
  · have h0 : rhoK k z = 0 := by rw [rhoK, Set.indicator_of_notMem hs]
    rw [h0]
    have : (fun n : ℕ => (n : ℝ) ^ ((k : ℝ) / 2) * discreteKernel n k z) = fun _ => 0 := by
      funext n; rw [discreteKernel_supp hs, mul_zero]
    rw [this]
    exact tendsto_const_nhds
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := IDL3a.simplex_gap hs
  have hev : ∀ᶠ n : ℕ in atTop, InDiscreteSimplex n (fun j => ⌈(n : ℝ) * (z j).1⌉₊) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    have hnN : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
    have hnδ : 1 < (n : ℝ) * δ := by
      have h := lt_of_lt_of_le hN hnN
      rw [div_lt_iff₀ hδ] at h
      linarith
    refine ⟨fun j => ⟨?_, ?_⟩, fun j j' hjj' => ?_⟩
    · have hp : 0 < (n : ℝ) * (z j).1 := mul_pos (by linarith) (by linarith [hδ1 j])
      exact Nat.ceil_pos.2 hp
    · exact Nat.ceil_le.2 (mul_le_of_le_one_right (by positivity) (hs j).2)
    · have h1 := hδ2 j j' hjj'
      have hp : 0 ≤ (n : ℝ) * (z j).1 := mul_nonneg (by linarith) (by linarith [hδ1 j])
      have h2 : (⌈(n : ℝ) * (z j).1⌉₊ : ℝ) < n * (z j).1 + 1 := Nat.ceil_lt_add_one hp
      have h3 : (n : ℝ) * (z j').1 ≤ ⌈(n : ℝ) * (z j').1⌉₊ := Nat.le_ceil _
      have h4 : (n : ℝ) * ((z j).1 + δ) ≤ n * (z j').1 :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have h5 : (⌈(n : ℝ) * (z j).1⌉₊ : ℝ) < ⌈(n : ℝ) * (z j').1⌉₊ := by nlinarith
      exact_mod_cast h5
  have hfac : ∀ j : Fin k, Tendsto (fun n : ℕ => Real.sqrt n / 2 *
      srwProb (⌈(n : ℝ) * (z j).1⌉₊ - ⌈(n : ℝ) * (withOrigin z j.castSucc).1⌉₊)
        (parityRound ⌈(n : ℝ) * (z j).1⌉₊ ((z j).2 * Real.sqrt n) -
          parityRound ⌈(n : ℝ) * (withOrigin z j.castSucc).1⌉₊
            ((withOrigin z j.castSucc).2 * Real.sqrt n)))
      atTop (𝓝 (heatKernel ((z j).1 - (withOrigin z j.castSucc).1)
        ((z j).2 - (withOrigin z j.castSucc).2))) := by
    intro j
    have h := factor_tendsto srwProb srwProb_eq_choose parityRound
      (fun i y => abs_sub_parityRound_le i y) (fun i y => parityMatch_parityRound i y)
      (withOrigin_fst_nonneg hs j.castSucc) (hs j).1 (x := (z j).2)
      (x' := (withOrigin z j.castSucc).2)
    exact h
  have hprod := tendsto_finset_prod (Finset.univ : Finset (Fin k)) (fun j _ => hfac j)
  rw [rhoK, Set.indicator_of_mem hs]
  refine hprod.congr' ?_
  filter_upwards [hev, eventually_ge_atTop 1] with n hD hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold discreteKernel
  rw [if_pos hD, pathKernelBar, pathKernel]
  have hpow : (n : ℝ) ^ ((k : ℝ) / 2) = Real.sqrt n ^ k := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  have hIc : ∀ j : Fin k, (Fin.cons 0 (fun j => ⌈(n : ℝ) * (z j).1⌉₊) : Fin (k + 1) → ℕ)
      j.castSucc = ⌈(n : ℝ) * (withOrigin z j.castSucc).1⌉₊ := by
    intro j
    have h := cons_eq_withOrigin (fun p : ℝ × ℝ => ⌈(n : ℝ) * p.1⌉₊) z j.castSucc
    simp only [mul_zero, Nat.ceil_zero] at h
    exact h
  have hXc : ∀ j : Fin k, (Fin.cons 0 (fun j => parityRound ⌈(n : ℝ) * (z j).1⌉₊
      ((z j).2 * Real.sqrt n)) : Fin (k + 1) → ℤ) j.castSucc =
      parityRound ⌈(n : ℝ) * (withOrigin z j.castSucc).1⌉₊
        ((withOrigin z j.castSucc).2 * Real.sqrt n) := by
    intro j
    have h := cons_eq_withOrigin
      (fun p : ℝ × ℝ => parityRound ⌈(n : ℝ) * p.1⌉₊ (p.2 * Real.sqrt n)) z j.castSucc
    simp only [mul_zero, Nat.ceil_zero, zero_mul, parityRound_zero_zero] at h
    exact h
  rw [hpow, ← mul_assoc, show Real.sqrt n ^ k * ((2 : ℝ) ^ k)⁻¹ =
      ∏ _j : Fin k, (Real.sqrt n / 2) by
    rw [prod_const, card_univ, Fintype.card_fin, div_pow, div_eq_mul_inv], ← prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [hIc j, hXc j]

/-- The `L²` local limit theorem (Lemma A.1, convergence part). -/
theorem LLT_child_thm (k : ℕ) :
    Tendsto (fun n : ℕ => eLpNorm (fun z => (n : ℝ) ^ ((k : ℝ) / 2) * discreteKernel n k z -
      rhoK k z) 2 (kernelMeasure k)) atTop (𝓝 0) :=
  LLT_of_ae k (ae_of_all _ (A3_pointwise k))

end IDL7

/-! ## IDL8: Prop 5.3 glue (Tannery + triangle + Slutsky), given the Lemma 5.2 identity. -/
namespace IDL8

open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory Filter Topology

lemma memLp_rhoK (k : ℕ) : MemLp (rhoK k) 2 (kernelMeasure k) :=
  (IDL6.memLp_Gk k).mono' (IDL6.measurable_rhoK k).aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact IDL5.abs_rhoK_le k z)

lemma coeFn_rhoKLp (k : ℕ) : (rhoKLp k : (Fin k → ℝ × ℝ) → ℝ) =ᵐ[kernelMeasure k] rhoK k := by
  rw [rhoKLp, dif_pos (memLp_rhoK k)]
  exact MemLp.coeFn_toLp _

lemma coeFn_dKLp (n k : ℕ) (hn : 1 ≤ n) :
    (discreteKernelLp n k : (Fin k → ℝ × ℝ) → ℝ) =ᵐ[kernelMeasure k] discreteKernel n k := by
  rw [discreteKernelLp, dif_pos (IDL5.memLp_discreteKernel n k hn)]
  exact MemLp.coeFn_toLp _

lemma simplexSupported_smul {k : ℕ} (c : ℝ) (f : Lp ℝ 2 (kernelMeasure k))
    (hf : SimplexSupported f) : SimplexSupported (c • f) := by
  unfold SimplexSupported at *
  filter_upwards [hf, Lp.coeFn_smul c f] with z hz hz' hzs
  rw [hz', Pi.smul_apply, hz hzs, smul_zero]

lemma simplexSupported_rhoKLp (k : ℕ) : SimplexSupported (rhoKLp k) := by
  unfold SimplexSupported
  filter_upwards [coeFn_rhoKLp k] with z hz hzs
  rw [hz, rhoK, Set.indicator_of_notMem hzs]

/-- the L² local limit in `Lp` norm form. -/
lemma norm_diff_tendsto (k : ℕ) :
    Tendsto (fun n : ℕ => ‖((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k - rhoKLp k‖)
      atTop (𝓝 0) := by
  have hL := IDL7.LLT_child_thm k
  have h2 : Tendsto (fun n : ℕ => (eLpNorm (fun z => (n : ℝ) ^ ((k : ℝ) / 2) *
      discreteKernel n k z - rhoK k z) 2 (kernelMeasure k)).toReal) atTop (𝓝 0) := by
    have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL
    simpa [Function.comp_def] using h3
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k) (rhoKLp k),
    Lp.coeFn_smul ((n : ℝ) ^ ((k : ℝ) / 2)) (discreteKernelLp n k), coeFn_dKLp n k hn,
    coeFn_rhoKLp k] with z h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]

lemma norm_rhoKLp_le (k : ℕ) : ‖rhoKLp k‖ ≤ IDL5.Bsup k := by
  have ht : Tendsto (fun n : ℕ => IDL5.Bsup k +
      ‖((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k - rhoKLp k‖) atTop
      (𝓝 (IDL5.Bsup k + 0)) := tendsto_const_nhds.add (norm_diff_tendsto k)
  rw [add_zero] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  calc ‖rhoKLp k‖ = ‖((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k -
        (((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k - rhoKLp k)‖ := by rw [sub_sub_cancel]
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := by gcongr; exact IDL5.norm_scaled_le_Bsup n k hn

lemma Bsup_nonneg (k : ℕ) : 0 ≤ IDL5.Bsup k := Real.sqrt_nonneg _

noncomputable def gLim (β : ℝ) (k : ℕ) : Lp ℝ 2 (kernelMeasure k) :=
  (Real.sqrt 2 * β) ^ k • rhoKLp k

noncomputable def gN (β : ℝ) (n k : ℕ) : Lp ℝ 2 (kernelMeasure k) :=
  (Real.sqrt 2 * β) ^ k • (((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k)

lemma norm_gN_sub_le {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    ‖gN β n k - gLim β k‖ ≤ (Real.sqrt 2 * β) ^ k * (2 * IDL5.Bsup k) := by
  have ha : 0 ≤ Real.sqrt 2 * β := by positivity
  rw [gN, gLim, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha k)]
  gcongr
  calc _ ≤ ‖((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k‖ + ‖rhoKLp k‖ := norm_sub_le _ _
    _ ≤ IDL5.Bsup k + IDL5.Bsup k :=
        add_le_add (IDL5.norm_scaled_le_Bsup n k hn) (norm_rhoKLp_le k)
    _ = _ := by ring

lemma summable_bound (β : ℝ) :
    Summable fun k : ℕ => (Real.sqrt 2 * β) ^ k * (2 * IDL5.Bsup k) := by
  have := (IDL5.summable_pow_mul_Bsup (Real.sqrt 2 * β)).mul_left 2
  refine this.congr fun k => ?_
  ring

lemma tsum_tendsto {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n : ℕ => ∑' k, ‖gN β n k - gLim β k‖) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun n k => ‖gN β n k - gLim β k‖) (g := fun _ => (0 : ℝ)) (summable_bound β)
    (fun k => ?_) ?_
  · simpa using h
  · have ha : 0 ≤ Real.sqrt 2 * β := by positivity
    have : Tendsto (fun n : ℕ => (Real.sqrt 2 * β) ^ k *
        ‖((n : ℝ) ^ ((k : ℝ) / 2)) • discreteKernelLp n k - rhoKLp k‖) atTop (𝓝 0) := by
      simpa using (norm_diff_tendsto k).const_mul ((Real.sqrt 2 * β) ^ k)
    refine this.congr fun n => ?_
    rw [gN, gLim, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha k)]
  · filter_upwards [eventually_ge_atTop 1] with n hn k
    rw [norm_norm]
    exact norm_gN_sub_le hβ hn k

lemma disc_close {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖discreteChaos ω Q n (gN β n) - discreteChaos ω Q n (gLim β)‖ ≤
      ∑' k, ‖gN β n k - gLim β k‖ := by
  have hss : ∀ k, SimplexSupported (gN β n k - gLim β k) := fun k =>
    IDL4.simplexSupported_sub _ _
      (simplexSupported_smul _ _ (simplexSupported_smul _ _
        (IDL5.simplexSupported_discreteKernelLp n k)))
      (simplexSupported_smul _ _ (simplexSupported_rhoKLp k))
  have hsum : Summable fun k => ‖gN β n k - gLim β k‖ :=
    (summable_bound β).of_nonneg_of_le (fun _ => norm_nonneg _) (norm_gN_sub_le hβ hn)
  have heq : discreteChaos ω Q n (gN β n) - discreteChaos ω Q n (gLim β) =
      ∑ k ∈ Finset.range (n + 1),
        ((n : ℝ) ^ (-(3 * (k : ℝ) / 4))) • uStatistic ω Q n k (gN β n k - gLim β k) := by
    unfold discreteChaos
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_sub]
    congr 1
    exact ((IDL2a.uStatL hω n k).map_sub (gN β n k) (gLim β k)).symm
  rw [heq]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => IDL2b.norm_scaled_uStatistic_le hω hn k _
    (hss k)).trans ?_
  exact hsum.sum_le_tsum _ (fun k _ => norm_nonneg _)

lemma measurable_mpf {Ω : Type*} [MeasurableSpace Ω] {ω : ℕ × ℤ → Ω → ℝ}
    (hm : ∀ p, Measurable (ω p)) (n : ℕ) (b : ℝ) :
    Measurable (modifiedPartitionFunction ω n b) := by
  unfold modifiedPartitionFunction
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun s _ => ?_
  exact Finset.measurable_prod _ fun m _ => (measurable_const.add
    (measurable_const.mul (hm _)))

/-- Prop 5.3 from the Lemma 5.2 identity `hP5`. -/
theorem glue {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ}
    (hω : IsStdEnvironment ω Q)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    (W : Set (ℝ × ℝ) → Ω' → ℝ) (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q')
    (hW : IsWhiteNoise W Q') (hI : IsMultipleIntegral W Q' I) (β : ℝ) (hβ : 0 < β)
    (hP5 : ∀ n : ℕ, 1 ≤ n → (discreteChaos ω Q n (gN β n) : Ω → ℝ) =ᵐ[Q]
      modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ)))) :
    TendstoInDistribution
      (fun n => modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))))
      atTop (wienerChaos I (Real.sqrt 2 * β)) (fun _ => Q) Q' := by
  have hgss : ∀ k, SimplexSupported (gLim β k) := fun k =>
    simplexSupported_smul _ _ (simplexSupported_rhoKLp k)
  have hgsum : Summable fun k => ‖gLim β k‖ := by
    have ha : 0 ≤ Real.sqrt 2 * β := by positivity
    refine (IDL5.summable_pow_mul_Bsup (Real.sqrt 2 * β)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun k => ?_
    rw [gLim, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha k)]
    gcongr
    exact norm_rhoKLp_le k
  have hX := IDL4.chaos_tendsto hω hW hI (gLim β) hgss hgsum
  refine tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n => (discreteChaos ω Q n (gLim β) : Ω → ℝ)) _ _ hX ?_
    (fun n => (measurable_mpf hω.measurable n _).aemeasurable)
  have hF : TendstoInMeasure Q (fun n => (discreteChaos ω Q n (gN β n) : Ω → ℝ) -
      (discreteChaos ω Q n (gLim β) : Ω → ℝ)) atTop 0 := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero
      (fun n => (Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
      aestronglyMeasurable_const ?_
    have hup : Tendsto (fun n : ℕ => ENNReal.ofReal (∑' k, ‖gN β n k - gLim β k‖)) atTop
        (𝓝 0) := by simpa using ENNReal.tendsto_ofReal (tsum_tendsto hβ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [sub_zero, IDL4.eLpNorm_sub_eq]
    exact ENNReal.ofReal_le_ofReal (disc_close hω hβ hn)
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hF
  filter_upwards [eventually_ge_atTop 1] with n hn
  filter_upwards [hP5 n hn] with a ha
  simp only [Pi.sub_apply]
  rw [ha]

end IDL8

/-! ## IDL9: Lemma 5.2 combinatorics (path counting and the chaos expansion of `𝔷_n`). -/
namespace IDL9

open IntermediateDisorder.PointToLine Finset

lemma walkPos_zero {n : ℕ} (s : Fin n → Bool) : walkPos s 0 = 0 := by
  simp [walkPos]

lemma walkPos_append {m r : ℕ} (u : Fin m → Bool) (v : Fin r → Bool) (t : ℕ) :
    walkPos (Fin.append u v) (m + t) = walkPos u m + walkPos v t := by
  unfold walkPos
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : ((Fin.castAdd r j : Fin (m + r)) : ℕ) < m + t := by
      simp only [Fin.val_castAdd]; omega
    rw [if_pos h1, if_pos j.isLt, Fin.append_left]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.append_right]
    simp only [Fin.val_natAdd, add_lt_add_iff_left]

lemma abs_walkPos_le' {n : ℕ} (s : Fin n → Bool) (i : ℕ) : |walkPos s i| ≤ n := by
  unfold walkPos
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin n, |(if (j : ℕ) < i then stepZ (s j) else 0)|
      ≤ ∑ _j : Fin n, (1 : ℤ) := Finset.sum_le_sum fun j _ => by
        split_ifs
        · unfold stepZ; split_ifs <;> simp
        · simp
    _ = n := by simp

lemma card_srw (m : ℕ) (y : ℤ) :
    (((univ.filter fun s : Fin m → Bool => walkPos s m = y).card : ℕ) : ℝ) =
      2 ^ m * srwProb m y := by
  unfold srwProb
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

lemma cons_sub_first {k : ℕ} (I : Fin (k + 1) → ℕ) :
    (Fin.cons 0 (fun j : Fin k => I j.succ - I 0) : Fin (k + 1) → ℕ) = fun m => I m - I 0 := by
  funext m
  cases m using Fin.cases <;> simp

lemma cons_sub_first_z {k : ℕ} (x : Fin (k + 1) → ℤ) :
    (Fin.cons 0 (fun j : Fin k => x j.succ - x 0) : Fin (k + 1) → ℤ) = fun m => x m - x 0 := by
  funext m
  cases m using Fin.cases <;> simp

lemma pathKernel_cons {k : ℕ} (I : Fin (k + 1) → ℕ) (x : Fin (k + 1) → ℤ) (hI : Monotone I) :
    pathKernel I x = srwProb (I 0) (x 0) *
      pathKernel (fun j : Fin k => I j.succ - I 0) (fun j => x j.succ - x 0) := by
  unfold pathKernel
  rw [Fin.prod_univ_succ, cons_sub_first, cons_sub_first_z]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j _ => ?_
    have e1 : (Fin.cons 0 I : Fin (k + 2) → ℕ) j.succ.castSucc = I j.castSucc := by
      rw [← Fin.succ_castSucc, Fin.cons_succ]
    have e2 : (Fin.cons 0 x : Fin (k + 2) → ℤ) j.succ.castSucc = x j.castSucc := by
      rw [← Fin.succ_castSucc, Fin.cons_succ]
    rw [e1, e2]
    have h0 : I 0 ≤ I j.castSucc := hI (Fin.zero_le _)
    have h1 : I j.castSucc ≤ I j.succ := hI (Fin.castSucc_le_succ j)
    dsimp only
    congr 1
    · omega
    · ring

/-- Markov property for SRW paths: the number of `n`-step paths through prescribed points. -/
theorem card_paths (k : ℕ) : ∀ (n : ℕ) (I : Fin k → ℕ) (x : Fin k → ℤ), Monotone I →
    (∀ j, I j ≤ n) →
    (((univ.filter fun s : Fin n → Bool => ∀ j, walkPos s (I j) = x j).card : ℕ) : ℝ) =
      2 ^ n * pathKernel I x := by
  induction k with
  | zero =>
    intro n I x _ _
    simp [pathKernel]
  | succ k ih =>
    intro n I x hI hle
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (hle 0)
    set A : Finset (Fin (I 0) → Bool) := univ.filter fun u => walkPos u (I 0) = x 0 with hA
    set B : Finset (Fin r → Bool) := univ.filter fun v =>
      ∀ j : Fin k, walkPos v (I j.succ - I 0) = x j.succ - x 0 with hB
    have hset : (univ.filter fun s : Fin (I 0 + r) → Bool => ∀ j, walkPos s (I j) = x j) =
        (A ×ˢ B).map (Fin.appendEquiv (I 0) r).toEmbedding := by
      ext s
      rw [Finset.mem_map_equiv]
      obtain ⟨⟨u, v⟩, rfl⟩ := (Fin.appendEquiv (α := Bool) (I 0) r).surjective s
      rw [Equiv.symm_apply_apply]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, hA, hB,
        Fin.forall_fin_succ]
      have hs : (Fin.appendEquiv (I 0) r) (u, v) = Fin.append u v := rfl
      rw [hs]
      have h0 : walkPos (Fin.append u v) (I 0) = walkPos u (I 0) := by
        have := walkPos_append u v 0
        rw [add_zero, walkPos_zero, add_zero] at this
        exact this
      have hj : ∀ j : Fin k, walkPos (Fin.append u v) (I j.succ) =
          walkPos u (I 0) + walkPos v (I j.succ - I 0) := by
        intro j
        have hle' : I 0 ≤ I j.succ := hI (Fin.zero_le _)
        rw [← walkPos_append u v, Nat.add_sub_cancel' hle']
      rw [h0]
      simp only [hj]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun j => ?_⟩
        have := h2 j
        rw [h1] at this
        linarith
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun j => ?_⟩
        rw [h1, h2 j]
        ring
    rw [hset, Finset.card_map, Finset.card_product, Nat.cast_mul, hA, card_srw, hB,
      ih r (fun j => I j.succ - I 0) (fun j => x j.succ - x 0)
        (fun a b hab => Nat.sub_le_sub_right (hI (Fin.succ_le_succ_iff.2 hab)) _)
        (fun j => by have := hle j.succ; omega),
      pathKernel_cons I x hI, pow_add]
    ring

end IDL9

namespace IDL9

open IntermediateDisorder.PointToLine Finset

lemma sum_paths {Ω : Type*} (ω : ℕ × ℤ → Ω → ℝ) {n k : ℕ} (i : Fin k → Fin n)
    (hi : StrictMono i) (a : Ω) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, ∏ j, ω (timesOf i j, walkPos s (timesOf i j)) a =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin k => Icc (-(n : ℤ)) n),
        pathKernel (timesOf i) x * envProduct ω (timesOf i) x a := by
  classical
  have hmaps : ∀ s ∈ (univ : Finset (Fin n → Bool)), (fun j => walkPos s (timesOf i j)) ∈
      Fintype.piFinset (fun _ : Fin k => Icc (-(n : ℤ)) n) := by
    intro s _
    rw [Fintype.mem_piFinset]
    intro j
    have h := abs_walkPos_le' s (timesOf i j)
    rw [Finset.mem_Icc]
    constructor
    · linarith [neg_abs_le (walkPos s (timesOf i j))]
    · linarith [le_abs_self (walkPos s (timesOf i j))]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hc : ∑ s ∈ univ.filter (fun s : Fin n → Bool => (fun j => walkPos s (timesOf i j)) = x),
      ∏ j, ω (timesOf i j, walkPos s (timesOf i j)) a =
      (((univ.filter fun s : Fin n → Bool => ∀ j, walkPos s (timesOf i j) = x j).card : ℕ) : ℝ) *
        envProduct ω (timesOf i) x a := by
    rw [Finset.sum_congr (s₂ := univ.filter fun s : Fin n → Bool =>
      ∀ j, walkPos s (timesOf i j) = x j) ?_ (fun s hs => ?_), Finset.sum_const, nsmul_eq_mul]
    · ext s
      simp [funext_iff]
    · simp only [Finset.mem_filter] at hs
      unfold envProduct
      exact Finset.prod_congr rfl fun j _ => by rw [hs.2 j]
  rw [hc, card_paths k n (timesOf i) x (fun a b h => Nat.succ_le_succ (hi.monotone h))
    (fun j => (i j).isLt)]
  rw [mul_assoc ((2 : ℝ) ^ n), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- Lemma 5.2 expansion of the modified partition function into U-statistics of paths. -/
lemma mpf_expand {Ω : Type*} (ω : ℕ × ℤ → Ω → ℝ) (n : ℕ) (b : ℝ) (a : Ω) :
    modifiedPartitionFunction ω n b a = ∑ k ∈ range (n + 1), b ^ k *
      ∑ i ∈ univ.filter (fun i : Fin k → Fin n => StrictMono i),
        ∑ x ∈ Fintype.piFinset (fun _ : Fin k => Icc (-(n : ℤ)) n),
          pathKernel (timesOf i) x * envProduct ω (timesOf i) x a := by
  classical
  unfold modifiedPartitionFunction
  simp_rw [Finset.prod_one_add, Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  symm
  refine Finset.sum_bij' (fun i _ => univ.image i)
    (fun t ht => ⇑(t.orderEmbOfFin (mem_powersetCard.1 ht).2)) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi
    rw [mem_powersetCard]
    exact ⟨subset_univ _, by rw [card_image_of_injective _ hi.2.injective, card_univ,
      Fintype.card_fin]⟩
  · intro t ht
    rw [Finset.mem_filter]
    exact ⟨mem_univ _, (t.orderEmbOfFin _).strictMono⟩
  · intro i hi
    rw [Finset.mem_filter] at hi
    exact (orderEmbOfFin_unique _ (fun x => mem_image_of_mem i (mem_univ x)) hi.2).symm
  · intro t ht
    exact image_orderEmbOfFin_univ t _
  · intro i hi
    rw [Finset.mem_filter] at hi
    rw [← sum_paths ω i hi.2 a]
    simp_rw [Finset.prod_image (fun x _ y _ h => hi.2.injective h), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.mul_sum, mul_left_comm]
    rfl

end IDL9

namespace IDL9

open IntermediateDisorder.PointToLine MeasureTheory Finset

lemma walkPos_parity {n : ℕ} (s : Fin n → Bool) {i : ℕ} (hi : i ≤ n) :
    Even ((i : ℤ) - walkPos s i) := by
  have hc : (i : ℤ) = ∑ j : Fin n, if (j : ℕ) < i then (1 : ℤ) else 0 := by
    rw [Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right hi]
  rw [hc, walkPos, ← Finset.sum_sub_distrib]
  refine Finset.sum_induction _ Even (fun a b ha hb => ha.add hb) ⟨0, by norm_num⟩ fun j _ => ?_
  split_ifs
  · unfold stepZ
    split_ifs
    exacts [⟨0, by norm_num⟩, ⟨1, by norm_num⟩]
  · exact ⟨0, by norm_num⟩

open scoped Classical in
lemma pathKernel_eq_zero_of_not_parity {k n : ℕ} {I : Fin k → ℕ} (hI : Monotone I)
    (hle : ∀ j, I j ≤ n) {x : Fin k → ℤ} (h : ¬ ParityMatch I x) : pathKernel I x = 0 := by
  have hc := card_paths k n I x hI hle
  have h0 : (univ.filter fun s : Fin n → Bool => ∀ j, walkPos s (I j) = x j) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro s _ hs
    exact h fun j => by rw [← hs j]; exact walkPos_parity s (hle j)
  rw [h0, Finset.card_empty, Nat.cast_zero] at hc
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  exact (mul_eq_zero.1 hc.symm).resolve_left h2

lemma pathKernel_eq_zero_of_not_mem {k n : ℕ} {I : Fin k → ℕ} (hI : Monotone I)
    (hle : ∀ j, I j ≤ n) {x : Fin k → ℤ}
    (hx : x ∉ Fintype.piFinset (fun _ : Fin k => Icc (-(n : ℤ)) n)) : pathKernel I x = 0 := by
  by_contra hne
  apply hx
  rw [Fintype.mem_piFinset]
  intro j
  have h1 := IDL5.abs_le_of_pathKernel_ne_zero hI hne j
  have h2 : ((I j : ℕ) : ℤ) ≤ n := by exact_mod_cast hle j
  have h3 := abs_le.1 (h1.trans h2)
  rw [Finset.mem_Icc]
  exact ⟨h3.1, h3.2⟩

open scoped Classical in
lemma Kfun_on_cell {n k : ℕ} (hn : 1 ≤ n) {I : Fin k → ℕ} (hI : I ∈ IDL5.Dn n k)
    {x : Fin k → ℤ} (hx : ParityMatch I x) {z : Fin k → ℝ × ℝ} (hz : z ∈ cell n I x) :
    IDL5.Kfun n k z = ((2 : ℝ) ^ k)⁻¹ * pathKernel I x := by
  have hD := (Finset.mem_filter.1 hI).2
  unfold IDL5.Kfun
  rw [Finset.sum_eq_single I]
  · by_cases hxX : x ∈ IDL5.Xn n k I
    · rw [Finset.sum_eq_single x]
      · rw [Set.indicator_of_mem hz, mul_one]
      · intro x' hx' hne
        have hp' : ParityMatch I x' := (Finset.mem_filter.1 hx').2
        rw [Set.indicator_of_notMem, mul_zero]
        exact fun hz' => Set.disjoint_left.1
          (IDL2a.cell_disjoint hn hx hp' (fun h => hne h.2.symm)) hz hz'
      · intro h
        exact absurd hxX h
    · have hnot : x ∉ Fintype.piFinset (fun _ : Fin k => Icc (-(n : ℤ)) n) :=
        fun h => hxX (Finset.mem_filter.2 ⟨h, hx⟩)
      rw [pathKernel_eq_zero_of_not_mem hD.2.monotone (fun j => (hD.1 j).2) hnot, mul_zero]
      refine Finset.sum_eq_zero fun x' hx' => ?_
      have hp' : ParityMatch I x' := (Finset.mem_filter.1 hx').2
      have hne : x' ≠ x := fun h => hxX (h ▸ hx')
      rw [Set.indicator_of_notMem, mul_zero]
      exact fun hz' => Set.disjoint_left.1
        (IDL2a.cell_disjoint hn hx hp' (fun h => hne h.2.symm)) hz hz'
  · intro I' _ hne
    refine Finset.sum_eq_zero fun x' hx' => ?_
    have hp' : ParityMatch I' x' := (Finset.mem_filter.1 hx').2
    rw [Set.indicator_of_notMem, mul_zero]
    exact fun hz' => Set.disjoint_left.1
      (IDL2a.cell_disjoint hn hx hp' (fun h => hne h.1.symm)) hz hz'
  · intro h
    exact absurd hI h

open scoped Classical in
lemma cellAverage_dKLp {n k : ℕ} (hn : 1 ≤ n) {I : Fin k → ℕ} (hI : I ∈ IDL5.Dn n k)
    {x : Fin k → ℤ} (hx : ParityMatch I x) :
    cellAverage (discreteKernelLp n k) n I x = ((2 : ℝ) ^ k)⁻¹ * pathKernel I x := by
  have hbd : ∀ j, 1 ≤ I j ∧ I j ≤ n := (Finset.mem_filter.1 hI).2.1
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (kernelMeasure k (cell n I x)).toReal ≠ 0 := by
    rw [IDL1b.kernelMeasure_cell n hn I hbd x]
    exact pow_ne_zero _ (mul_ne_zero (one_div_ne_zero hpos.ne')
      (div_ne_zero two_ne_zero (Real.sqrt_pos.2 hpos).ne'))
  unfold cellAverage
  rw [setIntegral_congr_ae (IDL1b.measurableSet_cell n I x)
      (g := fun _ => ((2 : ℝ) ^ k)⁻¹ * pathKernel I x) ?_]
  · rw [setIntegral_const, Measure.real, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · filter_upwards [IDL5.coeFn_discreteKernelLp n k hn] with z hz hzc
    rw [hz, Kfun_on_cell hn hI hx hzc]

open scoped Classical in
lemma timesOf_mem_Dn {n k : ℕ} {i : Fin k → Fin n} (hi : StrictMono i) :
    timesOf i ∈ IDL5.Dn n k := by
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun j => ?_, fun j => ?_,
    IDL2a.timesOf_strictMono hi⟩
  · rw [Finset.mem_Icc]
    exact ⟨Nat.succ_pos _, (i j).isLt⟩
  · exact ⟨Nat.succ_pos _, (i j).isLt⟩

open scoped Classical in
lemma uStat_dKLp {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} (ω : ℕ × ℤ → Ω → ℝ)
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    uStatistic ω Q n k (discreteKernelLp n k) =
      ∑ i ∈ univ.filter (fun i : Fin k → Fin n => StrictMono i),
        ∑ x ∈ Fintype.piFinset (fun _ : Fin k => Icc (-(n : ℤ)) n),
          (Real.sqrt 2 ^ k * (((2 : ℝ) ^ k)⁻¹ * pathKernel (timesOf i) x)) •
            envProductLp ω Q (timesOf i) x := by
  have hcoef : ∀ i : Fin k → Fin n, StrictMono i → ∀ x : Fin k → ℤ,
      Real.sqrt 2 ^ k * cellAverage (discreteKernelLp n k) n (timesOf i) x *
        (if ParityMatch (timesOf i) x then (1 : ℝ) else 0) =
      Real.sqrt 2 ^ k * (((2 : ℝ) ^ k)⁻¹ * pathKernel (timesOf i) x) := by
    intro i hi x
    by_cases hp : ParityMatch (timesOf i) x
    · rw [if_pos hp, mul_one, cellAverage_dKLp hn (timesOf_mem_Dn hi) hp]
    · rw [if_neg hp, mul_zero, pathKernel_eq_zero_of_not_parity
        (IDL2a.timesOf_strictMono hi).monotone (fun j => (i j).isLt) hp, mul_zero, mul_zero]
  unfold uStatistic
  symm
  refine (Finset.sum_congr rfl fun i hi => ?_).trans (Finset.sum_subset ?_ ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [tsum_eq_sum (s := Fintype.piFinset (fun _ : Fin k => Icc (-(n : ℤ)) n))]
    · refine Finset.sum_congr rfl fun x _ => ?_
      unfold uStatisticTerm
      rw [hcoef i hi x]
    · intro x hx
      unfold uStatisticTerm
      rw [hcoef i hi x, pathKernel_eq_zero_of_not_mem (IDL2a.timesOf_strictMono hi).monotone
        (fun j => (i j).isLt) hx, mul_zero, mul_zero, zero_smul]
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.injective
  · intro i hi hns
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hns
    refine (tsum_congr fun x => ?_).trans tsum_zero
    unfold uStatisticTerm
    rw [IDL2a.cellAverage_eq_zero_of_not_strictMono _
      (IDL5.simplexSupported_discreteKernelLp n k) hi hns x, mul_zero, zero_mul, zero_smul]

lemma const_eq (β : ℝ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (n : ℝ) ^ (-(3 * (k : ℝ) / 4)) * ((Real.sqrt 2 * β) ^ k * (n : ℝ) ^ ((k : ℝ) / 2)) *
      (Real.sqrt 2 ^ k * ((2 : ℝ) ^ k)⁻¹) = (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : Real.sqrt 2 ^ k * Real.sqrt 2 ^ k = (2 : ℝ) ^ k := by
    rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
  have hr : (n : ℝ) ^ (-(3 * (k : ℝ) / 4)) * (n : ℝ) ^ ((k : ℝ) / 2) =
      ((n : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
    rw [← Real.rpow_add hpos, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  calc _ = ((n : ℝ) ^ (-(3 * (k : ℝ) / 4)) * (n : ℝ) ^ ((k : ℝ) / 2)) * β ^ k *
        ((Real.sqrt 2 ^ k * Real.sqrt 2 ^ k) * ((2 : ℝ) ^ k)⁻¹) := by rw [mul_pow]; ring
    _ = ((n : ℝ) ^ (-(1 / 4 : ℝ))) ^ k * β ^ k * ((2 : ℝ) ^ k * ((2 : ℝ) ^ k)⁻¹) := by
        rw [hr, h2]
    _ = _ := by rw [mul_inv_cancel₀ (by positivity), mul_one, mul_pow, mul_comm]

/-- Lemma 5.2 (`𝔷_n(βn^{-1/4})` is the discrete chaos of the rescaled path kernels). -/
theorem P5 {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {ω : ℕ × ℤ → Ω → ℝ} (hω : IsStdEnvironment ω Q) (β : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (discreteChaos ω Q n (IDL8.gN β n) : Ω → ℝ) =ᵐ[Q]
      modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by
  have hL : discreteChaos ω Q n (IDL8.gN β n) =
      ∑ k ∈ range (n + 1), ∑ i ∈ univ.filter (fun i : Fin k → Fin n => StrictMono i),
        ∑ x ∈ Fintype.piFinset (fun _ : Fin k => Icc (-(n : ℤ)) n),
          ((β * (n : ℝ) ^ (-(1 / 4 : ℝ))) ^ k * pathKernel (timesOf i) x) •
            envProductLp ω Q (timesOf i) x := by
    unfold discreteChaos
    refine Finset.sum_congr rfl fun k _ => ?_
    have hs : uStatistic ω Q n k (IDL8.gN β n k) = ((Real.sqrt 2 * β) ^ k *
        (n : ℝ) ^ ((k : ℝ) / 2)) • uStatistic ω Q n k (discreteKernelLp n k) := by
      rw [IDL8.gN, smul_smul]
      exact (IDL2a.uStatL hω n k).map_smul _ _
    rw [hs, uStat_dKLp ω hn k, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_smul, ← const_eq β hn k]
    congr 1
    ring
  rw [hL]
  have hinj : ∀ k, ∀ i ∈ univ.filter (fun i : Fin k → Fin n => StrictMono i),
      Function.Injective (timesOf i) := fun k i hi =>
    IDL2a.timesOf_injective (Finset.mem_filter.1 hi).2.injective
  filter_upwards [Lp.coeFn_finsetSum (E := ℝ) (p := 2) (μ := Q) _ _,
    (Filter.eventually_all_finset _).2 fun k _ =>
      Lp.coeFn_finsetSum (E := ℝ) (p := 2) (μ := Q) _ _,
    (Filter.eventually_all_finset _).2 fun k _ => (Filter.eventually_all_finset _).2 fun i _ =>
      Lp.coeFn_finsetSum (E := ℝ) (p := 2) (μ := Q) _ _,
    (Filter.eventually_all_finset _).2 fun k _ => (Filter.eventually_all_finset _).2 fun i hi =>
      (Filter.eventually_all_finset _).2 fun x _ =>
        IDL1b.smul_envProductLp_ae hω ((β * (n : ℝ) ^ (-(1 / 4 : ℝ))) ^ k *
          pathKernel (timesOf i) x) (timesOf i) (hinj k i hi) x] with a h1 h2 h3 h4
  rw [mpf_expand, h1, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [h2 k hk, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h3 k hk i hi, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [h4 k hk i hi x hx]
  ring

end IDL9

open IntermediateDisorder.PointToLine MeasureTheory ProbabilityTheory Filter in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {ω : ℕ × ℤ → Ω → ℝ}
    (hω : IsStdEnvironment ω Q)
    {Ω' : Type*} [MeasurableSpace Ω'] {Q' : Measure Ω'} [IsProbabilityMeasure Q']
    (W : Set (ℝ × ℝ) → Ω' → ℝ) (I : (k : ℕ) → Lp ℝ 2 (kernelMeasure k) →L[ℝ] Lp ℝ 2 Q')
    (hW : IsWhiteNoise W Q') (hI : IsMultipleIntegral W Q' I) (β : ℝ) (hβ : 0 < β) :
    TendstoInDistribution
      (fun n => modifiedPartitionFunction ω n (β * (n : ℝ) ^ (-(1 / 4 : ℝ))))
      atTop (wienerChaos I (Real.sqrt 2 * β)) (fun _ => Q) Q' := by
  exact IDL8.glue hω W I hW hI β hβ fun _ hn => IDL9.P5 hω β hn
