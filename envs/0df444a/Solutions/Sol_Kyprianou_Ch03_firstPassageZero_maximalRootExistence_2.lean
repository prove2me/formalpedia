-- Prove2me | solution 2 for Kyprianou.Ch03.firstPassageZero_maximalRootExistence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:19:29.11721+00:00
-- url     : https://prove2.me/submissions/5b3a321d-ddfc-42e1-939e-c80b0cc72874

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false


namespace SCVAux

noncomputable def g (θ y : ℝ) : ℝ :=
  Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y

lemma g_bound (θ y : ℝ) (hθ : 0 ≤ θ) (hy : y < 0) :
    |g θ y| ≤ (1 + 2 * θ ^ 2) * min 1 (y ^ 2) := by
  unfold g
  by_cases hy1 : -1 < y
  · have hind : (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 1 :=
      Set.indicator_of_mem (show y ∈ Ioo (-1 : ℝ) 1 from ⟨hy1, by linarith⟩) _
    rw [hind, mul_one]
    have hmin : min 1 (y ^ 2) = y ^ 2 := min_eq_right (by nlinarith)
    rw [hmin]
    by_cases hs : |θ * y| ≤ 1
    · have := Real.abs_exp_sub_one_sub_id_le hs
      have h2 : (θ * y) ^ 2 = θ ^ 2 * y ^ 2 := by ring
      nlinarith [sq_nonneg y, sq_nonneg θ]
    · push Not at hs
      have hneg : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy.le
      have habs : |θ * y| = -(θ * y) := abs_of_nonpos hneg
      rw [habs] at hs
      have he1 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr hneg
      have he0 : 0 < Real.exp (θ * y) := Real.exp_pos _
      have hsq : 1 < θ ^ 2 * y ^ 2 := by nlinarith
      have hlin : -(θ * y) < θ ^ 2 * y ^ 2 := by nlinarith
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg y]
  · push Not at hy1
    have hind : (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 0 :=
      Set.indicator_of_notMem (fun h => by linarith [h.1]) _
    rw [hind, mul_zero, sub_zero]
    have hmin : min 1 (y ^ 2) = 1 := min_eq_left (by nlinarith)
    rw [hmin]
    have hneg : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy.le
    have he1 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr hneg
    have he0 : 0 < Real.exp (θ * y) := Real.exp_pos _
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg θ]


theorem strictIneq
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hcase : 0 < L.σ ∨ L.ν ≠ 0) (x z a b : ℝ) (hx0 : 0 ≤ x) (hz0 : 0 ≤ z) (hxz : x ≠ z)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    L.ψ (a * x + b * z) < a * L.ψ x + b * L.ψ z := by
  set μ : Measure ℝ := L.ν.restrict (Iio 0) with hμ
  -- integrability of min 1 y^2
  have hmeas_min : Measurable (fun y : ℝ => min 1 (y ^ 2)) := by fun_prop
  have hmin_int : Integrable (fun y : ℝ => min 1 (y ^ 2)) L.ν := by
    refine ⟨hmeas_min.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun y => le_min zero_le_one (sq_nonneg y)))]
    exact L.ν_integrable
  have hg_meas : ∀ θ, Measurable (SCVAux.g θ) := by
    intro θ
    unfold SCVAux.g
    have : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
      measurable_const.indicator measurableSet_Ioo
    fun_prop
  have hg_int : ∀ θ, 0 ≤ θ → Integrable (SCVAux.g θ) μ := by
    intro θ hθ
    refine Integrable.mono' ((hmin_int.restrict).const_mul (1 + 2 * θ ^ 2))
      (hg_meas θ).aestronglyMeasurable ?_
    rw [hμ, ae_restrict_iff' measurableSet_Iio]
    exact Eventually.of_forall (fun y hy => by
      rw [Real.norm_eq_abs]; exact SCVAux.g_bound θ y hθ hy)
  have hψ : ∀ θ, L.ψ θ = L.c * θ + L.σ ^ 2 * θ ^ 2 / 2 + ∫ y, SCVAux.g θ y ∂μ := by
    intro θ; rfl
  rw [hψ, hψ, hψ]
  set m := a * x + b * z with hm
  have hm0 : 0 ≤ m := by positivity
  -- pointwise difference
  set Df : ℝ → ℝ := fun y => a * SCVAux.g x y + b * SCVAux.g z y - SCVAux.g m y with hDf
  have hD : ∀ y, Df y = a * Real.exp (x * y) + b * Real.exp (z * y) - Real.exp (m * y) := by
    intro y
    simp only [hDf, SCVAux.g, hm]
    have hb' : b = 1 - a := by linarith
    subst hb'
    ring
  have hDpos : ∀ y, y ≠ 0 → 0 < Df y := by
    intro y hy
    rw [hD]
    have hne : x * y ≠ z * y := by
      intro h; exact hxz (mul_right_cancel₀ hy h)
    have := strictConvexOn_exp.2 (Set.mem_univ (x * y)) (Set.mem_univ (z * y)) hne ha hb hab
    simp only [smul_eq_mul] at this
    have hmy : m * y = a * (x * y) + b * (z * y) := by rw [hm]; ring
    rw [hmy]; linarith
  have hDnn : ∀ y, 0 ≤ Df y := by
    intro y
    by_cases hy : y = 0
    · rw [hD, hy]; simp; linarith
    · exact (hDpos y hy).le
  have hDint : Integrable Df μ :=
    (((hg_int x hx0).const_mul a).add ((hg_int z hz0).const_mul b)).sub (hg_int m hm0)
  have hIeq : ∫ y, Df y ∂μ = a * ∫ y, SCVAux.g x y ∂μ + b * ∫ y, SCVAux.g z y ∂μ -
      ∫ y, SCVAux.g m y ∂μ := by
    have i1 : Integrable (fun y => a * SCVAux.g x y) μ := (hg_int x hx0).const_mul a
    have i2 : Integrable (fun y => b * SCVAux.g z y) μ := (hg_int z hz0).const_mul b
    have i12 : Integrable (fun y => a * SCVAux.g x y + b * SCVAux.g z y) μ := i1.add i2
    simp only [hDf]
    rw [integral_sub i12 (hg_int m hm0), integral_add i1 i2, integral_const_mul,
      integral_const_mul]
  have hInn : 0 ≤ ∫ y, Df y ∂μ := integral_nonneg hDnn
  have hquad : a * x ^ 2 + b * z ^ 2 - m ^ 2 = a * b * (x - z) ^ 2 := by
    have hb' : b = 1 - a := by linarith
    rw [hm, hb']; ring
  have hxz2 : 0 < (x - z) ^ 2 := by
    have : x - z ≠ 0 := sub_ne_zero.mpr hxz
    positivity
  have hab0 : 0 < a * b * (x - z) ^ 2 := by positivity
  rcases hcase with hσ | hν
  · have hσ2 : 0 < L.σ ^ 2 := by positivity
    have : 0 < L.σ ^ 2 * (a * b * (x - z) ^ 2) := mul_pos hσ2 hab0
    have hlin : L.c * m = a * (L.c * x) + b * (L.c * z) := by rw [hm]; ring
    nlinarith [hquad, hIeq, hInn]
  · have hνpos : L.ν (Iio 0) ≠ 0 := by
      intro h0
      apply hν
      have hall : L.ν univ = 0 := by
        rw [← Set.Iio_union_Ici (a := (0:ℝ))]
        exact measure_union_null h0 L.ν_Ici
      exact Measure.measure_univ_eq_zero.mp hall
    have hIpos : 0 < ∫ y, Df y ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hDnn hDint]
      have hsub : Iio (0:ℝ) ⊆ Function.support Df := by
        intro y hy
        exact (hDpos y (ne_of_lt hy)).ne'
      have : μ (Iio 0) ≤ μ (Function.support Df) := measure_mono hsub
      rw [hμ, Measure.restrict_apply measurableSet_Iio, Set.inter_self] at this
      exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hνpos) this
    have hσ2 : 0 ≤ L.σ ^ 2 * (a * b * (x - z) ^ 2) := by positivity
    have hlin : L.c * m = a * (L.c * x) + b * (L.c * z) := by rw [hm]; ring
    nlinarith [hquad, hIeq, hIpos]

end SCVAux

namespace SCVAux
theorem psi_zero {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) : L.ψ 0 = 0 := by
  simp [AvramDividend.Classical.SpectrallyNegativeLevy.ψ, AvramDividend.Classical.laplaceExponent]

theorem psi_degen {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (h : ¬ (0 < L.σ ∨ L.ν ≠ 0)) (θ : ℝ) : L.ψ θ = L.c * θ := by
  push Not at h
  have hσ : L.σ = 0 := le_antisymm h.1 L.σ_nonneg
  simp [AvramDividend.Classical.SpectrallyNegativeLevy.ψ, AvramDividend.Classical.laplaceExponent,
    hσ, h.2]

theorem no_pos_root_degen {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (h : ¬ (0 < L.σ ∨ L.ν ≠ 0)) (phi : ℝ) (hpos : 0 < phi) (hr : L.ψ phi = 0)
    (hmax : ∀ theta : ℝ, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) : False := by
  rw [psi_degen P F L h] at hr
  have hc : L.c = 0 := by
    rcases mul_eq_zero.mp hr with h1 | h1
    · exact h1
    · linarith
  have := hmax (phi + 1) (by linarith) (by rw [psi_degen P F L h, hc, zero_mul])
  linarith
end SCVAux

namespace SCVAux

theorem meas_X {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) (t : NNReal) :
    Measurable (L.X t) :=
  (L.adapted t).mono (F.le t) le_rfl

theorem antitone_of_nonpos {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (h : ∀ t : NNReal, P {ω | 0 < L.X t ω} = 0) :
    ∀ᵐ ω ∂P, Antitone (fun t : NNReal => L.X t ω) := by
  have hinc : ∀ s t : NNReal, s ≤ t → ∀ᵐ ω ∂P, L.X t ω ≤ L.X s ω := by
    intro s t hst
    have hid := L.stationaryIncrements s t hst
    have h1 := hid.measure_mem_eq (measurableSet_Ioi (a := (0:ℝ)))
    have h2 : P ((fun ω => L.X t ω - L.X s ω) ⁻¹' Ioi 0) = 0 := by
      rw [h1]; exact h (t - s)
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h2
    simp only [Set.mem_ofPred_eq, not_le] at hω
    simp only [Set.mem_preimage, Set.mem_Ioi]
    linarith
  have hall : ∀ᵐ ω ∂P, ∀ q r : ℚ, Real.toNNReal q ≤ Real.toNNReal r →
      L.X (Real.toNNReal r) ω ≤ L.X (Real.toNNReal q) ω := by
    rw [ae_all_iff]; intro q
    rw [ae_all_iff]; intro r
    by_cases hqr : Real.toNNReal q ≤ Real.toNNReal r
    · filter_upwards [hinc _ _ hqr] with ω hω _ using hω
    · exact Eventually.of_forall (fun ω h' => absurd h' hqr)
  filter_upwards [hall] with ω hω
  intro s t hst
  simp only
  -- right continuity
  have hrc : ∀ u : NNReal, ContinuousWithinAt (fun v => L.X v ω) (Ici u) u := L.rightCont ω
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  obtain ⟨δt, hδt, hδt'⟩ := Metric.continuousWithinAt_iff.mp (hrc t) (ε / 2) (by linarith)
  obtain ⟨δs, hδs, hδs'⟩ := Metric.continuousWithinAt_iff.mp (hrc s) (ε / 2) (by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (t : ℝ) < (t : ℝ) + δt by linarith)
  have hsr : (s : ℝ) < min ((s : ℝ) + δs) (r : ℝ) := by
    apply lt_min (by linarith)
    have : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hsr
  have ht0 : (0 : ℝ) ≤ t := t.2
  have hs0 : (0 : ℝ) ≤ s := s.2
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by linarith
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by linarith
  have hrr : ((Real.toNNReal r : NNReal) : ℝ) = r := Real.coe_toNNReal _ hr0
  have hqq : ((Real.toNNReal q : NNReal) : ℝ) = q := Real.coe_toNNReal _ hq0
  have hqr : Real.toNNReal q ≤ Real.toNNReal r := by
    rw [← NNReal.coe_le_coe, hrr, hqq]
    exact le_trans (le_of_lt (lt_of_lt_of_le hq2 (min_le_right _ _))) le_rfl
  have hX := hω q r hqr
  have hdt := hδt' (x := Real.toNNReal r) (by
      show t ≤ Real.toNNReal r
      rw [← NNReal.coe_le_coe, hrr]; linarith)
    (by rw [NNReal.dist_eq, hrr, abs_lt]; constructor <;> linarith)
  have hds := hδs' (x := Real.toNNReal q) (by
      show s ≤ Real.toNNReal q
      rw [← NNReal.coe_le_coe, hqq]; linarith)
    (by
      rw [NNReal.dist_eq, hqq, abs_lt]
      have := lt_of_lt_of_le hq2 (min_le_left _ _)
      constructor <;> linarith)
  rw [Real.dist_eq, abs_lt] at hdt hds
  linarith [hdt.1, hds.2]

theorem psi_tendsto {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNot : ¬ (∀ᵐ omega : Omega ∂P, Antitone (fun t : NNReal => L.X t omega))) :
    Tendsto L.ψ atTop atTop := by
  have hex : ∃ t : NNReal, P {ω | 0 < L.X t ω} ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hNot (antitone_of_nonpos P F L hc)
  obtain ⟨t, ht⟩ := hex
  have hU : {ω | 0 < L.X t ω} = ⋃ n : ℕ, {ω | 1 / ((n : ℝ) + 1) < L.X t ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt h
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      exact lt_trans (by positivity) hn
  have hex2 : ∃ n : ℕ, P {ω | 1 / ((n : ℝ) + 1) < L.X t ω} ≠ 0 := by
    by_contra hc
    push Not at hc
    apply ht
    rw [hU]
    exact measure_iUnion_null hc
  obtain ⟨n, hn⟩ := hex2
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hεpos : 0 < ε := by positivity
  set A := {ω | ε < L.X t ω} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (meas_X P F L t)
  set p : ℝ := P.real A with hp
  have hppos : 0 < p := by
    rw [hp, measureReal_def]
    exact ENNReal.toReal_pos hn (measure_ne_top P A)
  have htpos : (0 : ℝ) < t := by
    rcases eq_or_lt_of_le t.2 with h0 | h0
    · exfalso
      have ht0 : t = 0 := NNReal.coe_eq_zero.mp h0.symm
      apply ht
      rw [ht0]
      simp [L.X_zero]
    · exact h0
  -- lower bound: t ψ θ ≥ θ ε + log p
  have hbound : ∀ θ : ℝ, 0 ≤ θ → (θ * ε + Real.log p) / t ≤ L.ψ θ := by
    intro θ hθ
    obtain ⟨hint, heq⟩ := L.laplace t θ hθ
    have hlow : ∫ ω, A.indicator (fun _ => Real.exp (θ * ε)) ω ∂P ≤
        ∫ ω, Real.exp (θ * L.X t ω) ∂P := by
      apply integral_mono ((integrable_const _).indicator hAm) hint
      intro ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (le_of_lt hω) hθ
      · rw [Set.indicator_of_notMem hω]; exact (Real.exp_pos _).le
    rw [integral_indicator_const _ hAm, heq, smul_eq_mul] at hlow
    have hlog := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hlog
    rw [div_le_iff₀ htpos]
    have : L.ψ θ * t = (t : ℝ) * AvramDividend.Classical.laplaceExponent L.c L.σ L.ν θ := by
      rw [mul_comm]; rfl
    rw [this]; rw [← hp] at hlog
    linarith
  have hlin : Tendsto (fun θ : ℝ => (θ * ε + Real.log p) / t) atTop atTop := by
    have h1 : Tendsto (fun θ : ℝ => θ * (ε / t) + Real.log p / t) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const (by positivity))
    refine h1.congr (fun θ => ?_)
    ring
  exact tendsto_atTop_mono' atTop
    (Filter.eventually_ge_atTop 0 |>.mono (fun θ hθ => hbound θ hθ)) hlin

end SCVAux

namespace SCVAux

theorem convexOn_psi {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    ConvexOn ℝ (Ioi 0) L.ψ := by
  by_cases hcase : 0 < L.σ ∨ L.ν ≠ 0
  · have hs : StrictConvexOn ℝ (Ioi 0) L.ψ := by
      refine ⟨convex_Ioi 0, fun x hx z hz hxz a b ha hb hab => ?_⟩
      simp only [smul_eq_mul]
      exact strictIneq P F L hcase x z a b (le_of_lt hx) (le_of_lt hz) hxz ha hb hab
    exact hs.convexOn
  · refine ⟨convex_Ioi 0, fun x _ z _ a b _ _ _ => ?_⟩
    simp only [smul_eq_mul]
    rw [psi_degen P F L hcase, psi_degen P F L hcase, psi_degen P F L hcase]
    apply le_of_eq; ring

theorem exists_root_after {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hT : Tendsto L.ψ atTop atTop) (θ1 : ℝ) (h1 : 0 < θ1) (hneg : L.ψ θ1 < 0) :
    ∃ r, θ1 < r ∧ L.ψ r = 0 := by
  obtain ⟨θ2, hθ2a, hθ2b⟩ :=
    ((hT.eventually (eventually_ge_atTop (1:ℝ))).and (eventually_ge_atTop (θ1 + 1))).exists
  have hcont : ContinuousOn L.ψ (Icc θ1 θ2) :=
    ((convexOn_psi P F L).continuousOn isOpen_Ioi).mono
      (fun y hy => lt_of_lt_of_le h1 hy.1)
  have hivt := intermediate_value_Icc (by linarith) hcont
  obtain ⟨r, hr, hr0⟩ := hivt (show (0:ℝ) ∈ Icc (L.ψ θ1) (L.ψ θ2) from ⟨hneg.le, by linarith⟩)
  refine ⟨r, ?_, hr0⟩
  rcases eq_or_lt_of_le hr.1 with h | h
  · rw [← h] at hr0; linarith
  · exact h

theorem nonneg_of_zero_max {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hT : Tendsto L.ψ atTop atTop)
    (hmax : ∀ theta : ℝ, 0 ≤ theta → L.ψ theta = 0 → theta ≤ 0) :
    ∀ θ : ℝ, 0 ≤ θ → 0 ≤ L.ψ θ := by
  intro θ hθ
  by_contra hneg
  push Not at hneg
  have hθpos : 0 < θ := by
    rcases eq_or_lt_of_le hθ with h | h
    · rw [← h, psi_zero P F L] at hneg; exact absurd hneg (lt_irrefl 0)
    · exact h
  obtain ⟨r, hr, hr0⟩ := exists_root_after P F L hT θ hθpos hneg
  have := hmax r (by linarith) hr0
  linarith

theorem max_root_exists {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hT : Tendsto L.ψ atTop atTop) :
    ∃ phi : ℝ, 0 ≤ phi ∧ L.ψ phi = 0 ∧
      (∀ theta : ℝ, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) := by
  by_cases hcase : 0 < L.σ ∨ L.ν ≠ 0
  · by_cases hpos : ∃ r, 0 < r ∧ L.ψ r = 0
    · obtain ⟨r, hr, hr0⟩ := hpos
      refine ⟨r, hr.le, hr0, fun θ hθ hθ0 => ?_⟩
      by_contra hlt
      push Not at hlt
      have hθpos : 0 < θ := lt_trans hr hlt
      set b := r / θ with hb
      have hb0 : 0 < b := div_pos hr hθpos
      have hb1 : b < 1 := (div_lt_one hθpos).mpr hlt
      have hs := strictIneq P F L hcase 0 θ (1 - b) b le_rfl hθpos.le (ne_of_lt hθpos)
        (by linarith) hb0 (by ring)
      have hpt : (1 - b) * 0 + b * θ = r := by
        rw [hb, mul_zero, zero_add, div_mul_cancel₀ r hθpos.ne']
      rw [hpt, hr0, psi_zero P F L, hθ0] at hs
      linarith
    · push Not at hpos
      refine ⟨0, le_rfl, psi_zero P F L, fun θ hθ hθ0 => ?_⟩
      by_contra hlt
      push Not at hlt
      exact hpos θ hlt hθ0
  · have hc : 0 < L.c := by
      by_contra hc
      push Not at hc
      obtain ⟨θ, hθa, hθb⟩ :=
        ((hT.eventually (eventually_ge_atTop (1:ℝ))).and (eventually_ge_atTop (0:ℝ))).exists
      rw [psi_degen P F L hcase] at hθa
      nlinarith
    refine ⟨0, le_rfl, psi_zero P F L, fun θ hθ hθ0 => ?_⟩
    rw [psi_degen P F L hcase] at hθ0
    rcases mul_eq_zero.mp hθ0 with h | h
    · linarith
    · linarith

end SCVAux

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        exists phi : Real,
      0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi) := by
  exact SCVAux.max_root_exists P F L (SCVAux.psi_tendsto P F L hNotDecreasing)
