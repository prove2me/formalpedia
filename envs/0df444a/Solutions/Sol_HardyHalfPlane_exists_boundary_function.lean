-- Prove2me | solution 1 for HardyHalfPlane.exists_boundary_function
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:26:30.96646+00:00
-- url     : https://prove2.me/submissions/756df604-f521-4191-9953-66d497e3e9cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy
import Theorems.Thm_HardyDisc_ae_exists_tendsto_nontangential
import Theorems.Thm_HardyHalfPlane_exists_bound_circle_eLpNorm_comp_cayley

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace Sol_HardyHalfPlane_exists_boundary_function

open Complex in
/-- The boundary point of the unit circle corresponding to the point `a + i y` of the line
`Re s = a` under the Cayley-type map `w ↦ a + (w + 1)/(w - 1)`. -/
lemma circleMap_bdry (y : ℝ) :
    circleMap 0 1 (Real.pi + 2 * Real.arctan y) =
      ((y : ℂ) * I + 1) / ((y : ℂ) * I - 1) := by
  have hs : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hsq : Real.sqrt (1 + y ^ 2) ^ 2 = 1 + y ^ 2 := Real.sq_sqrt hs.le
  have hsne : (Real.sqrt (1 + y ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hs).ne'
  have hden : (y : ℂ) * I - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have he : exp ((Real.arctan y : ℂ) * I) =
      (1 + (y : ℂ) * I) / (Real.sqrt (1 + y ^ 2) : ℂ) := by
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_arctan, Real.sin_arctan]
    push_cast
    field_simp
  rw [circleMap_zero]
  have : ((Real.pi + 2 * Real.arctan y : ℝ) : ℂ) * I =
      (Real.pi : ℂ) * I + ((Real.arctan y : ℂ) * I + (Real.arctan y : ℂ) * I) := by
    push_cast; ring
  rw [this, exp_add, exp_add, he, exp_pi_mul_I]
  have hsq' : ((Real.sqrt (1 + y ^ 2) : ℝ) : ℂ) ^ 2 = 1 + (y : ℂ) ^ 2 := by
    exact_mod_cast hsq
  rw [eq_div_iff hden]
  field_simp
  push_cast
  linear_combination (-(1 : ℂ) - (y : ℂ) * I) * hsq' + (-(y : ℂ) ^ 2 - (y : ℂ) ^ 3 * I) * I_sq

/-- The parametrisation `y ↦ π + 2 arctan y` of the circle pulls Lebesgue-null sets back to
Lebesgue-null sets. -/
lemma preimage_null {N : Set ℝ} (hN : volume N = 0) :
    volume ((fun y : ℝ => Real.pi + 2 * Real.arctan y) ⁻¹' N) = 0 := by
  have hsub : (fun y : ℝ => Real.pi + 2 * Real.arctan y) ⁻¹' N ⊆
      (fun t : ℝ => Real.tan ((t - Real.pi) / 2)) '' (N ∩ Set.Ioo 0 (2 * Real.pi)) := by
    intro y hy
    refine ⟨Real.pi + 2 * Real.arctan y, ⟨hy, ?_, ?_⟩, ?_⟩
    · have := Real.neg_pi_div_two_lt_arctan y; linarith
    · have := Real.arctan_lt_pi_div_two y; linarith
    · show Real.tan ((Real.pi + 2 * Real.arctan y - Real.pi) / 2) = y
      rw [show (Real.pi + 2 * Real.arctan y - Real.pi) / 2 = Real.arctan y by ring,
        Real.tan_arctan]
  refine measure_mono_null hsub ?_
  apply MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  · intro t ht
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℝ (fun t : ℝ => (t - Real.pi) / 2) t := by fun_prop
    have h2 : DifferentiableAt ℝ Real.tan ((t - Real.pi) / 2) := by
      apply Real.differentiableAt_tan_of_mem_Ioo
      constructor
      · have := ht.2.1; linarith
      · have := ht.2.2; linarith
    exact (DifferentiableAt.comp t h2 h1 :
      DifferentiableAt ℝ (Real.tan ∘ fun t : ℝ => (t - Real.pi) / 2) t)
  · exact measure_mono_null Set.inter_subset_left hN

open Complex in
/-- A horizontal segment ending at the boundary line is mapped by `z ↦ (z + 1)/(z - 1)` into a
Stolz angle of aperture `2` at the corresponding boundary point of the unit circle. -/
lemma stolz (y t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ‖(((-t : ℝ) : ℂ) + (y : ℂ) * I + 1) / (((-t : ℝ) : ℂ) + (y : ℂ) * I - 1)‖ < 1 ∧
      ‖((y : ℂ) * I + 1) / ((y : ℂ) * I - 1) -
          (((-t : ℝ) : ℂ) + (y : ℂ) * I + 1) / (((-t : ℝ) : ℂ) + (y : ℂ) * I - 1)‖ ≤
        2 * (1 - ‖(((-t : ℝ) : ℂ) + (y : ℂ) * I + 1) / (((-t : ℝ) : ℂ) + (y : ℂ) * I - 1)‖) := by
  set z : ℂ := ((-t : ℝ) : ℂ) + (y : ℂ) * I with hz
  set b : ℂ := (y : ℂ) * I - 1 with hb
  have hzm : z - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hz] at this; linarith
  have hbm : b ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hb] at this
  have hA2 : ‖z - 1‖ ^ 2 = (t + 1) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hz]; ring
  have hC2 : ‖z + 1‖ ^ 2 = (1 - t) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hz]; ring
  have hB2 : ‖b‖ ^ 2 = 1 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hb]; ring
  have hdiff : (y : ℂ) * I + 1 = b + 2 := by rw [hb]; ring
  have hid : ((y : ℂ) * I + 1) / b - (z + 1) / (z - 1) = -(2 * (t : ℂ)) / ((z - 1) * b) := by
    rw [div_sub_div _ _ hbm hzm, div_eq_div_iff (mul_ne_zero hbm hzm) (mul_ne_zero hzm hbm)]
    rw [hz, hb]; push_cast; ring_nf
  set A := ‖z - 1‖ with hA
  set B := ‖b‖ with hB
  set C := ‖z + 1‖ with hC
  have hA0 : 0 < A := norm_pos_iff.mpr hzm
  have hB0 : 0 < B := norm_pos_iff.mpr hbm
  have hC0 : 0 ≤ C := norm_nonneg _
  have hCA : C < A := by
    have : C ^ 2 < A ^ 2 := by rw [hA2, hC2]; nlinarith
    nlinarith
  have hAB : A ≤ 2 * B := by
    have : A ^ 2 ≤ (2 * B) ^ 2 := by rw [mul_pow, hA2, hB2]; nlinarith
    nlinarith
  have hw : ‖(z + 1) / (z - 1)‖ = C / A := by rw [norm_div]
  have hzw : ‖((y : ℂ) * I + 1) / b - (z + 1) / (z - 1)‖ = 2 * t / (A * B) := by
    rw [hid, norm_div, norm_neg, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hw, div_lt_one hA0]; exact hCA
  · rw [hzw, hw]
    have key : (A - C) * (A + C) = 4 * t := by
      have : A ^ 2 - C ^ 2 = 4 * t := by rw [hA2, hC2]; ring
      nlinarith
    rw [div_le_iff₀ (mul_pos hA0 hB0)]
    have h1 : 2 * (1 - C / A) * (A * B) = 2 * B * (A - C) := by field_simp
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left (show A + C ≤ 4 * B by linarith) (sub_nonneg.mpr hCA.le)]

open Complex in
/-- Along a horizontal ray `σ ↦ σ + i y`, `σ → a⁻`, the point `(z + 1)/(z - 1)` with
`z = (σ - a) + i y` tends to the boundary point `(i y + 1)/(i y - 1)` inside the Stolz angle of
aperture `2`. -/
lemma tendsto_stolz (a y : ℝ) :
    Tendsto (fun σ : ℝ => ((((σ - a : ℝ) : ℂ) + (y : ℂ) * I) + 1) /
        ((((σ - a : ℝ) : ℂ) + (y : ℂ) * I) - 1)) (𝓝[<] a)
      (𝓝[{w : ℂ | ‖w‖ < 1 ∧ ‖((y : ℂ) * I + 1) / ((y : ℂ) * I - 1) - w‖ ≤ 2 * (1 - ‖w‖)}]
        (((y : ℂ) * I + 1) / ((y : ℂ) * I - 1))) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun σ : ℝ => ((((σ - a : ℝ) : ℂ) + (y : ℂ) * I) + 1) /
        ((((σ - a : ℝ) : ℂ) + (y : ℂ) * I) - 1)) a := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      intro h; have := congrArg Complex.re h; simp at this
    have := hc.tendsto
    simpa using this
  · filter_upwards [Ioo_mem_nhdsLT (show a - 1 < a by linarith)] with σ hσ
    have h := stolz y (a - σ) (by linarith [hσ.2]) (by linarith [hσ.1])
    have he : ((σ - a : ℝ) : ℂ) = ((-(a - σ) : ℝ) : ℂ) := by congr 1; ring
    rw [he]
    exact h

end Sol_HardyHalfPlane_exists_boundary_function

open HardyHalfPlane Sol_HardyHalfPlane_exists_boundary_function in
theorem solution (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    (hΦ : MemLeftHardy Φ a p) :
    ∃ g : ℝ → ℂ, MemLp g p volume ∧
      ∀ᵐ y : ℝ ∂volume,
        Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a) (𝓝 (g y)) := by
  obtain ⟨hdiff, hfin⟩ := hΦ
  have hopen : IsOpen {s : ℂ | s.re < a} := isOpen_lt Complex.continuous_re continuous_const
  -- the transplanted function on the unit disc
  set F : ℂ → ℂ := fun w => Φ ((a : ℂ) + (w + 1) / (w - 1)) with hFdef
  have hFd : DifferentiableOn ℂ F (Metric.ball 0 1) := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    have hw1 : w - 1 ≠ 0 := by
      intro h
      have : w = 1 := sub_eq_zero.mp h
      rw [this] at hw'; simp at hw'
    have hre : ((a : ℂ) + (w + 1) / (w - 1)).re < a := by
      have hn : ((w + 1) / (w - 1)).re = (‖w‖ ^ 2 - 1) / ‖w - 1‖ ^ 2 := by
        rw [Complex.div_re, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
          Complex.normSq_apply]
        simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im,
          Complex.sub_im, Complex.one_im]
        field_simp
        ring
      have hpos : 0 < ‖w - 1‖ ^ 2 := by positivity
      have : ((w + 1) / (w - 1)).re < 0 := by
        rw [hn]; apply div_neg_of_neg_of_pos _ hpos
        nlinarith [norm_nonneg w]
      simp only [Complex.add_re, Complex.ofReal_re]; linarith
    apply DifferentiableAt.differentiableWithinAt
    have hΦd : DifferentiableAt ℂ Φ ((a : ℂ) + (w + 1) / (w - 1)) :=
      hdiff.differentiableAt (hopen.mem_nhds hre)
    have hm : DifferentiableAt ℂ (fun w : ℂ => (a : ℂ) + (w + 1) / (w - 1)) w := by
      apply DifferentiableAt.const_add
      exact DifferentiableAt.div (by fun_prop) (by fun_prop) hw1
    exact (DifferentiableAt.comp w hΦd hm :
      DifferentiableAt ℂ (Φ ∘ fun w : ℂ => (a : ℂ) + (w + 1) / (w - 1)) w)
  have hbd := HardyHalfPlane.exists_bound_circle_eLpNorm_comp_cayley Φ a p hp0 ⟨hdiff, hfin⟩
  have hae := HardyDisc.ae_exists_tendsto_nontangential F p hp0 hFd hbd
  -- transfer of the almost-everywhere statement from the circle to the line
  have hae' : ∀ᵐ y : ℝ ∂volume, ∃ L : ℂ,
      Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a) (𝓝 L) := by
    have hN := ae_iff.mp hae
    rw [ae_iff]
    refine measure_mono_null ?_ (preimage_null hN)
    intro y hy
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hy ⊢
    intro hgood
    apply hy
    obtain ⟨L, hL⟩ := hgood
    refine ⟨L, ?_⟩
    have hL2 := hL 2
    rw [circleMap_bdry] at hL2
    have hcomp := hL2.comp (tendsto_stolz a y)
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : σ < a := hσ
    set z : ℂ := ((σ - a : ℝ) : ℂ) + (y : ℂ) * Complex.I with hz
    have hz1 : z - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp [hz] at this; linarith
    have hcay : ((z + 1) / (z - 1) + 1) / ((z + 1) / (z - 1) - 1) = z := by
      rw [div_add_one hz1, div_sub_one hz1, div_div_div_cancel_right₀ hz1]
      have h2 : z + 1 - (z - 1) = 2 := by ring
      rw [h2]; ring
    show Φ ((a : ℂ) + ((z + 1) / (z - 1) + 1) / ((z + 1) / (z - 1) - 1)) = _
    rw [hcay, hz]
    congr 1
    push_cast; ring
  -- the boundary function
  set g : ℝ → ℂ := fun y =>
    limUnder (𝓝[<] a) (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) with hg
  have hlim : ∀ᵐ y : ℝ ∂volume,
      Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a) (𝓝 (g y)) := by
    filter_upwards [hae'] with y hy
    exact tendsto_nhds_limUnder hy
  refine ⟨g, ?_, hlim⟩
  -- a sequence of vertical lines tending to the boundary
  set s : ℕ → ℝ := fun n => a - 1 / ((n : ℝ) + 1) with hs
  have hsa : ∀ n, s n < a := fun n => by
    simp only [hs]; have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hseq : Tendsto s atTop (𝓝[<] a) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall hsa⟩
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub a
    simpa [hs] using this
  set f : ℕ → ℝ → ℂ := fun n y => Φ ((s n : ℂ) + (y : ℂ) * Complex.I) with hf
  have hfc : ∀ n, Continuous (f n) := by
    intro n
    apply hdiff.continuousOn.comp_continuous (by fun_prop)
    intro y
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im]
    simpa using hsa n
  have hfm : ∀ n, AEStronglyMeasurable (f n) volume := fun n => (hfc n).aestronglyMeasurable
  have hflim : ∀ᵐ y : ℝ ∂volume, Tendsto (fun n => f n y) atTop (𝓝 (g y)) := by
    filter_upwards [hlim] with y hy
    exact hy.comp hseq
  have hgm : AEStronglyMeasurable g volume := aestronglyMeasurable_of_tendsto_ae atTop hfm hflim
  refine ⟨hgm, ?_⟩
  refine lt_of_le_of_lt (Lp.eLpNorm_lim_le_liminf_eLpNorm hfm g hflim) (lt_of_le_of_lt ?_ hfin)
  apply liminf_le_of_frequently_le'
  refine Frequently.of_forall fun n => ?_
  exact le_iSup₂ (f := fun σ (_ : σ < a) =>
    eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) p volume) (s n) (hsa n)
