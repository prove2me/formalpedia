-- Prove2me | solution 1 for OAI.SymmetricMahler.equality_strip_images_dense_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:32:42.438797+00:00
-- url     : https://prove2.me/submissions/1eec3434-12a4-42af-8ede-74a2a161ab42

import Mathlib
import Definitions.Def_SymmetricMahlerEquality
import Definitions.Def_OAIQ2Ma000
import Theorems.Thm_OAI_Mahler_MassHypotheses_homogeneousSphereFlux_value_eq
import Theorems.Thm_OAI_Mahler_MassHypotheses_sourceCoordinateFlux_limit_eq
import Theorems.Thm_OAI_Mahler_source_regular_massBelow_of_flux_limit_eq
import Theorems.Thm_OAI_SymmetricMahler_stripMap_image_subset_product_eq
import Theorems.Thm_OAI_SymmetricMahler_stripMap_volume_eq_eq

section
-- module Solutions.OAIQ2_Mah.Mahler_Jacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Matrix Real

lemma weightedGram_apply {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (c : Fin N → ℝ) (i k : Fin n) :
    weightedGram A c i k = ∑ j : Fin N, A j i*c j*A j k := by
  unfold weightedGram
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConformalSeries
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conformal series and its logarithmic derivative. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

lemma D_zero : D 0 = 1 := by
  unfold D
  rw [tsum_eq_single 0]
  · norm_num
  · intro k hk
    have hp : 2*k ≠ 0 := by omega
    simp [zero_pow hp]

lemma pi_cast_ne : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

/-- Holomorphicity on the open unit disk. -/
theorem differentiableOn_F : DifferentiableOn ℂ F (ball 0 1) := by
  intro w hw
  exact (hasDerivAt_F_series (by simpa using hw)).differentiableAt.differentiableWithinAt

theorem F_zero : F 0 = 0 := by simp [F, series_zero]

/-- The removable value of the derivative at zero. -/
theorem hasDerivAt_F_zero : HasDerivAt F (8/(Real.pi : ℂ)^2) 0 := by
  simpa [D_zero] using hasDerivAt_F_series (w := 0) (by norm_num)

lemma log_cayley_ne_zero {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    Complex.log (cayley w) ≠ 0 := by
  intro h
  have hq0 : cayley w ≠ 0 := div_ne_zero (one_add_ne hw) (one_sub_ne hw)
  have he : cayley w = 1 := by rw [← Complex.exp_log hq0, h, Complex.exp_zero]
  have hl : 1+w = 1-w := (div_eq_one_iff_eq (one_sub_ne hw)).mp he
  apply hw0
  linear_combination (1/2 : ℂ) * hl

/-- Nonvanishing of the derivative. -/
theorem deriv_F_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : deriv F w ≠ 0 := by
  by_cases hw0 : w = 0
  · subst w
    rw [hasDerivAt_F_zero.deriv]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ pi_cast_ne)
  · rw [(hasDerivAt_F_log hw hw0).deriv]
    exact mul_ne_zero
      (div_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ pi_cast_ne) hw0))
      (log_cayley_ne_zero hw hw0)

/-- Conjugation symmetry of the conformal map. -/
theorem F_conj (w : ℂ) : F (starRingEnd ℂ w) = starRingEnd ℂ (F w) := by
  simp only [F, series, term, map_mul, map_div₀, map_pow, map_ofNat,
    map_natCast, Complex.conj_ofReal, Complex.conj_tsum]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_FiberPrimitive
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Set MeasureTheory

lemma planarError_nonneg (m : ℝ) : 0 ≤ planarError m := le_max_left _ _

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConformalInjectivity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

lemma norm_add_sub_sq (w : ℂ) : ‖1+w‖^2 - ‖1-w‖^2 = 4*w.re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

lemma re_mul_log_cayley_pos {w : ℂ} (hw : ‖w‖ < 1) (hx : w.re ≠ 0) :
    0 < w.re * (Complex.log (cayley w)).re := by
  have hnum : 0 < ‖1+w‖ := norm_pos_iff.mpr (one_add_ne hw)
  have hden : 0 < ‖1-w‖ := norm_pos_iff.mpr (one_sub_ne hw)
  have hn := norm_add_sub_sq w
  rw [Complex.log_re, cayley, norm_div]
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hc : ‖1+w‖/‖1-w‖ < 1 := (div_lt_one hden).mpr (by nlinarith)
    exact mul_pos_of_neg_of_neg hx (Real.log_neg (div_pos hnum hden) hc)
  · have hc : 1 < ‖1+w‖/‖1-w‖ := (one_lt_div hden).mpr (by nlinarith)
    exact mul_pos hx (Real.log_pos hc)

lemma re_mul_log_cayley_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ w.re * (Complex.log (cayley w)).re := by
  by_cases hx : w.re = 0
  · simp [hx]
  · exact (re_mul_log_cayley_pos hw hx).le

lemma im_mul_arg_cayley_pos {w : ℂ} (hw : ‖w‖ < 1) (hy : w.im ≠ 0) :
    0 < w.im * (cayley w).arg := by
  have hd : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
  rw [arg_eq_arctan_of_re_pos (cayley_re_pos hw), cayley_im_div_re hw]
  rcases lt_or_gt_of_ne hy with hy | hy
  · exact mul_pos_of_neg_of_neg hy
      (Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos (by linarith) hd))
  · exact mul_pos hy (Real.arctan_pos.mpr (div_pos (by linarith) hd))

lemma im_mul_arg_cayley_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ w.im * (cayley w).arg := by
  by_cases hy : w.im = 0
  · simp [hy]
  · exact (im_mul_arg_cayley_pos hw hy).le

/-- A consequence of the derivative formula on the full disk, used for injectivity.
This is not a formula for M'(r), nor does it assume univalence. -/
theorem deriv_F_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (deriv F w).re := by
  have hc : (4/(Real.pi : ℂ)^2) = ((4/Real.pi^2 : ℝ) : ℂ) := by push_cast; rfl
  by_cases hw0 : w = 0
  · subst w
    rw [hasDerivAt_F_zero.deriv]
    have he : (8/(Real.pi : ℂ)^2) = ((8/Real.pi^2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.ofReal_re]
    positivity
  have he : deriv F w = (4/(Real.pi : ℂ)^2)*(Complex.log (cayley w)/w) := by
    rw [(hasDerivAt_F_log hw hw0).deriv]
    dsimp [cayley]
    field_simp
  rw [he, hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_pos (by positivity)
  rw [Complex.div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hw0)
  have hx := re_mul_log_cayley_nonneg hw
  have hy := im_mul_arg_cayley_nonneg hw
  rw [Complex.log_im]
  by_cases hx0 : w.re = 0
  · have hy0 : w.im ≠ 0 := by
      intro hy0
      apply hw0
      apply Complex.ext <;> simp [hx0, hy0]
    have hp := im_mul_arg_cayley_pos hw hy0
    nlinarith
  · have hp := re_mul_log_cayley_pos hw hx0
    nlinarith

lemma segment_mem_disk {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) : ‖a+(t : ℂ)*(b-a)‖ < 1 := by
  have hc := (convex_ball (0 : ℂ) (1 : ℝ)) (by simpa using ha) (by simpa using hb)
    (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have he : (1-t) • a + t • b = a+(t : ℂ)*(b-a) := by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he] at hc
  simpa using hc

/-- Injectivity on the exact open unit disk, with no assumed inverse or central
univalence theorem. Positive real derivative makes the segment projection strict. -/
theorem F_injOn_disk : Set.InjOn F (ball (0 : ℂ) 1) := by
  intro a ha b hb hab
  by_contra hne
  have ha' : ‖a‖ < 1 := by simpa using ha
  have hb' : ‖b‖ < 1 := by simpa using hb
  have hd : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let g : ℝ → ℝ := fun t => (F (a+(t : ℂ)*(b-a))/(b-a)).re
  have hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt g (deriv F (a+(t : ℂ)*(b-a))).re t := by
    intro t ht
    have hw := segment_mem_disk ha' hb' ht
    have hf := (hasDerivAt_F_series hw).differentiableAt.hasDerivAt
    have hline : HasDerivAt (fun z : ℂ => a+z*(b-a)) (b-a) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (b-a)).const_add a
    have hs := ((hf.comp (t : ℂ) hline).div_const (b-a)).real_of_complex
    have he : (deriv F (a+(t : ℂ)*(b-a))*(b-a))/(b-a) =
        deriv F (a+(t : ℂ)*(b-a)) := mul_div_cancel_right₀ _ hd
    change HasDerivAt g _ t at hs
    rwa [he] at hs
  have hm : StrictMonoOn g (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hg t ht').deriv]
    exact deriv_F_re_pos (segment_mem_disk ha' hb' ht')
  have hlt := hm (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
  dsimp [g] at hlt
  simp only [zero_mul, add_zero, one_mul, add_sub_cancel] at hlt
  rw [hab] at hlt
  exact lt_irrefl _ hlt

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConformalInverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The biholomorphic map and its inverse.
The vertical interval property and P_m estimates are not asserted here. -/

noncomputable section
open Complex Set Metric Filter
open scoped Topology
namespace MahlerConformal

lemma inverseF_mem {u : ℂ} (hu : u ∈ Omega) : inverseF u ∈ ball (0 : ℂ) 1 :=
  Function.invFunOn_mem hu

lemma inverseF_right {u : ℂ} (hu : u ∈ Omega) : F (inverseF u) = u :=
  Function.invFunOn_eq hu

lemma inverseF_left {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : inverseF (F w) = w :=
  F_injOn_disk.leftInvOn_invFunOn hw

lemma hasStrictDerivAt_F {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    HasStrictDerivAt F (deriv F w) w :=
  ((differentiableOn_F.analyticAt (isOpen_ball.mem_nhds hw)).contDiffAt (n := 1)).hasStrictDerivAt
    (by norm_num)

theorem isOpen_Omega : IsOpen Omega := by
  apply isOpen_iff_mem_nhds.mpr
  rintro u ⟨w, hw, rfl⟩
  rw [← (hasStrictDerivAt_F hw).map_nhds_eq (deriv_F_ne_zero (by simpa using hw))]
  change F ⁻¹' Omega ∈ 𝓝 w
  apply Filter.mem_of_superset (isOpen_ball.mem_nhds hw)
  intro z hz
  exact ⟨z, hz, rfl⟩

/-- The selected inverse is holomorphic on its exact image domain, with the
reciprocal derivative. Its local inverse hypotheses follow from proved injectivity. -/
theorem hasDerivAt_inverseF {u : ℂ} (hu : u ∈ Omega) :
    HasDerivAt inverseF (deriv F (inverseF u))⁻¹ u := by
  have hw := inverseF_mem hu
  have hl : ∀ᶠ w in 𝓝 (inverseF u), inverseF (F w) = w := by
    filter_upwards [isOpen_ball.mem_nhds hw] with w hw
    exact inverseF_left hw
  have hd := (hasStrictDerivAt_F hw).to_local_left_inverse
    (deriv_F_ne_zero (by simpa using hw)) hl
  rw [inverseF_right hu] at hd
  exact hd.hasDerivAt

theorem differentiableOn_inverseF : DifferentiableOn ℂ inverseF Omega :=
  fun _ hu => (hasDerivAt_inverseF hu).differentiableAt.differentiableWithinAt

theorem inverseF_deriv_ne_zero {u : ℂ} (hu : u ∈ Omega) : deriv inverseF u ≠ 0 := by
  rw [(hasDerivAt_inverseF hu).deriv]
  exact inv_ne_zero (deriv_F_ne_zero (by simpa using inverseF_mem hu))

theorem zero_mem_Omega : (0 : ℂ) ∈ Omega := ⟨0, by simp, F_zero⟩

theorem inverseF_zero : inverseF 0 = 0 := by
  simpa only [F_zero] using inverseF_left (w := 0) (by simp)

theorem inverseF_eq_zero_iff {u : ℂ} (hu : u ∈ Omega) : inverseF u = 0 ↔ u = 0 := by
  constructor
  · intro h
    rw [← inverseF_right hu, h, F_zero]
  · intro h
    rw [h, inverseF_zero]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_VerticalRadius
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical geometry of the actual inverse. The squared inverse radius has
positive vertical derivative on the image of the upper half-disk. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

lemma hasDerivAt_normSq {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun x => Complex.normSq (f x))
      (2*((f t).re*f'.re+(f t).im*f'.im)) t := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  convert (hre.mul hre).add (him.mul him) using 1 <;> (try rfl)
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, Function.comp_apply]
  ring

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset
open scoped Topology ContDiff
open MahlerConformal

variable {n N : ℕ}

lemma rowCLM_apply (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (x : Fin n → ℝ) :
    rowCLM A j x = measurement A x j := by
  simp [rowCLM,measurement]

lemma stripCoordinateCLM_apply (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : stripCoordinateCLM A j z = stripCoordinate A z j := by
  simp [stripCoordinateCLM,stripCoordinate,rowCLM_apply,mul_comm]

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripVolume
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset MeasureTheory
open scoped Topology ENNReal Pointwise
open MahlerConformal
variable {n N : ℕ}

lemma isOpen_stripDomain (A : Matrix (Fin N) (Fin n) ℝ) : IsOpen (stripDomain A) := by
  have he : stripDomain A = ⋂ j, (stripCoordinateCLM A j) ⁻¹' Omega := by
    ext z
    simp only [stripDomain, mem_ofPred_eq, mem_iInter, Set.mem_preimage,stripCoordinateCLM_apply]
  rw [he]
  exact isOpen_iInter_of_finite (fun j => isOpen_Omega.preimage (stripCoordinateCLM A j).continuous)

lemma continuousOn_stripTau (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    ContinuousOn (stripTau A m) (stripDomain A) := by
  have hc : ∀ j, ContinuousOn (fun z => ‖inverseF (stripCoordinate A z j)‖^(2*m : ℕ)) (stripDomain A) := by
    intro j
    have hi : ContinuousOn (fun z => inverseF (stripCoordinate A z j)) (stripDomain A) := by
      apply differentiableOn_inverseF.continuousOn.comp
      · have h : ContinuousOn (stripCoordinateCLM A j) (stripDomain A) := (stripCoordinateCLM A j).continuous.continuousOn
        exact h.congr (fun z _ => (stripCoordinateCLM_apply A j z).symm)
      · intro z hz
        exact hz j
    exact hi.norm.pow _
  have h := continuousOn_finsetSum (univ : Finset (Fin N)) (fun j _ => hc j)
  convert h using 1
  funext z
  unfold stripTau
  apply sum_congr rfl
  intro j _
  rw [show 2*(m : ℝ) = ((2*m : ℕ) : ℝ) by norm_cast,Real.rpow_natCast]

lemma isOpen_stripSublevel (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    IsOpen (stripSublevel A m) :=
  (continuousOn_stripTau A m).isOpen_inter_preimage (isOpen_stripDomain A) isOpen_Iio

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ComplexStripMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset MeasureTheory
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

/-- The explicit separation of real and imaginary coordinates preserves
standard Lebesgue measure exactly, with no normalization factor. -/
lemma volume_preserving_complexToReal : MeasurePreserving (complexToReal (n := n)) := by
  have hp := volume_preserving_pi (ι := Fin n) (fun _ => Complex.volume_preserving_equiv_real_prod)
  have h := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).comp hp
  simpa [Function.comp_def,complexToReal,MeasurableEquiv.arrowProdEquivProdArrow,
    Equiv.arrowProdEquivProdArrow] using! h

lemma complexRow_apply (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (z : Fin n → ℂ) :
    complexRow A j z = ∑ i, (A j i : ℂ)*z i := by simp [complexRow]

lemma complexRow_re (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (z : Fin n → ℂ) :
    (complexRow A j z).re = measurement A (complexToReal z).1 j := by
  simp [complexRow_apply,measurement,complexToReal]

lemma complexRow_im (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (z : Fin n → ℂ) :
    (complexRow A j z).im = measurement A (complexToReal z).2 j := by
  simp [complexRow_apply,measurement,complexToReal]

lemma complexRow_eq_stripCoordinate (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (z : Fin n → ℂ) :
    complexRow A j z = stripCoordinate A (complexToReal z) j := by
  apply Complex.ext <;> simp [stripCoordinate,complexRow_re,complexRow_im]

lemma complexStripDomain_eq_preimage (A : Matrix (Fin N) (Fin n) ℝ) :
    complexStripDomain A = complexToReal ⁻¹' stripDomain A := by
  ext z
  simp only [complexStripDomain,stripDomain,mem_ofPred_eq,Set.mem_preimage,complexRow_eq_stripCoordinate]

lemma isOpen_complexStripDomain (A : Matrix (Fin N) (Fin n) ℝ) : IsOpen (complexStripDomain A) := by
  rw [complexStripDomain_eq_preimage]
  exact (isOpen_stripDomain A).preimage complexRealEquiv.continuous

lemma zero_mem_complexStripDomain (A : Matrix (Fin N) (Fin n) ℝ) : 0 ∈ complexStripDomain A := by
  intro j
  simpa using zero_mem_Omega

/-- The holomorphic map used in the mass inequality. -/
theorem differentiableOn_specialMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    DifferentiableOn ℂ (specialMap A m) (complexStripDomain A) := by
  apply differentiableOn_pi.mpr
  intro j
  have hr : DifferentiableOn ℂ (complexRow A j) (complexStripDomain A) :=
    (complexRow A j).differentiable.differentiableOn
  have hmaps : MapsTo (complexRow A j) (complexStripDomain A) Omega := fun z hz => hz j
  exact (differentiableOn_inverseF.comp hr hmaps).pow m

lemma complexRow_injective (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) :
    Function.Injective (fun z : Fin n → ℂ => fun j => complexRow A j z) := by
  intro z w h
  have hre : (complexToReal z).1 = (complexToReal w).1 := by
    apply hA
    funext j
    simpa [complexRow_re] using congrArg Complex.re (congrFun h j)
  have him : (complexToReal z).2 = (complexToReal w).2 := by
    apply hA
    funext j
    simpa [complexRow_im] using congrArg Complex.im (congrFun h j)
  have he := Prod.ext hre him
  exact complexRealLinearEquiv.injective he

/-- The actual map has precisely one common zero on its actual domain. -/
theorem specialMap_eq_zero_iff (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {z : Fin n → ℂ} (hz : z ∈ complexStripDomain A) : specialMap A m z = 0 ↔ z = 0 := by
  constructor
  · intro hf
    apply complexRow_injective A hA
    funext j
    have hp : inverseF (complexRow A j z)^m = 0 := congrFun hf j
    have h0 : inverseF (complexRow A j z) = 0 := by
      by_contra hn
      exact (pow_ne_zero m hn) hp
    simpa using (inverseF_eq_zero_iff (hz j)).mp h0
  · rintro rfl
    funext j
    simp [specialMap,inverseF_zero,hm.ne']

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ComplexVolume
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory WithLp
open scoped ENNReal
namespace SymmetricMahler

variable (n : ℕ)

/-- Euclidean complex coordinates to separated real coordinates, with exact volume. -/
theorem volume_preserving_complexEuclidean_split :
    MeasurePreserving (fun z : EuclideanSpace ℂ (Fin n) =>
      ((fun i => (z i).re), (fun i => (z i).im))) := by
  have h := ((PiLp.volume_preserving_ofLp (Fin n)).prod
      (PiLp.volume_preserving_ofLp (Fin n))).comp
    ((WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))).comp
      (complexEuclideanRealification n).measurePreserving)
  exact h

/-- Forgetting the L2 wrapper on complex coordinates preserves standard volume. -/
theorem volume_preserving_complex_ofLp :
    MeasurePreserving (@WithLp.ofLp 2 (Fin n → ℂ)) := by
  have hsplit := volume_preserving_complexEuclidean_split n
  have hjoin := (volume_preserving_pi (ι := Fin n)
    (fun _ => Complex.volume_preserving_equiv_real_prod.symm)).comp
      (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)).symm
  convert hjoin.comp hsplit using 1
  ext z i
  rfl

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConformalRadialRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

/-- The positive-real derivative yields a strictly positive projection on
any chord of the disk. -/
theorem F_chord_re_pos {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hab : a ≠ b) : 0 < ((F b - F a) / (b-a)).re := by
  have hd : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  let g : ℝ → ℝ := fun t => (F (a+(t : ℂ)*(b-a))/(b-a)).re
  have hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt g (deriv F (a+(t : ℂ)*(b-a))).re t := by
    intro t ht
    have hf := (hasDerivAt_F_series (segment_mem_disk ha hb ht)).differentiableAt.hasDerivAt
    have hl : HasDerivAt (fun z : ℂ => a+z*(b-a)) (b-a) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (b-a)).const_add a
    have h := ((hf.comp (t : ℂ) hl).div_const (b-a)).real_of_complex
    change HasDerivAt g _ t at h
    simpa only [mul_div_cancel_right₀ _ hd] using h
  have hm : StrictMonoOn g (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hg t (interior_subset ht)).deriv]
    exact deriv_F_re_pos (segment_mem_disk ha hb (interior_subset ht))
  have h := hm (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
  dsimp [g] at h
  simp only [zero_mul, add_zero,
    one_mul, add_sub_cancel] at h
  simpa only [sub_div, Complex.sub_re, sub_pos] using h

lemma F_re_mul_re_pos {w : ℂ} (hw : ‖w‖ < 1) (hx : w.re ≠ 0) :
    0 < (F w).re * w.re := by
  have hne : -starRingEnd ℂ w ≠ w := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at this
    exact hx (by linarith)
  have h := F_chord_re_pos (a := -starRingEnd ℂ w) (by simpa using hw) hw hne
  rw [F_odd, F_conj] at h
  simp only [Complex.div_re, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply] at h
  have hd : 0 < (w.re - -w.re) * (w.re - -w.re) + (w.im - - -w.im) * (w.im - - -w.im) := by
    nlinarith [sq_pos_of_ne_zero hx]
  rw [← add_div] at h
  have hp := (div_pos_iff.mp h)
  rcases hp with hp | hp
  · nlinarith [hp.1]
  · linarith [hp.2]

lemma F_im_mul_im_pos {w : ℂ} (hw : ‖w‖ < 1) (hy : w.im ≠ 0) :
    0 < (F w).im * w.im := by
  have hne : starRingEnd ℂ w ≠ w := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    exact hy (by linarith)
  have h := F_chord_re_pos (a := starRingEnd ℂ w) (by simpa using hw) hw hne
  rw [F_conj] at h
  simp only [Complex.div_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply] at h
  have hd : 0 < (w.re-w.re)*(w.re-w.re)+(w.im- -w.im)*(w.im- -w.im) := by
    nlinarith [sq_pos_of_ne_zero hy]
  rw [← add_div] at h
  rcases div_pos_iff.mp h with hp | hp
  · nlinarith [hp.1]
  · linarith [hp.2]

lemma F_re_eq_zero_of_re_eq_zero {w : ℂ} (hx : w.re = 0) : (F w).re = 0 := by
  have he : -starRingEnd ℂ w = w := by apply Complex.ext <;> simp [hx]
  have h := congrArg Complex.re (F_odd (starRingEnd ℂ w))
  rw [he, F_conj] at h
  simp only [Complex.neg_re, Complex.conj_re] at h
  linarith

lemma F_im_eq_zero_of_im_eq_zero {w : ℂ} (hy : w.im = 0) : (F w).im = 0 := by
  have he : starRingEnd ℂ w = w := by apply Complex.ext <;> simp [hy]
  have h := congrArg Complex.im (F_conj w)
  rw [he] at h
  simp only [Complex.conj_im] at h
  linarith

lemma mul_pos_of_common_factor {a b c : ℝ} (ha : 0 < a*c) (hb : 0 < c*b) :
    0 < a*b := by
  have h := mul_pos ha hb
  have hc : 0 ≤ c*c := mul_self_nonneg c
  nlinarith [show (a*c)*(c*b) = (a*b)*(c*c) by ring]

/-- The actual F and its radial derivative have positive Euclidean pairing.
This gives radial regularity for its inverse without invoking Sard. -/
theorem F_radial_pairing_pos {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    0 < (F w).re * (w * deriv F w).re + (F w).im * (w * deriv F w).im := by
  have he : w * deriv F w = ((4/Real.pi^2 : ℝ) : ℂ) * Complex.log (cayley w) := by
    rw [(hasDerivAt_F_log hw hw0).deriv]
    dsimp [cayley]
    push_cast
    field_simp
  rw [he, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  have hx : 0 ≤ (F w).re * (Complex.log (cayley w)).re := by
    by_cases hx : w.re = 0
    · simp [F_re_eq_zero_of_re_eq_zero hx]
    · exact (mul_pos_of_common_factor (F_re_mul_re_pos hw hx) (re_mul_log_cayley_pos hw hx)).le
  have hy : 0 ≤ (F w).im * (Complex.log (cayley w)).im := by
    rw [Complex.log_im]
    by_cases hy : w.im = 0
    · simp [F_im_eq_zero_of_im_eq_zero hy]
    · exact (mul_pos_of_common_factor (F_im_mul_im_pos hw hy) (im_mul_arg_cayley_pos hw hy)).le
  have hp : 0 < (F w).re * (Complex.log (cayley w)).re +
      (F w).im * (Complex.log (cayley w)).im := by
    by_cases hx0 : w.re = 0
    · have hy0 : w.im ≠ 0 := by
        intro hy0
        exact hw0 (Complex.ext (by simpa using hx0) (by simpa using hy0))
      have := mul_pos_of_common_factor (F_im_mul_im_pos hw hy0) (im_mul_arg_cayley_pos hw hy0)
      rw [← Complex.log_im] at this
      linarith
    · have := mul_pos_of_common_factor (F_re_mul_re_pos hw hx0) (re_mul_log_cayley_pos hw hx0)
      linarith
  nlinarith [mul_pos (show 0 < 4/Real.pi^2 by positivity) hp]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConvexApproximation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-strip approximation with coordinate definitions of the convex body and its polar. -/
namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I J : Type*} [Fintype I] [Fintype J]

lemma continuous_pairing (x : I → ℝ) : Continuous (fun p : I → ℝ => ∑ i, p i * x i) := by
  exact continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)

lemma coordinatePolar_antitone {K L : Set (I → ℝ)} (h : K ⊆ L) :
    coordinatePolar L ⊆ coordinatePolar K := fun _ hp x hx => hp x (h hx)

lemma zero_mem_coordinatePolar (K : Set (I → ℝ)) : (0 : I → ℝ) ∈ coordinatePolar K := by
  intro x hx
  simp

lemma isClosed_coordinatePolar (K : Set (I → ℝ)) : IsClosed (coordinatePolar K) := by
  have heq : coordinatePolar K = ⋂ x ∈ K, {p | (∑ i, p i*x i) ≤ 1} := by
    ext p
    simp [coordinatePolar]
  rw [heq]
  exact isClosed_biInter (fun x hx => isClosed_le (continuous_pairing x) continuous_const)

lemma polar_pairing_abs {K : Set (I → ℝ)} (hsym : ∀ x ∈ K, -x ∈ K)
    {p : I → ℝ} (hp : p ∈ coordinatePolar K) {x : I → ℝ} (hx : x ∈ K) :
    |∑ i, p i * x i| ≤ 1 := by
  refine abs_le.mpr ⟨?_, hp x hx⟩
  have h := hp (-x) (hsym x hx)
  simp only [Pi.neg_apply, mul_neg, sum_neg_distrib] at h
  linarith

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConvexGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I J : Type*} [fintypeI : Fintype I] [fintypeJ : Fintype J] [decidableEqI : DecidableEq I]

/-- The polar of a symmetric body is bounded because K contains a ball. -/
theorem isCompact_coordinatePolar {K : Set (I → ℝ)}
    (hsym : ∀ x ∈ K, -x ∈ K) (hzero : (0 : I → ℝ) ∈ interior K) :
    IsCompact (coordinatePolar K) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  have hb : ∀ i : I, Pi.single i (r/2) ∈ K := by
    intro i
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, Pi.norm_single, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    linarith
  apply (isCompact_Icc : IsCompact
    (Icc (fun _ : I => -(r/2)⁻¹) (fun _ => (r/2)⁻¹))).of_isClosed_subset
    (isClosed_coordinatePolar K)
  intro p hp
  have hpi : ∀ i, |p i| ≤ (r/2)⁻¹ := by
    intro i
    have h := polar_pairing_abs hsym hp (hb i)
    simp [Pi.single_apply, abs_mul, abs_of_pos (half_pos hr)] at h
    have h' : (r/2)*|p i| ≤ 1 := by nlinarith
    simpa using (le_inv_mul_iff₀ (half_pos hr)).mpr h'
  exact ⟨fun i => (abs_le.mp (hpi i)).1, fun i => (abs_le.mp (hpi i)).2⟩

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConvexPolarBody
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Finset
variable {I : Type*} [Fintype I] [decidableEqI : DecidableEq I]

omit decidableEqI in
lemma convex_coordinatePolar [DecidableEq I] (K : Set (I → ℝ)) : Convex ℝ (coordinatePolar K) := by
  intro p hp q hq a b ha hb hab x hx
  calc
    (∑ i, (a • p + b • q) i * x i) =
        a * (∑ i, p i*x i) + b * (∑ i, q i*x i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        sum_add_distrib, mul_sum]
      apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intros <;> ring
    _ ≤ a*1+b*1 := add_le_add
      (mul_le_mul_of_nonneg_left (hp x hx) ha) (mul_le_mul_of_nonneg_left (hq x hx) hb)
    _ = 1 := by linarith

omit decidableEqI in
lemma symmetric_coordinatePolar [DecidableEq I] {K : Set (I → ℝ)} (hsym : ∀ x ∈ K, -x ∈ K) :
    ∀ p ∈ coordinatePolar K, -p ∈ coordinatePolar K := by
  intro p hp x hx
  have h := (abs_le.mp (polar_pairing_abs hsym hp hx)).1
  simp only [Pi.neg_apply, neg_mul, sum_neg_distrib]
  linarith

omit decidableEqI in
/-- A compact K gives an open l1 neighborhood of zero inside the literal polar. -/
theorem zero_mem_interior_coordinatePolar [DecidableEq I] {K : Set (I → ℝ)} (hK : IsCompact K) :
    (0 : I → ℝ) ∈ interior (coordinatePolar K) := by
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_le
  let S : Set (I → ℝ) := {p | (∑ i, |p i|) < R⁻¹}
  have hS : IsOpen S := isOpen_lt
    (continuous_finsetSum _ (fun i _ => (continuous_apply i).abs)) continuous_const
  have hz : (0 : I → ℝ) ∈ S := by simpa [S] using inv_pos.mpr hR
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hS.mem_nhds hz)
  intro p hp x hx
  calc
    (∑ i, p i*x i) ≤ ∑ i, |p i| * R := by
      apply sum_le_sum
      intro i _
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm x i).trans (hb x hx)) (abs_nonneg _)
    _ = (∑ i, |p i|)*R := by rw [sum_mul]
    _ ≤ 1 := by
      have h : (∑ i, |p i|) < 1/R := by simpa only [S, Set.mem_ofPred_eq, one_div] using hp
      exact ((lt_div_iff₀ hR).mp h).le

/-- The polar of an origin-symmetric convex body is again such a body. -/
theorem coordinatePolar_is_symmetric_convex_body {K : Set (I → ℝ)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    IsCompact (coordinatePolar K) ∧ Convex ℝ (coordinatePolar K) ∧
      (∀ p ∈ coordinatePolar K, -p ∈ coordinatePolar K) ∧
      (interior (coordinatePolar K)).Nonempty :=
  ⟨isCompact_coordinatePolar hsym (zero_mem_interior_of_symmetric hconv hsym hint),
    convex_coordinatePolar K, symmetric_coordinatePolar hsym,
    ⟨0, zero_mem_interior_coordinatePolar hK⟩⟩

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HolomorphicRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex Set Metric Filter MeasureTheory
open scoped Topology Interval

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex Schwarz estimate gives a local bound on the full derivative,
from first-order holomorphicity alone. -/
lemma locally_bounded_fderiv {f : E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) :
    ∃ r > 0, ∃ C ≥ 0, ball x r ⊆ U ∧
      ∀ y ∈ ball x r, ‖fderiv ℂ f y‖ ≤ C := by
  have hc := (hf x hx).differentiableAt (hU.mem_nhds hx) |>.continuousAt
  have hn : U ∩ f ⁻¹' ball (f x) 1 ∈ 𝓝 x :=
    inter_mem (hU.mem_nhds hx) (hc.preimage_mem_nhds (ball_mem_nhds _ zero_lt_one))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r / 2, by positivity, 2 / (r / 2), by positivity, ?_, ?_⟩
  · intro y hy
    exact (hsub (ball_subset_ball (by linarith) hy)).1
  · intro y hy
    have hball : ball y (r / 2) ⊆ ball x r := by
      intro z hz
      have := dist_triangle z y x
      rw [mem_ball] at hy hz ⊢
      linarith
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
      (hf.mono (hball.trans (fun z hz => (hsub hz).1))) ?_ (by positivity)
    intro z hz
    have hzy := (hsub (hball hz)).2
    have hyx := (hsub (ball_subset_ball (by linarith) hy)).2
    rw [mem_closedBall]
    have := dist_triangle (f z) (f x) (f y)
    change dist (f z) (f x) < 1 at hzy
    change dist (f y) (f x) < 1 at hyx
    rw [dist_comm (f x) (f y)] at this
    linarith

variable [FiniteDimensional ℂ E]

/-- Differentiability of a Cauchy integral in an ambient finite-dimensional
complex parameter. The derivative bound is obtained locally by Schwarz. -/
lemma differentiable_cauchy_parameter {f : E → ℂ} {U : Set E} {x v : E}
    {R C r : ℝ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : 0 < R) (hr : 0 < r) (hv : r * ‖v‖ < R / 2)
    (hsub : ball x R ⊆ U)
    (hb : ∀ y ∈ ball x R, ‖fderiv ℂ f y‖ ≤ C) :
    DifferentiableAt ℂ
      (fun y => ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) x := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let c : ℝ → ℂ := circleMap 0 r
  let k : ℝ → ℂ := fun t => (c t * I) * (1 / c t ^ 2)
  have hc : Continuous c := continuous_circleMap _ _
  have hcn (t : ℝ) : ‖c t‖ = r := by simp [c, abs_of_pos hr]
  have hcz (t : ℝ) : c t ≠ 0 := by
    intro h
    have := hcn t
    rw [h, norm_zero] at this
    linarith
  have hk : Continuous k := (hc.mul continuous_const).mul
    (continuous_const.div (hc.pow 2) (fun t => pow_ne_zero _ (hcz t)))
  have hkn (t : ℝ) : ‖k t‖ = 1 / r := by
    simp [k, norm_pow, hcn, norm_I]
    field_simp
  have hshift {y : E} (hy : y ∈ ball x (R / 2)) (t : ℝ) :
      y + c t • v ∈ ball x R := by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have htri := norm_add_le (y - x) (c t • v)
    have he : y + c t • v - x = (y - x) + c t • v := by abel
    rw [he]
    rw [norm_smul, hcn] at htri
    linarith
  have hcont {y : E} (hy : y ∈ ball x (R / 2)) :
      Continuous (fun t => k t * f (y + c t • v)) := by
    apply hk.mul
    exact hf.continuousOn.comp_continuous (by fun_prop) (fun t => hsub (hshift hy t))
  let F' : E → ℝ → E →L[ℂ] ℂ := fun y t => k t • fderiv ℂ f (y + c t • v)
  have hd {y : E} (hy : y ∈ ball x (R / 2)) (t : ℝ) :
      HasFDerivAt (fun y => k t * f (y + c t • v)) (F' y t) y := by
    have hf' := ((hf _ (hsub (hshift hy t))).differentiableAt
      (hU.mem_nhds (hsub (hshift hy t)))).hasFDerivAt
    simpa only [F', Function.comp_apply, id_eq, ContinuousLinearMap.comp_id] using
      (hf'.comp y ((hasFDerivAt_id y).add_const (c t • v))).const_mul (k t)
  have hm : AEStronglyMeasurable (F' x) := by
    apply Measurable.aestronglyMeasurable
    exact hk.measurable.smul ((measurable_fderiv ℂ f).comp
      (show Continuous (fun t => x + c t • v) by fun_prop).measurable)
  have hint := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℂ) (μ := volume) (a := 0) (b := 2 * Real.pi)
    (F := fun y t => k t * f (y + c t • v)) (F' := F')
    (bound := fun _ => (1 / r) * C) (ball_mem_nhds x (by positivity : 0 < R / 2))
    (by filter_upwards [ball_mem_nhds x (by positivity : 0 < R / 2)] with y hy
        exact (hcont hy).aestronglyMeasurable)
    ((hcont (mem_ball_self (by positivity))).intervalIntegrable _ _)
    hm.restrict
    (by filter_upwards [] with t ht y hy
        simp only [F', norm_smul, hkn]
        exact mul_le_mul_of_nonneg_left (hb _ (hshift hy t)) (by positivity))
    (intervalIntegrable_const)
    (by filter_upwards [] with t ht y hy; exact hd hy t)
  have he : (fun y => ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) =
      (fun y => ∫ t in (0 : ℝ)..2 * Real.pi, k t * f (y + c t • v)) := by
    funext y
    simp only [circleIntegral, deriv_circleMap, smul_eq_mul, c, k, mul_assoc]
  rw [he]
  exact hint.differentiableAt

/-- A directional component of the ambient first derivative is holomorphic.
Only first-order holomorphicity on the open domain is assumed. -/
theorem differentiableAt_fderiv_apply_of_open {f : E → ℂ} {U : Set E} {x v : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableAt ℂ (fun y => fderiv ℂ f y v) x := by
  obtain ⟨R, hR, C, hC, hsub, hb⟩ := locally_bounded_fderiv hU hx hf
  let r := (R / 2) / (‖v‖ + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hv : r * ‖v‖ < R / 2 := by
    dsimp [r]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < ‖v‖ + 1)]
    nlinarith
  have hshift {y : E} (hy : y ∈ ball x (R / 2)) {z : ℂ}
      (hz : z ∈ closedBall 0 r) : y + z • v ∈ U := by
    apply hsub
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have hzn : ‖z‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
    have htri := norm_add_le (y - x) (z • v)
    have he : y + z • v - x = (y - x) + z • v := by abel
    rw [he]
    rw [norm_smul] at htri
    have hmul := mul_le_mul_of_nonneg_right hzn (norm_nonneg v)
    linarith
  have he : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x]
      (fun y => (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) := by
    filter_upwards [ball_mem_nhds x (by positivity : 0 < R / 2)] with y hy
    have hl : Differentiable ℂ (fun z : ℂ => y + z • v) := by fun_prop
    have hline : DifferentiableOn ℂ (fun z : ℂ => f (y + z • v)) (closedBall 0 r) :=
      hf.comp hl.differentiableOn (fun z hz => hshift hy hz)
    have hcauchy := hline.deriv_eq_smul_circleIntegral hr
    have hfy : DifferentiableAt ℂ f y :=
      (hf y (by simpa using hshift hy (mem_closedBall_self hr.le))).differentiableAt
        (hU.mem_nhds (by simpa using hshift hy (mem_closedBall_self hr.le)))
    have hl' : HasDerivAt (fun z : ℂ => y + z • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    have hfy' : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
      simpa using hfy.hasFDerivAt
    have hder := hfy'.comp_hasDerivAt 0 hl'
    change HasDerivAt (fun z : ℂ => f (y + z • v)) (fderiv ℂ f y v) 0 at hder
    rw [hder.deriv] at hcauchy
    simp only [sub_zero, smul_eq_mul] at hcauchy ⊢
    rw [hcauchy, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  exact ((differentiable_cauchy_parameter hU hf hR hr hv hsub hb).const_mul
    (2 * Real.pi * I : ℂ)⁻¹).congr_of_eventuallyEq he

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Hessian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators Topology

local notation "conj" => starRingEnd ℂ

namespace Mahler
variable {E : Type*} [normedAddCommGroupE : NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [normedSpaceRealE : NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

lemma dz_holomorphic {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℂ f x) :
    dz f x v = fderiv ℂ f x v := by
  rw [dz, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  change (fderiv ℂ f x v - I * fderiv ℂ f x (I • v)) / 2 = _
  rw [map_smul]
  simp only [smul_eq_mul]
  have hi := I_mul_I
  calc
    _ = (fderiv ℂ f x v - (I * I) * fderiv ℂ f x v) / 2 := by ring
    _ = _ := by rw [hi]; ring

lemma dbar_holomorphic {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℂ f x) :
    dbar f x v = 0 := by
  rw [dbar, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  change (fderiv ℂ f x v + I * fderiv ℂ f x (I • v)) / 2 = _
  rw [map_smul]
  simp only [smul_eq_mul]
  calc
    _ = (fderiv ℂ f x v + (I * I) * fderiv ℂ f x v) / 2 := by ring
    _ = _ := by rw [I_mul_I]; ring

omit isScalarTowerRealComplexE in
lemma dz_conj [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℝ f x) :
    dz (fun y => conj (f y)) x v = conj (dbar f x v) := by
  have h : HasFDerivAt (fun y => conj (f y))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x)) x :=
    Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt
  rw [dz, h.fderiv]
  simp [dbar, map_add, map_mul, conj_I, map_ofNat, sub_eq_add_neg]

omit isScalarTowerRealComplexE in
lemma dbar_conj [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℝ f x) :
    dbar (fun y => conj (f y)) x v = conj (dz f x v) := by
  have h : HasFDerivAt (fun y => conj (f y))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x)) x :=
    Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt
  rw [dbar, h.fderiv]
  simp [dz, map_sub, map_mul, conj_I, map_ofNat]

omit isScalarTowerRealComplexE in
lemma dz_mul [IsScalarTower ℝ ℂ E] {f g : E → ℂ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dz (fun y => f y * g y) x v = dz f x v * g x + f x * dz g x v := by
  have h := hf.hasFDerivAt.mul hg.hasFDerivAt
  simp only [Pi.mul_def] at h
  rw [dz, h.fderiv]
  simp [dz]
  ; ring

omit isScalarTowerRealComplexE in
lemma dbar_mul [IsScalarTower ℝ ℂ E] {f g : E → ℂ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dbar (fun y => f y * g y) x v = dbar f x v * g x + f x * dbar g x v := by
  have h := hf.hasFDerivAt.mul hg.hasFDerivAt
  simp only [Pi.mul_def] at h
  rw [dbar, h.fderiv]
  simp [dbar]
  ; ring

omit isScalarTowerRealComplexE in
lemma dz_sum [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    dz (fun y => ∑ j, f j y) x v = ∑ j, dz (f j) x v := by
  have h : HasFDerivAt (fun y => ∑ j, f j y) (∑ j, fderiv ℝ (f j) x) x :=
    HasFDerivAt.fun_sum (fun j _ => (hf j).hasFDerivAt)
  rw [dz, h.fderiv]
  simp only [dz, sum_apply, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

omit isScalarTowerRealComplexE in
lemma dbar_sum [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    dbar (fun y => ∑ j, f j y) x v = ∑ j, dbar (f j) x v := by
  have h : HasFDerivAt (fun y => ∑ j, f j y) (∑ j, fderiv ℝ (f j) x) x :=
    HasFDerivAt.fun_sum (fun j _ => (hf j).hasFDerivAt)
  rw [dbar, h.fderiv]
  simp only [dbar, sum_apply, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

variable {ι : Type*} [Fintype ι]

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma diff_conj [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => conj (f y)) x :=
  Complex.conjCLE.differentiableAt.comp x hf

lemma dz_energy {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) :
    dz (energy f) x v = ∑ j, conj (f j x) * fderiv ℂ (f j) x v := by
  change dz (fun y => ∑ j, conj (f j y) * f j y) x v = _
  rw [dz_sum (f := fun j y => conj (f j y) * f j y) (fun j => (diff_conj ((hf j).restrictScalars ℝ)).mul
    ((hf j).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dz_mul (diff_conj ((hf j).restrictScalars ℝ)) ((hf j).restrictScalars ℝ),
    dz_conj ((hf j).restrictScalars ℝ), dbar_holomorphic (hf j), dz_holomorphic (hf j)]
  simp

omit isScalarTowerRealComplexE in
lemma dbar_congr_nhds [IsScalarTower ℝ ℂ E] {u q : E → ℂ} {x v : E} (h : u =ᶠ[𝓝 x] q) :
    dbar u x v = dbar q x v := by
  simp only [dbar, h.fderiv_eq]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_OpenHessian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Complex Matrix
open scoped BigOperators Topology ComplexOrder
local notation "conj" => starRingEnd ℂ
namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι κ : Type*} [Fintype ι] [fintypeKappa : Fintype κ]

lemma dbar_numerator_of_open {f : ι → E → ℂ} {U : Set E} {x v w : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    dbar (numerator f v) x w = ∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v := by
  change dbar (fun y => ∑ j, conj (f j y) * fderiv ℂ (f j) y v) x w = _
  rw [dbar_sum (f := fun j y => conj (f j y) * fderiv ℂ (f j) y v) (fun j => (diff_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ)).mul
    ((differentiableAt_fderiv_apply_of_open hU hx (hf j)).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dbar_mul (diff_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ))
    ((differentiableAt_fderiv_apply_of_open hU hx (hf j)).restrictScalars ℝ),
    dbar_conj (((hf j x hx).differentiableAt (hU.mem_nhds hx)).restrictScalars ℝ),
    dz_holomorphic ((hf j x hx).differentiableAt (hU.mem_nhds hx)), dbar_holomorphic (differentiableAt_fderiv_apply_of_open hU hx (hf j))]
  simp

/-- Actual mixed Wirtinger derivative of the squared norm. -/
theorem mixed_energy_of_open {f : ι → E → ℂ} {U : Set E} {x v w : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    dbar (fun y => dz (energy f) y v) x w =
      ∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v := by
  have hh : ∀ᶠ y in 𝓝 x, ∀ j, DifferentiableAt ℂ (f j) y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fun j => (hf j y hy).differentiableAt (hU.mem_nhds hy)
  have he : (fun y => dz (energy f) y v) =ᶠ[𝓝 x] numerator f v := by
    filter_upwards [hh] with y hy
    exact dz_energy (fun j => hy j)
  rw [dbar_congr_nhds he, dbar_numerator_of_open hU hx hf]

omit fintypeKappa in
lemma complexHessian_energy_eq_gram_of_open [Fintype κ] {f : ι → E → ℂ} {U : Set E} {x : E}
    (e : κ → E) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    complexHessian (energy f) x e = (jacobian f x e)ᴴ * jacobian f x e := by
  ext i j
  exact mixed_energy_of_open hU hx hf

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SpecialLeadingTerm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter Finset Asymptotics
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

lemma inverseLinearCoefficient_ne_zero : inverseLinearCoefficient ≠ 0 :=
  inverseF_deriv_ne_zero zero_mem_Omega

lemma analyticAt_inverseF_zero : AnalyticAt ℂ inverseF 0 :=
  differentiableOn_inverseF.analyticAt (isOpen_Omega.mem_nhds zero_mem_Omega)

lemma analyticAt_inverseF_dslope : AnalyticAt ℂ (dslope inverseF 0) 0 := by
  obtain ⟨p,hp⟩ := analyticAt_inverseF_zero
  exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩

lemma inverseF_factor (w : ℂ) : w*dslope inverseF 0 w = inverseF w := by
  simpa [smul_eq_mul,inverseF_zero] using sub_smul_dslope inverseF (0 : ℂ) w

/-- The exact univariate power has its asserted degree-m leading term and
an order-(m+1) remainder. The divided difference handles the origin. -/
theorem inverseF_power_leading (m : ℕ) :
    (fun w : ℂ => inverseF w^m-(inverseLinearCoefficient*w)^m) =O[𝓝 0]
      (fun w : ℂ => ‖w‖^(m+1)) := by
  have hd := (analyticAt_inverseF_dslope.pow m).differentiableAt.isBigO_sub
  have hm := (isBigO_refl (fun w : ℂ => w^m) (𝓝 0)).mul hd
  have he : ∀ w : ℂ, w^m*((dslope inverseF 0 w)^m-(dslope inverseF 0 0)^m) =
      inverseF w^m-(inverseLinearCoefficient*w)^m := by
    intro w
    rw [mul_sub,← mul_pow,inverseF_factor,dslope_same]
    simp only [inverseLinearCoefficient,mul_pow]
    ring
  simpa only [Pi.pow_apply,he,sub_zero,norm_mul,norm_pow,pow_succ] using hm.norm_right

lemma specialLeadingPolynomial_eval (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (j : Fin N) (z : Fin n → ℂ) :
    MvPolynomial.eval z (specialLeadingPolynomial A m j) = specialLeadingMap A m z j := by
  simp [specialLeadingPolynomial,specialLeadingMap,complexRow_apply,Finset.mul_sum,mul_assoc]

lemma specialLeadingPolynomial_homogeneous (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) (j : Fin N) :
    (specialLeadingPolynomial A m j).IsHomogeneous m := by
  have h : (∑ i : Fin n, MvPolynomial.C (inverseLinearCoefficient*(A j i : ℂ))*MvPolynomial.X i).IsHomogeneous 1 := by
    exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa only [specialLeadingPolynomial,one_mul] using h.pow m

/-- The leading homogeneous map is nonzero away from zero whenever the rows
have full rank. This includes every coordinate, rather than a scalar slice. -/
theorem specialLeadingMap_eq_zero_iff (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    (z : Fin n → ℂ) : specialLeadingMap A m z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply complexRow_injective A hA
    funext j
    have hp : (inverseLinearCoefficient*complexRow A j z)^m = 0 := congrFun h j
    have hr : complexRow A j z = 0 := by
      by_contra hn
      exact (pow_ne_zero m (mul_ne_zero inverseLinearCoefficient_ne_zero hn)) hp
    simpa using hr
  · rintro rfl
    funext j
    simp [specialLeadingMap,hm.ne']

/-- The special holomorphic map has the homogeneous leading
map, with a norm-controlled order-(m+1) error in all complex variables. -/
theorem specialMap_leading_remainder (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    (fun z : Fin n → ℂ => specialMap A m z-specialLeadingMap A m z) =O[𝓝 0]
      (fun z : Fin n → ℂ => ‖z‖^(m+1)) := by
  apply isBigO_pi.mpr
  intro j
  have hrow : Tendsto (complexRow A j) (𝓝 0) (𝓝 0) := by
    simpa using (complexRow A j).continuous.tendsto (0 : Fin n → ℂ)
  have h := (inverseF_power_leading m).comp_tendsto hrow
  have hr := ((complexRow A j).isBigO_id (𝓝 (0 : Fin n → ℂ))).norm_norm.pow (m+1)
  exact h.trans hr

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripRankGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SymmetricMahler
open Set Finset Complex
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

omit fintypeJ in
lemma stripCoordinate_injective [Fintype J] (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) : Function.Injective (stripCoordinate A) := by
  intro z w h
  apply Prod.ext
  · apply hA
    funext j
    have := congrArg Complex.re (congrFun h j)
    simpa [stripCoordinate] using this
  · apply hA
    funext j
    have := congrArg Complex.im (congrFun h j)
    simpa [stripCoordinate] using this

/-- Rank n implies properness of the full complexified matrix. -/
theorem stripCoordinate_isClosedEmbedding (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) :
    Topology.IsClosedEmbedding (stripCoordinate A) :=
  (stripCoordinateLinear A).isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr (stripCoordinate_injective A hA))

/-- Compact coordinate constraints have compact inverse image, with no
additional boundedness assumption on z. -/
theorem stripCoordinate_compact_preimage (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {K : Set (J → ℂ)} (hK : IsCompact K) :
    IsCompact (stripCoordinate A ⁻¹' K) :=
  (stripCoordinate_isClosedEmbedding A hA).isCompact_preimage hK

lemma stripCoordinate_eq_zero_iff (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {z : (I → ℝ) × (I → ℝ)} :
    stripCoordinate A z = 0 ↔ z = 0 := by
  rw [← stripCoordinate_zero A]
  exact (stripCoordinate_injective A hA).eq_iff

@[simp] lemma zero_mem_stripDomain (A : J → I → ℝ) :
    (0 : (I → ℝ) × (I → ℝ)) ∈ stripDomain A := by
  intro j
  simpa only [stripCoordinate_zero, Pi.zero_apply] using zero_mem_Omega

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripCompactSublevels
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact-sublevel property, with no regular-value
or compactness premise, for stripTau and stripDomain. -/
noncomputable section
namespace SymmetricMahler
open Set Finset Complex Metric Real
open MahlerConformal
variable {I J : Type*} [Fintype I] [Fintype J]

lemma stripTau_term_le (A : J → I → ℝ) (m : ℕ)
    (z : (I → ℝ) × (I → ℝ)) (j : J) :
    ‖inverseF (stripCoordinate A z j)‖ ^ (2 * (m : ℝ)) ≤ stripTau A m z := by
  unfold stripTau
  exact single_le_sum (fun k _ => Real.rpow_nonneg (norm_nonneg (inverseF (stripCoordinate A z k))) _) (mem_univ j)

/-- The coordinate bound using a closed disk
of radius R^(1/(2m)). -/
theorem strip_sublevel_coordinate_bound (A : J → I → ℝ) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) {z : (I → ℝ) × (I → ℝ)}
    (hz : z ∈ stripDomain A) (hτ : stripTau A m z ≤ R) (j : J) :
    stripCoordinate A z j ∈ F '' closedBall (0 : ℂ) (R ^ (2 * (m : ℝ))⁻¹) := by
  refine ⟨inverseF (stripCoordinate A z j), ?_, inverseF_right (hz j)⟩
  rw [mem_closedBall_zero_iff]
  exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hR (by positivity)).mpr
    ((stripTau_term_le A m z j).trans hτ)

lemma strip_radius_lt_one {m : ℕ} (hm : 0 < m) {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    R ^ (2 * (m : ℝ))⁻¹ < 1 := by
  exact (Real.rpow_lt_one_iff' hR (by positivity)).mpr hR1

lemma strip_disk_compact {m : ℕ} (hm : 0 < m) {R : ℝ}
    (hR : 0 ≤ R) (hR1 : R < 1) :
    IsCompact (F '' closedBall (0 : ℂ) (R ^ (2 * (m : ℝ))⁻¹)) ∧
    F '' closedBall (0 : ℂ) (R ^ (2 * (m : ℝ))⁻¹) ⊆ Omega := by
  have hs : closedBall (0 : ℂ) (R ^ (2 * (m : ℝ))⁻¹) ⊆ ball (0 : ℂ) 1 :=
    closedBall_subset_ball (strip_radius_lt_one hm hR hR1)
  exact ⟨(isCompact_closedBall _ _).image_of_continuousOn (differentiableOn_F.continuousOn.mono hs),
    image_mono hs⟩

/-- Rank gives a compact subset of U containing the closed
R-sublevel. The compact set is the inverse image of the product
of the F-images of closed disks. -/
theorem strip_sublevel_compact_container (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    ∃ K : Set ((I → ℝ) × (I → ℝ)), IsCompact K ∧ K ⊆ stripDomain A ∧
      {z | z ∈ stripDomain A ∧ stripTau A m z ≤ R} ⊆ K := by
  let C := F '' closedBall (0 : ℂ) (R ^ (2 * (m : ℝ))⁻¹)
  have hC := strip_disk_compact hm hR hR1
  refine ⟨stripCoordinate A ⁻¹' {u : J → ℂ | ∀ j, u j ∈ C},
    stripCoordinate_compact_preimage A hA (isCompact_pi_infinite (fun _ => hC.1)), ?_, ?_⟩
  · intro z hz j
    exact hC.2 (hz j)
  · intro z hz j
    exact strip_sublevel_coordinate_bound A hm hR hz.1 hz.2 j

/-- The compact-sublevel mass hypothesis holds for the
finite-strip construction for every 0<R<1. Closure is ambient closure,
and is contained in the open domain. -/
theorem strip_sublevel_compact_closure (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsCompact (closure {z | z ∈ stripDomain A ∧ stripTau A m z < R}) ∧
      closure {z | z ∈ stripDomain A ∧ stripTau A m z < R} ⊆ stripDomain A := by
  obtain ⟨K, hK, hKU, hsub⟩ := strip_sublevel_compact_container A hA hm hR.le hR1
  have hs : {z | z ∈ stripDomain A ∧ stripTau A m z < R} ⊆ K :=
    fun z hz => hsub ⟨hz.1, hz.2.le⟩
  have hc := closure_minimal hs hK.isClosed
  exact ⟨hK.of_isClosed_subset isClosed_closure hc, hc.trans hKU⟩

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripSublevelTopology
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Topological and rank properties of the finite-strip
sublevels. No differential, Jacobian or change-of-variables result is assumed. -/
noncomputable section
namespace SymmetricMahler
open Set Finset Complex Metric Real
open scoped Topology
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

lemma stripTau_eq_sum_pow (A : J → I → ℝ) (m : ℕ) (z : (I → ℝ) × (I → ℝ)) :
    stripTau A m z = ∑ j, ‖inverseF (stripCoordinate A z j)‖ ^ (2*m) := by
  simp only [stripTau, show 2 * (m : ℝ) = ((2*m : ℕ) : ℝ) by norm_cast,
    Real.rpow_natCast]

/-- The literal tau is exactly the squared Euclidean norm of the displayed
holomorphic vector f_j = h((Az)_j)^m, expressed as a coordinate sum. -/
theorem stripTau_eq_sum_norm_sq (A : J → I → ℝ) (m : ℕ)
    (z : (I → ℝ) × (I → ℝ)) :
    stripTau A m z = ∑ j, ‖inverseF (stripCoordinate A z j) ^ m‖ ^ 2 := by
  simp [stripTau_eq_sum_pow, norm_pow, ← pow_mul, Nat.mul_comm]

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SymmetricMahler
open Set Finset Complex Metric Real
open MahlerConformal
variable {I J : Type*} [Fintype I] [Fintype J]

lemma stripTau_zero (A : J → I → ℝ) {m : ℕ} (hm : 0 < m) :
    stripTau A m 0 = 0 := by
  simp [stripTau_eq_sum_pow, stripCoordinate_zero, inverseF_zero, hm.ne']

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SpecialMassHypotheses
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter Finset Asymptotics
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

lemma specialTau_eq_stripTau (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) (z : Fin n → ℂ) :
    specialTau A m z = stripTau A m (complexToReal z) := by
  simpa only [specialTau,specialMap,complexRow_eq_stripCoordinate] using!
    (stripTau_eq_sum_norm_sq (fun j i => A j i) m (complexToReal z)).symm

/-- The compact-closure premise transfers to actual complex coordinates. -/
theorem specialTau_compact_closure (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsCompact (closure {z | z ∈ complexStripDomain A ∧ specialTau A m z < R}) ∧
      closure {z | z ∈ complexStripDomain A ∧ specialTau A m z < R} ⊆ complexStripDomain A := by
  have h := strip_sublevel_compact_closure A hA hm hR hR1
  let S := {z | z ∈ stripDomain A ∧ stripTau A m z < R}
  let K := (complexRealEquiv (n := n)) ⁻¹' closure S
  have hK : IsCompact K := complexRealEquiv.toHomeomorph.isCompact_preimage.mpr h.1
  have hs : {z | z ∈ complexStripDomain A ∧ specialTau A m z < R} ⊆ K := by
    intro z hz
    apply subset_closure
    have hu := hz.1
    rw [complexStripDomain_eq_preimage] at hu
    exact ⟨hu,by
      change stripTau A m (complexToReal z) < R
      simpa only [specialTau_eq_stripTau] using hz.2⟩
  have hclosure := closure_minimal hs hK.isClosed
  refine ⟨hK.of_isClosed_subset isClosed_closure hclosure,?_⟩
  intro z hz
  have hmem : complexToReal z ∈ closure S := hclosure hz
  rw [complexStripDomain_eq_preimage]
  exact h.2 hmem

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_EuclideanSpecialMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter Finset Asymptotics
open scoped Topology
variable {n N : ℕ}

lemma euclideanSpecialTau (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Mahler.ComplexEuclidean n) :
    Mahler.tau (euclideanSpecialMap A m) z = specialTau A m (euclideanCoordinates z) := by
  simp only [Mahler.tau,euclideanSpecialMap,specialTau,Complex.normSq_eq_norm_sq]

lemma differentiableOn_euclideanSpecialMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (j : Fin N) : DifferentiableOn ℂ (euclideanSpecialMap A m j) (euclideanStripDomain A) := by
  have h := differentiableOn_pi.mp (differentiableOn_specialMap A m) j
  exact h.comp euclideanCoordinates.differentiable.differentiableOn (fun z hz => hz)

lemma euclideanSpecial_remainder (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    IsBigO (𝓝[≠] (0 : Mahler.ComplexEuclidean n))
      (fun z => (WithLp.toLp 2 (fun j => euclideanSpecialMap A m j z -
        MvPolynomial.eval (fun i => z i) (specialLeadingPolynomial A m j)) :
          Mahler.ComplexEuclidean N)) (fun z => ‖z‖ ^ (m + 1)) := by
  have ht : Tendsto (euclideanCoordinates (n := n)) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [map_zero] using
      ((euclideanCoordinates (n := n)).continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hcomp := (specialMap_leading_remainder A m).comp_tendsto ht
  have hnorm := (euclideanCoordinates.toContinuousLinearMap.isBigO_id
    (𝓝[≠] (0 : Mahler.ComplexEuclidean n))).norm_norm.pow (m+1)
  have hout := (euclideanCoordinates (n := N)).symm.isBigO_comp
    (fun z : Mahler.ComplexEuclidean n => specialMap A m (euclideanCoordinates z) -
      specialLeadingMap A m (euclideanCoordinates z)) (𝓝[≠] 0)
  have h := hout.trans (hcomp.trans hnorm)
  simpa only [euclideanSpecialMap,specialLeadingPolynomial_eval,euclideanCoordinates,
    PiLp.coe_continuousLinearEquiv,PiLp.coe_symm_continuousLinearEquiv,Pi.sub_apply] using! h

lemma euclideanSpecial_compact_closure (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsCompact (closure (euclideanStripDomain A ∩ {z | Mahler.tau (euclideanSpecialMap A m) z < R})) ∧
      closure (euclideanStripDomain A ∩ {z | Mahler.tau (euclideanSpecialMap A m) z < R}) ⊆
        euclideanStripDomain A := by
  have h := specialTau_compact_closure A hA hm hR hR1
  let S := {z | z ∈ complexStripDomain A ∧ specialTau A m z < R}
  let K := (euclideanCoordinates (n := n)) ⁻¹' closure S
  have hK : IsCompact K := euclideanCoordinates.toHomeomorph.isCompact_preimage.mpr h.1
  have hs : euclideanStripDomain A ∩ {z | Mahler.tau (euclideanSpecialMap A m) z < R} ⊆ K := by
    intro z hz
    apply subset_closure
    exact ⟨hz.1,by simpa only [euclideanSpecialTau,mem_ofPred_eq] using hz.2⟩
  have hclosure := closure_minimal hs hK.isClosed
  exact ⟨hK.of_isClosed_subset isClosed_closure hclosure,fun z hz => h.2 (hclosure hz)⟩

/-- The mass hypotheses hold
for the special map, including the Euclidean Taylor estimate. -/
theorem euclideanSpecial_massHypotheses (A : Matrix (Fin N) (Fin n) ℝ)
    (hn : 1 ≤ n) (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 2 ≤ m) :
    Mahler.MassHypotheses n N m (euclideanStripDomain A)
      (euclideanSpecialMap A m) (specialLeadingPolynomial A m) := by
  have hm0 : 0 < m := by omega
  refine ⟨hn,by omega,?_,?_,differentiableOn_euclideanSpecialMap A m,?_,
    specialLeadingPolynomial_homogeneous A m,?_,euclideanSpecial_remainder A m,?_⟩
  · exact (isOpen_complexStripDomain A).preimage euclideanCoordinates.continuous
  · change euclideanCoordinates 0 ∈ complexStripDomain A
    simpa only [map_zero] using zero_mem_complexStripDomain A
  · intro z hz
    have h := specialMap_eq_zero_iff A hA hm0 hz
    constructor
    · intro hf
      have he := h.mp (funext hf)
      exact euclideanCoordinates.injective (he.trans (map_zero _).symm)
    · intro hz0 j
      have he := h.mpr (by simp only [hz0,map_zero])
      exact congrFun he j
  · intro z hz
    by_contra h
    push Not at h
    have he : specialLeadingMap A m (euclideanCoordinates z) = 0 := by
      funext j
      simpa only [specialLeadingPolynomial_eval,euclideanCoordinates,PiLp.coe_continuousLinearEquiv,Pi.zero_apply] using! h j
    have hz0 := (specialLeadingMap_eq_zero_iff A hA hm0 _).mp he
    exact hz (euclideanCoordinates.injective (hz0.trans (map_zero _).symm))
  · intro R hR hR1
    exact euclideanSpecial_compact_closure A hA hm0 hR hR1

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SpecialJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Matrix Set Finset
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

/-- The actual holomorphic derivative, with its full m and h' factors. -/
theorem hasFDerivAt_specialMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    {z : Fin n → ℂ} (hz : z ∈ complexStripDomain A) :
    HasFDerivAt (specialMap A m) (specialDerivative A m z) z := by
  apply hasFDerivAt_pi.mpr
  intro j
  have hh : HasDerivAt inverseF (deriv inverseF (complexRow A j z)) (complexRow A j z) :=
    (hasDerivAt_inverseF (hz j)).differentiableAt.hasDerivAt
  have h := (hh.pow m).hasFDerivAt.comp z (complexRow A j).hasFDerivAt
  have hc : (ContinuousLinearMap.toSpanSingleton ℂ (specialRowFactor A m z j)).comp (complexRow A j) =
      specialRowFactor A m z j • complexRow A j := by
    ext v
    simp [smul_eq_mul,mul_comm]
  change HasFDerivAt (fun x => inverseF (complexRow A j x)^m)
    (specialRowFactor A m z j • complexRow A j) z
  rw [← hc]
  simpa only [Function.comp_def,Pi.pow_apply,specialRowFactor] using h

lemma specialJacobianMatrix_derivative (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Fin n → ℂ) (j : Fin N) (k : Fin n) :
    specialDerivative A m z (Pi.single k 1) j = specialJacobianMatrix A m z j k := by
  simp [specialDerivative,specialJacobianMatrix,complexRow_apply,Pi.single_apply]

lemma specialRowFactor_normSq (A : Matrix (Fin N) (Fin n) ℝ) {m : ℕ} (hm : 1 ≤ m)
    (z : Fin n → ℂ) (j : Fin N) :
    Complex.normSq (specialRowFactor A m z j) =
      hessianWeight m (inverseF (complexRow A j z)) (deriv inverseF (complexRow A j z)) := by
  have he : ((2*(m-1) : ℕ) : ℝ) = 2*(m : ℝ)-2 := by
    rw [Nat.cast_mul,Nat.cast_sub hm]
    norm_num
    ; ring
  unfold specialRowFactor hessianWeight
  rw [Complex.normSq_mul,Complex.normSq_mul,Complex.normSq_natCast,
    map_pow,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,← pow_mul,
    ← Real.rpow_natCast,he]
  ring

theorem specialJacobian_gram (A : Matrix (Fin N) (Fin n) ℝ) {m : ℕ} (hm : 1 ≤ m)
    (z : Fin n → ℂ) :
    (specialJacobianMatrix A m z).conjTranspose * specialJacobianMatrix A m z =
      (weightedGram A (fun j => hessianWeight m (inverseF (complexRow A j z))
        (deriv inverseF (complexRow A j z)))).map (algebraMap ℝ ℂ) := by
  ext i k
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,specialJacobianMatrix,map_mul,
    Matrix.map_apply,weightedGram_apply,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← specialRowFactor_normSq A hm z j]
  change star (specialRowFactor A m z j*(A j i : ℂ)) *
      (specialRowFactor A m z j*(A j k : ℂ)) =
      (A j i : ℂ)*(Complex.normSq (specialRowFactor A m z j) : ℂ)*(A j k : ℂ)
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
  ring

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SpecialMassBridge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Matrix Set Filter Finset MeasureTheory
open scoped Topology ENNReal
open MahlerConformal
variable {n N : ℕ}

lemma specialGramDet_eq_stripHessianDet (A : Matrix (Fin N) (Fin n) ℝ) {m : ℕ}
    (hm : 1 ≤ m) (z : Fin n → ℂ) :
    specialGramDet A m z = stripHessianDet A m (complexToReal z) := by
  unfold specialGramDet
  rw [specialJacobian_gram A hm z]
  have hd := (algebraMap ℝ ℂ).map_det
    (weightedGram A (fun j => hessianWeight m (inverseF (complexRow A j z))
      (deriv inverseF (complexRow A j z))))
  have hd' := congrArg Complex.re hd.symm
  simpa only [stripHessianDet,complexRow_eq_stripCoordinate,Complex.ofReal_re] using! hd'

lemma specialSublevel_eq_preimage (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    specialSublevel A m = complexToReal ⁻¹' stripSublevel A m := by
  ext z
  simp only [specialSublevel,stripSublevel,complexStripDomain_eq_preimage,
    specialTau_eq_stripTau,mem_ofPred_eq,Set.mem_preimage,mem_inter_iff]

lemma measurableEmbedding_complexToReal : MeasurableEmbedding (complexToReal (n := n)) :=
  complexRealEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding

theorem specialGram_integral_eq (A : Matrix (Fin N) (Fin n) ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (∫⁻ z in specialSublevel A m, ENNReal.ofReal (specialGramDet A m z)) =
      ∫⁻ z in stripSublevel A m, ENNReal.ofReal (stripHessianDet A m z) := by
  rw [specialSublevel_eq_preimage]
  simp_rw [specialGramDet_eq_stripHessianDet A hm]
  simpa using! (volume_preserving_complexToReal (n := n)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_complexToReal (n := n))
    (fun z => ENNReal.ofReal (stripHessianDet A m z)) (stripSublevel A m)

/-- The n! factor converts the complex mass inequality into
the mass premise for the finite-strip reduction. -/
theorem stripMassBound_of_special_gram_mass (A : Matrix (Fin N) (Fin n) ℝ)
    {m : ℕ} (hm : 2 ≤ m)
    (hmass : ENNReal.ofReal ((Real.pi*(m : ℝ))^n) ≤
      ∫⁻ z in specialSublevel A m, ENNReal.ofReal ((Nat.factorial n : ℝ)*specialGramDet A m z)) :
    StripMassBound A m := by
  have hf : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  have hI : (∫⁻ z in specialSublevel A m, ENNReal.ofReal ((Nat.factorial n : ℝ)*specialGramDet A m z)) =
      ENNReal.ofReal (Nat.factorial n : ℝ)*
        (∫⁻ z in stripSublevel A m, ENNReal.ofReal (stripHessianDet A m z)) := by
    simp_rw [ENNReal.ofReal_mul hf.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,specialGram_integral_eq A (by omega)]
  rw [hI] at hmass
  apply (ENNReal.mul_le_mul_iff_right (show ENNReal.ofReal (Nat.factorial n : ℝ) ≠ 0 by positivity)
    ENNReal.ofReal_ne_top).mp
  rw [← ENNReal.ofReal_mul hf.le]
  have he : (Nat.factorial n : ℝ)*((Real.pi*(m : ℝ))^n/(Nat.factorial n : ℝ)) =
      (Real.pi*(m : ℝ))^n := by field_simp
  rw [he]
  exact hmass

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_EuclideanMassDensity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Matrix Set MeasureTheory
open scoped Topology ENNReal
variable {n N : ℕ}

lemma euclideanSpecial_jacobian (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    {z : Mahler.ComplexEuclidean n} (hz : z ∈ euclideanStripDomain A) :
    Mahler.jacobian (euclideanSpecialMap A m) z
      (fun i => EuclideanSpace.single i (1 : ℂ)) =
        specialJacobianMatrix A m (euclideanCoordinates z) := by
  ext j k
  have hj := hasFDerivAt_pi.mp (hasFDerivAt_specialMap A m hz) j
  have hd := hj.comp z euclideanCoordinates.hasFDerivAt
  change HasFDerivAt (euclideanSpecialMap A m j) _ z at hd
  change fderiv ℂ (euclideanSpecialMap A m j) z (EuclideanSpace.single k 1) = _
  rw [hd.fderiv]
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    euclideanCoordinates,PiLp.coe_continuousLinearEquiv,PiLp.ofLp_single] using!
      specialJacobianMatrix_derivative A m (euclideanCoordinates z) j k

/-- The complex Hessian has precisely the
n! times Gram-determinant density used in the finite-strip mass bridge. -/
theorem euclideanSpecial_massDensity (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    {z : Mahler.ComplexEuclidean n} (hz : z ∈ euclideanStripDomain A) :
    Mahler.massDensity (euclideanSpecialMap A m) z =
      (Nat.factorial n : ℝ) * specialGramDet A m (euclideanCoordinates z) := by
  unfold Mahler.massDensity Mahler.sourceHessian
  rw [Matrix.det_transpose,Mahler.complexHessian_energy_eq_gram_of_open
    (fun i => EuclideanSpace.single i (1 : ℂ))
    ((isOpen_complexStripDomain A).preimage euclideanCoordinates.continuous) hz
    (differentiableOn_euclideanSpecialMap A m),euclideanSpecial_jacobian A m hz]
  rfl

/-- Measure transport converts the complex Euclidean mass integral
to the real-coordinate integral. The integrands and domains are
those of the general mass theorem and the finite-strip construction. -/
theorem euclideanSpecial_massIntegral
    (hvolume : MeasurePreserving (euclideanCoordinates (n := n)))
    (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    Mahler.massIntegral (euclideanStripDomain A) (euclideanSpecialMap A m) =
      ∫⁻ z in specialSublevel A m,
        ENNReal.ofReal ((Nat.factorial n : ℝ) * specialGramDet A m z) := by
  have hset : euclideanStripDomain A ∩ {z | Mahler.tau (euclideanSpecialMap A m) z < 1} =
      euclideanCoordinates ⁻¹' specialSublevel A m := by
    ext z
    simp only [euclideanStripDomain,specialSublevel,euclideanSpecialTau,
      mem_inter_iff,Set.mem_preimage,mem_ofPred_eq]
  have hmeas : MeasurableSet (euclideanStripDomain A ∩
      {z | Mahler.tau (euclideanSpecialMap A m) z < 1}) := by
    rw [hset,specialSublevel_eq_preimage]
    exact (isOpen_stripSublevel A m).measurableSet.preimage
      (complexRealEquiv.continuous.comp euclideanCoordinates.continuous).measurable
  unfold Mahler.massIntegral
  calc
    _ = ∫⁻ z in euclideanStripDomain A ∩ {z | Mahler.tau (euclideanSpecialMap A m) z < 1},
        ENNReal.ofReal ((Nat.factorial n : ℝ) * specialGramDet A m (euclideanCoordinates z)) := by
      apply setLIntegral_congr_fun hmeas
      intro z hz
      dsimp only
      rw [euclideanSpecial_massDensity A m hz.1]
    _ = _ := by
      rw [hset]
      simpa using! hvolume.setLIntegral_comp_preimage_emb
        euclideanCoordinates.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun z => ENNReal.ofReal ((Nat.factorial n : ℝ) * specialGramDet A m z))
        (specialSublevel A m)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_InverseRadialRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Complex Set Metric
namespace MahlerConformal

/-- The derivative in the outward radial direction, at a point of Omega. -/
theorem hasDerivAt_inverseRadius_radial {u : ℂ} (hu : u ∈ Omega) :
    HasDerivAt (fun t : ℝ => Complex.normSq (inverseF ((t : ℂ)*u)))
      (inverseRadiusRadialSlope u) 1 := by
  have hl : HasDerivAt (fun t : ℂ => t*u) u (1 : ℂ) := by
    simpa using (hasDerivAt_id (1 : ℂ)).mul_const u
  have hi : HasDerivAt inverseF (deriv F (inverseF u))⁻¹ ((fun t : ℂ => t*u) 1) := by
    simpa using hasDerivAt_inverseF hu
  have hf := (hi.comp (1 : ℂ) hl).comp_ofReal
  have hn := hasDerivAt_normSq hf
  simp only [Function.comp_apply, Complex.ofReal_one, one_mul] at hn
  convert hn using 1 ; try rfl
  unfold inverseRadiusRadialSlope
  rw [← div_eq_inv_mul]
  simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.normSq_eq_norm_sq]
  ring

theorem inverseRadiusRadialSlope_pos {u : ℂ} (hu : u ∈ Omega) (hu0 : u ≠ 0) :
    0 < inverseRadiusRadialSlope u := by
  have hw := inverseF_mem hu
  have hw0 : inverseF u ≠ 0 := (inverseF_eq_zero_iff hu).not.mpr hu0
  have hp := F_radial_pairing_pos (by simpa using hw) hw0
  rw [inverseF_right hu] at hp
  exact div_pos (mul_pos (by norm_num) hp)
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (deriv_F_ne_zero (by simpa using hw))))

theorem inverseRadiusRadialSlope_nonneg {u : ℂ} (hu : u ∈ Omega) :
    0 ≤ inverseRadiusRadialSlope u := by
  by_cases h : u = 0
  · simp [h]
  · exact (inverseRadiusRadialSlope_pos hu h).le

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripRegularValues
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular positive levels of the literal strip tau. This specializes the
regular-value step to the actual conformal map; it is not a general Sard theorem. -/
noncomputable section
namespace SymmetricMahler
open Set Finset Complex
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

lemma stripTau_eq_sum_normSq_pow (A : J → I → ℝ) (m : ℕ)
    (z : (I → ℝ) × (I → ℝ)) :
    stripTau A m z = ∑ j, Complex.normSq (inverseF (stripCoordinate A z j)) ^ m := by
  simp [stripTau_eq_sum_pow, pow_mul, Complex.normSq_eq_norm_sq]

omit fintypeJ in
lemma stripCoordinate_real_smul [Fintype J] (A : J → I → ℝ) (t : ℝ)
    (z : (I → ℝ) × (I → ℝ)) (j : J) :
    stripCoordinate A (t • z) j = (t : ℂ) * stripCoordinate A z j := by
  have h := congrFun ((stripCoordinateLinear A).map_smul t z) j
  change stripCoordinate A (t • z) j = t • stripCoordinate A z j at h
  simpa only [Complex.real_smul] using h

theorem hasDerivAt_stripTau_radial (A : J → I → ℝ) (m : ℕ)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) :
    HasDerivAt (fun t : ℝ => stripTau A m (t • z)) (stripTauRadialSlope A m z) 1 := by
  simp_rw [stripTau_eq_sum_normSq_pow, stripCoordinate_real_smul]
  unfold stripTauRadialSlope
  convert (HasDerivAt.sum (u := Finset.univ) (fun j _ => by
    simpa using (hasDerivAt_inverseRadius_radial (hz j)).pow m)) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals (ext t; simp)

theorem stripTauRadialSlope_pos (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) (hz0 : z ≠ 0) :
    0 < stripTauRadialSlope A m z := by
  have hn : ∃ j, stripCoordinate A z j ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 ((stripCoordinate_eq_zero_iff A hA).mp (funext h))
  obtain ⟨j, hj⟩ := hn
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Complex.normSq_nonneg _) _))
      (inverseRadiusRadialSlope_nonneg (hz k))
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    exact mul_pos (mul_pos (by exact_mod_cast hm)
      (pow_pos (Complex.normSq_pos.mpr ((inverseF_eq_zero_iff (hz j)).not.mpr hj)) _))
      (inverseRadiusRadialSlope_pos (hz j) hj)

theorem differentiableAt_stripTau (A : J → I → ℝ) (m : ℕ)
    {z : (I → ℝ) × (I → ℝ)} (hz : z ∈ stripDomain A) :
    DifferentiableAt ℝ (stripTau A m) z := by
  have hcoord : DifferentiableAt ℝ (stripCoordinate A) z :=
    (stripCoordinateLinear A).toContinuousLinearMap.differentiableAt
  have hinv : ∀ j, DifferentiableAt ℝ (fun z => inverseF (stripCoordinate A z j)) z := by
    intro j
    exact ((hasDerivAt_inverseF (hz j)).differentiableAt.restrictScalars ℝ).comp z
      ((ContinuousLinearMap.proj j : (J → ℂ) →L[ℝ] ℂ).differentiableAt.comp z hcoord)
  have heq : stripTau A m = fun z =>
      ∑ j, Complex.normSq (inverseF (stripCoordinate A z j)) ^ m := by
    funext z
    exact stripTau_eq_sum_normSq_pow A m z
  rw [heq]
  have hs : ∀ j, DifferentiableAt ℝ
      (fun z => Complex.normSq (inverseF (stripCoordinate A z j)) ^ m) z := by
    intro j
    have h := hinv j
    simp only [Complex.normSq_apply]
    fun_prop
  convert (DifferentiableAt.sum (u := Finset.univ) (fun j _ => hs j)) using 1
  all_goals try with_reducible_and_instances rfl
  all_goals (ext x; simp)

/-- Every positive value of the actual tau is regular. The derivative is
surjective onto the real scalars, the standard regular-value condition. -/
theorem stripTau_positive_regular (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) {z : (I → ℝ) × (I → ℝ)}
    (hz : z ∈ stripDomain A) (hlevel : stripTau A m z = R) :
    Function.Surjective (fderiv ℝ (stripTau A m) z) := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    rw [stripTau_zero A hm] at hlevel
    linarith
  have hl : HasDerivAt (fun t : ℝ => t • z) z 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).smul_const z)
  have hf : HasFDerivAt (stripTau A m) (fderiv ℝ (stripTau A m) z) ((1 : ℝ) • z) := by
    simpa using (differentiableAt_stripTau A m hz).hasFDerivAt
  have hd := hf.comp_hasDerivAt 1 hl
  have he : (fderiv ℝ (stripTau A m) z) z = stripTauRadialSlope A m z := by
    simpa using hd.unique (hasDerivAt_stripTau_radial A m hz)
  have hp := stripTauRadialSlope_pos A hA hm hz hz0
  intro y
  refine ⟨(y / stripTauRadialSlope A m z) • z, ?_⟩
  rw [map_smul, he]
  change y / stripTauRadialSlope A m z * stripTauRadialSlope A m z = y
  exact div_mul_cancel₀ y hp.ne'

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripMassExhaustion
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit regular-level exhaustion and
continuity from below for arbitrary nonnegative mass densities. -/
noncomputable section
namespace SymmetricMahler
open Set Filter MeasureTheory
open scoped Topology ENNReal
variable {I J : Type*} [Fintype I] [Fintype J]

lemma stripRegularLevel_mem (k : ℕ) : stripRegularLevel k ∈ Ioo (0 : ℝ) 1 := by
  have hp : 0 < (1/2 : ℝ)^k := pow_pos (by norm_num) _
  have hle : (1/2 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor <;> dsimp [stripRegularLevel] <;> nlinarith

lemma tendsto_stripRegularLevel : Tendsto stripRegularLevel atTop (𝓝 1) := by
  have hp : Tendsto (fun k : ℕ => (1/2 : ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Tendsto (fun k : ℕ => 1 - (1/2 : ℝ) * (1/2 : ℝ)^k) atTop (𝓝 1)
  simpa only [mul_zero, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub (hp.const_mul (1/2 : ℝ))

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_EuclideanRegularLevels
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Set Filter
open scoped Topology
variable {n N : ℕ}

lemma euclideanTau_eq_real (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z : Mahler.ComplexEuclidean n) :
    Mahler.tau (euclideanSpecialMap A m) z = stripTau A m (euclideanRealCoordinates z) := by
  rw [euclideanSpecialTau,specialTau_eq_stripTau]
  rfl

lemma euclideanDomain_eq_real (A : Matrix (Fin N) (Fin n) ℝ) :
    euclideanStripDomain A = euclideanRealCoordinates ⁻¹' stripDomain A := by
  ext z
  change euclideanCoordinates z ∈ complexStripDomain A ↔ _
  rw [complexStripDomain_eq_preimage]
  rfl

/-- Every positive level remains regular in the exact Euclidean coordinates
used by the mass theorem. This uses the actual special map, without Sard. -/
theorem euclideanSpecial_positive_regular (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) {z : Mahler.ComplexEuclidean n}
    (hz : z ∈ euclideanStripDomain A) (hlevel : Mahler.tau (euclideanSpecialMap A m) z = R) :
    Function.Surjective (fderiv ℝ (Mahler.tau (euclideanSpecialMap A m)) z) := by
  have hzr : euclideanRealCoordinates z ∈ stripDomain A := by
    simpa only [euclideanDomain_eq_real,mem_preimage] using hz
  have hder := (differentiableAt_stripTau A m hzr).hasFDerivAt.comp z
    euclideanRealCoordinates.hasFDerivAt
  have he : Mahler.tau (euclideanSpecialMap A m) =
      fun w => stripTau A m (euclideanRealCoordinates w) := funext (euclideanTau_eq_real A m)
  have hder' : HasFDerivAt (Mahler.tau (euclideanSpecialMap A m))
      ((fderiv ℝ (stripTau A m) (euclideanRealCoordinates z)).comp
        euclideanRealCoordinates.toContinuousLinearMap) z := by
    simpa only [Function.comp_def,← euclideanTau_eq_real] using! hder
  rw [hder'.fderiv]
  have hr := stripTau_positive_regular A hA hm hR hzr
    (by simpa only [euclideanTau_eq_real] using hlevel)
  exact hr.comp euclideanRealCoordinates.surjective

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_MassLimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
open Set MeasureTheory Filter
open scoped Topology ENNReal
variable {n N : ℕ}

lemma massBelow_mono (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) : Monotone (massBelow U f) := by
  intro R S hRS
  apply lintegral_mono_set
  intro z hz
  exact ⟨hz.1,hz.2.trans_le hRS⟩

lemma massBelow_one (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) : massBelow U f 1 = massIntegral U f := rfl

/-- Lower bounds on a sublevel sequence tending to one
imply the mass bound, even if the final integral is infinite.
The sublevel bounds are explicit hypotheses. -/
theorem massIntegral_lower_of_sublevels (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) (m : ℕ) {R : ℕ → ℝ}
    (hR : Tendsto R atTop (𝓝 1)) (hR1 : ∀ k, R k ≤ 1)
    (hbound : ∀ k, ENNReal.ofReal ((R k)^n * (Real.pi * (m : ℝ))^n) ≤ massBelow U f (R k)) :
    ENNReal.ofReal ((Real.pi * (m : ℝ))^n) ≤ massIntegral U f := by
  have hlim : Tendsto (fun k => ENNReal.ofReal ((R k)^n * (Real.pi * (m : ℝ))^n))
      atTop (𝓝 (ENNReal.ofReal ((Real.pi * (m : ℝ))^n))) := by
    simpa only [one_pow,one_mul] using ENNReal.tendsto_ofReal
      ((hR.pow n).mul_const ((Real.pi * (m : ℝ))^n))
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro k
  exact (hbound k).trans ((massBelow_mono U f (hR1 k)).trans_eq (massBelow_one U f))

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SpecialSourceMass
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SymmetricMahler

/-- The Stokes regularity condition holds for every positive level
of the finite-strip special map. -/
theorem euclideanSpecial_positive_regular_nonzero {n N m : ℕ}
    (A : Matrix (Fin N) (Fin n) ℝ) (hA : Function.Injective (measurement A))
    (hm : 0 < m) {R : ℝ} (hR : 0 < R)
    {z : Mahler.ComplexEuclidean n} (hz : z ∈ euclideanStripDomain A)
    (hlevel : Mahler.tau (euclideanSpecialMap A m) z = R) :
    fderiv ℝ (Mahler.tau (euclideanSpecialMap A m)) z ≠ 0 := by
  intro he
  obtain ⟨v,hv⟩ := euclideanSpecial_positive_regular A hA hm hR hz hlevel (1:ℝ)
  rw [he] at hv
  simp at hv

theorem special_regular_mass_of_source_flux_limit {n N m : ℕ}
    (A : Matrix (Fin N) (Fin (n+1)) ℝ) (hA : Function.Injective (measurement A))
    (hm : 2 ≤ m) (k : ℕ)
    (hlimit : Tendsto
      (fun r => MahlerStokes.sphereFlux r
        (Mahler.sourceCoordinateForm (Mahler.sourceCoordinates n)
          (Mahler.logTau (euclideanSpecialMap A m)) n))
      (𝓝[>] (0:ℝ)) (𝓝 ((Real.pi*(m:ℝ))^(n+1)))) :
    SpecialRegularMassBound A m k := by
  exact Mahler.source_regular_massBelow_of_flux_limit_eq
    (euclideanSpecial_massHypotheses A (by omega) hA hm)
    (stripRegularLevel_mem k).1 (stripRegularLevel_mem k).2
    (fun z hz he => euclideanSpecial_positive_regular_nonzero A hA (by omega)
      (stripRegularLevel_mem k).1 hz he) hlimit

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Lens
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Filter MeasureTheory
open scoped Topology ENNReal Pointwise

lemma unconditional_stripMassBound {n N : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin N) (Fin n) ℝ) (hA : Function.Injective (measurement A))
    {m : ℕ} (hm : 2 ≤ m) : StripMassBound A m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply stripMassBound_of_special_gram_mass A hm
  have hspecial := euclideanSpecial_massHypotheses A (by omega) hA hm
  have hvalue := hspecial.homogeneousSphereFlux_value_eq
  have hregular (j : ℕ) : SpecialRegularMassBound A m j := by
    apply special_regular_mass_of_source_flux_limit A hA hm j
    simpa only [hvalue] using hspecial.sourceCoordinateFlux_limit_eq
  have h := Mahler.massIntegral_lower_of_sublevels (euclideanStripDomain A)
    (euclideanSpecialMap A m) m tendsto_stripRegularLevel
    (fun j => (stripRegularLevel_mem j).2.le) hregular
  rwa [euclideanSpecial_massIntegral (volume_preserving_complex_ofLp (k+1)) A m] at h

lemma stripMap_volume_lower {n N : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin N) (Fin n) ℝ) (hA : Function.Injective (measurement A))
    {m : ℕ} (hm : 2 ≤ m) :
    ENNReal.ofReal ((4:ℝ)^n / (Nat.factorial n : ℝ)) ≤
      volume (stripMap A m '' stripSublevel A m) := by
  have hmass := unconditional_stripMassBound hn A hA hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpm : 0 < Real.pi*(m:ℝ) := mul_pos Real.pi_pos hm0
  have hc : 0 ≤ (4/(Real.pi*(m:ℝ)))^n := by positivity
  have he : (4/(Real.pi*(m:ℝ)))^n * ((Real.pi*(m:ℝ))^n/(Nat.factorial n:ℝ)) =
      (4:ℝ)^n/(Nat.factorial n:ℝ) := by
    rw [← mul_div_assoc, ← mul_pow, div_mul_cancel₀ _ hpm.ne']
  rw [stripMap_volume_eq_eq A hA hm]
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ = ENNReal.ofReal ((4/(Real.pi*(m:ℝ)))^n) *
        ENNReal.ofReal ((Real.pi*(m:ℝ))^n/(Nat.factorial n:ℝ)) := by
          rw [← ENNReal.ofReal_mul hc, he]
    _ ≤ _ := mul_le_mul le_rfl hmass (by positivity) (by positivity)

end SymmetricMahler

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace SymmetricMahler

lemma nonempty_inter_of_small_deficit {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {A S U : Set α} (hS : S ⊆ A) (hU : U ⊆ A)
    (hUm : MeasurableSet U) {M : ℝ≥0∞}
    (hM : M ≤ μ S) (hgap : μ A < M + μ U) : (S ∩ U).Nonempty := by
  by_contra hn
  have hdis : Disjoint S U := Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hn)
  have hunion : μ S + μ U = μ (S ∪ U) := (measure_union hdis hUm).symm
  have hle : M + μ U ≤ μ A := by
    calc
      M + μ U ≤ μ S + μ U := add_le_add hM le_rfl
      _ = μ (S ∪ U) := hunion
      _ ≤ μ A := measure_mono (union_subset hS hU)
  exact (not_lt_of_ge hle) hgap

lemma eventually_nonempty_inter_of_saturation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A S : ℕ → Set α) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hSA : ∀ j, S j ⊆ A j) (hvol : ∀ j, M ≤ μ (S j))
    (hlim : Tendsto (fun j => μ (A j)) atTop (𝓝 M))
    {U : Set α} (hU : MeasurableSet U) (hUpos : 0 < μ U)
    (hUA : ∀ᶠ j in atTop, U ⊆ A j) :
    ∀ᶠ j in atTop, (S j ∩ U).Nonempty := by
  have hlt : M < M + μ U := ENNReal.lt_add_right hM hUpos.ne'
  have he := hlim.eventually (Iio_mem_nhds hlt)
  filter_upwards [he,hUA] with j hj hUj
  exact nonempty_inter_of_small_deficit μ (hSA j) hUj hU (hvol j) hj

lemma exists_nearby_image_of_saturation {α : Type*} [MetricSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [Measure.IsOpenPosMeasure μ]
    (A S : ℕ → Set α) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hSA : ∀ j, S j ⊆ A j) (hvol : ∀ j, M ≤ μ (S j))
    (hlim : Tendsto (fun j => μ (A j)) atTop (𝓝 M))
    {x : α} (hpersist : ∀ ε > 0, ∃ U : Set α, IsOpen U ∧ U.Nonempty ∧
      U ⊆ ball x ε ∧ ∀ᶠ j in atTop, U ⊆ A j)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j ≥ k, ∃ z ∈ S j, dist z x < ε := by
  obtain ⟨U,hU,hUn,hUB,hUA⟩ := hpersist ε hε
  have he := eventually_nonempty_inter_of_saturation μ A S hM hSA hvol hlim
    hU.measurableSet (hU.measure_pos μ hUn) hUA
  obtain ⟨j,hjk,hj⟩ := (he.and (eventually_ge_atTop k)).exists
  obtain ⟨z,hzS,hzU⟩ := hjk
  exact ⟨j,hj,z,hzS,hUB hzU⟩

lemma exists_sequence_of_saturation {α : Type*} [MetricSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [Measure.IsOpenPosMeasure μ]
    (A S : ℕ → Set α) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hSA : ∀ j, S j ⊆ A j) (hvol : ∀ j, M ≤ μ (S j))
    (hlim : Tendsto (fun j => μ (A j)) atTop (𝓝 M))
    {x : α} (hpersist : ∀ ε > 0, ∃ U : Set α, IsOpen U ∧ U.Nonempty ∧
      U ⊆ ball x ε ∧ ∀ᶠ j in atTop, U ⊆ A j) :
    ∃ (j : ℕ → ℕ) (z : ℕ → α), Tendsto j atTop atTop ∧
      (∀ k, z k ∈ S (j k)) ∧ Tendsto z atTop (𝓝 x) := by
  have hex (k : ℕ) := exists_nearby_image_of_saturation μ A S hM hSA hvol hlim
    hpersist k (show 0 < 1 / ((k:ℝ)+1) by positivity)
  choose j hj z hz hdist using hex
  refine ⟨j,z,tendsto_atTop_mono hj tendsto_id,hz,?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun k => dist_nonneg) (fun k => (hdist k).le)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal Pointwise

lemma subset_dilate_of_one_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {C : Set E} (hC : Convex ℝ C) (h0 : (0:E) ∈ C) {c : ℝ} (hc : 1 ≤ c) :
    C ⊆ c • C := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  intro x hx
  refine ⟨c⁻¹ • x,hC.smul_mem_of_zero_mem h0 hx
    ⟨inv_nonneg.mpr hc0.le, inv_le_one_of_one_le₀ hc⟩,?_⟩
  simp only [smul_smul,mul_inv_cancel₀ hc0.ne',one_smul]

lemma persistent_open_test_of_body_product {n : ℕ}
    {B C : Set (Fin n → ℝ)} (hB : Convex ℝ B) (hC : Convex ℝ C)
    (hiB : (interior B).Nonempty) (hiC : (interior C).Nonempty)
    (A : ℕ → Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA : ∀ j, B ×ˢ C ⊆ A j)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ B ×ˢ C) :
    ∀ ε > 0, ∃ U : Set ((Fin n → ℝ) × (Fin n → ℝ)), IsOpen U ∧ U.Nonempty ∧
      U ⊆ ball x ε ∧ ∀ᶠ j in atTop, U ⊆ A j := by
  have hcl : x ∈ closure ((interior B) ×ˢ (interior C)) := by
    rw [closure_prod_eq,hB.closure_interior_eq_closure_of_nonempty_interior hiB,
      hC.closure_interior_eq_closure_of_nonempty_interior hiC]
    exact ⟨subset_closure hx.1,subset_closure hx.2⟩
  intro ε hε
  refine ⟨ball x ε ∩ (interior B ×ˢ interior C),
    isOpen_ball.inter (isOpen_interior.prod isOpen_interior),?_,inter_subset_left,?_⟩
  · exact mem_closure_iff.mp hcl _ isOpen_ball (mem_ball_self hε)
  · exact Eventually.of_forall (fun j =>
      inter_subset_right.trans ((Set.prod_mono interior_subset interior_subset).trans (hA j)))

lemma volume_body_product_dilate {n : ℕ} (B C : Set (Fin n → ℝ)) {c : ℝ} (hc : 0 ≤ c) :
    volume (B ×ˢ (c • C)) = volume B * (ENNReal.ofReal (c^n) * volume C) := by
  rw [Measure.volume_eq_prod,Measure.prod_prod,Measure.addHaar_smul_of_nonneg volume hc]
  simp only [Module.finrank_pi,Fintype.card_fin,
    ]

lemma tendsto_volume_body_product_dilate {n : ℕ}
    {B C : Set (Fin n → ℝ)} (hB : IsCompact B) (hC : IsCompact C)
    (A : ℕ → Set (Fin n → ℝ)) (hA : ∀ j, IsCompact (A j))
    (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hvol : Tendsto (fun j => (volume (A j)).toReal) atTop (𝓝 (volume B).toReal))
    (hc1 : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun j => volume (A j ×ˢ (c j • C))) atTop (𝓝 (volume B*volume C)) := by
  have hfin (j : ℕ) : volume (A j ×ˢ (c j • C)) ≠ ∞ := by
    rw [volume_body_product_dilate _ _ (hc j)]
    exact ENNReal.mul_ne_top (hA j).measure_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC.measure_ne_top)
  apply (ENNReal.tendsto_toReal_iff hfin (ENNReal.mul_ne_top hB.measure_ne_top hC.measure_ne_top)).mp
  simp only [volume_body_product_dilate _ _ (hc _),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (hc _) _)]
  convert hvol.mul ((hc1.pow n).mul_const (volume C).toReal) using 1
  simp only [one_pow,one_mul]

theorem equality_strip_images_dense_eq_oai {n : ℕ} (hn : 1 ≤ n)
    {B : Set (Fin n → ℝ)} (hB : IsCompact B) (hconv : Convex ℝ B)
    (hsym : ∀ x ∈ B, -x ∈ B) (hint : (interior B).Nonempty)
    (heq : (volume B).toReal * (volume (coordinatePolar B)).toReal =
      (4:ℝ)^n/(Nat.factorial n:ℝ))
    (a : ℕ → coordinatePolar B)
    (ha : ∀ j, Function.Injective (measurement (fun i : Fin (n+j) => (a i).val)))
    (hcompact : ∀ j, IsCompact (stripBody (fun i : Fin (n+j) => (a i).val)))
    (hsub : ∀ j, B ⊆ stripBody (fun i : Fin (n+j) => (a i).val))
    (hvol : Tendsto (fun j => (volume (stripBody (fun i : Fin (n+j) => (a i).val))).toReal)
      atTop (𝓝 (volume B).toReal))
    (m : ℕ → ℕ) (hm : ∀ j, 2 ≤ m j)
    (herr : Tendsto (fun j => ((n+j:ℕ):ℝ)*planarError (m j)) atTop (𝓝 0))
    {x e : Fin n → ℝ} (hx : x ∈ B) (he : e ∈ coordinatePolar B) :
    ∃ j : ℕ → ℕ, ∃ z : ℕ → ((Fin n → ℝ) × (Fin n → ℝ)),
      Tendsto j atTop atTop ∧
      (∀ k, z k ∈ stripSublevel (fun i : Fin (n+j k) => (a i).val) (m (j k))) ∧
      Tendsto (fun k => stripMap (fun i : Fin (n+j k) => (a i).val) (m (j k)) (z k))
        atTop (𝓝 (x,e)) := by
  let C := coordinatePolar B
  obtain ⟨hC,hCc,hCs,hCi⟩ := coordinatePolar_is_symmetric_convex_body hB hconv hsym hint
  let A (j : ℕ) : Matrix (Fin (n+j)) (Fin n) ℝ := fun i => (a i).val
  let c (j : ℕ) : ℝ := 1+((n+j:ℕ):ℝ)*planarError (m j)
  have hc (j : ℕ) : 1 ≤ c j := by
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (planarError_nonneg _))
  have hc1 : Tendsto c atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add herr
  let O (j : ℕ) := stripBody (A j) ×ˢ (c j • C)
  let S (j : ℕ) := stripMap (A j) (m j) '' stripSublevel (A j) (m j)
  have hSO (j : ℕ) : S j ⊆ O j := by
    apply (stripMap_image_subset_product_eq (A j) (hm j)).trans
    exact Set.prod_mono Subset.rfl (smul_set_mono (coordinatePolar_antitone (hsub j)))
  have hlim : Tendsto (fun j => volume (O j)) atTop (𝓝 (volume B*volume C)) :=
    tendsto_volume_body_product_dilate hB hC _ hcompact c (fun j => zero_le_one.trans (hc j)) hvol hc1
  have hconst : volume B * volume C = ENNReal.ofReal ((4:ℝ)^n/(Nat.factorial n:ℝ)) := by
    rw [← ENNReal.ofReal_toReal (ENNReal.mul_ne_top hB.measure_ne_top hC.measure_ne_top),ENNReal.toReal_mul]
    exact congrArg ENNReal.ofReal heq
  rw [hconst] at hlim
  have hpersist := persistent_open_test_of_body_product hconv hCc hint hCi O
    (fun j => Set.prod_mono (hsub j) (subset_dilate_of_one_le hCc (zero_mem_coordinatePolar B) (hc j)))
    (show (x,e) ∈ B ×ˢ C from ⟨hx,he⟩)
  obtain ⟨j,v,hj,hv,hvlim⟩ := exists_sequence_of_saturation volume O S ENNReal.ofReal_ne_top
    hSO (fun j => stripMap_volume_lower hn (A j) (ha j) (hm j)) hlim hpersist
  choose z hz hzv using hv
  refine ⟨j,z,hj,hz,?_⟩
  have heqv : (fun k => stripMap (A (j k)) (m (j k)) (z k)) = v := funext hzv
  rw [heqv]
  exact hvlim

end SymmetricMahler

open Set Filter Metric MeasureTheory Complex
open scoped Topology

open Set Filter
open scoped Topology

end

end OAI
end

theorem solution : type_of% @OAI.SymmetricMahler.equality_strip_images_dense_eq_oai := @OAI.SymmetricMahler.equality_strip_images_dense_eq_oai
