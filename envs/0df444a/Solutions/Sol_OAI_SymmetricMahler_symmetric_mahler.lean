-- Prove2me | solution 1 for OAI.SymmetricMahler.symmetric_mahler
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:51:31.517036+00:00
-- url     : https://prove2.me/submissions/832fe3a0-8218-47f6-bea9-ab701cfdaf0e

import Mathlib
import Definitions.Def_MahlerConjecture
import Definitions.Def_OAISMh000
import Theorems.Thm_OAI_Mahler_MassHypotheses_homogeneousSphereFlux_value
import Theorems.Thm_OAI_Mahler_MassHypotheses_sourceCoordinateFlux_limit
import Theorems.Thm_OAI_Mahler_source_regular_massBelow_of_flux_limit
import Theorems.Thm_OAI_SymmetricMahler_symmetric_mahler_from_regular_special_mass

section
-- module Solutions.OAIS_Mahler.Mahler_ConformalSeries
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_ConformalInjectivity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_ConformalInverse
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_VerticalRadius
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_StripDifferential
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_StripVolume
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ComplexStripMap
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_ConformalRadialRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_SpecialLeadingTerm
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_StripRankGeometry
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_StripCompactSublevels
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_StripSublevelTopology
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_StripGeometry
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_SpecialMassHypotheses
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_EuclideanSpecialMap
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_InverseRadialRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_StripRegularValues
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
  convert (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => by
    simpa using (hasDerivAt_inverseRadius_radial (hz j)).fun_pow m)) using 1 <;> first | rfl | (ext t; simp)

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
  convert (DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ => hs j)) using 1 <;> first | rfl | (ext x; simp)

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
-- module Solutions.OAIS_Mahler.Mahler_StripMassExhaustion
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_EuclideanRegularLevels
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_SpecialSourceMass
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
  exact Mahler.source_regular_massBelow_of_flux_limit
    (euclideanSpecial_massHypotheses A (by omega) hA hm)
    (stripRegularLevel_mem k).1 (stripRegularLevel_mem k).2
    (fun z hz he => euclideanSpecial_positive_regular_nonzero A hA (by omega)
      (stripRegularLevel_mem k).1 hz he) hlimit

/-- The arbitrary-body inequality conditional on the numerical coordinate
small-sphere limit. The general-dimensional homogeneous flux
value is retained as a hypothesis. -/
theorem symmetric_mahler_from_special_source_flux_limits (n : ℕ)
    (hlimit : ∀ N (A : Matrix (Fin N) (Fin (n+1)) ℝ),
      Function.Injective (measurement A) → ∀ m : ℕ, 2 ≤ m → Tendsto
      (fun r => MahlerStokes.sphereFlux r
        (Mahler.sourceCoordinateForm (Mahler.sourceCoordinates n)
          (Mahler.logTau (euclideanSpecialMap A m)) n))
      (𝓝[>] (0:ℝ)) (𝓝 ((Real.pi*(m:ℝ))^(n+1))))
    {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4:ℝ)^(n+1)/(Nat.factorial (n+1):ℝ) ≤
      (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  apply symmetric_mahler_from_regular_special_mass (by omega) _ hK hconv hsym hint
  intro N A hA m hm k
  exact special_regular_mass_of_source_flux_limit A hA hm k (hlimit N A hA m hm)

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousMassAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SymmetricMahler

/-- The final body theorem needs the homogeneous value only for the actual
finite-strip polynomial family. A general isolated-zero mass theorem or
Sard theorem is not an additional premise. -/
theorem symmetric_mahler_from_special_homogeneous_values (n : ℕ)
    (hvalue : ∀ N (A : Matrix (Fin N) (Fin (n+1)) ℝ),
      Function.Injective (measurement A) → ∀ m : ℕ, 2 ≤ m →
      Mahler.homogeneousSphereFlux n N (specialLeadingPolynomial A m) =
        (Real.pi*(m:ℝ))^(n+1))
    {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4:ℝ)^(n+1)/(Nat.factorial (n+1):ℝ) ≤
      (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  apply symmetric_mahler_from_special_source_flux_limits n _ hK hconv hsym hint
  intro N A hA m hm
  have h := euclideanSpecial_massHypotheses A (by omega) hA hm
  simpa only [hvalue N A hA m hm] using h.sourceCoordinateFlux_limit

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_MainTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace SymmetricMahler

/-- The symmetric Mahler inequality in every positive
dimension, for ordinary Lebesgue volume and the coordinate polar. -/
theorem symmetric_mahler_oai {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4:ℝ)^n/(Nat.factorial n:ℝ) ≤
      (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  cases n with
  | zero => omega
  | succ k =>
    apply symmetric_mahler_from_special_homogeneous_values k _ hK hconv hsym hint
    intro N A hA m hm
    exact (euclideanSpecial_massHypotheses A (by omega) hA hm).homogeneousSphereFlux_value

end SymmetricMahler

end

end OAI
end

theorem solution : type_of% @OAI.SymmetricMahler.symmetric_mahler_oai := @OAI.SymmetricMahler.symmetric_mahler_oai
