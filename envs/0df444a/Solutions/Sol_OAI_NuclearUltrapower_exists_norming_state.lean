-- Prove2me | solution 1 for OAI.NuclearUltrapower.exists_norming_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:01:35.408701+00:00
-- url     : https://prove2.me/submissions/1e7ec3f4-77d9-4dcd-83df-bc16d7e3918f

import Mathlib
import Definitions.Def_OAIQ019N020

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FaithfulGNS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u
open scoped ComplexOrder ENNReal
namespace NuclearUltrapower
variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

attribute [local instance] OAI.NuclearUltrapower.gnsSpectralOrder
attribute [local instance] OAI.NuclearUltrapower.gnsSpectralOrderedRing
/-- The disk estimate which exposes a positive element to Hahn--Banach. -/
theorem norm_positive_center (a : A) (ha : 0 ≤ a) :
    ‖a - (‖a‖ / 2 : ℝ) • (1 : A)‖ ≤ ‖a‖ / 2 := by
  have hsa := IsSelfAdjoint.of_nonneg ha
  have he : cfc (fun x : ℝ => x - ‖a‖ / 2) a = a - (‖a‖ / 2 : ℝ) • (1 : A) := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ => ‖a‖ / 2) a,
      cfc_id' ℝ a hsa, cfc_const _ a hsa]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [← he]
  apply norm_cfc_le (by positivity)
  intro x hx
  have hx0 : 0 ≤ x := (spectrum_nonneg_of_nonneg ha) hx
  have hxN : x ≤ ‖a‖ := (Real.le_norm_self x).trans (spectrum.norm_le_norm_of_mem hx)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Elementary disk intersection, used to retain the unit under norm-preserving extension. -/
theorem complex_disk_intersection (z : ℂ) (h0 : ‖z‖ ≤ 1) (h2 : ‖2-z‖ ≤ 1) : z = 1 := by
  have hr := Complex.abs_re_le_norm z
  have hr2 := Complex.abs_re_le_norm (2-z)
  have hzre : z.re = 1 := by
    have := (le_abs_self z.re).trans (hr.trans h0)
    have := (le_abs_self (2-z).re).trans (hr2.trans h2)
    norm_num [Complex.sub_re] at *
    linarith
  have hz : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    nlinarith [Complex.sq_norm z, Complex.normSq_apply z, norm_nonneg z]
  apply Complex.ext
  · simpa using hzre
  · simp only [Complex.one_im]
    nlinarith [sq_nonneg z.im]

/-- Hahn--Banach norms a positive element by a unital contraction. -/
theorem exists_unital_norming_functional (a : A) (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ f : A →L[ℂ] ℂ, ‖f‖ = 1 ∧ f 1 = 1 ∧ f a = (‖a‖ : ℂ) := by
  obtain ⟨f, hf, hfa⟩ := exists_dual_vector ℂ a (norm_ne_zero_iff.mpr ha0)
  refine ⟨f, hf, ?_, hfa⟩
  apply complex_disk_intersection
  · simpa [hf] using f.le_opNorm (1 : A)
  · have h := (f.le_opNorm (a - (‖a‖ / 2 : ℝ) • (1 : A))).trans
        (by simpa [hf] using norm_positive_center a ha)
    have hn : 0 < ‖a‖ / 2 := by positivity
    have he : f (a - (‖a‖ / 2 : ℝ) • (1 : A)) = (‖a‖ / 2 : ℂ) * (2-f 1) := by
      rw [map_sub, ContinuousLinearMap.map_smul_of_tower, hfa]
      simp only [Complex.real_smul]
      push_cast
      ring_nf
      simp
    rw [he, norm_mul] at h
    have he' : ‖(‖a‖ / 2 : ℂ)‖ = ‖a‖ / 2 := by
      rw [norm_div, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [he'] at h
    nlinarith

/-- A contractive unital functional is real on self-adjoint elements. -/
theorem contractive_unital_real (f : A →L[ℂ] ℂ) (hf : ‖f‖ ≤ 1) (h1 : f 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) : (f a).im = 0 := by
  have hbound (t : ℝ) : ‖(1 : A) + ((t : ℂ)*Complex.I) • a‖ ^ 2 ≤ 1 + t^2 * ‖a‖^2 := by
    have he : star ((1 : A) + ((t : ℂ)*Complex.I) • a) *
        ((1 : A) + ((t : ℂ)*Complex.I) • a) = 1 + (t^2 : ℝ) • (a*a) := by
      have hc : star (((t : ℂ)*Complex.I) • a) = -(((t : ℂ)*Complex.I) • a) := by
        simp [ha.star_eq, mul_comm]
      rw [star_add, star_one, hc]
      have hprod : (((t : ℂ)*Complex.I) • a) * (((t : ℂ)*Complex.I) • a) =
          -(t^2 : ℝ) • (a*a) := by
        rw [smul_mul_smul]
        have hcoeff : ((t : ℂ)*Complex.I)*((t : ℂ)*Complex.I) = -(t^2 : ℝ) := by
          push_cast
          calc ((t : ℂ)*Complex.I)*((t : ℂ)*Complex.I) = (t:ℂ)^2*Complex.I^2 := by ring
               _ = -(t:ℂ)^2 := by rw [Complex.I_sq]; ring
        rw [hcoeff]
        rw [← Complex.ofReal_neg]
        exact Complex.coe_smul _ _
      calc (1 + -(((t:ℂ)*Complex.I) • a)) * (1 + ((t:ℂ)*Complex.I) • a) =
          1 - (((t:ℂ)*Complex.I) • a) * (((t:ℂ)*Complex.I) • a) := by
            generalize ((t:ℂ)*Complex.I) • a = x
            noncomm_ring
           _ = 1 + (t^2 : ℝ) • (a*a) := by rw [hprod]; simp
    rw [sq, ← CStarRing.norm_star_mul_self, he]
    calc ‖(1 : A) + (t^2 : ℝ) • (a*a)‖ ≤ ‖(1 : A)‖ + ‖(t^2 : ℝ) • (a*a)‖ := norm_add_le _ _
         _ ≤ 1 + t^2 * ‖a‖^2 := by
           rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t), ha.norm_mul_self]
           simp
  have hscalar (t : ℝ) : -2*t*(f a).im ≤ t^2*‖a‖^2 := by
    have hc : ‖f ((1 : A) + ((t:ℂ)*Complex.I) • a)‖ ≤ ‖(1 : A) + ((t:ℂ)*Complex.I) • a‖ :=
      (f.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hf)
    rw [map_add, map_smul, h1] at hc
    simp only [smul_eq_mul] at hc
    have hs := hbound t
    have hc2 : ‖1 + ((t:ℂ)*Complex.I) * f a‖^2 ≤ 1 + t^2*‖a‖^2 := by
      exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hc).trans hs
    rw [Complex.sq_norm, Complex.normSq_apply] at hc2
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, zero_mul, sub_zero, zero_sub, mul_one, zero_add, add_zero,
      Complex.add_im, Complex.one_im] at hc2
    nlinarith [sq_nonneg (t * (f a).re), sq_nonneg (t * (f a).im)]
  have h := hscalar (-(f a).im / (‖a‖^2+1))
  have hp : 0 < ‖a‖^2+1 := by positivity
  have h' := (mul_le_mul_iff_left₀ (sq_pos_of_pos hp)).mpr h
  field_simp at h'
  nlinarith [sq_nonneg (f a).im, sq_nonneg (‖a‖ * (f a).im)]

/-- The norm-one / unit-preserving criterion for positivity. -/
theorem contractive_unital_positive (f : A →L[ℂ] ℂ) (hf : ‖f‖ ≤ 1) (h1 : f 1 = 1)
    (a : A) (ha : 0 ≤ a) : 0 ≤ f a := by
  apply RCLike.nonneg_iff.mpr
  constructor
  · have h := (f.le_opNorm (a - (‖a‖ / 2 : ℝ) • (1:A))).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hf).trans (norm_positive_center a ha))
    rw [map_sub, ContinuousLinearMap.map_smul_of_tower, h1] at h
    have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans h)).1
    simp only [Complex.sub_re, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at hr
    change 0 ≤ (f a).re
    linarith
  · exact contractive_unital_real f hf h1 a (IsSelfAdjoint.of_nonneg ha)

/-- Sufficiently many states, proved rather than assumed. -/
theorem exists_norming_state_oai (a : A) (ha : 0 ≤ a) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ f a = (‖a‖ : ℂ) := by
  have hex : ∃ f : A →L[ℂ] ℂ, ‖f‖ = 1 ∧ f 1 = 1 ∧ f a = (‖a‖ : ℂ) := by
    by_cases ha0 : a = 0
    · obtain ⟨f, hf, h1⟩ := exists_dual_vector ℂ (1:A) (by simp)
      refine ⟨f, hf, ?_, ?_⟩
      · simpa using h1
      · simp [ha0]
    · exact exists_unital_norming_functional a ha ha0
  obtain ⟨f, hf, h1, hfa⟩ := hex
  let p : A →ₚ[ℂ] ℂ := { f.toLinearMap with
    monotone' := by
      intro x y hxy
      change f x ≤ f y
      have : 0 ≤ f (y-x) := contractive_unital_positive f hf.le h1 (y-x) (sub_nonneg.mpr hxy)
      simpa only [map_sub, sub_nonneg] using this }
  exact ⟨p, h1, hfa⟩

end NuclearUltrapower
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.NuclearUltrapower.exists_norming_state_oai.{u} := @OAI.NuclearUltrapower.exists_norming_state_oai.{u}
