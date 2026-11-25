-- Prove2me | solution 1 for GlobalTheory.DegActCheck.halfUnit_add_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:59.348198+00:00
-- url     : https://prove2.me/submissions/8e9f0f4f-eef1-47dd-988c-c0aa189e8abf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_PsiUnitOnIffInterior

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DegActCheck
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.DegActCheck
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    have h2 := IsCMField.complexEmbedding_complexConj E τ (H.rt : E)
    rw [h1] at h2
    have h3 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
      simpa using this
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2.symm
    rw [hr] at h3
    have : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h3
    nlinarith [sq_nonneg r]
  have hb : H.bar H.rt = -H.rt := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, hb, map_ofNat] at this
    rw [this]; ring
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero this
end GlobalTheory.DegActCheck
