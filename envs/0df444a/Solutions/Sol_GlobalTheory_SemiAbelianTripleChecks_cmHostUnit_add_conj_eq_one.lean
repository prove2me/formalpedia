-- Prove2me | solution 1 for GlobalTheory.SemiAbelianTripleChecks.cmHostUnit_add_conj_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:10:39.442235+00:00
-- url     : https://prove2.me/submissions/0c0aaeff-6910-4209-b8d6-6d2d6e61f8e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_CubeMapTripleProductUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SemiAbelianTripleChecks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
namespace GlobalTheory.SemiAbelianTripleChecks
theorem _root_.solution (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have hd : (H.d : 𝓞 E) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq]; simp
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    have h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h2 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h1] at h2
    have h3 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    have h4 : (φ H.rt) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, h3]; simp
    have h5 : (φ H.rt).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
    have h6 := congrArg Complex.re h4
    simp [pow_two, h5] at h6
    have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ H.rt).re]
  have hb : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact absurd h hne
    · exact h
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, hb, map_ofNat] at this
    rw [this]; ring
  have h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3
end GlobalTheory.SemiAbelianTripleChecks
