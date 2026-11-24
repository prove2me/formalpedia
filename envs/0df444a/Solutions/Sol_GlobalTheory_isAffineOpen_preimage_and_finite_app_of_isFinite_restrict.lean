-- Prove2me | solution 1 for GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:35.321228+00:00
-- url     : https://prove2.me/submissions/3ac44b42-f492-4404-bb27-eafa38c843e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) →
      IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by
  intro X Z φ V hV hf
  haveI : IsAffine (V : Scheme) := hV
  have h1 : IsAffine (φ ⁻¹ᵁ V : Scheme) := isAffine_of_isAffineHom (φ ∣_ V)
  refine ⟨h1, ?_⟩
  have h2 := hf.finite_app ⊤ (isAffineOpen_top _)
  rw [morphismRestrict_app] at h2
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [← e]
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).mp h2
end GlobalTheory
