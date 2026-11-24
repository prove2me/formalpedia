-- Prove2me | solution 1 for GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:32.398196+00:00
-- url     : https://prove2.me/submissions/5eadd48b-0f49-4d0e-ae0b-914dfe18a354

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedImmersionMorphismRestrictBasicOpenOfMulM
import Theorems.Thm_GlobalTheory_appLE_basicOpen_surjective_of_mul_mem_range

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
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) →
      ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) →
        IsClosedImmersion (φ ∣_ Z.basicOpen r) := by
  intro X Z φ V hV haff r h
  have hpre : φ ⁻¹ᵁ Z.basicOpen r = X.basicOpen ((φ.app V).hom r) := Scheme.preimage_basicOpen φ r
  haveI : IsAffine (Z.basicOpen r) := hV.basicOpen r
  haveI : IsAffine (φ ⁻¹ᵁ Z.basicOpen r) := by
    have := haff.basicOpen ((φ.app V).hom r)
    rw [← hpre] at this
    exact this
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, morphismRestrict_appLE]
  exact appLE_basicOpen_surjective_of_mul_mem_range φ haff r h _ _ _ (by simp) (by simp [hpre])
end GlobalTheory
