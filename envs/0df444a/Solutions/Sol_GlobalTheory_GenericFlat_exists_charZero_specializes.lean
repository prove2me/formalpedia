-- Prove2me | solution 1 for GlobalTheory.GenericFlat.exists_charZero_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:49:02.361156+00:00
-- url     : https://prove2.me/submissions/834376ff-be5c-4a79-bcb6-9524849bb997

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InjectiveOfApplyEqGenericPoint
import Theorems.Thm_GlobalTheory_GenericFlat_injective_of_apply_eq_genericPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GenericFlat
namespace GlobalTheory.GenericFlat
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [CharZero O] (T : Scheme.{0})
    (s : T ⟶ Sp O) [Flat s] (x : T) : ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ) := by
  obtain ⟨ξ, hξ, e⟩ := Flat.generalizingMap s (genericPoint_specializes (s x))
  refine ⟨ξ, hξ, ?_⟩
  obtain ⟨δ, hδ⟩ := Spec.map_surjective (T.fromSpecResidueField ξ ≫ s)
  have hi : Function.Injective δ.hom := by
    refine injective_of_apply_eq_genericPoint (K := T.residueField ξ) δ.hom
      (⊥ : PrimeSpectrum (T.residueField ξ)) ?_
    change Spec.map δ _ = _
    rw [hδ]
    exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg s (Scheme.fromSpecResidueField_apply ξ _)).trans e)
  exact charZero_of_injective_ringHom hi
end GlobalTheory.GenericFlat
