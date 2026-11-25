-- Prove2me | solution 1 for GlobalTheory.SS.PlacesExt.exists_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:52:53.550382+00:00
-- url     : https://prove2.me/submissions/335e06a3-0d0a-44dd-a847-6c1bad33f4db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField
import Theorems.Thm_GlobalTheory_SS_PlacesExt_exists_ext
import Theorems.Thm_GlobalTheory_SS_PlacesExt_isAlgebraic_of_forall
import Theorems.Thm_GlobalTheory_SS_PlacesExt_projLine_dvr
import Theorems.Thm_GlobalTheory_SS_PlacesExt_projLine_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PlacesExt
open IsDedekindDomain Polynomial ReciprocityTheory.ChartRestriction.G.T0
namespace GlobalTheory.SS.PlacesExt
theorem _root_.solution : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (t : K), Transcendental k t →
    FiniteDimensional (IntermediateField.adjoin k {t}) K →
    Algebra.IsSeparable (IntermediateField.adjoin k {t}) K →
    ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → IsAlgebraic k x := by
  intro k K _ _ _ t ht hf hs
  let e := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc k) K :=
    ((algebraMap (IntermediateField.adjoin k {t}) K).comp e.toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower k (RatFunc k) K := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = algebraMap (IntermediateField.adjoin k {t}) K (e (algebraMap k _ c))
    rw [e.commutes]; rfl
  have H : RingHom.comp (algebraMap (RatFunc k) K) (e.symm.toRingEquiv : _ →+* _) =
      RingHom.comp (RingEquiv.refl K : K →+* K) (algebraMap (IntermediateField.adjoin k {t}) K) := by
    ext x
    change algebraMap (IntermediateField.adjoin k {t}) K (e (e.symm x)) = _
    rw [e.apply_symm_apply]; rfl
  haveI : FiniteDimensional (RatFunc k) K := Module.Finite.of_equiv_equiv _ _ H
  haveI : Algebra.IsSeparable (RatFunc k) K := Algebra.IsSeparable.of_equiv_equiv _ _ H
  obtain ⟨Pl, hPl⟩ := exists_ext K (projLinePlaces k) (projLine_dvr k)
  exact ⟨Pl, fun x hx => isAlgebraic_of_forall (projLinePlaces k) (projLine_const k) x (hPl x hx)⟩
end GlobalTheory.SS.PlacesExt
