-- Prove2me | solution 1 for GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:16.986451+00:00
-- url     : https://prove2.me/submissions/b5cfb68b-1436-4d61-8e2e-23923f5e064f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution {X : Scheme.{0}} {R : CommRingCat.{0}}
    (s : X ⟶ Spec R) [LocallyOfFiniteType s] (p : X) (ψ : R ⟶ X.residueField p)
    (h : Spec.map ψ = X.fromSpecResidueField p ≫ s) : ψ.hom.EssFiniteType := by
  haveI : (s p).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have e : ψ = CommRingCat.ofHom (algebraMap R (s p).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R (s p)).inv ≫ s.residueFieldMap p := by
    rw [← Spec.map_inj, h, Spec.map_comp, Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [e]
  refine .comp (RingHom.essFiniteType_algebraMap.mpr inferInstance) (.comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.Spec.residueFieldIso R (s p)).inv).2).essFiniteType
    (RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap s p)))
end GlobalTheory.SS
