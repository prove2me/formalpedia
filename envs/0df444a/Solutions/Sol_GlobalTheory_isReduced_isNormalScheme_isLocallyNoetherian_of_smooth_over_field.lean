-- Prove2me | solution 1 for GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:47.184431+00:00
-- url     : https://prove2.me/submissions/f7971997-524b-4655-9cdb-8b5e6fbe6eca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_stalk_Sp
import Theorems.Thm_GlobalTheory_forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k), Smooth s →
      IsReduced X ∧ IsNormalScheme X ∧ IsLocallyNoetherian X := by
  intro k _ X s hs
  have : Smooth s := hs
  have hN : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth s
      (fun y => isDomain_and_isIntegrallyClosed_stalk_Sp k y)
  refine ⟨?_, hN, ?_⟩
  · have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hN x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  · have : IsLocallyNoetherian (Sp k) := inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian s
end GlobalTheory
