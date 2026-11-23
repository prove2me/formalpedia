-- Prove2me | solution 1 for GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:29.382641+00:00
-- url     : https://prove2.me/submissions/e31344e4-1505-49ce-89c7-4b76e60bb8e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
namespace GlobalTheory.SplitTorus
theorem _root_.solution (R : Type*) [CommRing R] [IsLocalRing R] :
    ConnectedSpace (PrimeSpectrum R) := by
  have : PreconnectedSpace (PrimeSpectrum R) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint R) fun y _ =>
      ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_closure
  exact ⟨inferInstance⟩
end GlobalTheory.SplitTorus
