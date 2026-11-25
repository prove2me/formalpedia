-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.geometricallyConnected_laurent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:52:19.808065+00:00
-- url     : https://prove2.me/submissions/d17d5638-4165-437b-bad5-a07159093650

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
open scoped TensorProduct
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (R : Type) [CommRing R] : GeometricallyConnected
    (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R (ULift.{0} ℤ))))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ ↦ ?_⟩
  have : IsDomain (AddMonoidAlgebra K (ULift.{0} ℤ)) :=
    (AddMonoidAlgebra.domCongr K K (AddEquiv.ulift (α := ℤ))).toMulEquiv.isDomain _
  have : IsDomain (AddMonoidAlgebra R (ULift.{0} ℤ) ⊗[R] K) :=
    ((Algebra.TensorProduct.comm _ _ _).toRingEquiv.trans
      (AddMonoidAlgebra.scalarTensorEquiv (M := ULift.{0} ℤ) R K).toRingEquiv).toMulEquiv.isDomain _
  let e := (pullbackSpecIso R (AddMonoidAlgebra R (ULift.{0} ℤ)) K).inv
  exact e.homeomorph.surjective.connectedSpace e.homeomorph.continuous
end GlobalTheory.Published.SemiAbelianHomExtension
