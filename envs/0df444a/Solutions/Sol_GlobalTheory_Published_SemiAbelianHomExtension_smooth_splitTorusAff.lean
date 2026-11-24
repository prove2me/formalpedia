-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.smooth_splitTorusAff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:56:29.883846+00:00
-- url     : https://prove2.me/submissions/67baee3a-bbea-42cd-8264-2622fe5b119a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_smooth_laurent

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
theorem _root_.solution : Smooth (splitTorusAff ZU.{0} (ULift.{0} ℤ)).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ)))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.2 (smooth_laurent _)
end GlobalTheory.Published.SemiAbelianHomExtension
