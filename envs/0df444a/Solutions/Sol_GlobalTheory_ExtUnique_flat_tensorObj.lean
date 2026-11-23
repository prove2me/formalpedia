-- Prove2me | solution 1 for GlobalTheory.ExtUnique.flat_tensorObj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:15.736348+00:00
-- url     : https://prove2.me/submissions/871cb863-7e85-46c0-92dd-d221b69ecc67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
variable {U S : Scheme.{u}} (j : U ⟶ S) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
namespace GlobalTheory.ExtUnique
theorem _root_.solution (X Y : Over S) [Flat X.hom] [Flat Y.hom] : Flat (X ⊗ Y).hom := by
  change Flat (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance
end GlobalTheory.ExtUnique
