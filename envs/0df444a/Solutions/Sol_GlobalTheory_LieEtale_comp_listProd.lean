-- Prove2me | solution 1 for GlobalTheory.LieEtale.comp_listProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:29.584422+00:00
-- url     : https://prove2.me/submissions/d8ac033b-7995-4f2e-986d-276baa9cdbf6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift

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
noncomputable section
open GlobalTheory GlobalTheory.LieEtale
variable {S : Scheme.{0}} {O k : Type} {P E : Over S}
namespace GlobalTheory.LieEtale
theorem _root_.solution {G : Over S} [GrpObj G] (z : P ⟶ E) (l : List (E ⟶ G))
    (h : ∀ u ∈ l, z ≫ u = 1) : z ≫ l.prod = 1 := by
  induction l with
  | nil => exact MonObj.comp_one z
  | cons u l ih =>
    rw [List.prod_cons, MonObj.comp_mul, h u (by simp), ih fun w hw => h w (by simp [hw]),
      _root_.mul_one]
end GlobalTheory.LieEtale
