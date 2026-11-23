-- Prove2me | solution 1 for GlobalTheory.AbLocusPull.gs_secOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:28:39.815692+00:00
-- url     : https://prove2.me/submissions/94a25317-5adf-42b7-a068-071314c164d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLocusPull
theorem _root_.solution {M : LB X} {V : X.Opens} {t : ∀ i, Γ(X, V ⊓ M.U i)} (ht : t ∈ secOn M V) (r : Z ⟶ X) (z : Z)
    (i j : M.ι) (hV : r z ∈ V) (hi : r z ∈ M.U i) (hj : r z ∈ M.U j) :
    gs r z _ (t i) = (gm r z (M.U i ⊓ M.U j) (M.g i j)).val * gs r z _ (t j) := by
  have hz : r z ∈ V ⊓ M.U i ⊓ M.U j := ⟨⟨hV, hi⟩, hj⟩
  have e := congrArg (gs r z (V ⊓ M.U i ⊓ M.U j)) (ht i j)
  dsimp only [resG] at e
  rw [gs_mul r z _ hz, gs_res r z _ hz, gs_res r z _ hz, gs_res r z _ hz, gs_unit r z _ (show r z ∈ M.U i ⊓ M.U j from ⟨hi, hj⟩)] at e
  exact e
end GlobalTheory.AbLocusPull
