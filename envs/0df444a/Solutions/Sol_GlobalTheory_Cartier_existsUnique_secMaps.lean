-- Prove2me | solution 1 for GlobalTheory.Cartier.existsUnique_secMaps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:19.609594+00:00
-- url     : https://prove2.me/submissions/74ff3b22-c793-4b7a-932f-7e1594f09b5e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_SecMaps_isGen
import Theorems.Thm_GlobalTheory_Cartier_SecMaps_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
theorem _root_.solution {A B : LB X} {a : A.Sec} {b : B.Sec} (ha : IsRegularSec a)
    (h : ∀ (p : B.ι) (q : A.ι), Associated (resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q))
      (resG X (inf_le_left : B.U p ⊓ A.U q ≤ B.U p) (b.f p))) :
    ∃! w : LB.Iso A B, w.IsGen ∧ SecMaps w a b := by
  choose u hu using h
  let w : LB.Iso A B := ⟨fun p => u p.1 p.2⟩
  have hw : SecMaps w a b := fun p => ((mul_comm _ _).trans (hu p.1 p.2)).symm
  exact ⟨w, ⟨hw.isGen ha, hw⟩, fun w' hw' => hw'.2.unique hw ha⟩
end GlobalTheory.Cartier
