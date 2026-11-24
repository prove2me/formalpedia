-- Prove2me | solution 1 for GlobalTheory.GenPush.gen_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:09.491177+00:00
-- url     : https://prove2.me/submissions/132c31d9-bf8c-49ad-ae4d-6f2484e2e168

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorIsoExtendFromOpenContainingCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.GenPush
variable {X Y : Scheme.{0}}
private theorem gm_res_eq_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {U V : X.Opens} {h : V ≤ U} (hy : f y ∈ V)
    (a : Γ(X, U)ˣ) : gm f y V (res h a) = gm f y U a := by
  apply Units.ext
  rw [← gs_unit f y V hy, ← gs_unit f y U (h hy)]
  exact gs_res f y h hy a.val
end GlobalTheory.GenPush
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.GenPush
variable {X Y : Scheme.{0}}
namespace GlobalTheory.GenPush
theorem _root_.solution {N : LB Y} {t : N.Gen} (ht : t.IsGen) (y : Y) (i j : N.ι) (hi : y ∈ N.U i) (hj : y ∈ N.U j) :
    gm (𝟙 Y) y (N.U i) (t.s i) = gm (𝟙 Y) y (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) y (N.U j) (t.s j) := by
  unfold LB.Gen.IsGen at ht
  have hm : (𝟙 Y) y ∈ N.U i ⊓ N.U j := by simpa using (⟨hi, hj⟩ : y ∈ N.U i ⊓ N.U j)
  have e := congrArg (gm (𝟙 Y) y (N.U i ⊓ N.U j)) (ht i j)
  rw [map_mul, gm_res_eq_gm (𝟙 Y) y hm, gm_res_eq_gm (𝟙 Y) y hm] at e
  exact e
end GlobalTheory.GenPush
