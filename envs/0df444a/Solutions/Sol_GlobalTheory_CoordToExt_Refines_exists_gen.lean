-- Prove2me | solution 1 for GlobalTheory.CoordToExt.Refines.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:40.573072+00:00
-- url     : https://prove2.me/submissions/ac181bb8-c5df-46fe-abbf-7e7cc32aaa2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CoordToExt
variable {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.CoordToExt
namespace Refines
theorem _root_.solution (hL : L.IsLB) {M : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Refines M L φ ε)
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε) (t : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) :
    ∃ s : LB.Gen M, s.IsGen := by
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_gen hL hF t ht
  obtain ⟨σ, le, hg⟩ := h
  refine ⟨⟨fun i => res (le i) (u.s (σ i))⟩, fun i j => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (gen_trans hu (𝟙 Y) y (le i hy.1) (le j hy.2)))).trans
    (Eq.symm ?_)
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (hg _ _ y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))
end Refines
end GlobalTheory.CoordToExt
