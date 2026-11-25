-- Prove2me | solution 1 for GlobalTheory.TripleMap.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:13.619914+00:00
-- url     : https://prove2.me/submissions/10138bad-f0d9-4c11-b89f-6eaf86e80229

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOneOfAppLESectionEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGeometricallyIntegralAbLocusTensorObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSabMapOfLbIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.TripleMap
namespace GlobalTheory.TripleMap
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gm r z (LB.wchart L φ j) (u.s j) = gm r z ⊤ a * gm r z (LB.wchart L φ j) (u'.s j) := by
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι),
      gm r z (LB.wchart L φ j) (u.s j * (u'.s j)⁻¹) =
        gm r z (LB.wchart L φ j) (u.s j) * (gm r z (LB.wchart L φ j) (u'.s j))⁻¹ := fun Z r z j =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨a, ha⟩ := glue_unit ⊤ (LB.wchart L φ) (fun _ => le_top)
    (fun y _ => by
      choose p hp using fun k => exists_chart hL (φ k y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp⟩) (fun j => u.s j * (u'.s j)⁻¹)
    (fun j j' y hy => by
      rw [hv, hv, gen_trans hu (𝟙 Y) y hy.1 hy.2, gen_trans hu' (𝟙 Y) y hy.1 hy.2, mul_inv,
        _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨a, fun Z r z j hj => ?_⟩
  rw [← gm_res r z le_top hj a, ha j, hv, inv_mul_cancel_right]
end GlobalTheory.TripleMap
