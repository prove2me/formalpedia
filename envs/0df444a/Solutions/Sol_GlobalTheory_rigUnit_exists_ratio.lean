-- Prove2me | solution 1 for GlobalTheory.rigUnit_exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:40.468297+00:00
-- url     : https://prove2.me/submissions/8e60da00-054d-4ee9-8a75-5f6737222bb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBaseUnitRigidifiedGenericGenerator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} (M : LB X) (hM : M.IsLB) (f : Y ⟶ X)
    (t t' : LB.Gen (M.pull f)) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → M.ι), r z ∈ (M.pull f).U j →
      gm r z ((M.pull f).U j) (t.s j) = gm r z ⊤ w * gm r z ((M.pull f).U j) (t'.s j) := by
  obtain ⟨w, hw⟩ := glue_unit (X := Y) ⊤ (fun j : PUnit → M.ι => (M.pull f).U j) (fun _ => le_top)
    (fun y _ => by
      obtain ⟨i, hi⟩ := exists_chart hM (f y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩)
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      have h1 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      have h2 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht' (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 ((map_inv _ _).trans (congrArg (·⁻¹) h2)))).trans
        (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_inv _ _))).symm)
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      rfl)
  refine ⟨w, fun Z r z j hj => ?_⟩
  have e := (gm_res r z (le_top : (M.pull f).U j ≤ ⊤) hj w).symm.trans (congrArg (gm r z _) (hw j))
  rw [e, map_mul, map_inv, inv_mul_cancel_right]
end GlobalTheory
