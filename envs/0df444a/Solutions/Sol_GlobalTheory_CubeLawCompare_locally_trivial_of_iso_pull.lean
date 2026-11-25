-- Prove2me | solution 1 for GlobalTheory.CubeLawCompare.locally_trivial_of_iso_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:43:09.270172+00:00
-- url     : https://prove2.me/submissions/0356a213-442d-4f67-a573-47c284464e92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_RigidityTranslation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocallyTrivialOfIsoPull
import Theorems.Thm_GlobalTheory_CubeLawCompare_gen_restrict_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_pull


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CubeLawCompare
variable {Y T : Scheme.{0}}
namespace GlobalTheory.CubeLawCompare
theorem _root_.solution (p : Y ⟶ T) (M : LB Y) {N : LB T} (hN : N.IsLB)
    (u : LB.Iso (N.pull p) M) (hu : u.IsGen) (t : T) :
    ∃ V : T.Opens, t ∈ V ∧ ∃ c : LB.Gen (M.pull (p ⁻¹ᵁ V).ι), c.IsGen := by
  obtain ⟨i, hi⟩ := exists_chart hN t
  refine ⟨N.U i, hi, (gen_restrict_iff M _).2 ?_⟩
  have le : ∀ j, p ⁻¹ᵁ N.U i ⊓ M.U j ≤ M.U j ⊓ (N.pull p).U fun _ => i :=
    fun j y hy => ⟨hy.2, mem_pull.2 hy.1⟩
  refine ⟨fun j => res (le j) (u.s (j, fun _ => i)), fun j j' y hW hj hj' => ?_⟩
  have hI : (𝟙 Y : Y ⟶ Y) y ∈ (N.pull p).U fun _ => i := mem_pull.2 hW
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U j ⊓ (N.pull p).U (fun _ => i) ⊓ (M.U j' ⊓ (N.pull p).U fun _ => i) :=
    ⟨⟨hj, hI⟩, hj', hI⟩
  have e := (gm_res (𝟙 Y) y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _)
    (hu (j, fun _ => i) (j', fun _ => i))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div (N.pull p) M (𝟙 Y) y (j, fun _ => i) (j', fun _ => i) hm) (gm_res (𝟙 Y) y _ hm _))))
  rw [gm_self (LB.isLB_pull hN p) (𝟙 Y) y hI, inv_one, _root_.mul_one] at e
  exact (gm_res (𝟙 Y) y (le j) ⟨hW, hj⟩ _).trans
    (e.trans (congrArg _ (gm_res (𝟙 Y) y (le j') ⟨hW, hj'⟩ _).symm))
end GlobalTheory.CubeLawCompare
