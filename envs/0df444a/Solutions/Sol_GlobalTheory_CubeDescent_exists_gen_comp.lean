-- Prove2me | solution 1 for GlobalTheory.CubeDescent.exists_gen_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:30:58.496248+00:00
-- url     : https://prove2.me/submissions/410abdf9-22df-49f7-af1f-a77cbad06842

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
open GlobalTheory GlobalTheory.CubeDescent
variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]
namespace GlobalTheory.CubeDescent
theorem _root_.solution (L : LB X) (F : X' ⟶ X) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb (L.pull F) φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε), u.IsGen := by
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => φ k ≫ F) j ≤
      LB.wchart (L.pull F) φ (fun k _ => j k) := fun j y hy =>
    Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (t.s fun k _ => j k)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  refine (gm_res (𝟙 Y) y (le j) hj _).trans ((gen_trans ht (𝟙 Y) y (le j hj) (le j' hj')).trans
    (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y (le j') hj' _).symm))
  refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
  exact (gm_pull_g L F (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
    (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans (by rw [Category.assoc])
end GlobalTheory.CubeDescent
