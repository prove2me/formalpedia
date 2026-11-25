-- Prove2me | solution 1 for GlobalTheory.IsoExtend.exists_gen_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:38:16.225493+00:00
-- url     : https://prove2.me/submissions/40f446ef-4095-450e-a815-5965a4a90729

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LineBundleIsoExtendOfNormalBase
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IsoExtend
variable {X Y Y' : Scheme.{0}}
namespace GlobalTheory.IsoExtend
theorem _root_.solution {D : LB X} (hD : D.IsLB) (f : Y ⟶ X) (i : D.ι) (hf : ∀ y, f y ∈ D.U i) :
    ∃ t : LB.Gen (D.pull f), t.IsGen := by
  have le : ∀ J : PUnit → D.ι, (D.pull f).U J ≤ f ⁻¹ᵁ (D.U (J PUnit.unit) ⊓ D.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (D.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J, y ∈ (D.pull f).U J → gm (𝟙 Y) y _ (res (le J) (pullU f _ (D.g (J PUnit.unit) i))) =
      gm (𝟙 Y ≫ f) y _ (D.g (J PUnit.unit) i) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g D f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))).trans ?_
  exact gm_cocycle hD (𝟙 Y ≫ f) y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (hf y)
end GlobalTheory.IsoExtend
