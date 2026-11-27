-- Prove2me | solution 1 for GlobalTheory.lbIso_extend_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:20.634695+00:00
-- url     : https://prove2.me/submissions/3631d5b8-3f13-4949-9040-a4d1e873d6a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LineBundleIsoExtendOfNormalBase
import Theorems.Thm_GlobalTheory_IsoExtend_exists_gen_chartPull
import Theorems.Thm_GlobalTheory_IsoExtend_lbIso_pull_iff_gen
import Theorems.Thm_GlobalTheory_IsoExtend_exists_gen_of_chart
import Theorems.Thm_GlobalTheory_IsoExtend_exists_gen_of_diff
import Theorems.Thm_GlobalTheory_IsoExtend_exists_gen_diff
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_div


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
open GlobalTheory.IsoExtend
namespace GlobalTheory
theorem _root_.solution : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → ∀ (L M : LB H), L.IsLB → M.IsLB → LBIso (L.pull jH) (M.pull jH) → (LBIso (L.pull e) (M.pull e) → LBIso L M) ∧ ∀ s : S, ∃ N : S.Opens, s ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι) := by
  intro S _ _ hS U H HU _ j _ p e jH pU hp hg he sq L M hL hM h
  have hD : (LB.div M L).IsLB := LB.isLB_div hM hL
  obtain ⟨c, hc⟩ := exists_gen_diff S hS U H HU j p e jH pU hp hg he sq hD ((lbIso_pull_iff_gen L M jH).1 h)
  refine ⟨fun h' => ?_, fun s => ?_⟩
  · exact exists_gen_chartPull (chartPullUnpull (LB.div M L) (𝟙 H) rfl)
      (exists_gen_of_diff hD _ c hc (𝟙 H) p e (Category.id_comp _) ((lbIso_pull_iff_gen L M e).1 h'))
  · obtain ⟨i, hi⟩ := exists_chart hD (e s)
    refine ⟨e ⁻¹ᵁ (LB.div M L).U i, hi, (lbIso_pull_iff_gen L M _).2 ?_⟩
    exact exists_gen_of_diff hD _ c hc _ (𝟙 _) _ (Category.id_comp _).symm
      (exists_gen_of_chart hD _ i fun y => y.2)
end GlobalTheory
