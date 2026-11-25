-- Prove2me | solution 1 for GlobalTheory.IsoExtend.exists_gen_chartPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:58.011674+00:00
-- url     : https://prove2.me/submissions/74c5f44c-9237-46b0-b23f-908f484d6e80

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IsoExtend
variable {X Y Y' : Scheme.{0}}
namespace GlobalTheory.IsoExtend
theorem _root_.solution {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (H : ∃ t : LB.Gen A, t.IsGen) : ∃ t : LB.Gen A', t.IsGen := by
  obtain ⟨w, hw⟩ := H
  refine ⟨⟨fun i => res (a.le i) (pullU h _ (w.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have val : ∀ i, y ∈ A'.U i → gm (𝟙 Y') y _ (res (a.le i) (pullU h _ (w.s (a.idx i)))) =
      gm h y (A.U (a.idx i)) (w.s (a.idx i)) := fun i hi =>
    (gm_res (𝟙 Y') y (a.le i) hi _).trans ((gm_pull (𝟙 Y') h y _ (a.le i hi) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := congrArg (gm h y (A.U (a.idx i) ⊓ A.U (a.idx j))) (hw (a.idx i) (a.idx j))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    rfl (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (val i hy.1)).trans (e'.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2)
    ((gm_res (𝟙 Y') y _ hy _).trans (val j hy.2)))
end GlobalTheory.IsoExtend
