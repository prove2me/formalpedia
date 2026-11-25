-- Prove2me | solution 1 for GlobalTheory.IsoExtend.exists_gen_of_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:21:27.57529+00:00
-- url     : https://prove2.me/submissions/f10e2bdd-c658-4b0b-9663-7d611d2bf4c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LineBundleIsoExtendOfNormalBase
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


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
theorem _root_.solution {D : LB X} (hD : D.IsLB) (σ : X ⟶ X)
    (c : LB.Gen (LB.LinComb D ![𝟙 X, σ] ![1, -1])) (hc : c.IsGen) (r : Y ⟶ X) {B : Scheme.{0}} (q : Y ⟶ B)
    (τ : B ⟶ X) (hr : r ≫ σ = q ≫ τ) (H : ∃ t : LB.Gen (D.pull τ), t.IsGen) :
    ∃ t : LB.Gen (D.pull r), t.IsGen := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨u, hu, -⟩ := exists_gen hD (φ' := fun _ : PUnit => r) (ε' := fun _ => 1) (by
      intro U _ h
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, hr])
    (LB.mulGen D _ _ _ _ (LB.pullGen D _ _ c r) (LB.pullGen D _ _ t q))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ c hc r) (DVR.pullGen_isGen _ _ _ t ht q))
  exact ⟨u, hu⟩
end GlobalTheory.IsoExtend
