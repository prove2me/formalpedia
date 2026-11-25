-- Prove2me | solution 1 for GlobalTheory.IsoExtend.exists_gen_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:34:46.257938+00:00
-- url     : https://prove2.me/submissions/b9264ed3-5258-4ef0-b499-627549d56e69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LineBundleIsoExtendOfNormalBase
import Theorems.Thm_GlobalTheory_GenExtendNormal_existsUnique_gen_extend
import Theorems.Thm_GlobalTheory_GenExtend_existsUnique_gen_extend
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_oneGen


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
theorem _root_.solution (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H)
    (pU : HU ⟶ U) (hp : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (sq : IsPullback jH pU p j)
    {D : LB H} (hD : D.IsLB) (H₀ : ∃ t : LB.Gen (D.pull jH), t.IsGen) :
    ∃ c : LB.Gen (LB.LinComb D ![𝟙 H, p ≫ e] ![1, -1]), c.IsGen := by
  obtain ⟨t, ht⟩ := H₀
  let eU : U ⟶ HU := sq.lift (j ≫ e) (𝟙 U) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : eU ≫ jH = j ≫ e := sq.lift_fst _ _ _
  have h₂ : eU ≫ pU = 𝟙 U := sq.lift_snd _ _ _
  have h₃ : jH ≫ p ≫ e = (pU ≫ eU) ≫ jH := by rw [Category.assoc, h₁, sq.w_assoc]
  obtain ⟨t', ht', vt⟩ := exists_gen hD (φ' := fun i => jH ≫ ![𝟙 H, p ≫ e] i) (ε' := ![1, -1]) (by
      intro U _ h
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, h₃])
    (LB.mulGen D _ _ _ _ t (LB.invGen D _ _ (LB.pullGen D _ _ t (pU ≫ eU))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ t ht _)))
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen hD (φ' := fun i => e ≫ ![𝟙 H, p ≫ e] i) (ε' := ![1, -1]) (by
      intro U _ h
      simp [Fin.prod_univ_two, reassoc_of% he])
    (LB.oneGen D) (LB.isGen_oneGen D)
  obtain ⟨c, ⟨hc, -⟩, -⟩ := GlobalTheory.GenExtendNormal.existsUnique_gen_extend S hS U H HU H j p e jH pU eU hp hg he sq h₁ D hD (Fin 2) _ _ t' ρ ht' hρ
    (corr_of_val hD fun y J hJ => by
      rw [val_pull hJ, val_pull hJ, vt _ _ _ _ hJ, vρ _ _ _ _ hJ, val_mul hJ, val_inv, val_pull hJ, val_one,
        Category.id_comp, reassoc_of% h₂, mul_inv_cancel])
  exact ⟨c, hc⟩
end GlobalTheory.IsoExtend
