-- Prove2me | solution 1 for GlobalTheory.GtBaseChange.isGt_extBC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:58:47.91579+00:00
-- url     : https://prove2.me/submissions/935b67a2-f236-4bcd-8811-742400c49021

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Theorems.Thm_GlobalTheory_GtBaseChange_translate_mem
import Theorems.Thm_GlobalTheory_GtBaseChange_hasWeight_iff
import Theorems.Thm_GlobalTheory_GtBaseChange_coord_of_hasWeight
import Theorems.Thm_GlobalTheory_GtBaseChange_HasWeight_baseChange
import Theorems.Thm_GlobalTheory_GtBaseChange_chart_le_preimage
import Theorems.Thm_GlobalTheory_TorusExtBaseChange_exists_extension
import Theorems.Thm_GlobalTheory_splitTorus_baseChange
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] SplitExt.free SplitExt.finite
noncomputable section
open GlobalTheory
open GlobalTheory.GtBaseChange
variable {S S' : Scheme.{0}} (f : S' ⟶ S)
namespace GlobalTheory.GtBaseChange
theorem _root_.solution (E : SplitExt S) (G : Over S) [GrpObj G] (d : E.GtDatum G) :
    (extBC f E).IsGt ((Over.pullback f).obj G) := by
  have := d.q_hom
  have := d.i_hom
  have : IsMonHom (Iso.refl ((Over.pullback f).obj G)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  have : IsMonHom (Iso.refl ((Over.pullback f).obj E.B)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨eT, mT, hT⟩ := splitTorus_baseChange S S' f E.X
  obtain ⟨q, i, h1, h2, h3, h4, h5, h6, h7, h8⟩ := TorusExtBaseChange.exists_extension f eT
    (Iso.refl ((Over.pullback f).obj G)) (Iso.refl ((Over.pullback f).obj E.B)) d.i d.q d.q_flat d.q_surjective
    d.q_affine d.isKernel
  have hq : q.left ≫ pullback.fst E.B.hom f = pullback.fst G.hom f ≫ d.q.left := by simpa using h7
  have hi : i.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst _ f) ≫ d.i.left := by simpa using h8
  have le : ∀ j : (extBC f E).ChartIdx, q.left ⁻¹ᵁ (extBC f E).chart j ≤
      pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) := fun j y hy => by
    change (pullback.fst G.hom f ≫ d.q.left) y ∈ E.chart (fun k => j k PUnit.unit)
    rw [← hq]
    exact chart_le_preimage f E j hy
  let u : ∀ (j : (extBC f E).ChartIdx) (_ : Module.Free.ChooseBasisIndex ℤ E.X),
      Γ(((Over.pullback f).obj G).left, q.left ⁻¹ᵁ (extBC f E).chart j)ˣ := fun j k =>
    res (le j) (pullU (pullback.fst G.hom f) _ (d.u (fun k => j k PUnit.unit) k))
  have hw : ∀ j k, HasWeight i _ (u j k) (E.basis k) := fun j k =>
    HasWeight.baseChange f ((hasWeight_iff d.i _ _ _ (d.act_le _) _).2 (d.equiv _ k)) i _ (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w eT.hom)) hi (hT _) (le j)
      fun Z t g z hz => translate_mem q i h6 t g _ z hz
  refine ⟨
    { q := q
      i := i
      q_hom := h1
      i_hom := h5
      q_flat := h2
      q_surjective := h3
      q_affine := h4
      isKernel := h6
      u := u
      coord := fun j V hV h => coord_of_hasWeight E.basis q i h2 h3 h4 h6 _ (u j) (hw j) V hV h
      trans := fun j j' k => unit_ext fun y hy => ?_
      act_le := fun j y hy => translate_mem q i h6 (fst _ _) (snd _ _) ((extBC f E).chart j) y hy
      equiv := fun j k => (hasWeight_iff i _ _ _ _ _).1 (hw j k)
      unit_norm := fun j k => unit_ext fun y hy => ?_ }⟩
  · have hm : pullback.fst G.hom f y ∈ d.q.left ⁻¹ᵁ
        (E.chart (fun k => j k PUnit.unit) ⊓ E.chart (fun k => j' k PUnit.unit)) := ⟨le j hy.1, le j' hy.2⟩
    have e := congrArg (gm (pullback.fst G.hom f) y _)
      (d.trans (fun k => j k PUnit.unit) (fun k => j' k PUnit.unit) k)
    have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_pull _ d.q.left y _ hm _).trans (gm_res (pullback.fst G.hom f ≫ d.q.left) y _ hm _))
      (gm_res _ y _ hm _))))
    refine ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j') hy.2 _)).trans (e'.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j) hy.1 _)))
    refine ((gm_pull (𝟙 _) q.left y _ hy _).trans (gm_res (𝟙 _ ≫ q.left) y _ hy _)).trans ?_
    refine (gm_pull_g (E.O (E.basis k)).L (pullback.fst E.B.hom f) (𝟙 _ ≫ q.left) y (j k) (j' k)
      ((extBC f E).chart_le j k hy.1) ((extBC f E).chart_le j' k hy.2)).trans ?_
    rw [Category.id_comp, hq]
  · have hs := eSec_fst f G
    have h₁ : (eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f) y ∈
        d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit) := le j hy.1
    rw [hs] at h₁
    have h₂ := (rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k) hy.2
    let f' : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left := f
    have hm : f' y ∈ eSec G ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) ⊓
        ((E.O (E.basis k)).L.pull (eSec E.B)).U (fun _ => j k PUnit.unit) := ⟨h₁, h₂⟩
    have e := congrArg (gm f' y _) (d.unit_norm (fun k => j k PUnit.unit) k)
    have e' := ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res_pullU f' _ y _ hm _) (gm_res f' y _ hm _))).symm.trans (e.trans (map_one _))
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)).trans (e'.trans (map_one _).symm)
    · refine (gm_res_pullU' _ y _ hy _).trans ((gm_res_pullU _ _ y (le j) hy.1 _).trans ?_)
      rw [hs]
    · exact (gm_res (𝟙 _) y _ hy _).trans
        (gm_res_pullU' f' y ((rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k)) hy.2 _)
end GlobalTheory.GtBaseChange
