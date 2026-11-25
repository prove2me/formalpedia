-- Prove2me | solution 1 for GlobalTheory.ZM.RepMap.lbIso_of_germs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:05.163688+00:00
-- url     : https://prove2.me/submissions/852cc827-a570-4295-af1e-38838761ca3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSchemeMapOfProjectiveCoordinates
import Theorems.Thm_GlobalTheory_ZM_RepMap_gs_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepMap
variable {X : Scheme.{0}} {σ : Type}
namespace GlobalTheory.ZM.RepMap
theorem _root_.solution (A B : LB X) (a : σ → A.Sec) (b : σ → B.Sec)
    (H : ∀ (y : X) (j : B.ι) (k : A.ι), y ∈ B.U j → y ∈ A.U k → (∃ i, IsUnit (gs (𝟙 X) y (A.U k) ((a i).f k))) ∧
      ∃ u : (X.presheaf.stalk y)ˣ, ∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u * gs (𝟙 X) y (A.U k) ((a i).f k)) :
    LBIso A B := by
  have uniq : ∀ (y : X) (j : B.ι) (k : A.ι), y ∈ B.U j → y ∈ A.U k → ∀ u u' : (X.presheaf.stalk y)ˣ,
      (∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u * gs (𝟙 X) y (A.U k) ((a i).f k)) →
      (∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u' * gs (𝟙 X) y (A.U k) ((a i).f k)) → u = u' := by
    intro y j k hj hk u u' h h'
    obtain ⟨i, hi⟩ := (H y j k hj hk).1
    exact Units.ext (hi.mul_right_cancel ((h i).symm.trans (h' i)))
  have loc : ∀ (j : B.ι) (k : A.ι) (y : ↥(B.U j ⊓ A.U k : X.Opens)), ∃ (W : X.Opens) (_ : W ≤ B.U j ⊓ A.U k) (c : Γ(X, W)ˣ),
      y.1 ∈ W ∧ ∀ z ∈ W, ∀ i, gs (𝟙 X) z (B.U j) ((b i).f j) = gm (𝟙 X) z W c * gs (𝟙 X) z (A.U k) ((a i).f k) := by
    rintro j k ⟨y, hy⟩
    obtain ⟨⟨i₀, hi₀⟩, u, hu⟩ := H y j k hy.1 hy.2
    let t : Γ(X, B.U j ⊓ A.U k) := resG X inf_le_left ((b i₀).f j) * resG X inf_le_right ((a i₀).f k)
    have hle := X.basicOpen_le t
    have ht : IsUnit (resG X hle t) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace t
    rw [map_mul] at ht
    obtain ⟨c₁, h₁⟩ := isUnit_of_mul_isUnit_left ht
    obtain ⟨c₂, h₂⟩ := isUnit_of_mul_isUnit_right ht
    refine ⟨X.basicOpen t, hle, c₁ * c₂⁻¹, ?_, fun z hz i => ?_⟩
    · rw [X.mem_basicOpen t y hy, ← gs_one y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, hu]
      exact (u.isUnit.mul hi₀).mul hi₀
    · obtain ⟨-, u', hu'⟩ := H z j k (hle hz).1 (hle hz).2
      have e₁ : (gm (𝟙 X) z _ c₁).val = gs (𝟙 X) z (B.U j) ((b i₀).f j) := by
        rw [← gs_unit _ z _ hz, h₁, gs_res _ z _ hz, gs_res _ z _ (hle hz)]
      have e₂ : (gm (𝟙 X) z _ c₂).val = gs (𝟙 X) z (A.U k) ((a i₀).f k) := by
        rw [← gs_unit _ z _ hz, h₂, gs_res _ z _ hz, gs_res _ z _ (hle hz)]
      have e : gm (𝟙 X) z _ c₁ = u' * gm (𝟙 X) z _ c₂ := Units.ext (by rw [Units.val_mul, e₁, e₂, hu'])
      rw [map_mul, map_inv, e, mul_inv_cancel_right, hu']
  choose W hW c hy hc using loc
  have glue : ∀ (j : B.ι) (k : A.ι), ∃ w : Γ(X, B.U j ⊓ A.U k)ˣ, ∀ z ∈ B.U j ⊓ A.U k, ∀ i,
      gs (𝟙 X) z (B.U j) ((b i).f j) = gm (𝟙 X) z _ w * gs (𝟙 X) z (A.U k) ((a i).f k) := by
    intro j k
    obtain ⟨w, hw⟩ := glue_unit (B.U j ⊓ A.U k) (W j k) (hW j k)
      (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hy j k ⟨z, hz⟩⟩) (c j k)
      (fun p q z hz => uniq z j k (hW j k p hz.1).1 (hW j k p hz.1).2 _ _ (hc j k p z hz.1) (hc j k q z hz.2))
    refine ⟨w, fun z hz i => ?_⟩
    rw [← gm_res (𝟙 X) z (hW j k ⟨z, hz⟩) (hy j k ⟨z, hz⟩), hw]
    exact hc j k ⟨z, hz⟩ z (hy j k ⟨z, hz⟩) i
  choose w hw using glue
  refine ⟨⟨fun p => w p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 X) y p q hy)
    (gm_res _ y _ hy _))).symm)
  refine uniq y p.1 p.2 hy.1.1 hy.1.2 _ _ (hw p.1 p.2 y hy.1) fun i => ?_
  have hB : y ∈ B.U p.1 ⊓ B.U q.1 := ⟨hy.1.1, hy.2.1⟩
  have hA : y ∈ A.U p.2 ⊓ A.U q.2 := ⟨hy.1.2, hy.2.2⟩
  have eB := congrArg (gs (𝟙 X) y _) ((b i).compat p.1 q.1)
  have eA := congrArg (gs (𝟙 X) y _) ((a i).compat p.2 q.2)
  rw [gs_mul _ y _ hB, gs_res _ y _ hB, gs_res _ y _ hB, gs_unit _ y _ hB] at eB
  rw [gs_mul _ y _ hA, gs_res _ y _ hA, gs_res _ y _ hA, gs_unit _ y _ hA] at eA
  rw [eB, eA, hw q.1 q.2 y hy.2 i]
  change _ = ((_ * _ * gm (𝟙 X) y _ (w q.1 q.2) : (X.presheaf.stalk y)ˣ) : X.presheaf.stalk y) * _
  rw [Units.val_mul, Units.val_mul]
  have := (gm (𝟙 X) y _ (A.g p.2 q.2)).inv_mul
  linear_combination (-(gm (𝟙 X) y _ (B.g p.1 q.1)).val * (gm (𝟙 X) y _ (w q.1 q.2)).val *
    gs (𝟙 X) y (A.U q.2) ((a i).f q.2)) * this
end GlobalTheory.ZM.RepMap
