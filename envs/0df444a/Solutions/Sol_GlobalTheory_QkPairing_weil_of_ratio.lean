-- Prove2me | solution 1 for GlobalTheory.QkPairing.weil_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:53:13.628044+00:00
-- url     : https://prove2.me/submissions/7f863cea-e585-49ac-9c48-76422a8883b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ClosedPointWeilPower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_WeilQkPairingExistsUniqueTorus
import Theorems.Thm_GlobalTheory_QkPairing_cub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_isSmul_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_phiRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sval_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_uVal_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_uVal_tr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.QkPairing
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
namespace GlobalTheory.QkPairing
theorem _root_.solution (hG : GlobalFnsSt) (p p' : QkPt D F k) {ζ : Fˣ} (H : IsRatio p p' ζ.val) :
    WeilQkIs D F k p p' ζ.val := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ r₁ r₂ r₃ r₄
  rw [phiRel_iff hG _ _ hw'] at r₁ r₄
  rw [phiRel_iff hG _ _ hw] at r₂ r₃
  rw [isSmul_iff]
  refine fam_ext fun β j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  obtain ⟨α, rfl⟩ : ∃ α, α + p'.y + p.y = β := ⟨β - p.y - p'.y, by abel⟩
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have hy : ∀ q : QkPt D F k, cP D (DegPre.BF D F) q.y = (fst (TF (R := R) F) D.P.A ≫ q.g.b) ^ k := fun q => by
    rw [← comp_cP D (fst (TF (R := R) F) D.P.A), cPoint_y]; exact map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _
  have e₂ := r₂ (α + p'.y) _ rfl _ (𝟙 _) y J hJ
  have e₁ := r₁ α _ rfl _ (DegPre.trPt D F p.g.b) y J hJ
  have e₄ := r₄ (α + p.y) _ (add_right_comm α p.y p'.y) _ (𝟙 _) y J hJ
  have e₃ := r₃ α _ rfl _ (DegPre.trPt D F p'.g.b) y J hJ
  rw [Category.id_comp, Category.id_comp, Over.id_left, e₁, tr_fst, uVal_tr, uVal_id, val_mul hJ, val_mul hJ,
    cPoint_add, hy] at e₂
  rw [Category.id_comp, Category.id_comp, Over.id_left, e₃, tr_fst, uVal_tr, uVal_id, val_mul hJ, val_mul hJ,
    cPoint_add, hy, tr_comm] at e₄
  have t₁ := gt_mul (fst (TF (R := R) F) D.P.A) hJ p'.g α p.y
  have t₂ := gt_mul (fst (TF (R := R) F) D.P.A) hJ p.g α p'.y
  rw [hy] at t₁ t₂
  have t₃ := H _ (fst (TF (R := R) F) D.P.A) y J hJ
  obtain ⟨c, hc⟩ : ∃ c : ((DegPre.BF D F).left.presheaf.stalk y)ˣ, c.val =
      gs (fst (TF (R := R) F) D.P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ.val) :=
    ⟨_, (gs_unit _ y ⊤ trivial (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ)).symm⟩
  rw [← hc, ← Units.val_mul] at t₃
  have key := cub_comm C k _ _ _ (DegPre.prB D F) _ _ _ _ _ _ _ t₁ t₂ (Units.ext t₃)
  rw [sval_smul _ _ _ _ y hJ, Category.id_comp, ← hc, e₂, e₄, _root_.mul_assoc (sval _ _ _ _), _root_.mul_assoc (sval _ _ _ _),
    ← Units.val_mul, ← Units.val_mul, mul_left_comm c.val, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at key' ⊢
  linear_combination (norm := abel) key'
end GlobalTheory.QkPairing
