-- Prove2me | solution 1 for GlobalTheory.UT.TorusWeight.phiRel_tor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:10.781093+00:00
-- url     : https://prove2.me/submissions/3776b958-d542-49d7-b058-712f013efdb8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TxFrameOfOne
import Theorems.Thm_GlobalTheory_UT_TorusWeight_val_const
import Theorems.Thm_GlobalTheory_UT_TorusWeight_sval_const
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_inv
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_phiRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV


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
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.TorusWeight
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.TorusWeight
theorem _root_.solution (hG : GlobalFnsSt) {N : ℕ} (p : QkPt D F N) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) {w : Frm D F N p.g.b} (hw : FrmOne w) (s s' : Fam D F N) :
    PhiRel D F N p w s s' ↔
      ∀ α j, (s'.s α).f j = DegPre.constBF D F (τ (Multiplicative.ofAdd α)).val _ * (s.s α).f j := by
  have tr : DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.id_comp]; exact tr_fst D F _
    · rw [Category.id_comp]
      refine (tr_pr D F _).trans ?_
      rw [hτ.1, MonObj.comp_one, _root_.mul_one]
  have v : ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      (uVal D F N α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val =
        gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd α)).val) := by
    intro α T ρ z J hJ
    have C : IsCub (th D z J) := isCub_cubV D.cub hJ
    have hu : uVal D F N α p.g.b ρ z J = 1 := by
      rw [uVal, hτ.1]
      simp only [MonObj.comp_one]
      unfold cubN
      simp only [C.face₃, C.face₂, Finset.prod_const_one, inv_one, _root_.mul_one]
    have h₁ := val_const (p.g.s α) _ (hτ.2 α) (ρ ≫ fst _ _).left z hJ
    have h₂ := val_const w 1 (fun y J hJ => by
      rw [hw.2 y J hJ, gs_eq _ _ ⊤ trivial, map_one, map_one]; rfl) (ρ ≫ fst _ _).left z hJ
    rw [gs_eq _ _ ⊤ trivial, map_one, map_one] at h₂
    rw [hu, _root_.one_mul, val_mul hJ, Units.val_mul, h₁, h₂, _root_.mul_one]
  rw [phiRel_iff hG p w hw.1]
  constructor
  · intro H α
    refine (sval_const α _ _ _).2 fun T ρ z J hJ => ?_
    have := H α α (by rw [hy, add_zero]) T ρ z J hJ
    rwa [v α T ρ z J hJ, tr, Category.comp_id] at this
  · intro H α β h T ρ z J hJ
    obtain rfl : α = β := by rw [← h, hy, add_zero]
    rw [v α T ρ z J hJ, tr, Category.comp_id]
    exact (sval_const α _ _ _).1 (H α) T ρ z J hJ
end GlobalTheory.UT.TorusWeight
