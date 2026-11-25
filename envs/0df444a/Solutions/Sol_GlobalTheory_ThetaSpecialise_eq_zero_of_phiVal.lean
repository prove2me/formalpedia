-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.eq_zero_of_phiVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:08.79107+00:00
-- url     : https://prove2.me/submissions/a332eb94-3156-49a2-b5af-29aad88fb57e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_zero__c17798940263
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (s : Fam D F k)
    (h : PhiVal p w s.s (0 : Fam D F k).s) : s = 0 := by
  have := D.P.isAb.comm
  have r : DegPre.trPt D F p.g.b⁻¹ ≫ DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, tr_fst, Category.id_comp]
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D F _)).trans ?_)
      rw [MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst, _root_.mul_assoc, ← MonObj.comp_mul, inv_mul_cancel,
        MonObj.comp_one, _root_.mul_one, Category.id_comp]
  refine fam_ext fun α j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  have e := h α _ rfl _ (DegPre.trPt D F p.g.b⁻¹) y J hJ
  rw [r] at e
  have z : ∀ β (r : (DegPre.BF D F).left ⟶ (DegPre.BF D F).left), sval ((0 : Fam D F k).s β) r y J = 0 := fun β r =>
    sval_zero' (π := famBase D F) hJ r
  rw [z] at e ⊢
  exact (Units.mul_left_eq_zero _).1 e.symm
end GlobalTheory.ThetaSpecialise
