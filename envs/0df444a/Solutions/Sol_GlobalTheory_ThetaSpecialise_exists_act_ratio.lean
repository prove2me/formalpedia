-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.exists_act_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:59.682795+00:00
-- url     : https://prove2.me/submissions/a0b5c3ba-23a9-461c-881e-ac9272f367ac

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
import Theorems.Thm_GlobalTheory_ThetaSpecialise_lpow_ext
import Theorems.Thm_P2M_GlobalTheory_ThetaSpecialise_secVal_smul__73f8796224c6
import Theorems.Thm_GlobalTheory_ThetaAct_exists_ratio
import Theorems.Thm_GlobalTheory_ThetaBaseChange_actVal_of_isActOf
import Theorems.Thm_GlobalTheory_ThetaSpecialise_exists_ratio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
variable {S₀ : Scheme.{0}} {A : Over S₀} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S₀}
  {S : Type} [CommRing S]
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {F : Type} [Field F]
    {t : Spec (CommRingCat.of F) ⟶ S₀} (θ θ' : ThetaGrp A L k (Over.mk t)) (h : θ.pt = θ'.pt)
    (π : (Over.mk t ⊗ A).left ⟶ Spec (CommRingCat.of F)) (hπ : π = (fst (Over.mk t) A).left) :
    ∃ c : F, c ≠ 0 ∧ ∀ s s₁ s₂ : SecOver π (LPow A L k (Over.mk t)), IsActOf A L k θ s s₁ →
      IsActOf A L k θ' s s₂ → s₂ = c • s₁ := by
  obtain ⟨u, hu⟩ := ThetaAct.exists_ratio hG hA hL θ θ' h
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 u.val
  refine ⟨c, ?_, fun s s₁ s₂ h₁ h₂ => lpow_ext hL fun y J hJ => ?_⟩
  · rintro rfl
    have : Nontrivial Γ((Over.mk t).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
    exact u.ne_zero (hc.symm.trans (map_zero _))
  · refine (actVal_of_isActOf h₂ _ _ y J hJ).trans (Eq.trans ?_ (secVal_smul' π _ _ _ y hJ).symm)
    rw [actVal_of_isActOf h₁ _ _ y J hJ, ← _root_.mul_assoc, h]
    refine congrArg (· * _) ((hu _ _ y J hJ).trans (congrArg (· * _) ?_))
    rw [hπ, ← hc]; rfl
end GlobalTheory.ThetaSpecialise
