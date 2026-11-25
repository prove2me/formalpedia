-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.appLE_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:07.043708+00:00
-- url     : https://prove2.me/submissions/6e806985-15b8-42d3-8aee-fa290db0743e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution {X : Scheme.{0}} (U : X.Opens) (e : U ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U e).hom x = x := by
  have h : X.presheaf.map (homOfLE e).op = 𝟙 _ := by
    rw [show (homOfLE e).op = 𝟙 (op U) from Subsingleton.elim _ _]; exact X.presheaf.map_id _
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  erw [h]
  rfl
end GlobalTheory.CompanionTheory.HopfSys
