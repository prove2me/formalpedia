-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dict.dictSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:35:59.752737+00:00
-- url     : https://prove2.me/submissions/a9c7c119-e2e9-47f0-9667-c1ea6dba02c3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_L0_bijective_cochain
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_L1_bijective_cochain
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_L2_bijective_cochain
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_L3_bijective_cochain
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_L1_dn_zero_eq_d0_L0
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_L2_dn_one_eq_d1_L1
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_L3_dn_two_eq_d2_L2
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dict
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.Dict
theorem _root_.solution : DictSt := by
  intro R _ C _ F
  refine ⟨LinearEquiv.ofBijective (L0 F) (L0_bijective_cochain F), LinearEquiv.ofBijective (L1 F) (L1_bijective_cochain F),
    LinearEquiv.ofBijective (L2 F) (L2_bijective_cochain F), LinearEquiv.ofBijective (L3 F) (L3_bijective_cochain F),
    fun _ _ => ?_, fun _ _ _ _ => ?_, fun _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_,
    fun f => ?_, fun f => ?_, fun f => ?_⟩ <;> simp only [LinearEquiv.ofBijective_apply]
  · rfl
  · rfl
  · rfl
  · rfl
  · exact L1_dn_zero_eq_d0_L0 F f
  · exact L2_dn_one_eq_d1_L1 F f
  · exact L3_dn_two_eq_d2_L2 F f
end GlobalTheory.CompanionTheory.Dict
