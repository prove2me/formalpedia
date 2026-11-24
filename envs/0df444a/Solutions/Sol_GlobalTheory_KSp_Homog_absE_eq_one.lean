-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.absE_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:24:39.574512+00:00
-- url     : https://prove2.me/submissions/b650f779-299e-4097-8444-c94b4998527b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_of_valuation_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Homog
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.KSp.Homog
theorem _root_.solution {x : F} (hx : valuation F x = 1) : absE x = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h := GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (x := Units.mk0 x hx0) (by simpa using hx)
  simp only [GlobalTheory.SplitWeil.nabs, NNReal.coe_eq_one] at h
  simp [absE, hx0, h]
end GlobalTheory.KSp.Homog
