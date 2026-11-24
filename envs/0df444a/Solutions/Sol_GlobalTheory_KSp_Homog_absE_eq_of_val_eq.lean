-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.absE_eq_of_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:37:14.743387+00:00
-- url     : https://prove2.me/submissions/6bdbac56-e1e8-4076-a217-6d09caac7ead

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
import Theorems.Thm_GlobalTheory_KSp_Homog_absE_eq_one

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
theorem _root_.solution {x y : F} (h : valuation F y = valuation F x) : absE y = absE x := by
  by_cases hx : x = 0
  · subst hx
    have : y = 0 := by simpa using h
    rw [this]
  have hy : y ≠ 0 := by rintro rfl; exact hx (by simpa using h.symm)
  have hu : valuation F (y / x) = 1 := by
    rw [map_div₀, h, div_self (by simpa using hx)]
  have e1 := absE_eq_one hu
  have hyx : Units.mk0 y hy = Units.mk0 x hx * Units.mk0 (y / x) (div_ne_zero hy hx) := by
    ext; simp [mul_div_cancel₀ _ hx]
  simp only [absE, dif_neg hy, dif_neg hx, dif_neg (div_ne_zero hy hx)] at e1 ⊢
  rw [hyx, map_mul, ENNReal.coe_mul, e1, mul_one]
end GlobalTheory.KSp.Homog
