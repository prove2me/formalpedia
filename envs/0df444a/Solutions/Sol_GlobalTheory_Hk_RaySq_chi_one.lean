-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.chi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:09.482408+00:00
-- url     : https://prove2.me/submissions/a19e263e-23cb-4555-9df1-c98dc43df1a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
variable {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution (ε : D.G → ℝ) (h1 : ε 1 = 1) : chi D ε 1 = 1 := by
  have hc : IsCoprime (1 : Ideal (𝓞 K)) (Ideal.span {(M : 𝓞 K)}) := isCoprime_one_left
  have hb : (1 : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ideal.one_eq_top]
    exact top_ne_bot
  have hcls : D.cls 1 = 1 := by
    have e := D.cls_mul 1 1 hc hc hb hb
    rw [one_mul] at e
    exact mul_left_cancel (by rw [mul_one]; exact e.symm : D.cls 1 * D.cls 1 = D.cls 1 * 1)
  rw [chi, if_pos ⟨hb, hc⟩, hcls, h1]
end GlobalTheory.Hk.RaySq
