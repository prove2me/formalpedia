-- Prove2me | solution 1 for GlobalTheory.polyChart_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:05.201885+00:00
-- url     : https://prove2.me/submissions/5600d33d-e7c7-4c4d-8365-aa9284cb49ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PolyChartSmoothFractionLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {K F₀ : Type} (V : Type) [Field K] [Field F₀] [Algebra K F₀] (R₀ : Subalgebra K F₀)
namespace GlobalTheory
theorem _root_.solution (h : ∀ x : F₀, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a)
    (p : MvPolynomial V F₀) :
    ∃ b : R₀, (b : F₀) ≠ 0 ∧ ∃ q : MvPolynomial V R₀,
      p * C (b : F₀) = MvPolynomial.map (R₀.val : R₀ →+* F₀) q := by
  induction p using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h x
    refine ⟨⟨b, hb⟩, hb0, C ⟨a, ha⟩, ?_⟩
    rw [MvPolynomial.map_C, ← map_mul]
    exact congrArg C e
  | add p q hp hq =>
    obtain ⟨b, hb, p', e⟩ := hp
    obtain ⟨c, hc, q', f⟩ := hq
    refine ⟨b * c, mul_ne_zero hb hc, p' * C c + q' * C b, ?_⟩
    rw [map_add, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, ← e, ← f]
    change (p + q) * C ((b : F₀) * c) = p * C (b : F₀) * C (c : F₀) + q * C (c : F₀) * C (b : F₀)
    rw [map_mul]
    ring
  | mul_X p v hp =>
    obtain ⟨b, hb, p', e⟩ := hp
    refine ⟨b, hb, p' * X v, ?_⟩
    rw [map_mul, MvPolynomial.map_X, ← e]
    ring
end GlobalTheory
