-- Prove2me | solution 1 for GlobalTheory.ColengthDifferent.mul_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:30:02.044832+00:00
-- url     : https://prove2.me/submissions/b26a1878-7c65-47e6-8fb3-2f210fcd0552

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero
import Theorems.Thm_GlobalTheory_ColengthDifferent_mul_dual_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ColengthDifferent
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.ColengthDifferent
theorem _root_.solution {T : Type} [CommRing T] (t : 𝓞 E →+* T) {R : Type} [Ring R] [Algebra T R]
    (A : 𝓞 E →+* R) {c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E} {δ : 𝓞 E}
    (hc : ∀ k, algebraMap (𝓞 E) E (c k) = algebraMap (𝓞 E) E δ * (integralBasis E).traceDual k)
    (a : 𝓞 E) :
    A a * ∑ k, t (c k) • A (RingOfIntegers.basis E k) =
      t a • ∑ k, t (c k) • A (RingOfIntegers.basis E k) := by
  set ω := RingOfIntegers.basis E
  have h1 : ∀ l, t (a * c l) • A (ω l) = ∑ k, (ω.repr (a * ω k) l) • (t (c k) • A (ω l)) := by
    intro l
    rw [mul_dual_expand hc, map_sum, Finset.sum_smul]
    simp only [map_zsmul, smul_assoc]
    rfl
  calc A a * ∑ k, t (c k) • A (ω k) = ∑ k, t (c k) • A (a * ω k) := by
        rw [Finset.mul_sum]; simp only [mul_smul_comm, map_mul]
    _ = ∑ k, ∑ l, (ω.repr (a * ω k) l) • (t (c k) • A (ω l)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        conv_lhs => rw [← ω.sum_repr (a * ω k)]
        rw [map_sum, Finset.smul_sum]
        simp only [map_zsmul, smul_comm (t (c k))]
    _ = ∑ l, t (a * c l) • A (ω l) := by rw [Finset.sum_comm]; simp only [h1]
    _ = t a • ∑ k, t (c k) • A (ω k) := by rw [Finset.smul_sum]; simp only [map_mul, mul_smul]
end GlobalTheory.ColengthDifferent
