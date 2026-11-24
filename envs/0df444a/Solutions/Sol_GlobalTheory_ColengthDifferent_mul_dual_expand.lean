-- Prove2me | solution 1 for GlobalTheory.ColengthDifferent.mul_dual_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:14:38.129703+00:00
-- url     : https://prove2.me/submissions/5ae9412a-bba0-484f-984a-0b90d0cca4de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero

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
theorem _root_.solution {c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E} {δ : 𝓞 E}
    (hc : ∀ k, algebraMap (𝓞 E) E (c k) = algebraMap (𝓞 E) E δ * (integralBasis E).traceDual k)
    (a : 𝓞 E) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    a * c l = ∑ k, (RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l • c k := by
  apply FaithfulSMul.algebraMap_injective (𝓞 E) E
  set b := integralBasis E
  set ω := RingOfIntegers.basis E
  rw [map_mul, hc, map_sum]
  have hrepr : ∀ k, algebraMap (𝓞 E) E ((ω.repr (a * ω k) l) • c k) =
      (b.traceDual.repr (algebraMap (𝓞 E) E a * b.traceDual l) k) •
        (algebraMap (𝓞 E) E δ * b.traceDual k) := by
    intro k
    rw [map_zsmul, hc, ← Int.cast_smul_eq_zsmul ℚ]
    congr 1
    rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]
    have h := (b.traceDual).traceDual_repr_apply (algebraMap (𝓞 E) E (a * ω k)) l
    rw [Module.Basis.traceDual_traceDual, integralBasis_repr_apply, Algebra.traceForm_apply] at h
    have hb : b k = algebraMap (𝓞 E) E (ω k) := integralBasis_apply E k
    rw [← eq_intCast (algebraMap ℤ ℚ), h, hb]
    congr 1
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl fun k _ => hrepr k]
  simp_rw [← mul_smul_comm, ← Finset.mul_sum]
  rw [b.traceDual.sum_repr]
  ring
end GlobalTheory.ColengthDifferent
