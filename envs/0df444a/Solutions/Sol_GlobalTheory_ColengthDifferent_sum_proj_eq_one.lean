-- Prove2me | solution 1 for GlobalTheory.ColengthDifferent.sum_proj_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:30:03.207885+00:00
-- url     : https://prove2.me/submissions/765709d6-446a-4277-a56a-940d70eafbc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero
import Theorems.Thm_GlobalTheory_ColengthDifferent_sum_eq_trace

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
theorem _root_.solution {F : Type} [Field F] [CharZero F] {ι : Type} [Fintype ι]
    (σ : ι → (E →+* F)) (hσ : Function.Injective σ) (hcard : Fintype.card ι = Module.finrank ℚ E)
    {R : Type} [Ring R] [Algebra F R] (A : 𝓞 E →+* R)
    (δ : ι → 𝓞 E) (hδ0 : ∀ i, δ i ≠ 0) (c : ι → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E)
    (hc : ∀ i k, algebraMap (𝓞 E) E (c i k) =
      algebraMap (𝓞 E) E (δ i) * (integralBasis E).traceDual k) :
    ∑ i, (σ i (algebraMap (𝓞 E) E (δ i)))⁻¹ •
      ∑ k, σ i (algebraMap (𝓞 E) E (c i k)) • A (RingOfIntegers.basis E k) = 1 := by
  set b := integralBasis E
  set ω := RingOfIntegers.basis E
  have hd : ∀ i, σ i (algebraMap (𝓞 E) E (δ i)) ≠ 0 := fun i => by
    rw [map_ne_zero_iff _ (σ i).injective]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mpr (hδ0 i)
  have h1 : ∀ i, (σ i (algebraMap (𝓞 E) E (δ i)))⁻¹ •
      ∑ k, σ i (algebraMap (𝓞 E) E (c i k)) • A (ω k) = ∑ k, σ i (b.traceDual k) • A (ω k) := by
    intro i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc, map_mul, smul_smul, ← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
  have htr : ∀ k, ∑ i, σ i (b.traceDual k) = ((ω.repr 1 k : ℤ) : F) := by
    intro k
    rw [sum_eq_trace σ hσ hcard]
    have h := (b.traceDual).traceDual_repr_apply (algebraMap (𝓞 E) E 1) k
    rw [Module.Basis.traceDual_traceDual, integralBasis_repr_apply, Algebra.traceForm_apply,
      RingHom.map_one (algebraMap (𝓞 E) E), one_mul] at h
    rw [← h]
    rw [eq_intCast, eq_ratCast, Rat.cast_intCast]
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, htr, Int.cast_smul_eq_zsmul, ← map_zsmul, ← map_sum, ω.sum_repr, map_one]
end GlobalTheory.ColengthDifferent
