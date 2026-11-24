-- Prove2me | solution 1 for GlobalTheory.UnRep.NormOne.exists_coprime_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:55.365889+00:00
-- url     : https://prove2.me/submissions/75529741-912f-4b9f-b52f-6ca9a74b7931

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.UnRep.NormOne
theorem _root_.solution (N : ℕ) (hN : 0 < N) (z : 𝓞 E) (hw : 1 + (N : 𝓞 E) * z ≠ 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∃ γ : 𝓞 E, (t : 𝓞 E) = (1 + (N : 𝓞 E) * z) * γ := by
  set I : Ideal (𝓞 E) := Ideal.span {1 + (N : 𝓞 E) * z} with hI
  have hb : I ≠ ⊥ := by rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact hw
  have : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hb
  have h0 : Ideal.Quotient.mk I (1 + (N : 𝓞 E) * z) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hu : IsUnit (Ideal.Quotient.mk I (N : 𝓞 E)) :=
    IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (-z)) (by
      rw [map_add, map_one, map_mul] at h0
      rw [map_neg]; linear_combination -h0)
  obtain ⟨v, hv⟩ := hu
  obtain ⟨k, hk, hvk⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite v)
  have h1 : 1 ≤ N ^ k := Nat.one_le_pow _ _ hN
  refine ⟨N ^ k - 1, ?_, ?_⟩
  · have : (N ^ k - 1).Coprime (N ^ k) := by
      have := (Nat.coprime_self_sub_left h1).mpr (Nat.coprime_one_left _)
      exact this
    exact (Nat.coprime_pow_right_iff hk _ _).mp this
  · apply Ideal.mem_span_singleton.mp
    rw [← hI, ← Ideal.Quotient.eq_zero_iff_mem, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, map_sub,
      map_pow, ← hv, ← Units.val_pow_eq_pow_val, hvk]
    simp
end GlobalTheory.UnRep.NormOne
