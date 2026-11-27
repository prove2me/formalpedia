-- Prove2me | solution 1 for GlobalTheory.LocLatInert.set_classify
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:49:24.608137+00:00
-- url     : https://prove2.me/submissions/7877d030-d9bc-45d3-a6d6-287a019ce3ad

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableLatticeEqZpowStdInertCompletion
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open scoped Matrix
open GlobalTheory GlobalTheory.LocLatInert
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.LocLatInert
theorem _root_.solution (I : Set K) (hmul : ∀ a : K, Valued.v a ≤ 1 → ∀ t ∈ I, a * t ∈ I)
    (N : K) (hN : N ≠ 0) (hNI : N ∈ I) (hb : ∀ t ∈ I, Valued.v (N * t) ≤ 1) :
    ∃ M : ℤ, ∀ t, t ∈ I ↔ Valued.v t ≤ WithZero.exp M := by
  have hvN : Valued.v N ≠ 0 := (Valuation.ne_zero_iff _).2 hN

  let S : Set ℤ := {m | ∃ t ∈ I, Valued.v t = WithZero.exp m}
  have hS : S.Nonempty := ⟨WithZero.log (Valued.v N), N, hNI, (WithZero.exp_log hvN).symm⟩
  have hbdd : BddAbove S := by
    refine ⟨-WithZero.log (Valued.v N), ?_⟩
    rintro m ⟨t, ht, hvt⟩
    have h1 := hb t ht
    rw [map_mul, hvt, ← WithZero.exp_log hvN, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h1
    omega

  obtain ⟨t0, ht0, hvt0⟩ : sSup S ∈ S := Int.csSup_mem hS hbdd
  refine ⟨sSup S, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · by_cases h0 : t = 0
    · rw [h0, map_zero]; exact zero_le
    · have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 h0
      rw [← WithZero.exp_log hvt, WithZero.exp_le_exp]
      exact le_csSup hbdd ⟨t, ht, (WithZero.exp_log hvt).symm⟩
  · have ht00 : t0 ≠ 0 := by
      intro h0; rw [h0, map_zero] at hvt0; exact WithZero.exp_ne_zero hvt0.symm
    have e : t = (t * t0⁻¹) * t0 := by field_simp
    rw [e]
    refine hmul _ ?_ t0 ht0
    rw [map_mul, map_inv₀, hvt0]
    calc Valued.v t * (WithZero.exp (sSup S))⁻¹
        ≤ WithZero.exp (sSup S) * (WithZero.exp (sSup S))⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero
end GlobalTheory.LocLatInert
