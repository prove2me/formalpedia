-- Prove2me | solution 1 for GlobalTheory.ValConjClosure.ratCast_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:08.423023+00:00
-- url     : https://prove2.me/submissions/edafd50d-8242-4c66-8cbf-7b6fd74933a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsTopWTopWOfExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsGaloisConjValuationSubringSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsConjOverPrime
import Theorems.Thm_GlobalTheory_ValConjClosure_valuation_intCast_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
open GlobalTheory GlobalTheory.ValConjClosure
namespace GlobalTheory.ValConjClosure
theorem _root_.solution {Ω : Type} [Field Ω] [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (a : ℚ) : (a : Ω) ∈ A ↔ ¬ p ∣ a.den := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hden0 : (a.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  rw [Rat.cast_def, ← A.valuation_le_one_iff]
  constructor
  · intro ha hd
    have hnum : ¬ (p : ℤ) ∣ a.num := by
      intro h
      have h1 : p ∣ a.num.natAbs := Int.natCast_dvd.mp h
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 a.reduced) hd)
    have hv1 := valuation_intCast_eq_one hp A hA a.num hnum
    obtain ⟨k, hk⟩ := hd
    have hdlt : A.valuation (a.den : Ω) < 1 := by
      rw [hk, Nat.cast_mul, map_mul]
      calc A.valuation (p : Ω) * A.valuation (k : Ω) ≤ A.valuation (p : Ω) * 1 :=
            mul_le_mul' le_rfl (by exact_mod_cast hle k)
        _ < 1 := by rwa [mul_one]
    have hnd : A.valuation (a.num : Ω) ≤ A.valuation (a.den : Ω) := by
      rw [← div_mul_cancel₀ (a.num : Ω) hden0, map_mul]
      calc A.valuation ((a.num : Ω) / (a.den : Ω)) * A.valuation (a.den : Ω) ≤
            1 * A.valuation (a.den : Ω) := mul_le_mul' ha le_rfl
        _ = A.valuation (a.den : Ω) := one_mul _
    rw [hv1] at hnd
    exact absurd (lt_of_le_of_lt hnd hdlt) (lt_irrefl 1)
  · intro hd
    have hv1 : A.valuation (a.den : Ω) = 1 := by
      have h := valuation_intCast_eq_one hp A hA (a.den : ℤ) (by exact_mod_cast hd)
      exact_mod_cast h
    rw [map_div₀, hv1, div_one]
    exact hle a.num
end GlobalTheory.ValConjClosure
