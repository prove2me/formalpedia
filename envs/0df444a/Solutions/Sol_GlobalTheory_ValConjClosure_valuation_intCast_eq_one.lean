-- Prove2me | solution 1 for GlobalTheory.ValConjClosure.valuation_intCast_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:30.519803+00:00
-- url     : https://prove2.me/submissions/eaf09d90-d77f-437e-bb23-4c3c040049a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsTopWTopWOfExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsGaloisConjValuationSubringSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsConjOverPrime

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
theorem _root_.solution {Ω : Type} [Field Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : A.valuation (n : Ω) = 1 := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  refine le_antisymm (hle n) (not_lt.mp fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hn
  have hab' : (a : Ω) * (p : Ω) + (b : Ω) * (n : Ω) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have h1 : A.valuation ((a : Ω) * (p : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (a : Ω) * A.valuation (p : Ω) ≤ 1 * A.valuation (p : Ω) :=
          mul_le_mul' (hle a) le_rfl
      _ < 1 := by rwa [one_mul]
  have h2 : A.valuation ((b : Ω) * (n : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (b : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) :=
          mul_le_mul' (hle b) le_rfl
      _ < 1 := by rwa [one_mul]
  have hadd := A.valuation.map_add ((a : Ω) * (p : Ω)) ((b : Ω) * (n : Ω))
  rw [hab', map_one] at hadd
  exact absurd hadd (not_le.mpr (max_lt h1 h2))
end GlobalTheory.ValConjClosure
