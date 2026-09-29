-- Prove2me | solution 1 for IsAlgClosed.exists_isPrimitiveRoot_pow_and_pow_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/62fcf9b4-db5c-5e7f-94aa-0e31547f1066

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAlgClosed_exists_isPrimitiveRoot_pow_and_pow_succ_eq

set_option autoImplicit false

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) :
    ∃ ζ : ℕ → k, (∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) ∧ ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  haveI : NeZero (ℓ : k) := ⟨hℓ⟩
  obtain ⟨ζ₁, hζ₁⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k ℓ
  have hroot : ∀ x : k, ∃ z : k, z ^ ℓ = x := fun x => IsAlgClosed.exists_pow_nat_eq x hℓp.pos
  choose step hstep using hroot
  let ζ : ℕ → k := fun n => Nat.rec (motive := fun _ => k) 1 (fun m z => if m = 0 then ζ₁ else step z) n
  have hζ0 : ζ 0 = 1 := rfl
  have hζs : ∀ n : ℕ, ζ (n + 1) = if n = 0 then ζ₁ else step (ζ n) := fun n => rfl
  have hcompat : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n := by
    intro n
    rw [hζs]
    split_ifs with h
    · subst h; rw [hζ0]; exact hζ₁.pow_eq_one
    · exact hstep _
  have hprim : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n) := by
    intro n
    induction n with
    | zero => rw [hζ0, pow_zero]; exact IsPrimitiveRoot.one
    | succ n ih =>
      rcases n with _ | n
      · rw [hζs, if_pos rfl, zero_add, pow_one]; exact hζ₁
      · have hω : ζ (n + 2) ^ ℓ = ζ (n + 1) := hcompat (n + 1)
        have hη : IsPrimitiveRoot (ζ (n + 2) ^ ℓ ^ (n + 1)) ℓ := by
          have h' : ζ (n + 2) ^ ℓ ^ (n + 1) = ζ (n + 1) ^ ℓ ^ n := by
            rw [← hω, ← pow_mul, ← pow_succ']
          rw [h']
          exact ih.pow (pow_pos hℓp.pos _) (pow_succ ℓ n)
        rw [IsPrimitiveRoot.iff_def]
        refine ⟨?_, fun l hl => ?_⟩
        · rw [pow_succ, pow_mul, hη.pow_eq_one]
        · have h1 : ℓ ^ (n + 1) ∣ l := by
            rw [← ih.pow_eq_one_iff_dvd, ← hω, ← pow_mul, mul_comm, pow_mul, hl, one_pow]
          obtain ⟨t, rfl⟩ := h1
          rw [pow_mul] at hl
          have h2 : ℓ ∣ t := (hη.pow_eq_one_iff_dvd t).1 hl
          rw [pow_succ]
          exact Nat.mul_dvd_mul_left _ h2
  exact ⟨ζ, hprim, hcompat⟩

end S_IsAlgClosed_exists_isPrimitiveRoot_pow_and_pow_succ_eq
end P2MW
export P2MW.S_IsAlgClosed_exists_isPrimitiveRoot_pow_and_pow_succ_eq (solution)
