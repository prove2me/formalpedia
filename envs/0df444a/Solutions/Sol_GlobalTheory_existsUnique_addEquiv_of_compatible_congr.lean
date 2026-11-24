-- Prove2me | solution 1 for GlobalTheory.existsUnique_addEquiv_of_compatible_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:07.327068+00:00
-- url     : https://prove2.me/submissions/04dc483f-b8c0-4fc5-8165-ebb1525eb9d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module
namespace GlobalTheory
private theorem int_eq_zero_of_forall_pow_dvd (n : ℕ) (hn : 2 ≤ n) (c : ℤ)
    (h : ∀ j : ℕ, (n : ℤ) ^ j ∣ c) : c = 0 := by
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h c.natAbs) ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)
private theorem eq_zero_of_forall_pow_nsmul_dvd (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (n : ℕ) (hn : 2 ≤ n) (z : X) (h : ∀ j : ℕ, ∃ μ : X, z = n ^ j • μ) :
    z = 0 := by
  set b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  refine int_eq_zero_of_forall_pow_dvd n hn _ fun j => ?_
  obtain ⟨μ, hμ⟩ := h j
  refine ⟨b.repr μ i, ?_⟩
  rw [hμ, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  push_cast
  ring
end GlobalTheory
end

set_option autoImplicit false
open Module
open GlobalTheory
open Module
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (n : ℕ), 2 ≤ n → ∀ r : ℕ → X → X' → Prop, (∀ j x, ∃ x', r j x x') → (∀ j x', ∃ x, r j x x') → (∀ j x y x' y', r j x x' → r j y y' → r j (x + y) (x' + y')) → (∀ j x y x' y', r j x x' → r j y y' → ((∃ μ, y = x + n ^ j • μ) ↔ ∃ μ', y' = x' + n ^ j • μ')) → (∀ j x x' μ μ', r j x x' → r j (x + n ^ j • μ) (x' + n ^ j • μ')) → (∀ x, ∃ x', ∀ j, r j x x') → (∀ x', ∃ x, ∀ j, r j x x') → ∃! e : X ≃+ X', ∀ j x, r j x (e x) := by
  intro X X' _ _ _ _ _ _ n hn r _ _ hadd hcong _ hfwd hbwd
  have sepR : ∀ x x' y', (∀ j, r j x x') → (∀ j, r j x y') → x' = y' := by
    intro x x' y' hx hy
    refine (sub_eq_zero.1 (eq_zero_of_forall_pow_nsmul_dvd X' n hn (y' - x') fun j => ?_)).symm
    obtain ⟨μ', hμ'⟩ := (hcong j x x x' y' (hx j) (hy j)).1 ⟨0, by simp⟩
    exact ⟨μ', by rw [hμ', add_sub_cancel_left]⟩
  have sepL : ∀ x y x', (∀ j, r j x x') → (∀ j, r j y x') → x = y := by
    intro x y x' hx hy
    refine (sub_eq_zero.1 (eq_zero_of_forall_pow_nsmul_dvd X n hn (y - x) fun j => ?_)).symm
    obtain ⟨μ, hμ⟩ := (hcong j x y x' x' (hx j) (hy j)).2 ⟨0, by simp⟩
    exact ⟨μ, by rw [hμ, add_sub_cancel_left]⟩
  choose f hf using hfwd
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y =>
    sepR _ _ _ (hf (x + y)) fun j => hadd j x y _ _ (hf x j) (hf y j)
  have bij : Function.Bijective f := by
    refine ⟨fun x y hxy => sepL x y (f x) (hf x) fun j => ?_, fun x' => ?_⟩
    · rw [hxy]
      exact hf y j
    · obtain ⟨x, hx⟩ := hbwd x'
      exact ⟨x, sepR _ _ _ (hf x) hx⟩
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' f fadd) bij, fun j x => hf x j, fun e he => ?_⟩
  ext x
  exact sepR x (e x) (f x) (fun j => he j x) (hf x)
end _root_.GlobalTheory
end GlobalTheory
