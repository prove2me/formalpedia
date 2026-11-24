-- Prove2me | solution 1 for GlobalTheory.powerSeries_generic_relation_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:47.417811+00:00
-- url     : https://prove2.me/submissions/f7ffa84a-7338-4b19-a4d1-0013035a204d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PowerSeriesGenericRelationChain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] [Infinite k] (ρ : PowerSeries k → PowerSeries k → Prop) (Gen : ℕ → ℕ → Prop), (∀ z w, ρ z w → ρ w z) → (∀ x y z, ρ x y → ρ y z → ρ x z) → (∀ m n, Gen m n → ∀ z : PowerSeries k, z.order = (m : ℕ∞) → ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → ρ z (PowerSeries.C t * PowerSeries.X ^ n)) → (∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) → w.order = (m : ℕ∞) → ρ z w) ∧ ∀ m₀, (∀ m, m₀ ≤ m → Gen m (m + 1)) → ∀ (m n : ℕ) (z w : PowerSeries k), m₀ ≤ m → m₀ ≤ n → z.order = (m : ℕ∞) → w.order = (n : ℕ∞) → ρ z w := by
  intro k _ _ ρ Gen hs ht hg
  have h1 : ∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) →
      w.order = (m : ℕ∞) → ρ z w := by
    intro m n hmn z w hz hw
    obtain ⟨S, hS, hzS⟩ := hg m n hmn z hz
    obtain ⟨T, hT, hwT⟩ := hg m n hmn w hw
    obtain ⟨t, htt⟩ := (hS.union hT).exists_notMem
    simp only [Set.mem_union, not_or] at htt
    exact ht _ _ _ (hzS t htt.1) (hs _ _ (hwT t htt.2))
  refine ⟨h1, fun m₀ hG => ?_⟩
  have h2 : ∀ m, m₀ ≤ m → ∀ z : PowerSeries k, z.order = (m : ℕ∞) →
      ρ z (PowerSeries.X ^ m₀) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun z hz => h1 _ _ (hG _ le_rfl) _ _ hz (PowerSeries.order_X_pow _)
    | succ m hm ih =>
      intro z hz
      obtain ⟨S, hS, hXS⟩ := hg m _ (hG m hm) (PowerSeries.X ^ m) (PowerSeries.order_X_pow _)
      obtain ⟨t, htt⟩ := (hS.insert 0).exists_notMem
      simp only [Set.mem_insert_iff, not_or] at htt
      have ho : (PowerSeries.C t * PowerSeries.X ^ (m + 1) : PowerSeries k).order
          = ((m + 1 : ℕ) : ℕ∞) := by
        rw [PowerSeries.X_pow_eq, ← PowerSeries.monomial_zero_eq_C_apply,
          PowerSeries.monomial_mul_monomial, zero_add, mul_one]
        exact PowerSeries.order_monomial_of_ne_zero _ _ htt.1
      exact ht _ _ _ (h1 _ _ (hG _ (Nat.le_succ_of_le hm)) _ _ hz ho)
        (ht _ _ _ (hs _ _ (hXS t htt.2)) (ih _ (PowerSeries.order_X_pow _)))
  intro m n z w hm hn hz hw
  exact ht _ _ _ (h2 m hm z hz) (hs _ _ (h2 n hn w hw))
end GlobalTheory
