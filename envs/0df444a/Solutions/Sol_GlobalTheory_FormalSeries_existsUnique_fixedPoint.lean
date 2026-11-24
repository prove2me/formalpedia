-- Prove2me | solution 1 for GlobalTheory.FormalSeries.existsUnique_fixedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:46:57.898071+00:00
-- url     : https://prove2.me/submissions/9a5523b9-5a56-4820-9d54-3b4617fd7d32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
import Theorems.Thm_GlobalTheory_FormalSeries_le_order_sub
import Theorems.Thm_GlobalTheory_FormalSeries_coeff_eq_of_le_order_sub
import Theorems.Thm_GlobalTheory_FormalSeries_eq_of_forall_le_order_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply
attribute [local simp] GlobalTheory.FormalSeries.jacobian_X

set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
variable [Algebra R S]
namespace GlobalTheory.FormalSeries
theorem _root_.solution (Φ : (σ → MvPowerSeries τ S) → (σ → MvPowerSeries τ S))
    (h0 : ∀ a, (∀ s, constantCoeff (a s) = 0) → ∀ s, constantCoeff (Φ a s) = 0)
    (hΦ : ∀ a b (k : ℕ), (∀ s, constantCoeff (a s) = 0) → (∀ s, constantCoeff (b s) = 0) →
      (∀ s, (k : ℕ∞) ≤ (a s - b s).order) → ∀ s, ((k + 1 : ℕ) : ℕ∞) ≤ (Φ a s - Φ b s).order) :
    ∃! a, (∀ s, constantCoeff (a s) = 0) ∧ Φ a = a := by
  have hA0 : ∀ n s, constantCoeff ((Φ^[n] 0) s) = 0 := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih => intro s; rw [Function.iterate_succ_apply']; exact h0 _ ih s
  have hcl : ∀ n j : ℕ, ∀ s, (n : ℕ∞) ≤ ((Φ^[n + j] 0) s - (Φ^[n] 0) s).order := by
    intro n
    induction n with
    | zero => intro j s; simp
    | succ n ih =>
      intro j s
      rw [show n + 1 + j = (n + j) + 1 by omega, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      exact hΦ _ _ n (hA0 _) (hA0 _) (ih j) s
  have hst : ∀ (d : τ →₀ ℕ) s n, d.degree < n →
      coeff d ((Φ^[n] 0) s) = coeff d ((Φ^[d.degree + 1] 0) s) := by
    intro d s n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show d.degree + 1 ≤ n by omega)
    exact coeff_eq_of_le_order_sub (hcl _ j s) (Nat.lt_succ_self _)
  obtain ⟨a, hca⟩ : ∃ a : σ → MvPowerSeries τ S,
      ∀ s d, coeff d (a s) = coeff d ((Φ^[d.degree + 1] 0) s) :=
    ⟨fun s d => coeff d ((Φ^[d.degree + 1] 0) s), fun s d => rfl⟩
  have hac : ∀ n : ℕ, ∀ s, (n : ℕ∞) ≤ (a s - (Φ^[n] 0) s).order := fun n s =>
    nat_le_order fun d hd => by rw [map_sub, hca, hst d s n hd, sub_self]
  have haz : ∀ s, constantCoeff (a s) = 0 := fun s => by
    rw [← coeff_zero_eq_constantCoeff_apply, hca, coeff_zero_eq_constantCoeff_apply]
    exact hA0 _ s
  have hfix : Φ a = a := by
    funext s
    refine eq_of_forall_le_order_sub fun n => ?_
    have e : Φ a s - a s = (Φ a s - Φ (Φ^[n] 0) s) - (a s - (Φ^[n + 1] 0) s) := by
      rw [Function.iterate_succ_apply']
      abel
    have hn : (n : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ n
    rw [e]
    exact le_order_sub (hn.trans (hΦ a _ n haz (hA0 n) (hac n) s)) (hn.trans (hac (n + 1) s))
  refine ⟨a, ⟨haz, hfix⟩, ?_⟩
  rintro b ⟨hbz, hbfix⟩
  have key : ∀ n : ℕ, ∀ s, (n : ℕ∞) ≤ (b s - a s).order := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      have := hΦ b a n hbz haz ih s
      rwa [hbfix, hfix] at this
  funext s
  exact eq_of_forall_le_order_sub fun n => key n s
end GlobalTheory.FormalSeries
