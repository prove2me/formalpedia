-- Prove2me | solution 1 for GlobalTheory.wittVector_dvd_of_saturated_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:52:37.168627+00:00
-- url     : https://prove2.me/submissions/696a97ec-b525-4b62-ab62-13eb4b612a82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorDvdOfSaturatedIdeal
import Theorems.Thm_GlobalTheory_wittVector_coeff_pow_mul_eq_zero
import Theorems.Thm_GlobalTheory_wittVector_coeff_add_pow_mul
import Theorems.Thm_GlobalTheory_wittVector_dvd_of_coeff_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WittVector
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R]
    [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J →
    (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) →
    ∀ a ∈ J, μ ∣ a := by
  intro l _ R _ _ _ J μ hμ hsat hdiv a ha

  have step : ∀ d : J, ∃ c : WittVector l R, ∃ d' : J,
      (d : WittVector l R) = μ * c + (l : WittVector l R) * d' := by
    intro d
    obtain ⟨c₀, hc₀⟩ := hdiv d d.2
    set x := (d : WittVector l R) - μ * teichmuller l c₀ with hxdef
    have hx0 : x.coeff 0 = 0 := by
      have e : (d : WittVector l R) = x + μ * teichmuller l c₀ := by rw [hxdef]; ring
      have h2 := congrArg (fun y : WittVector l R => y.coeff 0) e
      simp only [add_coeff_zero, mul_coeff_zero, teichmuller_coeff_zero] at h2
      rw [hc₀] at h2
      linear_combination -h2
    obtain ⟨y, hy⟩ := wittVector_dvd_of_coeff_zero x hx0
    have hyJ : y ∈ J := by
      apply hsat
      rw [← hy, hxdef]
      exact J.sub_mem d.2 (J.mul_mem_right _ hμ)
    refine ⟨teichmuller l c₀, ⟨y, hyJ⟩, ?_⟩
    rw [← hy, hxdef]; ring
  choose cf df hcd using step
  let seq : ℕ → J := fun n => Nat.rec ⟨a, ha⟩ (fun _ d => df d) n
  let s : ℕ → WittVector l R := fun n =>
    ∑ k ∈ Finset.range n, (l : WittVector l R) ^ k * cf (seq k)
  have hs_succ : ∀ n, s (n + 1) = s n + (l : WittVector l R) ^ n * cf (seq n) := by
    intro n; simp only [s, Finset.sum_range_succ]
  have hmain : ∀ n, a = μ * s n + (l : WittVector l R) ^ n * (seq n).1 := by
    intro n
    induction n with
    | zero => simp [s, seq]
    | succ n ih =>
      have e : (seq (n + 1)).1 = (df (seq n)).1 := rfl
      rw [hs_succ, e]
      have := hcd (seq n)
      rw [ih, this]; ring
  have hstab : ∀ n m, n ≤ m → ∃ t, s m = s n + (l : WittVector l R) ^ n * t := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨0, by ring⟩
    | succ m hnm ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (l : WittVector l R) ^ (m - n) * cf (seq m), ?_⟩
      rw [hs_succ, ht, mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]; ring
  let c : WittVector l R := WittVector.mk l (fun k => (s (k + 1)).coeff k)
  refine ⟨c, ?_⟩
  ext k

  have htc : truncate (k + 1) c = truncate (k + 1) (s (k + 1)) := by
    ext i
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate]
    obtain ⟨t, ht⟩ := hstab ((i : ℕ) + 1) (k + 1) (by omega)
    show (s ((i : ℕ) + 1)).coeff i = _
    rw [ht, wittVector_coeff_add_pow_mul _ _ _ _ (by omega)]
  have hta : truncate (k + 1) a = truncate (k + 1) (μ * c) := by
    have e := hmain (k + 1)
    have h0 : truncate (k + 1) ((l : WittVector l R) ^ (k + 1) * (seq (k + 1)).1)
        = 0 := by
      ext i
      rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      exact wittVector_coeff_pow_mul_eq_zero _ _ i i.2
    conv_lhs => rw [e]
    rw [map_add, h0, add_zero, map_mul, map_mul, htc]
  have := congrArg (fun y => TruncatedWittVector.coeff ⟨k, Nat.lt_succ_self k⟩ y) hta
  simpa only [WittVector.coeff_truncate] using this
end GlobalTheory
