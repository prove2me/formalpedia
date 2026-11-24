-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.val_zpow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:24.476552+00:00
-- url     : https://prove2.me/submissions/0381d74b-c907-416f-9827-68bfe0eb47ba

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongIndex
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ}
namespace GlobalTheory.CompanionTheory.CongIndex
theorem _root_.solution {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1) (m : ℕ) (e : ℤ) (x : k) :
    (valuation k x ≤ valuation k (ϖ ^ m) ∧ valuation k (ϖ ^ e * x) ≤ valuation k (ϖ ^ m)) ↔
      valuation k x ≤ valuation k (ϖ ^ (m + (-e).toNat)) := by
  have hpos : ∀ t : ℕ, 0 < valuation k (ϖ ^ t) := fun t => by
    rw [zero_lt_iff]; simpa using pow_ne_zero t h0
  rcases le_total 0 e with he | he
  · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le he
    have : (-(t : ℤ)).toNat = 0 := by omega
    rw [this, add_zero, zpow_natCast]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [map_mul]
    exact (mul_le_of_le_one_left' (by rw [map_pow]; exact pow_le_one' h1.le t)).trans h
  · obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 he)
    have he' : e = -(t : ℤ) := by omega
    subst he'
    have : (-(-(t : ℤ))).toNat = t := by omega
    rw [this]
    have hx : x = ϖ ^ t * (ϖ ^ (-(t : ℤ)) * x) := by
      rw [zpow_neg, zpow_natCast]; field_simp
    generalize hy : ϖ ^ (-(t : ℤ)) * x = y at hx ⊢
    clear hy
    subst hx
    rw [(valuation k).map_mul (ϖ ^ t) y, pow_add, (valuation k).map_mul (ϖ ^ m) (ϖ ^ t)]
    constructor
    · rintro ⟨-, h⟩
      rw [mul_comm]
      exact mul_le_mul_left h _
    · intro h
      rw [mul_comm (valuation k (ϖ ^ m))] at h
      have h' : valuation k y ≤ valuation k (ϖ ^ m) := le_of_mul_le_mul_left h (hpos t)
      exact ⟨(mul_le_of_le_one_left' (by rw [map_pow]; exact pow_le_one' h1.le t)).trans h', h'⟩
end GlobalTheory.CompanionTheory.CongIndex
