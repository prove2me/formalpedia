-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.red_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:09.438162+00:00
-- url     : https://prove2.me/submissions/581baebe-792e-41e2-838f-df3af6ede524

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_red_of_le

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
namespace GlobalTheory.CompanionTheory.CongIndex
theorem _root_.solution {ϖ : k} (h0 : ϖ ≠ 0) (h1 : valuation k ϖ < 1)
    (hu : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) {c : ℕ} {x : k}
    (hx : valuation k x ≤ valuation k (ϖ ^ c)) :
    red ϖ c x = 0 ↔ valuation k x ≤ valuation k (ϖ ^ (c + 1)) := by
  have hp : 0 < valuation k (ϖ ^ c) := by
    rw [zero_lt_iff]; simpa using (pow_ne_zero c h0)
  have key : valuation k x = valuation k (ϖ ^ c) * valuation k (x * (ϖ ^ c)⁻¹) := by
    rw [← map_mul]; congr 1; field_simp
  rw [red_of_le h0 hx, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)]
  have hle := scaled_le h0 hx
  constructor
  · intro h
    have hlt : valuation k (x * (ϖ ^ c)⁻¹) < 1 := lt_of_le_of_ne hle h
    rw [key, pow_succ ϖ c, (valuation k).map_mul (ϖ ^ c) ϖ]
    exact mul_le_mul_right (hu _ hlt) _
  · intro h hone
    apply absurd h
    rw [not_le, key]
    have hone' : valuation k (x * (ϖ ^ c)⁻¹) = 1 := hone
    rw [hone', pow_succ ϖ c, (valuation k).map_mul (ϖ ^ c) ϖ, mul_one]
    exact mul_lt_of_lt_one_right hp h1
end GlobalTheory.CompanionTheory.CongIndex
