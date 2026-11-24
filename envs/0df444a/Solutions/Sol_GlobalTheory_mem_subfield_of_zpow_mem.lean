-- Prove2me | solution 1 for GlobalTheory.mem_subfield_of_zpow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:37.266801+00:00
-- url     : https://prove2.me/submissions/63681868-4192-4e64-8831-345aaa722834

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSubfieldOfBilinFormBasisMonomials

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
theorem _root_.solution {K : Type} [Field K] (k₀ : Subfield K) [IsAlgClosed k₀]
    (u : Kˣ) (m : ℤ) (hm : m ≠ 0) (h : ((u ^ m : Kˣ) : K) ∈ k₀) : (u : K) ∈ k₀ := by
  have h1 : (u : K) ^ m.natAbs ∈ k₀ := by
    rw [Units.val_zpow_eq_zpow_val] at h
    rcases Int.natAbs_eq m with h2 | h2
    · rw [h2, zpow_natCast] at h; exact h
    · rw [h2, zpow_neg, zpow_natCast] at h
      simpa using k₀.inv_mem h
  have hint : IsIntegral k₀ (u : K) := by
    apply IsIntegral.of_pow (Int.natAbs_pos.mpr hm)
    exact isIntegral_algebraMap (R := k₀) (x := ⟨_, h1⟩)
  obtain ⟨y, hy⟩ := minpoly.mem_range_of_degree_eq_one k₀ (u : K)
    (IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint))
  rw [← hy]
  exact y.2
end GlobalTheory
