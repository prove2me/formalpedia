-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongruenceBasis.exists_pow_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:09.865537+00:00
-- url     : https://prove2.me/submissions/6208b9d9-8b1f-4ea8-a044-7aa16ac906e9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCongruenceSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Filter Topology Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongruenceBasis
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.CongruenceBasis
theorem _root_.solution {a γ : ValueGroupWithZero k} (ha0 : a ≠ 0) (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ (m + 1) < γ := by
  haveI : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  have h1 : 1 < a⁻¹ := (one_lt_inv₀ (zero_lt_iff.2 ha0)).2 ha
  obtain ⟨n, hn⟩ := MulArchimedean.arch γ⁻¹ h1
  refine ⟨n, ?_⟩
  have h2 : a ^ n ≤ γ := by
    rw [inv_pow] at hn
    exact (inv_le_inv₀ (zero_lt_iff.2 hγ) (zero_lt_iff.2 (pow_ne_zero n ha0))).1 hn
  exact lt_of_lt_of_le (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ha0) ha n.lt_succ_self) h2
end GlobalTheory.CompanionTheory.CongruenceBasis
