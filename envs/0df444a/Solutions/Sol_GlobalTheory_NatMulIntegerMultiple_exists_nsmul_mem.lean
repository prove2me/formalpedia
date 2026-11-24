-- Prove2me | solution 1 for GlobalTheory.NatMulIntegerMultiple.exists_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:24:34.793582+00:00
-- url     : https://prove2.me/submissions/c2cd09bc-a8fe-4324-af02-ac457860f39b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNatMulEqInteger
import Theorems.Thm_GlobalTheory_NatMulIntegerMultiple_exists_nat_mul_eq_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.NatMulIntegerMultiple
open NumberField
namespace GlobalTheory.NatMulIntegerMultiple
theorem _root_.solution {K : Type*} {V : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    ∀ x ∈ Submodule.span K (L : Set V), ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, one_ne_zero, by simpa using h⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    have e1 : (m * n) • x = n • (m • x) := by rw [mul_nsmul]
    have e2 : (m * n) • y = m • (n • y) := by rw [mul_comm, mul_nsmul]
    rw [e1, e2]
    exact L.add_mem (L.nsmul_mem hmx n) (L.nsmul_mem hny m)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_eq_integer c
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have : (m * n) • (c • x) = a • (n • x) := by
      calc (m * n) • (c • x) = ((m : K) * c) • (n • x) := by
            rw [← Nat.cast_smul_eq_nsmul K (m * n), ← Nat.cast_smul_eq_nsmul K n, smul_smul, smul_smul]
            push_cast; ring_nf
        _ = algebraMap (𝓞 K) K a • (n • x) := by rw [ha]
        _ = a • (n • x) := algebraMap_smul K a (n • x)
    rw [this]; exact L.smul_mem a hnx
end GlobalTheory.NatMulIntegerMultiple
