-- Prove2me | solution 1 for GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:33.036439+00:00
-- url     : https://prove2.me/submissions/295d1270-2118-421a-83c0-d561f2984c74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNormSubEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.SplitEmbSep
open NumberField
namespace GlobalTheory.SplitEmbSep
namespace _root_.GlobalTheory.SplitEmbSep
theorem _root_.solution {C : Type*} [NormedField C] [IsUltrametricDist C]
    {x : C} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  rw [← Polynomial.aeval_def, hm.as_sum] at hp
  simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
    algebraMap_int_eq, eq_intCast, map_intCast] at hp
  set n := p.natDegree
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at hp
    simp at hp
  have hs : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr hn.ne'
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty hs
    (fun i => ((p.coeff i : ℤ) : C) * x ^ i)
  have hxn : x ^ n = -∑ i ∈ Finset.range n, ((p.coeff i : ℤ) : C) * x ^ i :=
    eq_neg_of_add_eq_zero_left hp
  have h1 : ‖x‖ ^ n ≤ ‖x‖ ^ i := by
    calc ‖x‖ ^ n = ‖x ^ n‖ := (norm_pow x n).symm
      _ = ‖∑ i ∈ Finset.range n, ((p.coeff i : ℤ) : C) * x ^ i‖ := by rw [hxn, norm_neg]
      _ ≤ ‖((p.coeff i : ℤ) : C) * x ^ i‖ := hle
      _ = ‖((p.coeff i : ℤ) : C)‖ * ‖x‖ ^ i := by rw [norm_mul, norm_pow]
      _ ≤ 1 * ‖x‖ ^ i := by
        gcongr
        exact IsUltrametricDist.norm_intCast_le_one C _
      _ = ‖x‖ ^ i := one_mul _
  have h2 : ‖x‖ ^ i < ‖x‖ ^ n := pow_lt_pow_right₀ h (Finset.mem_range.mp hi)
  exact absurd h1 (not_le.mpr h2)
end _root_.GlobalTheory.SplitEmbSep
end GlobalTheory.SplitEmbSep
