-- Prove2me | solution 1 for GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:12:30.912544+00:00
-- url     : https://prove2.me/submissions/7080f912-b428-406b-a3fc-26deb457fb7e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
namespace GlobalTheory.Cyc
namespace _root_.GlobalTheory.Cyc
theorem _root_.solution {K : Type*} [NormedField K]
    [IsUltrametricDist K]
    {n : ℕ} (hn : n ≠ 0) {ζ μ : K} (hζ : IsPrimitiveRoot ζ n) (hμ : μ ^ n = 1) :
    ‖μ - 1‖ ≤ ‖ζ - 1‖ := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  have hnorm : ‖ζ‖ = 1 := by
    have h := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn).mp h
  clear hμ
  induction k with
  | zero => simp
  | succ k ih =>
    have : ζ ^ (k + 1) - 1 = ζ ^ k * (ζ - 1) + (ζ ^ k - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
    rw [norm_mul, norm_pow, hnorm, one_pow, one_mul]
end _root_.GlobalTheory.Cyc
end GlobalTheory.Cyc
