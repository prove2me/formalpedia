-- Prove2me | solution 1 for OAI.Erdos3.cutoff_weighted_replacement_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:51:27.790879+00:00
-- url     : https://prove2.me/submissions/419384b6-5b19-40db-9ef5-b8f598fb206c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_integerBoxGcdCutoff_spec
import Theorems.Thm_OAI_Erdos3_weightedReplacementTolerance_pos

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem replacementAccuracy_spec {B epsilon : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    0 < replacementAccuracy B epsilon ∧ replacementAccuracy B epsilon ≤ 1 ∧
      B * replacementAccuracy B epsilon ≤ epsilon := by
  have hden : 0 < 1 + B := by positivity
  refine ⟨lt_min zero_lt_one (div_pos hepsilon hden), min_le_left _ _, ?_⟩
  calc
    _ ≤ B * (epsilon / (1 + B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
    _ ≤ epsilon := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

theorem integerBoxBadPairBudget_nonneg (d B R r : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ integerBoxBadPairBudget d B R r M := by
  unfold integerBoxBadPairBudget
  positivity

theorem integerBoxBadPairBudget_le_separated (d B R r : ℕ) {M C nu : ℝ}
    (hd : 2 ≤ d) (hB : 0 < B) (hBM : (B : ℝ) ≤ M) (hC : 0 ≤ C)
    (hR : (R : ℝ) ≤ C * M) (hr : (r : ℝ) ≤ nu * M)
    (hinv : 1 / M ≤ nu) :
    integerBoxBadPairBudget d B R r M ≤
      2 ^ (d - 1) * (1 + C) / (B : ℝ) ^ (d - 1) + (3 * nu) ^ d := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hM : 0 < M := hBp.trans_le hBM
  have hpow : (B : ℝ) ^ (d - 1) ≤ M ^ (d - 1) :=
    pow_le_pow_left₀ hBp.le hBM _
  have hR' : (R : ℝ) / M ^ d ≤ C / (B : ℝ) ^ (d - 1) := by
    calc
      _ ≤ (C * M) / M ^ d := div_le_div_of_nonneg_right hR (by positivity)
      _ = C / M ^ (d - 1) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
        field_simp
      _ ≤ C / (B : ℝ) ^ (d - 1) := div_le_div_of_nonneg_left hC (by positivity) hpow
  have hnear : (2 * (r : ℝ) + 1) / M ≤ 3 * nu := by
    have hrr : (r : ℝ) / M ≤ nu := (div_le_iff₀ hM).mpr hr
    calc
      _ = 2 * ((r : ℝ) / M) + 1 / M := by ring
      _ ≤ 3 * nu := by linarith
  unfold integerBoxBadPairBudget
  calc
    _ ≤ 2 ^ (d - 1) * (1 / (B : ℝ) ^ (d - 1) + C / (B : ℝ) ^ (d - 1)) +
        (3 * nu) ^ d := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hR') (by positivity))
      (pow_le_pow_left₀ (by positivity) hnear d)
    _ = _ := by ring

theorem integerBoxBadPairBudget_le_linear (d B R r : ℕ) {M C nu : ℝ}
    (hd : 2 ≤ d) (hB : 0 < B) (hBM : (B : ℝ) ≤ M) (hC : 0 ≤ C)
    (hR : (R : ℝ) ≤ C * M) (hr : (r : ℝ) ≤ nu * M)
    (hinv : 1 / M ≤ nu) (hnu : nu ≤ 1) :
    integerBoxBadPairBudget d B R r M ≤
      2 ^ (d - 1) * (1 + C) / (B : ℝ) + 3 ^ d * nu := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hM : 0 < M := hBp.trans_le hBM
  have hnu0 : 0 ≤ nu := (by positivity : 0 ≤ 1 / M).trans hinv
  have hpow : (B : ℝ) ≤ (B : ℝ) ^ (d - 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hB1 (show 1 ≤ d - 1 by omega)
  have hnpow : nu ^ d ≤ nu := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hnu0 hnu) hnu0).trans_eq (one_mul nu)
  apply (integerBoxBadPairBudget_le_separated d B R r hd hB hBM hC hR hr hinv).trans
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hBp hpow
  · rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hnpow (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCutoffLogBounds
namespace OAI

section

namespace Erdos3

theorem integerBoxNearRatio_spec (d : ℕ) {epsilon : ℝ} (heps : 0 < epsilon) :
    0 < integerBoxNearRatio d epsilon ∧ integerBoxNearRatio d epsilon ≤ 1 ∧
      (3 : ℝ) ^ d * integerBoxNearRatio d epsilon ≤ epsilon / 2 := by
  have h := replacementAccuracy_spec (by positivity : 0 ≤ 2 * (3 : ℝ) ^ d) heps
  change 0 < integerBoxNearRatio d epsilon ∧ integerBoxNearRatio d epsilon ≤ 1 ∧
    2 * (3 : ℝ) ^ d * integerBoxNearRatio d epsilon ≤ epsilon at h
  exact ⟨h.1, h.2.1, by linarith [h.2.2]⟩

theorem integerBoxBadPairBudget_of_cutoffs (d R : ℕ) {C epsilon M : ℝ}
    (hd : 2 ≤ d) (hC : 0 ≤ C) (heps : 0 < epsilon)
    (hscale : integerBoxPairScale d C epsilon ≤ M) (hR : (R : ℝ) ≤ C * M) :
    integerBoxBadPairBudget d (integerBoxGcdCutoff d C epsilon) R
      ⌊integerBoxNearRatio d epsilon * M⌋₊ M ≤ epsilon := by
  have hB := integerBoxGcdCutoff_spec d (C := C) heps
  have hnu := integerBoxNearRatio_spec d heps
  have hBM : (integerBoxGcdCutoff d C epsilon : ℝ) ≤ M := (le_max_left _ _).trans hscale
  have hM : 0 < M := (by exact_mod_cast hB.1 : (0 : ℝ) < integerBoxGcdCutoff d C epsilon).trans_le hBM
  have hinv : 1 / M ≤ integerBoxNearRatio d epsilon := by
    have h := (le_max_right (integerBoxGcdCutoff d C epsilon : ℝ)
      (1 / integerBoxNearRatio d epsilon)).trans hscale
    have hh := (div_le_iff₀ hnu.1).mp h
    apply (div_le_iff₀ hM).mpr
    nlinarith
  have h := integerBoxBadPairBudget_le_linear d (integerBoxGcdCutoff d C epsilon) R
    ⌊integerBoxNearRatio d epsilon * M⌋₊ hd hB.1 hBM hC hR
    (Nat.floor_le (mul_nonneg hnu.1.le hM.le)) hinv hnu.2.1
  linarith [hB.2, hnu.2.2]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

theorem weightedReplacementTolerance_bound {F E epsilon beta : ℝ}
    (hF : 0 ≤ F) (hE : 0 ≤ E) (heps : 0 < epsilon) (hbeta : 0 ≤ beta)
    (hsmall : beta ≤ weightedReplacementTolerance F E epsilon) :
    F * Real.sqrt (E * beta + weightedReplacementTolerance F E epsilon) ≤ epsilon := by
  have htol := weightedReplacementTolerance_pos (F := F) hE heps
  have hcost := (replacementAccuracy_spec
    (mul_nonneg (sq_nonneg F) (by linarith : 0 ≤ 1 + E)) (sq_pos_of_pos heps)).2.2
  change F ^ 2 * (1 + E) * weightedReplacementTolerance F E epsilon ≤ epsilon ^ 2 at hcost
  have harg : 0 ≤ E * beta + weightedReplacementTolerance F E epsilon := by positivity
  have hsquare : (F * Real.sqrt (E * beta + weightedReplacementTolerance F E epsilon)) ^ 2 ≤
      epsilon ^ 2 := by
    calc
      _ = F ^ 2 * (E * beta + weightedReplacementTolerance F E epsilon) := by
        rw [mul_pow, Real.sq_sqrt harg]
      _ ≤ F ^ 2 * (E * weightedReplacementTolerance F E epsilon +
          weightedReplacementTolerance F E epsilon) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hsmall hE) le_rfl) (sq_nonneg F)
      _ = F ^ 2 * (1 + E) * weightedReplacementTolerance F E epsilon := by ring
      _ ≤ epsilon ^ 2 := hcost
  exact (sq_le_sq₀ (mul_nonneg hF (Real.sqrt_nonneg _)) heps.le).mp hsquare

theorem cutoff_weighted_replacement_bound (d R : ℕ) {F E epsilon C M : ℝ}
    (hd : 2 ≤ d) (hF : 0 ≤ F) (hE : 0 ≤ E) (hC : 0 ≤ C) (heps : 0 < epsilon)
    (hscale : integerBoxPairScale d C (weightedReplacementTolerance F E epsilon) ≤ M)
    (hR : (R : ℝ) ≤ C * M) :
    F * Real.sqrt (E * integerBoxBadPairBudget d
      (integerBoxGcdCutoff d C (weightedReplacementTolerance F E epsilon)) R
      ⌊integerBoxNearRatio d (weightedReplacementTolerance F E epsilon) * M⌋₊ M +
      weightedReplacementTolerance F E epsilon) ≤ epsilon := by
  have htol := weightedReplacementTolerance_pos (F := F) hE heps
  have hM : 0 ≤ M := by
    have h : (integerBoxGcdCutoff d C (weightedReplacementTolerance F E epsilon) : ℝ) ≤ M :=
      (le_max_left _ _).trans hscale
    exact (Nat.cast_nonneg _).trans h
  exact weightedReplacementTolerance_bound hF hE heps
    (integerBoxBadPairBudget_nonneg _ _ _ _ hM)
    (integerBoxBadPairBudget_of_cutoffs d R hd hC htol hscale hR)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.cutoff_weighted_replacement_bound := @OAI.Erdos3.cutoff_weighted_replacement_bound
