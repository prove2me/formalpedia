-- Prove2me | solution 1 for OAI.Erdos3.integerBoxRetainedGap_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:32:16.643048+00:00
-- url     : https://prove2.me/submissions/4ee51f80-8339-477d-b0f9-01201f844eff

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

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

theorem integerBoxRetainedGap_spec (d D : ℕ) {c epsilon L M : ℝ}
    (hD : 0 < D) (hc : 0 < c) (heps : 0 < epsilon) (hside : c * L ≤ M) :
    0 < integerBoxRetainedGap d D c epsilon ∧
      integerBoxRetainedGap d D c epsilon * L ≤
        (D : ℝ) * (⌊integerBoxNearRatio d epsilon * M⌋₊ + 1 : ℕ) := by
  have hnu := (integerBoxNearRatio_spec d heps).1
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · unfold integerBoxRetainedGap
    positivity
  · unfold integerBoxRetainedGap
    push_cast
    calc
      _ = (D : ℝ) * (integerBoxNearRatio d epsilon * (c * L)) := by ring
      _ ≤ (D : ℝ) * (integerBoxNearRatio d epsilon * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hside hnu.le) hDr.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one _).le hDr.le

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.integerBoxRetainedGap_spec := @OAI.Erdos3.integerBoxRetainedGap_spec
