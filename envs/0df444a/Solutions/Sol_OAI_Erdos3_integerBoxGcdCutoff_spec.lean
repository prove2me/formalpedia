-- Prove2me | solution 1 for OAI.Erdos3.integerBoxGcdCutoff_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:46:32.622067+00:00
-- url     : https://prove2.me/submissions/c0ad4d7d-84bc-4d1c-a1b5-448dc5e88be2

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCutoffLogBounds
namespace OAI

section

namespace Erdos3

theorem integerBoxGcdCutoff_spec (d : ℕ) {C epsilon : ℝ}
    (heps : 0 < epsilon) :
    0 < integerBoxGcdCutoff d C epsilon ∧
      (2 : ℝ) ^ (d - 1) * (1 + C) / integerBoxGcdCutoff d C epsilon ≤ epsilon / 2 := by
  have hp : 0 < integerBoxGcdCutoff d C epsilon := by
    unfold integerBoxGcdCutoff
    omega
  refine ⟨hp, ?_⟩
  have hpr : (0 : ℝ) < integerBoxGcdCutoff d C epsilon := by exact_mod_cast hp
  have hceil : 2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon ≤
      (integerBoxGcdCutoff d C epsilon : ℝ) := by
    unfold integerBoxGcdCutoff
    push_cast
    linarith [Nat.le_ceil (2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon)]
  have hh := (div_le_iff₀ heps).mp hceil
  apply (div_le_iff₀ hpr).mpr
  nlinarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.integerBoxGcdCutoff_spec := @OAI.Erdos3.integerBoxGcdCutoff_spec
