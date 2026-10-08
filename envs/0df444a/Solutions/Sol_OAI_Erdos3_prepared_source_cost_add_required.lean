-- Prove2me | solution 1 for OAI.Erdos3.prepared_source_cost_add_required
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:21:37.116537+00:00
-- url     : https://prove2.me/submissions/af38faa7-8047-4165-86a8-ffe052b3dfe7

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedSourceSideBudget
namespace OAI

section

namespace Erdos3

theorem prepared_source_cost_add_required {p required : ℝ} {c e : ℕ}
    (hp : 2 ≤ p) (hrequired : required ≤ (p + 2) ^ e) :
    (p + 2) ^ c + required ≤ (p + 2) ^ (max c e + 1) := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hc : (p + 2) ^ c ≤ (p + 2) ^ max c e :=
    pow_le_pow_right₀ hbase (Nat.le_max_left _ _)
  have he : (p + 2) ^ e ≤ (p + 2) ^ max c e :=
    pow_le_pow_right₀ hbase (Nat.le_max_right _ _)
  rw [pow_succ]
  have hpow : 0 ≤ (p + 2) ^ max c e := by positivity
  nlinarith

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.prepared_source_cost_add_required := @OAI.Erdos3.prepared_source_cost_add_required
