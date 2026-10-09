-- Prove2me | solution 1 for OAI.Erdos3.physicalPairGridAccuracy_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:21:07.204089+00:00
-- url     : https://prove2.me/submissions/93f9e081-0942-4977-90c0-4eb54d11e3dc

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

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

theorem residualGridAccuracy_spec {M S K epsilon : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hK : 0 ≤ K) (heps : 0 < epsilon) :
    0 < residualGridAccuracy M S K epsilon ∧ residualGridAccuracy M S K epsilon ≤ 1 ∧
      6 * M * S * K * residualGridAccuracy M S K epsilon ≤ epsilon :=
  replacementAccuracy_spec (by positivity) heps

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

theorem physicalPairGridAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ : ℝ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let rho := physicalPairGridAccuracy n k C κ A epsilon
    0 < rho ∧ rho ≤ 1 ∧
      6 * A ^ (2 * n) * (2 : ℝ) ^ n * (smoothPairKernelLip n k C κ : ℝ) * rho ≤ epsilon :=
  residualGridAccuracy_spec (by positivity) (by positivity) (NNReal.coe_nonneg _) heps

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

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.physicalPairGridAccuracy_spec.{u_1} := @OAI.Erdos3.physicalPairGridAccuracy_spec.{u_1}
