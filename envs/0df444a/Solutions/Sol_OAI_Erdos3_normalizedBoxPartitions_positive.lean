-- Prove2me | solution 1 for OAI.Erdos3.normalizedBoxPartitions_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:32:16.472881+00:00
-- url     : https://prove2.me/submissions/6d3a360e-ad76-4614-9294-196298de3772

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B013

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem comparableBoxPartitions_length {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (i : I)
    (k : (comparableBoxPartitions N H hH hHN i).Label) :
    H i ≤ (comparableBoxPartitions N H hH hHN i).length k ∧
      (comparableBoxPartitions N H hH hHN i).length k < 2 * H i :=
  FiniteProgressionPartition.mergedIntervals_length_bounds (N i) (H i) (hH i) (hHN i) k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedBoxPartitions_positive {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    0 < (normalizedBoxPartitions N H ρ hlarge hwhole i).length c := by
  exact (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).1.trans_le
    (comparableBoxPartitions_length N _ _ _ i c).1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.normalizedBoxPartitions_positive.{u_1} := @OAI.Erdos3.normalizedBoxPartitions_positive.{u_1}
