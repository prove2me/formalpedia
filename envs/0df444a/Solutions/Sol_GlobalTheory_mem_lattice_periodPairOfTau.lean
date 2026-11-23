-- Prove2me | solution 1 for GlobalTheory.mem_lattice_periodPairOfTau
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:50.848801+00:00
-- url     : https://prove2.me/submissions/9ee1898f-3c10-4e6c-a96d-64408a675431

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups Filter EisensteinSeries
open scoped Real Topology
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (τ : ℍ) (x : ℂ) :
    x ∈ (periodPairOfTau τ).lattice ↔ ∃ m n : ℤ, 1 * (m * (τ : ℂ) + n) = x := by
  simp [PeriodPair.mem_lattice, periodPairOfTau]
end GlobalTheory
