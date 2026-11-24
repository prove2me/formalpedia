-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalLattice.coe_ballSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:02.843699+00:00
-- url     : https://prove2.me/submissions/1abc8667-7823-49ae-8392-cf8731bc80be

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOpenCompactLatticeContaining

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalLattice
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.LocalLattice
theorem _root_.solution (n : ℕ) (γ : ValueGroupWithZero k) :
    (ballSubgroup k n γ : Set (Fin n → k)) =
      Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
  ext x
  simp only [Set.mem_univ_pi, Set.mem_setOf_eq]
  rfl
end GlobalTheory.CompanionTheory.LocalLattice
