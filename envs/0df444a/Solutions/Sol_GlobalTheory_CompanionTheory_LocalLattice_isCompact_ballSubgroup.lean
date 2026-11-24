-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalLattice.isCompact_ballSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:49:53.803812+00:00
-- url     : https://prove2.me/submissions/311937da-9e38-4630-a395-b9bc6b24c3f5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOpenCompactLatticeContaining
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalLattice_coe_ballSubgroup

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
    IsCompact (ballSubgroup k n γ : Set (Fin n → k)) := by
  rw [coe_ballSubgroup]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
end GlobalTheory.CompanionTheory.LocalLattice
