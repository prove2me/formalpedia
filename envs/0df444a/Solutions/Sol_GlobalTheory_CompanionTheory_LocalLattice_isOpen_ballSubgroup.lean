-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:49:54.781078+00:00
-- url     : https://prove2.me/submissions/9ce65355-6276-4602-8e17-6c1bb7b8acaa

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
theorem _root_.solution (n : ℕ) {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    IsOpen (ballSubgroup k n γ : Set (Fin n → k)) := by
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  rw [GlobalTheory.CompanionTheory.LocalLattice.coe_ballSubgroup]
  refine set_pi_mem_nhds Set.finite_univ fun i _ => ?_
  exact (IsValuativeTopology.mem_nhds_zero_iff _).2
    ⟨Units.mk0 γ hγ, fun x (hx : valuation k x < γ) => hx.le⟩
end GlobalTheory.CompanionTheory.LocalLattice
