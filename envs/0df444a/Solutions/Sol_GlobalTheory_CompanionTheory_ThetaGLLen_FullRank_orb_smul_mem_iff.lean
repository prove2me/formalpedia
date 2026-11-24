-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.orb_smul_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:42:23.348066+00:00
-- url     : https://prove2.me/submissions/0c6005f4-3a72-48d2-b28f-a0aab6bf2528

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
variable {H X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace X] [MulAction H X]
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution {N : Subgroup H} {x₀ x : X} {n : H} (hn : n ∈ N) :
    n • x ∈ orb N x₀ ↔ x ∈ orb N x₀ := by
  constructor
  · rintro ⟨m, hm, e⟩
    refine ⟨n⁻¹ * m, N.mul_mem (N.inv_mem hn) hm, ?_⟩
    show (n⁻¹ * m) • x₀ = x
    rw [mul_smul]
    have e' : m • x₀ = n • x := e
    rw [e', inv_smul_smul]
  · rintro ⟨m, hm, e⟩
    refine ⟨n * m, N.mul_mem hn hm, ?_⟩
    have e' : m • x₀ = x := e
    show (n * m) • x₀ = n • x
    rw [mul_smul, e']
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
