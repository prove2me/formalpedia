-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.exists_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:11.113622+00:00
-- url     : https://prove2.me/submissions/04e77ea1-5218-4150-9860-b4e32bad4bb3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermDiag
variable {R : Type} [CommRing R]
variable {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.HermDiag
theorem _root_.solution (hR : IsUnrQuad R σ ϖ q ε) {y : R} (hy : y ∉ lev ϖ 1) :
    ∃ s, s * y + σ (s * y) ∉ lev ϖ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, hu, -⟩ := hR.basis
  apply hy
  have h3 : (u - σ u) * y ∈ lev ϖ 1 := by
    have : (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y)) := by
      simp only [map_mul, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ (hcon u) (Ideal.mul_mem_left _ _ (hcon 1))
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have : y = v * ((u - σ u) * y) := by rw [← mul_assoc, hv, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h3
end GlobalTheory.CompanionTheory.HermDiag
