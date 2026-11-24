-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.range_topEmbR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:36.402939+00:00
-- url     : https://prove2.me/submissions/aed3303d-94bd-4037-8aa7-e71f5a620a5d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OmegaEquivInducedFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]
namespace GlobalTheory.CompanionTheory.ThetaGLLen
theorem _root_.solution (e : c ⊕ d ≃ b) {κ : ℕ} :
    Set.range (topEmbR (k := k) (a := a) e (κ := κ)) = {x | ∀ j i, x.1 (e (.inr j)) i = 0} := by
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩ j i
    exact topR_inr e _ j i
  · have hxy : x.1 = topR e (x.1.submatrix (fun i => e (.inl i)) id) := by
      ext i l
      obtain ⟨i | i, rfl⟩ := e.surjective i
      · simp
      · simpa using hx i l
    have hr : (x.1.submatrix (fun i => e (.inl i)) id).rank = κ := by
      rw [← rank_topR e, ← hxy]
      exact x.2
    exact ⟨⟨_, hr⟩, Subtype.ext hxy.symm⟩
end GlobalTheory.CompanionTheory.ThetaGLLen
