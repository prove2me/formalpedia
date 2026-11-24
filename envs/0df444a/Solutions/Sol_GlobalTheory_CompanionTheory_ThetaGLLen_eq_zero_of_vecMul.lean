-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.eq_zero_of_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:35.534446+00:00
-- url     : https://prove2.me/submissions/6faa81c9-59c2-4dcd-bf64-d7d5d5178046

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OmegaEquivInducedFibre
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_T_leftColumns_mulVec_injective_of_rank_eq_card


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
theorem _root_.solution (e : c ⊕ d ≃ b) {κ : ℕ} (hκ : κ = Fintype.card c) (y : RankIn k a c {κ})
    (v : c → k) (h : v ᵥ* y.1 = 0) : v = 0 := by
  refine GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k a c d b e (topR e y.1)ᵀ
    ((rank_transpose _).trans (((rank_topR e y.1).trans y.2).trans hκ)) (fun i j => topR_inr e _ j i) v ?_
  have hs : (topR e y.1)ᵀ.submatrix id (fun i => e (.inl i)) = y.1ᵀ := by
    ext i l; simp
  rw [hs, mulVec_transpose, h]
end GlobalTheory.CompanionTheory.ThetaGLLen
