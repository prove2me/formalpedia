-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.isClosedEmbedding_topEmbR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:35.149245+00:00
-- url     : https://prove2.me/submissions/3083aa1a-ae38-42ff-9685-65a2d2b49414

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OmegaEquivInducedFibre
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_range_topEmbR
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


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
    IsClosedEmbedding (topEmbR (k := k) (a := a) e (κ := κ)) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨IsEmbedding.of_comp (g := fun x : RankIn k a b {κ} => x.1.submatrix (fun i => e (.inl i)) id)
    (Continuous.subtype_mk (continuous_matrix fun i l => ?_) _)
    (continuous_subtype_val.matrix_submatrix _ _) ?_, ?_⟩
  · obtain ⟨i | i, rfl⟩ := e.surjective i
    · simp only [topR_inl]
      exact continuous_subtype_val.matrix_elem _ _
    · simp only [topR_inr]
      exact continuous_const
  · convert IsEmbedding.subtypeVal (p := fun y : Matrix c a k => y.rank ∈ ({κ} : Set ℕ)) using 1
    funext y
    ext i l
    exact topR_inl e _ i l
  · rw [range_topEmbR]
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_subtype_val.matrix_elem _ _) continuous_const
end GlobalTheory.CompanionTheory.ThetaGLLen
