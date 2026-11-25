-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.lAct_topEmbR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:34.087447+00:00
-- url     : https://prove2.me/submissions/c79b6f02-5ba9-4547-b78a-c75612f72c6a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OmegaEquivInducedFibre
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_mul_topR
import Theorems.Thm_GlobalTheory_RankStrataProof_lAct_val
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_mem_parab_two


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
theorem _root_.solution (e : c ⊕ d ≃ b) {κ : ℕ} (y : RankIn k a c {κ}) (p : parab k (two e)) :
    lAct _ (topEmbR e y) p = topEmbR e (lAct _ y (show GL c k from leviProj k (two e) p false)) := by
  refine Subtype.ext ?_
  rw [lAct_val]
  ext i l
  refine (mul_topR e _ _ i l).trans ?_
  obtain ⟨i | i, rfl⟩ := e.surjective i
  · refine Eq.trans ?_ (topR_inl e _ i l).symm
    rw [lAct_val]
    have : (show GL c k from leviProj k (two e) p false)⁻¹ = leviProj k (two e) p⁻¹ false := by
      rw [map_inv]; rfl
    rw [this]
    rfl
  · refine Eq.trans ?_ (topR_inr e _ i l).symm
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [(mem_parab_two k).1 (inv_mem p.2), zero_mul]
end GlobalTheory.CompanionTheory.ThetaGLLen
