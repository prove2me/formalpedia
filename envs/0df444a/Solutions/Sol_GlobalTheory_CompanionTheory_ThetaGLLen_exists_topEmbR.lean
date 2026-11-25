-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.exists_topEmbR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:45.244711+00:00
-- url     : https://prove2.me/submissions/def1494e-9b9e-421a-9989-a5952c604767

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OmegaEquivInducedFibre
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_range_topEmbR
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_lAct_topEmbR
import Theorems.Thm_GlobalTheory_RankStrataProof_lAct_mul
import Theorems.Thm_GlobalTheory_RankStrataProof_lAct_one
import Theorems.Thm_GlobalTheory_RankStrataProof_lAct_val
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_mem_parab_two
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular
import Theorems.Thm_GlobalTheory_T_exists_GL_mul_rightColumns_eq_zero_of_rank


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
theorem _root_.solution (e : c ⊕ d ≃ b) {κ : ℕ} (hκ : κ = Fintype.card c) (x : RankIn k a b {κ}) :
    ∃ y, ∃ w ∈ KO k b, x = lAct _ (topEmbR e y) w := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k a c d b e x.1ᵀ ((rank_transpose _).trans (x.2.trans hκ))
  obtain ⟨u, hu⟩ := (isUnit_transpose _).2 g.isUnit
  obtain ⟨p, hp, w, hw, h⟩ := iwasawa_blockTriangular k b (fun i => (blk (two e) i).toNat) u
  have hp' : p ∈ parab k (two e) := (mem_parab_two k).2 fun i j => hp (by
    rw [← two_false e, ← two_true e]; simp only [blk_apply]; simp)
  have : lAct _ x u⁻¹ ∈ Set.range (topEmbR (k := k) (a := a) e (κ := κ)) := by
    rw [range_topEmbR]
    intro j i
    rw [lAct_val, inv_inv, hu, ← transpose_transpose x.1, ← transpose_mul]
    exact hg i j
  obtain ⟨y, hy⟩ := this
  refine ⟨_, w, hw, Eq.trans ?_ (congrArg (lAct _ · w) (lAct_topEmbR e y ⟨p, hp'⟩))⟩
  show x = lAct _ (lAct _ _ p) w
  rw [hy, ← lAct_mul, ← lAct_mul, ← h, inv_mul_cancel, lAct_one]
end GlobalTheory.CompanionTheory.ThetaGLLen
