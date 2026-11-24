-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_gl_mul_eq_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:15.823802+00:00
-- url     : https://prove2.me/submissions/179bd15f-6e57-43b0-a4aa-7267530c9deb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_T_exists_GL_mul_rightColumns_eq_zero_of_rank
import Theorems.Thm_GlobalTheory_T_leftColumns_mulVec_injective_of_rank_eq_card


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
variable {k a c d : Type} [Field k] [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution (e : c ⊕ d ≃ a) (x : Matrix c a k) (hx : x.rank = Fintype.card c) :
    ∃ g : GL a k, ∀ i s, (x * g.val) i (e s) = Sum.elim (fun j => (1 : Matrix c c k) i j) (fun _ => 0) s := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k c c d a e x hx
  have hr : (x * g.val).rank = Fintype.card c := by
    rw [rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 g.isUnit)]
    exact hx
  have h := GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k c c d a e (x * g.val) hr hg
  have hu : IsUnit ((x * g.val).submatrix id fun i => e (.inl i)) :=
    mulVec_injective_iff_isUnit.1 fun v w hvw => sub_eq_zero.1 (h _ (by rw [mulVec_sub, hvw, sub_self]))
  set u : Matrix c c k := (x * g.val).submatrix id fun i => e (.inl i) with hudef
  have hud : IsUnit u.det := (isUnit_iff_isUnit_det _).1 hu
  have hD : IsUnit (reindex e e (fromBlocks u⁻¹ 0 0 (1 : Matrix d d k))).det := by
    rw [det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]
    exact (isUnit_iff_isUnit_det _).1 (isUnit_nonsing_inv_iff.2 hu)
  obtain ⟨G, hG⟩ := (isUnit_iff_isUnit_det _).2 hD
  refine ⟨g * G, fun i s => ?_⟩
  rw [Units.val_mul, ← Matrix.mul_assoc, hG, mul_apply_of_cols e hg]
  rcases s with j | j
  · have := congrFun (congrFun (mul_nonsing_inv u hud) i) j
    rw [mul_apply] at this
    simpa [hudef] using this
  · simp
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
