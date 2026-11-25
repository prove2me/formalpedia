-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_gl_eq_mul_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:49.075029+00:00
-- url     : https://prove2.me/submissions/25afa27f-5875-4254-be9c-678d06b8b499

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_gl_mul_eq_base

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
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution : ∀ (k a c : Type) [Field k] [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] (x y : Matrix c a k), x.rank = Fintype.card c → y.rank = Fintype.card c → ∃ g : GL a k, y = x * g.val := by
  intro k a c _ _ _ _ _ x y hx hy
  have hle : Fintype.card c ≤ Fintype.card a := hx ▸ rank_le_card_width x
  have e : c ⊕ Fin (Fintype.card a - Fintype.card c) ≃ a := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨gx, hgx⟩ := exists_gl_mul_eq_base e x hx
  obtain ⟨gy, hgy⟩ := exists_gl_mul_eq_base e y hy
  have h : x * gx.val = y * gy.val := by
    ext i l
    obtain ⟨s, rfl⟩ := e.surjective l
    rw [hgx, hgy]
  refine ⟨gx * gy⁻¹, ?_⟩
  calc y = (y * gy.val) * (gy⁻¹).val := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = x * (gx * gy⁻¹).val := by rw [← h, Units.val_mul, Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
