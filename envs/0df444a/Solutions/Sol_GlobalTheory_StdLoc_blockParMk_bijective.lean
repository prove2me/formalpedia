-- Prove2me | solution 1 for GlobalTheory.StdLoc.blockParMk_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:49:00.013061+00:00
-- url     : https://prove2.me/submissions/f28cd250-0a50-4af2-b7ae-0bd45dcd7a5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardBlockParabolicSubgroupGL
import Theorems.Thm_GlobalTheory_StdLoc_blockParMk_val
import Theorems.Thm_GlobalTheory_StdLoc_mem_blockPar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.StdLoc
namespace GlobalTheory.StdLoc
theorem _root_.solution {R : Type} [CommRing R] {a b : ℕ} :
    Function.Bijective (blockParMk (R := R) (a := a) (b := b)) := by
  constructor
  · rintro ⟨A, D, B⟩ ⟨A', D', B'⟩ h
    have h1 : blockMat A.1 B D.1 = blockMat A'.1 B' D'.1 := by
      have := congrArg (fun g : blockPar R a (a + b) => (g.1 : Matrix (Fin (a + b)) (Fin (a + b)) R)) h
      simpa only [blockParMk_val] using this
    have h2 := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h1
    obtain ⟨hA, hB, -, hD⟩ := Matrix.fromBlocks_inj.1 h2
    exact Prod.ext (Units.ext hA) (Prod.ext (Units.ext hD) hB)
  · rintro ⟨g, hg⟩
    set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R :=
      (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm (g : Matrix (Fin (a + b)) (Fin (a + b)) R) with hM
    have h0 : M.toBlocks₂₁ = 0 := by
      ext i j
      exact (mem_blockPar g).1 hg (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) (by simp) (by simp)
    have hb : blockMat M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂ = g := by
      rw [blockMat, ← h0, Matrix.fromBlocks_toBlocks, hM, Equiv.apply_symm_apply]
    have hu : IsUnit (M.toBlocks₁₁.det * M.toBlocks₂₂.det) := by
      rw [← det_blockMat _ M.toBlocks₁₂, hb]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    refine ⟨(Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_left hu),
      Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_right hu), M.toBlocks₁₂), ?_⟩
    exact Subtype.ext (Units.ext hb)
end GlobalTheory.StdLoc
