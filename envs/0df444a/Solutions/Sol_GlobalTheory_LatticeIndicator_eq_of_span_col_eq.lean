-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.eq_of_span_col_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:41:29.794097+00:00
-- url     : https://prove2.me/submissions/9e41fe94-3f85-4543-92af-8083aa4d1317

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_LatticeIndicator_exists_gl_of_span_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open GlobalTheory.LatticeIndicator
namespace GlobalTheory.LatticeIndicator
theorem _root_.solution {O m n R : Type*} [CommRing O] [IsLocalRing O] [Fintype n]
    [DecidableEq n] (c : O) (ψ : Matrix m n O → R)
    (hinv : ∀ (z : Matrix m n O) (k : GL n O), ψ (z * (k : Matrix n n O)) = ψ z)
    (hper : ∀ z y : Matrix m n O, ψ (z + c • y) = ψ z) (z z' : Matrix m n O)
    (h : Submodule.span O
        (Set.range fun j => (Ideal.span {c} • (⊤ : Submodule O (m → O))).mkQ (z.col j)) =
      Submodule.span O
        (Set.range fun j => (Ideal.span {c} • (⊤ : Submodule O (m → O))).mkQ (z'.col j))) :
    ψ z = ψ z' := by
  obtain ⟨g, hg⟩ := exists_gl_of_span_eq _ _ h
  have : ∀ j, ∃ y : m → O, c • y = z.col j - (z' * (g : Matrix n n O)).col j := by
    intro j
    have h1 : z.col j - (z' * (g : Matrix n n O)).col j ∈
        Ideal.span {c} • (⊤ : Submodule O (m → O)) := by
      rw [← Submodule.Quotient.eq]
      have h2 : (z' * (g : Matrix n n O)).col j = ∑ i, (g : Matrix n n O) i j • z'.col i := by
        ext i
        simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
      have h3 := hg j
      simp_rw [← map_smul, ← map_sum] at h3
      rw [h2]
      exact h3
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨y, -, hy⟩ := h1
    exact ⟨y, hy⟩
  choose y hy using this
  have hz : z = z' * (g : Matrix n n O) + c • Matrix.of fun i j => y j i := by
    ext i j
    have := congrFun (hy j) i
    simp only [Pi.smul_apply, Pi.sub_apply, Matrix.col_apply] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, this]
    ring
  rw [hz, hper, hinv]
end GlobalTheory.LatticeIndicator
