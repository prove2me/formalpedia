-- Prove2me | solution 1 for OAI.DirectCrouzeix.tensor_entryPair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:50:05.617112+00:00
-- url     : https://prove2.me/submissions/ae870134-59be-4395-a514-0c97dcec1dc7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/SingularPairs.lean:L88-L113
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.tensor_entryPair. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs

-- ---- from OAI.Analysis.DirectCrouzeix.SingularPairs ----
namespace OAI

universe u_37 u_38 u_39 u_40

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem tensor_entryPair {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) (X Y : Matrix (Fin n) (Fin m) ℂ) :
    inner ℂ (hsVector Y)
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (A ⊗ₖ C) (hsVector X)) =
      entryPair (Yᴴ * A * X) C := by
  simp only [hsVector, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toEuclideanCLM_toLp, dotProduct, Matrix.mulVec,
    Pi.star_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    entryPair, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs =>
    arg 2
    intro a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.tensor_entryPair := @_root_.OAI.DirectCrouzeix.tensor_entryPair
