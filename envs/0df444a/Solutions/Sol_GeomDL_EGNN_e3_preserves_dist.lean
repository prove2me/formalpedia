-- Prove2me | solution 1 for GeomDL.EGNN.e3_preserves_dist
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-22T03:42:10.513598+00:00
-- url     : https://prove2.me/submissions/4e68d0d1-a964-477f-afaa-8b766f26050a

import Definitions.Def_GeomDL_EGNN_Defs
import Mathlib.Tactic.NormNum

open GeomDL.EGNN Matrix

namespace D22EGNN

lemma orthogonal_norm (R : Matrix.orthogonalGroup (Fin 3) ℝ) (z : E3) :
    ‖Matrix.toEuclideanLin R.1 z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanLin_apply, star_trivial]
  rw [← Matrix.dotProduct_transpose_mulVec R.1 (WithLp.ofLp z) (R.1 *ᵥ WithLp.ofLp z),
    Matrix.mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp R.2,
    Matrix.one_mulVec]

lemma rigid_sub (R : Matrix.orthogonalGroup (Fin 3) ℝ) (b x y : E3) :
    rigid R b x - rigid R b y = Matrix.toEuclideanLin R.1 (x - y) := by
  simp [rigid, map_sub]

lemma rigid_dist (R : Matrix.orthogonalGroup (Fin 3) ℝ) (b x y : E3) :
    ‖rigid R b x - rigid R b y‖ = ‖x - y‖ := by
  rw [rigid_sub, orthogonal_norm]

end D22EGNN

theorem solution (R : Matrix.orthogonalGroup (Fin 3) ℝ) (b : E3) (x y : E3) :
    ‖rigid R b x - rigid R b y‖ = ‖x - y‖ := D22EGNN.rigid_dist R b x y

#print axioms solution
