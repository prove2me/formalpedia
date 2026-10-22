-- Prove2me | solution 1 for GeomDL.EGNN.layer_E3_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-22T03:42:24.980694+00:00
-- url     : https://prove2.me/submissions/dd09cab0-e9af-405e-b32f-cf733454be2f

import Definitions.Def_GeomDL_EGNN_Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

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

/-- §5.5, pp. 83–84: the Satorras et al. (2021) layer is E(3)-equivariant. If the coordinates
are transformed by `g ∈ E(3)`, `x_u ↦ Rx_u + b` with `R ∈ O(3)` and `b ∈ ℝ³`, then the output
features `f'_u` are unchanged and the output coordinates transform in the same way,
`x'_u ↦ Rx'_u + b`. -/
theorem solution {n d : ℕ} {M M' F' : Type*} (φ : (Fin d → ℝ) → M' → F')
    (agg : Multiset M → M') (ψf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → M)
    (ψc : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (f : Matrix (Fin n) (Fin d) ℝ) (x : Fin n → E3)
    (R : Matrix.orthogonalGroup (Fin 3) ℝ) (b : E3) :
    (egnnLayer φ agg ψf ψc A f (fun u => rigid R b (x u))).1 = (egnnLayer φ agg ψf ψc A f x).1 ∧
    ∀ u, (egnnLayer φ agg ψf ψc A f (fun u => rigid R b (x u))).2 u =
      rigid R b ((egnnLayer φ agg ψf ψc A f x).2 u) := by
  constructor
  · funext u
    simp only [egnnLayer, egnnFeat]
    simp_rw [D22EGNN.rigid_dist]
  · intro u
    change rigid R b (x u) +
      ∑ v ∈ Finset.univ.filter (fun v => v ≠ u),
        ψc (f u) (f v) (‖rigid R b (x u) - rigid R b (x v)‖ ^ 2) •
          (rigid R b (x u) - rigid R b (x v)) =
      rigid R b (x u + ∑ v ∈ Finset.univ.filter (fun v => v ≠ u),
        ψc (f u) (f v) (‖x u - x v‖ ^ 2) • (x u - x v))
    simp_rw [D22EGNN.rigid_dist, D22EGNN.rigid_sub]
    simp only [rigid, map_add, map_sum, map_smul]
    abel

#print axioms solution

