-- Prove2me | solution 1 for OAI.Paper256.polynomial_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:27:48.337264+00:00
-- url     : https://prove2.me/submissions/777f8047-86b8-43e7-834c-db1548d9e7ac

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PolynomialHomogeneous.lean:L77-L103
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.polynomial_homogeneous. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates

-- ---- from OAI.Analysis.HyperbolicCones.PolynomialHomogeneous ----
namespace OAI

noncomputable section

open Matrix MvPolynomial
open scoped BigOperators

universe u v

namespace Paper256

theorem determinant_homogeneous {ι : Type u} {σ : Type v} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℝ)) (d : ℕ)
    (hM : ∀ i j, (M i j).IsHomogeneous d) :
    M.det.IsHomogeneous (Fintype.card ι * d) := by
  classical
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro p _
  have hp : (∏ i, M (p i) i).IsHomogeneous (Fintype.card ι * d) := by
    simpa using IsHomogeneous.prod Finset.univ (fun i => M (p i) i)
      (fun _ => d) (fun i _ => hM (p i) i)
  simpa using hp.C_mul ((Equiv.Perm.sign p : ℤ) : ℝ)

theorem adjugate_homogeneous {σ : Type u} {n : ℕ}
    (M : Mat (n + 1) (MvPolynomial σ ℝ)) (d : ℕ)
    (hM : ∀ i j, (M i j).IsHomogeneous d) (i j : Fin (n + 1)) :
    (M.adjugate i j).IsHomogeneous (n * d) := by
  classical
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hc : ((-1 : MvPolynomial σ ℝ) ^ (j.val + i.val)).IsHomogeneous 0 := by
    simpa using (isHomogeneous_one (σ := σ) (R := ℝ)).neg.pow (j.val + i.val)
  have hm := determinant_homogeneous (M.submatrix j.succAbove i.succAbove) d
    (fun a b => hM (j.succAbove a) (i.succAbove b))
  simpa using hc.mul hm

theorem qMatrix_homogeneous {σ : Type u} (y : Fin 3 → MvPolynomial σ ℝ)
    (hy : ∀ i, (y i).IsHomogeneous 1) (i j : Fin 3) :
    (qMatrix y i j).IsHomogeneous 2 := by
  classical
  by_cases h : i = j
  · simpa [qMatrix, h] using ((hy i).pow 2).add ((hy (i + 1)).pow 2)
  · simpa [qMatrix, h] using ((hy i).mul (hy j)).neg

theorem phi_homogeneous {σ : Type u} (y : Fin 3 → MvPolynomial σ ℝ)
    (M : Mat 4 (MvPolynomial σ ℝ))
    (hy : ∀ i, (y i).IsHomogeneous 1)
    (hM : ∀ i j, (M i j).IsHomogeneous 3) (i j : Fin 4) :
    (phi y M i j).IsHomogeneous 5 := by
  classical
  have hq := qMatrix_homogeneous y hy
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [phi, Fin.cases_zero, Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Matrix.submatrix_apply]
      apply IsHomogeneous.sum
      intro a _
      apply IsHomogeneous.sum
      intro b _
      exact (hq a b).mul (hM b.succ a.succ)
    · simp only [phi, Fin.cases_zero, Fin.cases_succ]
      apply IsHomogeneous.neg
      apply IsHomogeneous.sum
      intro a _
      exact (hM 0 a.succ).mul (hq a j)
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [phi, Fin.cases_succ, Fin.cases_zero]
      apply IsHomogeneous.neg
      apply IsHomogeneous.sum
      intro a _
      exact (hq i a).mul (hM a.succ 0)
    · simp only [phi, Fin.cases_succ]
      exact (hM 0 0).mul (hq i j)

theorem polynomial_homogeneous : polynomial.IsHomogeneous 20 := by
  classical
  let X : Mat 4 (MvPolynomial Coord ℝ) :=
    symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inl ij))
  let Z : Mat 4 (MvPolynomial Coord ℝ) :=
    symmetricCoordinates fun ij => MvPolynomial.X (Sum.inl (Sum.inr ij))
  let y : Fin 3 → MvPolynomial Coord ℝ := fun i => MvPolynomial.X (Sum.inr i)
  have hX : ∀ i j, (X i j).IsHomogeneous 1 := by
    intro i j
    dsimp [X, symmetricCoordinates]
    split <;> exact isHomogeneous_X _ _
  have hZ : ∀ i j, (Z i j).IsHomogeneous 1 := by
    intro i j
    dsimp [Z, symmetricCoordinates]
    split <;> exact isHomogeneous_X _ _
  have hy : ∀ i, (y i).IsHomogeneous 1 := fun i => isHomogeneous_X _ _
  have hd : X.det.IsHomogeneous 4 := by
    simpa using determinant_homogeneous X 1 hX
  have ha : ∀ i j, (X.adjugate i j).IsHomogeneous 3 := by
    intro i j
    simpa using adjugate_homogeneous X 1 hX i j
  have hp := phi_homogeneous y X.adjugate hy ha
  have hm : ∀ i j, (((X.det) • Z - phi y X.adjugate) i j).IsHomogeneous 5 := by
    intro i j
    exact (hd.mul (hZ i j)).sub (hp i j)
  simpa [polynomial, matrixValue, X, Z, y] using
    determinant_homogeneous ((X.det) • Z - phi y X.adjugate) 5 hm

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Matrix MvPolynomial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Paper256.polynomial_homogeneous := @_root_.OAI.Paper256.polynomial_homogeneous
