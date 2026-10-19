-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.vertexRoot_insert
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:29:09.362892+00:00
-- url     : https://prove2.me/submissions/10888ed7-ab6e-4e39-84de-65502c626a24

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]


theorem solution (g d : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    vertexRoot g * blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) * vertexRoot g =
      Matrix.diagonal (fun a => (g a.1 a.2 * d a.1 a.2 : ℂ)) := by
  ext ⟨v, i⟩ ⟨w, j⟩
  simp only [vertexRoot, blockD, blocks, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.comp_apply,
    Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases hv : v = w
  · subst hv
    by_cases hi : i = j
    · subst hi
      simp only [and_self, if_true, Matrix.diagonal_apply_eq]
      rw [show (g v i : ℂ) = (√(g v i) : ℂ) * (√(g v i) : ℂ) by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg v i)]]
      ring
    · simp [hi]
  · simp [hv]

