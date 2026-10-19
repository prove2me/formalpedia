-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.weightedGram_rowBare_congr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:27:19.645008+00:00
-- url     : https://prove2.me/submissions/87bc047a-c232-4e3c-a471-f8e63323cbef

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]


theorem solution (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (v : Three) (f f' : BlockSpace ι → ℝ) (he : ∀ i, f (v,i)=f' (v,i)) :
    weightedGram (rowBare A g v) f = weightedGram (rowBare A g v) f' := by
  have key : Matrix.diagonal (fun a => (f a : ℂ)) * vertexProj v =
      Matrix.diagonal (fun a => (f' a : ℂ)) * vertexProj v := by
    simp only [vertexProj, Matrix.diagonal_mul_diagonal]
    congr 1; funext a
    obtain ⟨w, i⟩ := a
    by_cases h : w = v
    · subst h; simp [he]
    · simp [h]
  simp only [weightedGram, rowBare, rowStar, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal _) (vertexProj v), key, Matrix.mul_assoc]

