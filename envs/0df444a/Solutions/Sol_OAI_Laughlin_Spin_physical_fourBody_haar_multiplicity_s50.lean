-- Prove2me | solution 1 for OAI.Laughlin.Spin.physical_fourBody_haar_multiplicity_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T19:12:04.211405+00:00
-- url     : https://prove2.me/submissions/82609de1-80d2-41db-bc31-a6fc46ec18a8

import Mathlib
import Definitions.Def_OAIQ050L024
import Theorems.Thm_OAI_Laughlin_Rotation_source_spin_haar_schur_s50
import Theorems.Thm_OAI_Laughlin_Spin_fourBody_haar_compressed_s50
import Theorems.Thm_OAI_Laughlin_Spin_retainedFourReal_outer_trace_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ErrorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem source_rows_admissible : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2,
    row.1 ≤ e.1+e.2.1 := by decide

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem fourSpinWeight_dimension (Q D : ℕ) (hQ : D+2 ≤ Q) :
    fourSpinWeight Q D+1=4*Q-1-2*D := by unfold fourSpinWeight; omega

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_HaarOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped Matrix

theorem source_equal_spin_haar_trace (Q : ℕ) (M : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :
    rectangularIntegral sourceHaar
      (rectangularOrbit (sourceSpinRepresentation Q) (sourceSpinRepresentation Q) M)=
      (Matrix.trace M/(Q+1 : ℕ)) • (1 : Matrix (Fin (Q+1)) (Fin (Q+1)) ℂ) :=
  source_spin_haar_schur_s50 Q M

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_MultiplicityHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem fourBody_haar_multiplicity_block (Q D : ℕ) (hD : D+2 ≤ Q)
    (r s : OddPairLabel D) (M : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) M) * retainedFourInclusion Q D hD s =
      (Matrix.trace ((retainedFourInclusion Q D hD r)ᴴ*M*retainedFourInclusion Q D hD s) /
        (4*Q-1-2*D : ℕ)) • 1 := by
  rw [fourBody_haar_compressed_s50,source_equal_spin_haar_trace]
  have hd : ((fourSpinWeight Q D+1 : ℕ) : ℂ) = ((4*Q-1-2*D : ℕ) : ℂ) := by
    exact_mod_cast fourSpinWeight_dimension Q D hD
  rw [hd]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TraceReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem retainedFourReal_complex (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) :
    (retainedFourReal Q D hQ r).map Complex.ofReal = retainedFourInclusion Q D hQ r := rfl

theorem fourBodyTermMatrix_trace (Q D t : ℕ) (hQ : D+2 ≤ Q) (r s : OddPairLabel D)
    (e f : ℕ × ℕ × ℤ) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1)
    (hTQ : e.1+e.2.1+(f.1+f.2.1-t)+2 ≤ Q) :
    Matrix.trace ((retainedFourReal Q D hQ r)ᵀ * fourBodyTermMatrix Q t e f *
      retainedFourReal Q D hQ s) = -fourErrorEntry Q D (oddPairDeficit r) (oddPairDeficit s) t e f := by
  rw [fourBodyTermMatrix,Matrix.mul_smul,Matrix.smul_mul,Matrix.trace_smul,
    retainedFourReal_outer_trace_s50 Q D (e.1+e.2.1+(f.1+f.2.1-t)) _ _ _ _ _ _ hQ hTQ r s rfl (by omega)]
  unfold fourErrorEntry
  dsimp only
  split_ifs <;> simp only [smul_eq_mul] <;> ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_PhysicalTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem trace_sandwich_list_sum {I J : Type*} [Fintype I] [Fintype J]
    (V W : Matrix I J ℝ) (l : List (Matrix I I ℝ)) :
    Matrix.trace (Vᵀ*l.sum*W) = (l.map (fun M => Matrix.trace (Vᵀ*M*W))).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons,List.map_cons,Matrix.mul_add,Matrix.add_mul,Matrix.trace_add,ih]

theorem negative_list_sum {I : Type*} (l : List I) (a b : I → ℝ)
    (h : ∀ i ∈ l, a i = -b i) : (l.map a).sum = -(l.map b).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons,h i (by simp),ih (fun j hj => h j (by simp [hj]))]
    ring

theorem source_fourBody_rows_support : ∀ row ∈ Certificate.rows, ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
    e.1+e.2.1+(f.1+f.2.1-row.1) ≤ 23 := by decide

theorem source_physical_fourBody_trace_identity (Q D : ℕ) (hQ : 25 ≤ Q) (hD : D+2 ≤ Q)
    (r s : OddPairLabel D) :
    Matrix.trace ((retainedFourReal Q D hD r)ᵀ * physicalFourBodyMatrix Q * retainedFourReal Q D hD s) =
      physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s) := by
  unfold physicalFourBodyMatrix physicalFourError
  rw [trace_sandwich_list_sum]
  simp only [List.map_map,Function.comp_def]
  apply negative_list_sum
  intro row hrow
  unfold fourErrorRow
  rw [trace_sandwich_list_sum]
  simp only [List.map_map,Function.comp_def]
  apply negative_list_sum
  intro e he
  rw [trace_sandwich_list_sum]
  simp only [List.map_map,Function.comp_def]
  apply negative_list_sum
  intro f hf
  exact fourBodyTermMatrix_trace Q D row.1 hD r s e f
    (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)
    (by have := source_fourBody_rows_support row hrow e he f hf; omega)

theorem trace_real_sandwich_complex {I J : Type*} [Fintype I] [Fintype J]
    (V W : Matrix I J ℝ) (M : Matrix I I ℝ) :
    Matrix.trace ((V.map Complex.ofReal)ᴴ*M.map Complex.ofReal*W.map Complex.ofReal) =
      Complex.ofReal (Matrix.trace (Vᵀ*M*W)) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.transpose_apply,Matrix.map_apply,Complex.star_def,Complex.conj_ofReal,
    Complex.ofReal_sum,Complex.ofReal_mul]

theorem physical_fourBody_haar_multiplicity_s50_oai (Q D : ℕ) (hQ : 25 ≤ Q) (hD : D+2 ≤ Q)
    (r s : OddPairLabel D) :
    (retainedFourInclusion Q D hD r)ᴴ * matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) *
        retainedFourInclusion Q D hD s =
      ((physicalFourError Q D (oddPairDeficit r) (oddPairDeficit s) : ℂ) / (4*Q-1-2*D : ℕ)) • 1 := by
  rw [fourBody_haar_multiplicity_block,← retainedFourReal_complex Q D hD r,
    ← retainedFourReal_complex Q D hD s,trace_real_sandwich_complex,
    source_physical_fourBody_trace_identity Q D hQ hD]

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.physical_fourBody_haar_multiplicity_s50_oai := @OAI.Laughlin.Spin.physical_fourBody_haar_multiplicity_s50_oai
