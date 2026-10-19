-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.posSemidef_entry_abs_le_trace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:01:26.664704+00:00
-- url     : https://prove2.me/submissions/f7229dd9-d1cc-4bae-ab10-cf45f7a0e5a7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatrixBounds.lean:L50-L79
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.posSemidef_entry_abs_le_trace. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests

-- ---- from OAI.Combinatorics.MatchingPSD.MatrixBounds ----
namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder
variable {R : Type u_1} [Fintype R] [DecidableEq R]

lemma posSemidef_entry_abs_le_trace {A : Matrix R R ℝ} (hA : A.PosSemidef) (i j : R) :
    |A i j| ≤ A.trace := by
  have hi : 0 ≤ A i i := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1)
    simpa using he
  have hj : 0 ≤ A j j := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single j 1)
    simpa using he
  have hsym : A j i = A i j := by
    simpa using congrArg (fun M : Matrix R R ℝ => M i j) hA.isHermitian.eq
  have hplus : -(A i i + A j j)/2 ≤ A i j := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_add, dotProduct_add,
      add_dotProduct, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at he
    rw [hsym] at he
    linarith
  have hminus : A i j ≤ (A i i + A j j)/2 := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_sub, dotProduct_sub,
      sub_dotProduct, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at he
    rw [hsym] at he
    linarith
  have hdiag (k : R) : A k k ≤ A.trace := by
    change A k k ≤ ∑ l, A l l
    apply Finset.single_le_sum (f := fun l => A l l)
    · intro l _
      have he := hA.dotProduct_mulVec_nonneg (Pi.single l 1)
      simpa using he
    · exact Finset.mem_univ k
  exact (abs_le.mpr ⟨by linarith, hminus⟩).trans (by linarith [hdiag i, hdiag j])

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open Matrix
open scoped MatrixOrder


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.posSemidef_entry_abs_le_trace := @_root_.OAI.PerfectMatchingPSD.posSemidef_entry_abs_le_trace
