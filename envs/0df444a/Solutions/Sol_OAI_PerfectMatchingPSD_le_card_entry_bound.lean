-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.le_card_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:59:08.176643+00:00
-- url     : https://prove2.me/submissions/d6ae4194-e66f-4403-a255-b40f1b3bcb3b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatrixBounds.lean:L23-L48
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.le_card_entry_bound. The node keeps its source
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

lemma entry_product_bound {a x y b : ℝ} (hb : 0 ≤ b) (ha : |a| ≤ b) :
    x*a*y ≤ b*(x^2+y^2)/2 := by
  have hxy : 2 * |x| * |y| ≤ x^2+y^2 := by
    nlinarith [sq_nonneg (|x|-|y|), sq_abs x, sq_abs y]
  have he : x*a*y ≤ b*(|x| * |y|) := by
    calc
      _ ≤ |x*a*y| := le_abs_self _
      _ = |a| *(|x| * |y|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hxy hb]

lemma le_card_entry_bound {E : Matrix R R ℝ} (hE : E.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b) (hbound : ∀ i j, |E i j| ≤ b) :
    E ≤ ((Fintype.card R : ℝ)*b) • (1 : Matrix R R ℝ) := by
  apply sub_nonneg.mp
  apply Matrix.PosSemidef.nonneg
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_one.smul (.of_nonneg (mul_nonneg (Nat.cast_nonneg _) hb))).sub hE
  · intro x
    have hsum : (∑ i, ∑ j, x i*E i j*x j) ≤
        (Fintype.card R : ℝ)*b*(∑ i, (x i)^2) := by
      calc
        _ ≤ ∑ i, ∑ j, (b/2*(x i)^2 + b/2*(x j)^2) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          have he := entry_product_bound (x := x i) (y := x j) hb (hbound i j)
          linarith
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, ← Finset.mul_sum]
          ring
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, star_trivial]
    rw [sub_nonneg]
    simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, pow_two, smul_eq_mul, mul_assoc] using hsum

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open Matrix
open scoped MatrixOrder


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.le_card_entry_bound := @_root_.OAI.PerfectMatchingPSD.le_card_entry_bound
