-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.numerical_selection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:23:50.622448+00:00
-- url     : https://prove2.me/submissions/6329b8ce-e962-4dc2-bc09-86e88c80c63e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/NumericalBounds.lean:L29-L66
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.numerical_selection. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Padding
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Parameters

-- ---- from OAI.Combinatorics.MatchingPSD.NumericalBounds ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix
open scoped BigOperators MatrixOrder

lemma blockSize_ge (d t : ℕ) : t^4 ≤ blockSize d t := by
  dsimp [blockSize]
  simpa only [one_mul] using Nat.mul_le_mul_right (t^4) (show 1 ≤ 4*(d+1) by omega)

lemma selection_of_cleared {q r T m L b : ℝ} (hb : 0 < b) (hc : 0 < r*m*L)
    (hnum : q*r^6*T*m^2*L^2 ≤ b) :
    q*r^4*T*b⁻¹ ≤ (1/(r*m*L))^2 := by
  rw [← div_eq_mul_inv, div_pow, one_pow]
  apply (div_le_div_iff₀ hb (sq_pos_of_pos hc)).mpr
  calc
    _ = q*r^6*T*m^2*L^2 := by ring
    _ ≤ b := hnum
    _ = _ := by ring

lemma numerical_selection (p d t r n T : ℕ) (ht : 2 ≤ t) (hr : 0 < r)
    (hn : n ≤ t^6) (hT : T ≤ t) (hrn : (r:ℝ) ≤ (n:ℝ)^p) :
    (t:ℝ)*r^4*T*((2*(3*(blockSize d t:ℝ)+1))^(2*(10*(p+1))))⁻¹ ≤
      (1/((r:ℝ)*((n:ℝ)+1)*(2*(t:ℝ)^4)))^2 := by
  have ht2 : (2:ℝ) ≤ t := by exact_mod_cast ht
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hn6 : (n:ℝ) ≤ (t:ℝ)^6 := by exact_mod_cast hn
  have hrp : (r:ℝ) ≤ (t:ℝ)^(6*p) := by
    simpa only [pow_mul] using hrn.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) hn6 p)
  have hm : (n:ℝ)+1 ≤ (t:ℝ)^7 := by
    have h6 : (1:ℝ) ≤ (t:ℝ)^6 := one_le_pow₀ ht1
    calc
      _ ≤ (t:ℝ)^6+(t:ℝ)^6 := add_le_add hn6 h6
      _ = 2*(t:ℝ)^6 := by ring
      _ ≤ (t:ℝ)*(t:ℝ)^6 := mul_le_mul_of_nonneg_right ht2 (pow_nonneg ht0 _)
      _ = _ := by ring
  have hL : 2*(t:ℝ)^4 ≤ (t:ℝ)^5 := by
    calc
      _ ≤ (t:ℝ)*(t:ℝ)^4 := mul_le_mul_of_nonneg_right ht2 (pow_nonneg ht0 _)
      _ = _ := by ring
  have hTr : (T:ℝ) ≤ t := by exact_mod_cast hT
  have hbase : (t:ℝ)^4 ≤ 2*(3*(blockSize d t:ℝ)+1) := by
    have hs : (t:ℝ)^4 ≤ (blockSize d t:ℝ) := by exact_mod_cast blockSize_ge d t
    have hs0 : (0:ℝ) ≤ (blockSize d t:ℝ) := Nat.cast_nonneg _
    linarith
  have hb : 0 < (2*(3*(blockSize d t:ℝ)+1))^(2*(10*(p+1))) := by positivity
  apply selection_of_cleared hb (by positivity)
  calc
    _ ≤ (t:ℝ)*((t:ℝ)^(6*p))^6*(t:ℝ)*((t:ℝ)^7)^2*((t:ℝ)^5)^2 := by gcongr
    _ = (t:ℝ)^(36*p+26) := by
      have he : 36*p+26 = 1+(6*p)*6+1+7*2+5*2 := by omega
      rw [he]
      simp only [pow_add, pow_mul, pow_one]
    _ ≤ (t:ℝ)^(8*(10*(p+1))) := pow_le_pow_right₀ ht1 (by omega)
    _ = ((t:ℝ)^4)^(2*(10*(p+1))) := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := pow_le_pow_left₀ (pow_nonneg ht0 _) hbase _

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix
open scoped BigOperators MatrixOrder


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.numerical_selection := @_root_.OAI.PerfectMatchingPSD.numerical_selection
