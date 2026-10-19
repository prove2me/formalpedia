-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.domination_decoder
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:12:11.768565+00:00
-- url     : https://prove2.me/submissions/a5a582dc-9e76-4e83-a405-0862a7868dd8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/DominationDecoder.lean:L12-L62
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.domination_decoder. The node keeps its source
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
import Theorems.Thm_OAI_PerfectMatchingPSD_nearly_perfect_bit_tests
import Theorems.Thm_OAI_PerfectMatchingPSD_states_of_domination

-- ---- from OAI.Combinatorics.MatchingPSD.DeterminantNormalization ----
namespace OAI

universe u_1 u_2 u_3

namespace PerfectMatchingPSD
open Matrix Set
variable {R : Type u_1} {I : Type u_2} {J : Type u_3} [Fintype R] [DecidableEq R]

open scoped MatrixOrder

lemma trace_mul_nonneg {A B : Matrix R R ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let G := CFC.sqrt B
  have hG : G.PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hGG : G * G = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have h := (hA.conjTranspose_mul_mul_same G).trace_nonneg
  rw [hG.isHermitian.eq, Matrix.trace_mul_cycle, hGG] at h
  simpa only [Matrix.trace_mul_comm B A] using h

lemma trace_mul_le_of_le {A B D : Matrix R R ℝ} (hA : A.PosSemidef) (hBD : B ≤ D) :
    (A * B).trace ≤ (A * D).trace := by
  have h := trace_mul_nonneg hA hBD
  rwa [mul_sub, Matrix.trace_sub, sub_nonneg] at h

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatrixBounds ----
namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder
variable {R : Type u_1} [Fintype R] [DecidableEq R]

omit [Fintype R] [DecidableEq R] in
lemma matrix_sum_psd {X : Type u_2} (s : Finset X) (f : X → Matrix R R ℝ)
    (hf : ∀ x ∈ s, (f x).PosSemidef) : (∑ x ∈ s, f x).PosSemidef :=
  (Finset.sum_nonneg (fun x hx => (hf x hx).nonneg)).posSemidef

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.DominationDecoder ----
namespace OAI

universe u_1

namespace PerfectMatchingPSD
open Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

lemma domination_decoder {R : Type u_1} [Fintype R] [DecidableEq R] {q : ℕ}
    (Q : (Fin q → Bool) → Matrix R R ℝ)
    (T : Fin q → Bool → Matrix R R ℝ) (P E : Fin q → Matrix R R ℝ)
    (S : Matrix R R ℝ)
    (hQ : ∀ y, (Q y).PosSemidef) (hT : ∀ i b, (T i b).PosSemidef)
    (hP : ∀ i, (P i).PosSemidef) (hE : ∀ i, (E i).PosSemidef) (hS : S.PosSemidef)
    (hdom : ∀ i, T i false + T i true ≤ S+(2:ℝ) • P i+E i)
    (hzero : ∀ y i, (Q y*P i).trace=0) (hstar : ∀ y, (Q y*S).trace=2)
    (hbit : ∀ y i, (Q y*T i (y i)).trace=2)
    {m e δ : ℝ} (hδ : 0 < δ) (hm : ∀ y, (Q y).trace ≤ m)
    (he : ∀ y i, (Q y*E i).trace ≤ e)
    (hε : 0 ≤ (q:ℝ)*e+δ*m)
    (hsmall : (q:ℝ)*Real.sqrt ((q:ℝ)*e+δ*m) ≤ 1/4) :
    (2:ℝ)^q/2 ≤ Fintype.card R := by
  let F := fun i => (2:ℝ) • P i+E i
  have hF (i : Fin q) : (F i).PosSemidef := (hP i).smul (by norm_num) |>.add (hE i)
  let D := S+(∑ i, F i)+δ • (1 : Matrix R R ℝ)
  have hsum : (∑ i, F i).PosSemidef := matrix_sum_psd _ _ (fun i _ => hF i)
  have hdelt : (δ • (1 : Matrix R R ℝ)).PosDef := Matrix.PosDef.one.smul hδ
  have hD : D.PosDef := by
    simpa only [D, add_comm] using hdelt.add_posSemidef (hS.add hsum)
  have hleS : S ≤ D := by
    have he := add_nonneg hsum.nonneg hdelt.posSemidef.nonneg
    dsimp [D]
    simpa only [add_assoc] using le_add_of_nonneg_right he
  have hdomD (i : Fin q) : T i false+T i true ≤ D := by
    apply (hdom i).trans
    have hi : F i ≤ ∑ j, F j := Finset.single_le_sum (fun j _ => (hF j).nonneg) (Finset.mem_univ i)
    calc
      S+(2:ℝ) • P i+E i = S+F i := by dsimp [F]; abel
      _ ≤ S+(∑ j, F j) := by simpa only [add_comm] using add_le_add_left hi S
      _ ≤ D := le_add_of_nonneg_right hdelt.posSemidef.nonneg
  have htr (y : Fin q → Bool) : 2 ≤ (Q y*D).trace ∧ (Q y*D).trace ≤ 2+((q:ℝ)*e+δ*m) := by
    constructor
    · rw [← hstar y]
      exact trace_mul_le_of_le (hQ y) hleS
    · dsimp [D]
      rw [mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, hstar,
        Finset.mul_sum, Matrix.trace_sum, mul_smul_comm, Matrix.trace_smul, mul_one]
      have hsumtr : (∑ i, (Q y*F i).trace) ≤ (q:ℝ)*e := by
        have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => he y i)
        have hFi (i : Fin q) : (Q y*F i).trace = (Q y*E i).trace := by
          simp only [F, mul_add, Matrix.trace_add, mul_smul_comm, Matrix.trace_smul,
            hzero, smul_zero, zero_add]
        simpa only [hFi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
      have hδm := mul_le_mul_of_nonneg_left (hm y) hδ.le
      change _ + δ*(Q y).trace ≤ _
      linarith
  obtain ⟨ρ,H,hρ,htρ,hH,hpair,hbit'⟩ := states_of_domination Q T D hD hQ hT hdomD
    ((q:ℝ)*e+δ*m) hε htr hbit
  exact nearly_perfect_bit_tests ρ H hρ htρ hH hpair _ hε hsmall hbit'

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.domination_decoder := @_root_.OAI.PerfectMatchingPSD.domination_decoder
