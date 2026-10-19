-- Prove2me | solution 1 for OAI.MatchingInterpolation.interpolation_matrix_domination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:07:33.394197+00:00
-- url     : https://prove2.me/submissions/19990737-afb2-4d72-ad2f-bb12a16f2e29

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatrixInterpolation.lean:L71-L125
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingInterpolation.interpolation_matrix_domination. The node keeps its source
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
import Theorems.Thm_OAI_MatchingInterpolation_weighted_interpolation
import Theorems.Thm_OAI_PerfectMatchingPSD_le_card_entry_bound

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

-- ---- from OAI.Combinatorics.MatchingPSD.MatrixInterpolation ----
namespace OAI

universe u_1 u_2

namespace MatchingInterpolation
open MatchingSmoothing Matrix PerfectMatchingPSD
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

lemma weightMass_nonneg (d : ℕ) (L : ℝ) : 0 ≤ weightMass d L :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma sum_abs_specialCoeff : (∑ j, |specialCoeff j|) = 6 := by
  norm_num [specialCoeff, Fin.sum_univ_succ]

lemma five_interpolation {d : ℕ} (P : Point → ℝ) (hP : P ∈ lowDegree coord d)
    {L : ℝ} (hL : L ≠ 0) :
    (∑ j, specialCoeff j * P (specialPoint j)) = ∑ g, weight d L g * P (scaledNode L g) := by
  have h := weighted_interpolation d P hP L hL
  simp only [specialCoeff, specialPoint, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, one_mul, neg_mul, Fin.sum_univ_zero, add_zero] at *
  change _ = ∑ g, weight d L g * P (fun a => origin a+L*(g a:ℝ))
  linarith

lemma finite_weighted_error {X : Type u_1} [Fintype X]
    (c e : X → ℝ) {η : ℝ} (he : ∀ x, |e x| ≤ η) :
    |∑ x, c x*e x| ≤ (∑ x, |c x|)*η := by
  calc
    _ ≤ ∑ x, |c x*e x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |c x| *η := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (he x) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma interpolation_error {d : ℕ} (F P : Point → ℝ)
    (hP : P ∈ lowDegree coord d) {L η : ℝ} (hL : L ≠ 0)
    (hs : ∀ j, |F (specialPoint j)-P (specialPoint j)| ≤ η)
    (hg : ∀ g : GridIndex d, |F (scaledNode L g)-P (scaledNode L g)| ≤ η) :
    |(∑ j, specialCoeff j*F (specialPoint j)) -
      ∑ g, weight d L g*F (scaledNode L g)| ≤ (6+weightMass d L)*η := by
  have hidentity : (∑ j, specialCoeff j*F (specialPoint j)) -
      ∑ g, weight d L g*F (scaledNode L g) =
    (∑ j, specialCoeff j*(F (specialPoint j)-P (specialPoint j))) -
      ∑ g, weight d L g*(F (scaledNode L g)-P (scaledNode L g)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, five_interpolation P hP hL]
    ring
  rw [hidentity]
  have h1 := finite_weighted_error specialCoeff (fun j => F (specialPoint j)-P (specialPoint j)) hs
  have h2 := finite_weighted_error (weight d L) (fun g => F (scaledNode L g)-P (scaledNode L g)) hg
  rw [sum_abs_specialCoeff] at h1
  calc
    _ ≤ |∑ j, specialCoeff j*(F (specialPoint j)-P (specialPoint j))| +
        |∑ g, weight d L g*(F (scaledNode L g)-P (scaledNode L g))| := abs_sub _ _
    _ ≤ 6*η + weightMass d L*η := add_le_add h1 h2
    _ = _ := by ring

section Matrices
variable {R : Type u_2} [Fintype R] [DecidableEq R]

lemma interpolation_matrix_domination (d : ℕ)
    (B : Point → Matrix R R ℝ) (hB : ∀ x, (B x).PosSemidef)
    (P : R → R → Point → ℝ) (hP : ∀ u v, P u v ∈ lowDegree coord d)
    {L η : ℝ} (hL : L ≠ 0) (hη : 0 ≤ η)
    (hs : ∀ j u v, |B (specialPoint j) u v-P u v (specialPoint j)| ≤ η)
    (hg : ∀ g : GridIndex d, ∀ u v, |B (scaledNode L g) u v-P u v (scaledNode L g)| ≤ η) :
    ∃ E : Matrix R R ℝ, E.PosSemidef ∧
      B (origin+dirA)+B (origin+dirB) ≤ B (origin+dirStar)+(2:ℝ) • B (origin+dirP)+E ∧
      ∀ (Q : Matrix R R ℝ) (m k : ℝ), Q.trace ≤ m →
        (∀ g : GridIndex d, (Q*B (scaledNode L g)).trace ≤ k) →
        (Q*E).trace ≤ weightMass d L*k +
          (Fintype.card R : ℝ)*(6+weightMass d L)*η*m := by
  let H := (∑ j, specialCoeff j • B (specialPoint j)) -
    ∑ g, weight d L g • B (scaledNode L g)
  let b := (6+weightMass d L)*η
  let c := (Fintype.card R : ℝ)*b
  let W := ∑ g, |weight d L g| • B (scaledNode L g)
  have hb : 0 ≤ b := mul_nonneg (by linarith [weightMass_nonneg d L]) hη
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) hb
  have hH : H.IsHermitian := by
    have hh (x : Point) := (hB x).isHermitian.eq
    simp only [H, Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul, star_trivial, hh]
  have hentry (u v : R) : |H u v| ≤ b := by
    simpa only [H, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
      interpolation_error (fun x => B x u v) (P u v) (hP u v) hL (fun j => hs j u v) (fun g => hg g u v)
  have hbound : H ≤ c • (1 : Matrix R R ℝ) := le_card_entry_bound hH hb hentry
  have hW : W.PosSemidef := matrix_sum_psd _ _ (fun g _ => (hB _).smul (abs_nonneg _))
  let E := W+c • (1 : Matrix R R ℝ)
  have hE : E.PosSemidef := hW.add (Matrix.PosSemidef.one.smul hc)
  refine ⟨E,hE,?_,?_⟩
  · apply sub_nonneg.mp
    apply Matrix.PosSemidef.nonneg
    have hdiff : (∑ g : GridIndex d, (|weight d L g|-weight d L g) • B (scaledNode L g)).PosSemidef :=
      matrix_sum_psd _ _ (fun g _ => (hB _).smul (sub_nonneg.mpr (le_abs_self _)))
    convert ((sub_nonneg.mpr hbound).posSemidef.add (hB origin)).add hdiff using 1
    dsimp [E,W,H]
    simp only [sub_smul, Finset.sum_sub_distrib, specialPoint, specialCoeff, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, one_smul, neg_smul,
      Fin.sum_univ_zero, add_zero]
    module
  · intro Q m k hm hk
    change (Q*(W+c • (1 : Matrix R R ℝ))).trace ≤ _
    rw [mul_add, Matrix.trace_add, mul_smul_comm, Matrix.trace_smul, mul_one]
    have hWt : (Q*W).trace ≤ weightMass d L*k := by
      dsimp [W,weightMass]
      rw [Finset.mul_sum, Matrix.trace_sum, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro g _
      rw [mul_smul_comm, Matrix.trace_smul]
      exact mul_le_mul_of_nonneg_left (hk g) (abs_nonneg _)
    have he := add_le_add hWt (mul_le_mul_of_nonneg_left hm hc)
    calc
      _ ≤ weightMass d L*k + c*m := he
      _ = _ := by dsimp [c,b]; ring

end Matrices
end MatchingInterpolation

end OAI

-- ---- platform node ----
open OAI OAI.MatchingInterpolation
open MatchingSmoothing Matrix PerfectMatchingPSD
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingInterpolation.interpolation_matrix_domination := @_root_.OAI.MatchingInterpolation.interpolation_matrix_domination
