-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.states_of_domination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:57:17.068529+00:00
-- url     : https://prove2.me/submissions/a12a3283-81fe-4f48-8eef-e83f0d702eb9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/BitTests.lean:L39-L80
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.states_of_domination. The node keeps its source
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

-- ---- from OAI.Combinatorics.MatchingPSD.SequentialTests ----
namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {R : Type u_1} [Fintype R] [DecidableEq R]

omit [DecidableEq R] in
lemma congruence_mono {A B : Matrix R R ℝ} (h : A ≤ B) (X : Matrix R R ℝ) :
    Xᵀ * A * X ≤ Xᵀ * B * X := by
  change (Xᵀ * B * X - Xᵀ * A * X).PosSemidef
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, mul_sub, sub_mul]
    using h.conjTranspose_mul_mul_same X

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.BitTests ----
namespace OAI

universe u_1

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder
variable {R : Type u_1} [Fintype R] [DecidableEq R]

lemma two_div_success {μ ε : ℝ} (hμ : 2 ≤ μ) (hε : 0 ≤ ε) (hub : μ ≤ 2+ε) :
    1-ε ≤ 2/μ := by
  rw [le_div_iff₀ (by linarith : 0 < μ)]
  have hh : ε ≤ ε*μ := by nlinarith
  nlinarith

lemma normalized_gauge_pair (G Q T : Matrix R R ℝ) (hu : IsUnit G) :
    (G*Q*G*(G⁻¹*T*G⁻¹)).trace = (Q*T).trace := by
  have hunit := (Matrix.isUnit_iff_isUnit_det G).mp hu
  have hl : G⁻¹*G=1 := Matrix.nonsing_inv_mul G hunit
  have hr : G*G⁻¹=1 := Matrix.mul_nonsing_inv G hunit
  have he : G*Q*G*(G⁻¹*T*G⁻¹) = G*(Q*T)*G⁻¹ := by
    calc
      _ = G*Q*(G*G⁻¹)*T*G⁻¹ := by simp only [mul_assoc]
      _ = _ := by rw [hr, mul_one]; simp only [mul_assoc]
  rw [he, Matrix.trace_mul_cycle, hl, one_mul]

lemma inverse_sqrt_congruence (D : Matrix R R ℝ) (hD : D.PosDef) :
    (CFC.sqrt D)⁻¹ * D * (CFC.sqrt D)⁻¹ = 1 := by
  let G := CFC.sqrt D
  have hGG : G*G=D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  have hu : IsUnit G := (IsUnit.mul_iff.mp (hGG ▸ hD.isUnit)).1
  have hl : G⁻¹*G=1 := Matrix.nonsing_inv_mul G ((Matrix.isUnit_iff_isUnit_det G).mp hu)
  have hr : G*G⁻¹=1 := Matrix.mul_nonsing_inv G ((Matrix.isUnit_iff_isUnit_det G).mp hu)
  change G⁻¹*D*G⁻¹=1
  rw [← hGG, ← mul_assoc, hl, one_mul, hr]

lemma states_of_domination {q : ℕ}
    (Q : (Fin q → Bool) → Matrix R R ℝ) (T : Fin q → Bool → Matrix R R ℝ)
    (D : Matrix R R ℝ) (hD : D.PosDef)
    (hQ : ∀ y, (Q y).PosSemidef) (hT : ∀ i b, (T i b).PosSemidef)
    (hdom : ∀ i, T i false + T i true ≤ D)
    (ε : ℝ) (hε : 0 ≤ ε)
    (htr : ∀ y, 2 ≤ (Q y*D).trace ∧ (Q y*D).trace ≤ 2+ε)
    (hbit : ∀ y i, (Q y * T i (y i)).trace = 2) :
    ∃ (ρ : (Fin q → Bool) → Matrix R R ℝ) (F : Fin q → Bool → Matrix R R ℝ),
      (∀ y, (ρ y).PosSemidef) ∧ (∀ y, (ρ y).trace = 1) ∧
      (∀ i b, 0 ≤ F i b) ∧ (∀ i, F i false + F i true ≤ 1) ∧
      ∀ y i, 1-ε ≤ (ρ y*F i (y i)).trace := by
  let G := CFC.sqrt D
  have hG : G.PosSemidef := (CFC.sqrt_nonneg D).posSemidef
  have hGG : G*G=D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  have hu : IsUnit G := (IsUnit.mul_iff.mp (hGG ▸ hD.isUnit)).1
  have hGi : G⁻¹.PosSemidef := hG.inv
  let μ := fun y => (Q y*D).trace
  have hμ (y : Fin q → Bool) : 0 < μ y := lt_of_lt_of_le (by norm_num) (htr y).1
  refine ⟨fun y => (μ y)⁻¹ • (G*Q y*G), fun i b => G⁻¹*T i b*G⁻¹,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    apply Matrix.PosSemidef.smul _ (le_of_lt (inv_pos.mpr (hμ y)))
    simpa only [hG.isHermitian.eq] using (hQ y).conjTranspose_mul_mul_same G
  · intro y
    rw [Matrix.trace_smul, Matrix.trace_mul_cycle, hGG, Matrix.trace_mul_comm]
    change (μ y)⁻¹ * μ y = 1
    exact inv_mul_cancel₀ (ne_of_gt (hμ y))
  · intro i b
    apply Matrix.PosSemidef.nonneg
    simpa only [hGi.isHermitian.eq] using (hT i b).conjTranspose_mul_mul_same G⁻¹
  · intro i
    have hg := congruence_mono (hdom i) G⁻¹
    have hGit : (G⁻¹)ᵀ=G⁻¹ := hGi.isHermitian.eq
    rw [hGit, inverse_sqrt_congruence D hD, mul_add, add_mul] at hg
    exact hg
  · intro y i
    rw [smul_mul_assoc, Matrix.trace_smul, normalized_gauge_pair G (Q y) (T i (y i)) hu,
      hbit y i]
    change 1-ε ≤ (μ y)⁻¹*2
    rw [mul_comm, ← div_eq_mul_inv]
    exact two_div_success (htr y).1 hε (htr y).2

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open Matrix
open scoped MatrixOrder


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.states_of_domination := @_root_.OAI.PerfectMatchingPSD.states_of_domination
