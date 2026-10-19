-- Prove2me | solution 1 for OAI.KervaireIncidenceCurrent.model_fiber_blocks
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:43:19.073389+00:00
-- url     : https://prove2.me/submissions/c230d4dd-178a-4209-b09e-0121c1d37439

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree

open OAI OAI.KervaireIncidenceCurrent
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]


theorem solution (X A : Mat K) (B : Matrix K R ℂ) (C : Matrix R K ℂ)
    (D T : Mat R) (hQ : fromBlocks A B C D ∈ unitary (Mat (K ⊕ R)))
    (heq : KervaireIncidenceCurrent.diag X (-1) * fromBlocks A B C D = fromBlocks A B C D * KervaireIncidenceCurrent.diag 1 T) :
    X = 1 ∧ B = 0 ∧ C = 0 ∧ T = -1 ∧ A ∈ unitary (Mat K) ∧ D ∈ unitary (Mat R) := by
  have hQ1 := hQ.1
  have hQ2 := hQ.2
  rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hQ1 hQ2
  unfold KervaireIncidenceCurrent.diag at heq
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at heq
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.neg_mul, Matrix.mul_neg] at heq
  obtain ⟨hA, hB, hC, hD⟩ := Matrix.fromBlocks_inj.mp heq
  have hC0 : C = 0 := by
    have : (2 : ℂ) • C = 0 := by rw [two_smul]; nth_rewrite 1 [← hC]; simp
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  subst hC0
  rw [← Matrix.fromBlocks_one] at hQ1 hQ2
  obtain ⟨q11, q12, q21, q22⟩ := Matrix.fromBlocks_inj.mp hQ1
  obtain ⟨p11, p12, p21, p22⟩ := Matrix.fromBlocks_inj.mp hQ2
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at q11 q12 q21 q22 p11 p12 p21 p22
  -- q11 : Aᴴ * A = 1
  have hAA : A * Aᴴ = 1 := mul_eq_one_comm.mp q11
  have hX : X = 1 := by
    have : X * A * Aᴴ = A * Aᴴ := by rw [hA]
    rwa [Matrix.mul_assoc, hAA, Matrix.mul_one] at this
  subst hX
  have hBB : B * Bᴴ = 0 := by rw [hAA] at p11; simpa using p11
  have hB0 : B = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp hBB
  subst hB0
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, zero_add] at q22
  have hDD : D * Dᴴ = 1 := mul_eq_one_comm.mp q22
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · have : Dᴴ * (D * T) = Dᴴ * (-D) := by rw [hD]
    rwa [← Matrix.mul_assoc, q22, Matrix.one_mul, Matrix.mul_neg, q22] at this
  · exact ⟨q11, hAA⟩
  · exact ⟨q22, hDD⟩

