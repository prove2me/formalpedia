-- Prove2me | solution 1 for OAI.KervaireTraversal.offDiagonal_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:44:31.683337+00:00
-- url     : https://prove2.me/submissions/649928f6-93ad-4574-acb4-adcd915053c0

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
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal

open OAI OAI.KervaireTraversal
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
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix
open Matrix KervaireFixed
open scoped Classical
variable {E : Type*} [Fintype E] [DecidableEq E]


theorem solution (N : Matrix (E ⊕ E) (E ⊕ E) ℂ)
    (hNs : star N = N) (hNu : N ∈ unitary (Matrix (E ⊕ E) (E ⊕ E) ℂ))
    (h₀ : ∀ i j, N (.inl i) (.inl j) = 0)
    (h₁ : ∀ i j, N (.inr i) (.inr j) = 0) :
    ∃ P : unitary (Matrix E E ℂ), N = fromBlocks 0 (star (P : Matrix E E ℂ)) P 0 := by
  have hN : N = fromBlocks 0 N.toBlocks₁₂ N.toBlocks₂₁ 0 := by
    conv_lhs => rw [← fromBlocks_toBlocks N]
    congr 1
    · ext i j; exact h₀ i j
    · ext i j; exact h₁ i j
  set B := N.toBlocks₁₂
  set C := N.toBlocks₂₁
  have hs := hNs
  rw [hN, star_eq_conjTranspose, fromBlocks_conjTranspose] at hs
  obtain ⟨-, hB, -, -⟩ := fromBlocks_inj.mp hs
  have hu := (Unitary.mem_iff.mp hNu).1
  rw [hNs, hN, fromBlocks_multiply, ← fromBlocks_one] at hu
  obtain ⟨h1, -, -, h2⟩ := fromBlocks_inj.mp hu
  simp only [zero_mul, mul_zero, zero_add, add_zero] at h1 h2
  rw [← hB] at h1 h2
  have hC : C ∈ unitary (Matrix E E ℂ) := by
    rw [Unitary.mem_iff, star_eq_conjTranspose]; exact ⟨h1, h2⟩
  refine ⟨⟨C, hC⟩, ?_⟩
  simp only [star_eq_conjTranspose]
  rw [hB]
  exact hN

