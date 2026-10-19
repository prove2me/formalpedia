-- Prove2me | solution 1 for OAI.KervaireRibbon.one_defect_of_holonomy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:42:40.341965+00:00
-- url     : https://prove2.me/submissions/413cab13-060c-4db5-9035-d052f658b0b3

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
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow

open OAI OAI.KervaireRibbon
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
open Equiv Equiv.Perm KervaireCycle
open scoped Classical
variable {D A : Type*} [Group A]


theorem solution [Fintype D] (σ : Equiv.Perm D) (b u : D → A) (p : D)
    {Z : Type*} (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ D)
    (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (hu : ∀ d, d ≠ p → b d = u (σ d) * (u d)⁻¹)
    (hm : ∀ z, orbitWeight (finRotate (n z+1)) (fun i ↦ b (e ⟨z,i⟩)) (n z+1) 0 = 1) :
    b p = u (σ p) * (u p)⁻¹ := by
  obtain ⟨⟨z, k⟩, rfl⟩ := e.surjective p
  let R := finRotate (n z + 1)
  let B : Fin (n z + 1) → A := fun i ↦ b (e ⟨z,i⟩)
  let U : Fin (n z + 1) → A := fun i ↦ u (e ⟨z,i⟩)
  let δ : Fin (n z + 1) → A := fun i ↦ (U (R i))⁻¹ * B i * U i
  have hB : ∀ i, B i = U (R i) * δ i * (U i)⁻¹ := by intro i; simp only [δ]; group
  have hW : ∀ m, orbitWeight R B m 0 = U ((R^m) 0) * orbitWeight R δ m 0 * (U 0)⁻¹ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [orbitWeight_succ, orbitWeight_succ, ih, hB, pow_succ', Perm.mul_apply]
      group
  have hδ : ∀ i, i ≠ k → δ i = 1 := by
    intro i hi
    have hne : e ⟨z,i⟩ ≠ e ⟨z,k⟩ := fun h => hi (by
      have := e.injective h; simp at this; exact this)
    have := hu _ hne
    simp only [δ, B, U, R]
    rw [this, he]; group
  have hP : ∀ m, m ≤ n z + 1 → orbitWeight R δ m 0 = if k.val < m then δ k else 1 := by
    open Fin.NatCast in
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [orbitWeight_succ, ih (by omega), rotate_pow_apply]
      have hv : ((0 : Fin (n z + 1)) + (m : Fin (n z + 1))).val = m := by
        simp [Fin.val_natCast]; omega
      by_cases hk : k.val = m
      · have : (0 : Fin (n z + 1)) + (m : Fin (n z + 1)) = k := Fin.ext (by rw [hv, hk])
        rw [this, if_neg (by omega), if_pos (by omega), mul_one]
      · have : (0 : Fin (n z + 1)) + (m : Fin (n z + 1)) ≠ k := fun h => hk (by rw [← h, hv])
        rw [hδ _ this, one_mul]
        by_cases h2 : k.val < m
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
  have h1 := hW (n z + 1)
  rw [hP (n z + 1) le_rfl, if_pos k.isLt, rotate_pow_self] at h1
  have h2 : δ k = 1 := by
    have := hm z
    change orbitWeight R B (n z + 1) 0 = 1 at this
    rw [h1] at this
    simp only [Perm.one_apply] at this
    have := congrArg (fun g => (U 0)⁻¹ * g * U 0) this
    simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] at this
    exact this
  have h3 : b (e ⟨z,k⟩) = u (σ (e ⟨z,k⟩)) * δ k * (u (e ⟨z,k⟩))⁻¹ := by
    rw [he]; simp only [δ, B, U, R]; group
  rw [h3, h2, mul_one]

