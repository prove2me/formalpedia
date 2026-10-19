-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.exists_rational_parking
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:05:46.448994+00:00
-- url     : https://prove2.me/submissions/871e7c2f-308c-4bf2-a045-f698f3d6ae16

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]


theorem solution (a b : ι → Space) {D R : ℝ} (hD : 0 ≤ D) :
    RationalConstant D → RationalConstant R →
    ∃ p : ι → Space, RationalCenters p ∧
      (∀ i j, D < |a i 0 - p j 0|) ∧
      (∀ i j, D < |b i 0 - p j 0|) ∧
      (∀ i j, i ≠ j → D < |p i 0 - p j 0|) ∧
      (∀ i, 2 + R < p i 0) := by
  intro _ _
  obtain ⟨K, hK⟩ := exists_nat_gt (D + |R| + 2 + ∑ i, |a i 0| + ∑ i, |b i 0|)
  have hsa : ∀ i, |a i 0| ≤ ∑ j, |a j 0| := fun i =>
    Finset.single_le_sum (f := fun j => |a j 0|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hsb : ∀ i, |b i 0| ≤ ∑ j, |b j 0| := fun i =>
    Finset.single_le_sum (f := fun j => |b j 0|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hsa0 : 0 ≤ ∑ j, |a j 0| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hsb0 : 0 ≤ ∑ j, |b j 0| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  let idx : ι → ℕ := fun i => (Fintype.equivFin ι i).val
  let p : ι → Space := fun i => ![(K:ℝ) * ((idx i : ℝ) + 1), 0, 0]
  have hp0 : ∀ i, p i 0 = K * ((idx i : ℝ) + 1) := fun i => rfl
  have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hRa := le_abs_self R
  have hRb := abs_nonneg R
  have hpK : ∀ i, (K:ℝ) ≤ p i 0 := by
    intro i; rw [hp0]
    have : (0:ℝ) ≤ idx i := Nat.cast_nonneg _
    nlinarith
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    fin_cases k
    · exact ⟨(K:ℚ) * ((idx i : ℚ) + 1), by simp [p]⟩
    · exact ⟨0, by simp [p]⟩
    · exact ⟨0, by simp [p]⟩
  · intro i j
    have h1 := hsa i
    have h2 := hpK j
    have h3 := le_abs_self (a i 0)
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · intro i j
    have h1 := hsb i
    have h2 := hpK j
    have h3 := le_abs_self (b i 0)
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · intro i j hij
    have hne : idx i ≠ idx j := fun h => hij ((Fintype.equivFin ι).injective (Fin.ext h))
    rw [hp0, hp0]
    have he : (K:ℝ) * ((idx i : ℝ) + 1) - K * ((idx j : ℝ) + 1) = K * ((idx i : ℝ) - idx j) := by ring
    rw [he, abs_mul, abs_of_nonneg hK0]
    have h1 : (1:ℝ) ≤ |(idx i : ℝ) - idx j| := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have : (idx i : ℝ) + 1 ≤ idx j := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      · have : (idx j : ℝ) + 1 ≤ idx i := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
    nlinarith
  · intro i
    have := hpK i
    linarith

