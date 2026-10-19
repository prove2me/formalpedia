-- Prove2me | solution 1 for OAI.KervaireRegular.eq_zero_of_delta_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:20:40.890433+00:00
-- url     : https://prove2.me/submissions/3e04affc-e430-48e2-9391-160d404a6f38

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

open OAI OAI.KervaireRegular
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
variable {α β γ : Type*}
variable {A : Type*} [Group A]
theorem solution {T : Operator A} (hT : InCommutant T)
    (h : T (delta 1) = 0) : T = 0 := by
  classical
  have hdel : ∀ x : A, T (delta x) = 0 := by
    intro x
    have h1 : (right x⁻¹ : ℓ²(A, ℂ) ≃ₗᵢ[ℂ] ℓ²(A, ℂ)) (delta 1) = delta x := by
      rw [right, reindex_delta]; simp
    have hc := hT x⁻¹
    have := congrArg (fun S : Operator A => S (delta 1)) hc.eq
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [← h1]
    change T ((right x⁻¹ : Operator A) (delta 1)) = 0
    rw [this, h]; simp
  ext1 f
  have hs := lp.hasSum_single (E := fun _ : A => ℂ) (p := 2) (by norm_num) f
  have h2 := hs.mapL T
  have h3 : ∀ i, T (lp.single 2 i (f i)) = 0 := by
    intro i
    have : lp.single 2 i (f i) = f i • delta i := by
      rw [delta, ← lp.single_smul]; simp
    rw [this, map_smul, hdel, smul_zero]
  simp only [h3] at h2
  rw [ContinuousLinearMap.zero_apply]
  exact h2.unique hasSum_zero

