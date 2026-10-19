-- Prove2me | solution 1 for OAI.KervaireMatrix.trace_mul_eq_sum_tsum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:23:00.524806+00:00
-- url     : https://prove2.me/submissions/aedebf4a-198f-4af8-825a-f098a4f31f54

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

open OAI OAI.KervaireMatrix
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open KervaireRegular
variable {D A : Type*} [Group A]
variable [Fintype D]
theorem km_formula {S T : Operator D A} (hS : InCommutant S) :
    trace (S*T) = ∑ i : D, ∑ j : D, ∑' x : A,
      S (delta (j,1)) (i,x⁻¹) * T (delta (i,1)) (j,x) := by
  classical
  rw [KervaireMatrix.trace_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  set f : Space D A := T (delta (i,1))
  have hs := lp.hasSum_single (E := fun _ : D × A => ℂ) (p := 2) (by norm_num) f
  have h2 := (hs.mapL S).mapL (innerSL ℂ (delta (i,(1:A))))
  have hterm : ∀ q : D × A, (innerSL ℂ (delta (i,(1:A)))) (S (lp.single 2 q (f q))) =
      S (delta (q.1,1)) (i, q.2⁻¹) * f q := by
    rintro ⟨j, x⟩
    have hsd : lp.single 2 (j,x) (f (j,x)) = f (j,x) • delta (j,x) := by
      ext q
      simp only [lp.coeFn_smul, Pi.smul_apply, delta, lp.single_apply, Pi.single_apply]
      split_ifs <;> simp
    have hdx : delta (j,x) = (KervaireMatrix.right (D := D) x⁻¹ : Space D A ≃ₗᵢ[ℂ] Space D A) (delta (j,1)) := by
      rw [KervaireMatrix.right_delta]; simp
    have hc := congrArg (fun R : Operator D A => R (delta (j,1))) (hS x⁻¹).eq
    simp only [ContinuousLinearMap.mul_apply] at hc
    rw [hsd, map_smul, map_smul, hdx]
    change f (j,x) • inner ℂ (delta (i,(1:A))) (S ((KervaireMatrix.right (D := D) x⁻¹ : Operator D A) (delta (j,1)))) = _
    rw [hc, inner_delta_left]
    change f (j,x) * (KervaireMatrix.right (D := D) x⁻¹ (S (delta (j,1)))) (i,1) = _
    rw [KervaireMatrix.right_apply]
    simp only [one_mul]
    exact mul_comm _ _
  simp only [hterm] at h2
  change HasSum _ (inner ℂ (delta (i,(1:A))) (S f)) at h2
  rw [ContinuousLinearMap.mul_apply]
  have hsum := h2.summable
  have hfib : ∀ j : D, HasSum (fun x : A => S (delta (j,1)) (i, x⁻¹) * f (j,x))
      (∑' x : A, S (delta (j,1)) (i, x⁻¹) * f (j,x)) := fun j => (hsum.prod_factor j).hasSum
  exact (h2.prod_fiberwise hfib).unique (hasSum_fintype _)

theorem solution {S T : Operator D A} (hS : InCommutant S) :
    trace (S*T) = ∑ i : D, ∑ j : D, ∑' x : A,
      S (delta (j,1)) (i,x⁻¹) * T (delta (i,1)) (j,x) := km_formula hS
