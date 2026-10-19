-- Prove2me | solution 1 for OAI.KervaireClosedCurrent.contDiff_multilinear_eval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:55:21.54802+00:00
-- url     : https://prove2.me/submissions/a3f79d07-0a9b-422b-98a0-69fe443e86ff

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

open OAI
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem kc_eval : ∀ (n : ℕ) {f : E → ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F}
    {V : Fin n → E → E}, ContDiff ℝ ∞ f → (∀ i, ContDiff ℝ ∞ (V i)) →
    ContDiff ℝ ∞ (fun x ↦ f x (V · x))
  | 0, f, V, hf, _ => by
    have : (fun x ↦ f x (V · x)) = fun x ↦ (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 ↦ E) F
        (fun _ => 0)) (f x) := by
      funext x
      simp only [ContinuousMultilinearMap.apply_apply]
      congr 1
      exact Subsingleton.elim _ _
    rw [this]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 ↦ E) F _).contDiff.comp hf
  | n + 1, f, V, hf, hV => by
    let g : E → ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F := fun x ↦ (f x).curryLeft (V 0 x)
    have hΨ : ContDiff ℝ ∞ (fun x ↦ (f x).curryLeft) :=
      (IsBoundedLinearMap.contDiff (f := fun g : ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) ↦ E) F =>
        g.curryLeft) (IsLinearMap.with_bound ⟨fun g h => rfl, fun c g => rfl⟩ 1
        (fun g => by rw [ContinuousMultilinearMap.curryLeft_norm, one_mul]))).comp hf
    have hg : ContDiff ℝ ∞ g := hΨ.clm_apply (hV 0)
    have := kc_eval n hg (V := fun i ↦ V i.succ) (fun i ↦ hV i.succ)
    convert this using 2 with x
    simp only [g, ContinuousMultilinearMap.curryLeft_apply]
    congr 1
    exact (Fin.cons_self_tail (fun i ↦ V i x)).symm

theorem solution {n : ℕ}
    {f : E → ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F}
    {V : Fin n → E → E} (hf : ContDiff ℝ ∞ f) (hV : ∀ i, ContDiff ℝ ∞ (V i)) :
    ContDiff ℝ ∞ (fun x ↦ f x (V · x)) := kc_eval n hf hV
