-- Prove2me | solution 1 for OAI.KervaireIncidenceCurrent.fderiv_incidence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:00:36.14083+00:00
-- url     : https://prove2.me/submissions/0ea8cdbf-5a4a-4574-b7a8-9e35bf941c8d

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
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
theorem ki_contDiff {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (incidence f) := by
  unfold incidence
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × Alg K R => f (p.1, p.2.1)) :=
    hf.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × Alg K R => p.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have h4 : ContDiff ℝ ∞ (fun p : ℝ × Alg K R => p.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have h3 : ContDiff ℝ ∞ (fun p : ℝ × Alg K R => diag (1 : Mat K) (star p.2.2.2)) := by
    simp_rw [diag_eq_corner]
    exact contDiff_const.add ((in22 (K := K) (R := R)).contDiff.comp ((starL' ℝ : Mat R ≃L[ℝ] Mat R).contDiff.comp h4))
  exact ((h1.mul h2).mul h3).mul ((starL' ℝ : Mat (K ⊕ R) ≃L[ℝ] Mat (K ⊕ R)).contDiff.comp h2)


theorem solution {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (p v : ℝ × Alg K R) :
    fderiv ℝ (incidence f) p v =
      fderiv ℝ f (p.1,p.2.1) (v.1,v.2.1) * p.2.2.1 * KervaireIncidenceCurrent.diag 1 (star p.2.2.2) * star p.2.2.1 +
      f (p.1,p.2.1) * v.2.2.1 * KervaireIncidenceCurrent.diag 1 (star p.2.2.2) * star p.2.2.1 +
      f (p.1,p.2.1) * p.2.2.1 * in22 (star v.2.2.2) * star p.2.2.1 +
      f (p.1,p.2.1) * p.2.2.1 * KervaireIncidenceCurrent.diag 1 (star p.2.2.2) * star v.2.2.1 := by
  have hd : DifferentiableAt ℝ (incidence f) p :=
    ((ki_contDiff hf).differentiable (by simp)) p
  have hline : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hd' : HasFDerivAt (incidence f) (fderiv ℝ (incidence f) p) (p + (0:ℝ) • v) := by
    rw [zero_smul, add_zero]; exact hd.hasFDerivAt
  have key := hd'.comp_hasDerivAt (0 : ℝ) hline
  -- direct computation along the line
  have hA : HasDerivAt (fun s : ℝ => f ((p + s • v).1, (p + s • v).2.1))
      (fderiv ℝ f (p.1, p.2.1) (v.1, v.2.1)) 0 := by
    have hl : HasDerivAt (fun s : ℝ => ((p + s • v).1, (p + s • v).2.1)) (v.1, v.2.1) 0 := by
      exact hline.fst.prodMk (hline.snd.fst)
    have hfd : HasFDerivAt f (fderiv ℝ f (p.1, p.2.1)) ((p + (0:ℝ) • v).1, (p + (0:ℝ) • v).2.1) := by
      rw [zero_smul, add_zero]; exact ((hf.differentiable (by simp)) _).hasFDerivAt
    exact hfd.comp_hasDerivAt (0 : ℝ) hl
  have hB : HasDerivAt (fun s : ℝ => (p + s • v).2.2.1) v.2.2.1 0 := hline.snd.snd.fst
  have hT : HasDerivAt (fun s : ℝ => (p + s • v).2.2.2) v.2.2.2 0 := hline.snd.snd.snd
  have hC : HasDerivAt (fun s : ℝ => KervaireIncidenceCurrent.diag (1 : Mat K) (star (p + s • v).2.2.2)) (in22 (K := K) (R := R) (star v.2.2.2)) 0 := by
    simp_rw [diag_eq_corner]
    have := ((in22 (K := K) (R := R)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((starL' ℝ : Mat R ≃L[ℝ] Mat R).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hT)).const_add (in11 (1 : Mat K))
    simpa using this
  have hD : HasDerivAt (fun s : ℝ => star (p + s • v).2.2.1) (star v.2.2.1) 0 := by
    exact (starL' ℝ : Mat (K ⊕ R) ≃L[ℝ] Mat (K ⊕ R)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hB
  have hprod := ((hA.mul hB).mul hC).mul hD
  have huniq := key.unique (hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => rfl)))
  simp only [Pi.mul_apply, zero_smul, add_zero] at huniq
  rw [huniq]
  noncomm_ring
