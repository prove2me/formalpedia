-- Prove2me | solution 1 for OAI.KervaireIncidenceCurrent.fderiv_model_gauge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:37:52.585546+00:00
-- url     : https://prove2.me/submissions/01adf144-37eb-4575-978f-832b7f6e004e

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


theorem ki_fderiv {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
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

theorem ki_model_fderiv (t : ℝ) (X : Mat K) (v : ℝ × Mat K) :
    fderiv ℝ (model (K := K) (R := R)) (t, X) v = KervaireIncidenceCurrent.diag v.2 0 := by
  have h : HasFDerivAt (model (K := K) (R := R))
      ((in11 (K := K) (R := R)).comp (ContinuousLinearMap.snd ℝ ℝ (Mat K))) (t, X) := by
    have : (model (K := K) (R := R)) = fun p => in11 (K := K) (R := R) p.2 + in22 (K := K) (R := R) (-1) := by
      funext p; unfold model; rw [diag_eq_corner]
    rw [this]
    exact ((in11 (K := K) (R := R)).hasFDerivAt.comp (t, X) hasFDerivAt_snd).add_const _
  rw [h.fderiv]
  simp [in11, KervaireIncidenceCurrent.diag]

theorem ki_model_contDiff : ContDiff ℝ ∞ (model (K := K) (R := R)) := by
  have : (model (K := K) (R := R)) = fun p => in11 (K := K) (R := R) p.2 + in22 (K := K) (R := R) (-1) := by
    funext p; unfold model; rw [diag_eq_corner]
  rw [this]
  exact ((in11 (K := K) (R := R)).contDiff.comp contDiff_snd).add contDiff_const

theorem solution (t : ℝ) (U : unitary (Mat K)) (V : unitary (Mat R))
    (h : Horizontal K R) :
    fderiv ℝ (incidence model) (t,(gaugePoint U V : Alg K R))
      (0,(gaugePoint U V : Alg K R)*(direction h : Alg K R)) =
      (modelHorizontalEquiv U V h : Mat (K ⊕ R)) := by
  have hR : ((modelHorizontalEquiv U V h : skewAdjoint.submodule ℝ (Mat (K ⊕ R))) : Mat (K ⊕ R)) =
      star (star (gaugeFrame U V : Mat (K ⊕ R))) *
        KervaireFixedSpace.derivativeMatrix 1 (skewConj U h.1) h.2.1 h.2.2 *
        star (gaugeFrame U V : Mat (K ⊕ R)) := rfl
  have hSC : ((skewConj U h.1 : skewAdjoint.submodule ℝ (Mat K)) : Mat K) =
      star (U : Mat K) * (h.1 : Mat K) * U := rfl
  rw [hR, ki_fderiv ki_model_contDiff, ki_model_fderiv, star_star]
  unfold KervaireFixedSpace.derivativeMatrix
  rw [hSC]
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩, Z⟩ := h
  have hA' : star A = -A := hA
  have hB' : star B = -B := hB
  have hU1 : (U : Mat K) * star (U : Mat K) = 1 := U.2.2
  have hV1 : (V : Mat R) * star (V : Mat R) = 1 := V.2.2
  simp only [gaugePoint, gaugeFrame, direction, model, LinearMap.coe_mk,
    AddHom.coe_mk, Prod.mk_mul_mk, one_mul, neg_mul, one_smul]
  simp only [KervaireIncidenceCurrent.diag, off, in22, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_conjTranspose, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_zero]
  rw [Matrix.star_eq_conjTranspose] at hA' hB' hU1 hV1
  congr 1
  · have e : (U : Mat K) * ((U : Mat K)ᴴ * A * U) * (U : Mat K)ᴴ =
        ((U : Mat K) * (U : Mat K)ᴴ) * A * ((U : Mat K) * (U : Mat K)ᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [e, hU1, Matrix.mul_assoc, hU1, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, two_smul]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul]
    rw [neg_smul, two_smul]
    simp only [Matrix.mul_assoc]
    abel
  · rw [hB', Matrix.mul_neg, Matrix.neg_mul]

