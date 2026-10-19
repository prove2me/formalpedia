-- Prove2me | solution 1 for OAI.KervaireIncidenceCurrent.fderiv_frame_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:03:02.891286+00:00
-- url     : https://prove2.me/submissions/03b29647-5802-4670-beea-75f1e70601c3

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


theorem ki_block (U : Mat K) (V T : Mat R) (hU : star U = -U) (hV : star V = -V) (hT : T * star T = 1) :
    KervaireIncidenceCurrent.diag U V * KervaireIncidenceCurrent.diag 1 (star T) +
      KervaireIncidenceCurrent.diag 1 (star T) * star (KervaireIncidenceCurrent.diag U V) =
    in22 (K := K) (star (T * (star T * V * T - V))) := by
  have hin : ∀ Z : Mat R, in22 (K := K) Z = Matrix.fromBlocks 0 0 0 Z := fun Z => rfl
  rw [hin]
  simp only [KervaireIncidenceCurrent.diag, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp only [← Matrix.star_eq_conjTranspose, star_zero, hV]
  have h1 : T * (star T * V * T - V) = V * T - T * V := by
    rw [mul_sub, ← mul_assoc, ← mul_assoc, hT, one_mul]
  rw [h1, star_sub, star_mul, star_mul, hV]
  congr 1 <;> simp only [Matrix.conjTranspose_zero, mul_zero, zero_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, mul_one,
    one_mul, hU, add_neg_cancel] <;> try noncomm_ring

theorem solution {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (X : Mat K) (Q : Mat (K ⊕ R)) (T : unitary (Mat R))
    (U : skewAdjoint.submodule ℝ (Mat K)) (V : skewAdjoint.submodule ℝ (Mat R)) :
    fderiv ℝ (incidence f) (t,X,Q,(T : Mat R)) (0,0,Q*KervaireIncidenceCurrent.diag U V,0) =
    fderiv ℝ (incidence f) (t,X,Q,(T : Mat R)) (0,0,0,(T : Mat R)*compensated T V) := by
  rw [ki_fderiv hf, ki_fderiv hf]
  simp only [Prod.mk_zero_zero, _root_.map_zero, zero_mul, add_zero, zero_add, mul_zero, star_zero]
  have hb := ki_block (U : Mat K) (V : Mat R) (T : Mat R) U.property V.property (Unitary.mul_star_self_of_mem T.property)
  have hc : ((compensated T V : skewAdjoint.submodule ℝ (Mat R)) : Mat R) = star (T : Mat R) * V * T - V := rfl
  rw [hc, ← hb, star_mul]
  noncomm_ring
