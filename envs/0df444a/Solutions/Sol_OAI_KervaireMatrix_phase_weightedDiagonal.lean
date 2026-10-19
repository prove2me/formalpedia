-- Prove2me | solution 1 for OAI.KervaireMatrix.phase_weightedDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:31:09.95411+00:00
-- url     : https://prove2.me/submissions/d48b003e-4967-451f-a06c-c10001d07bc2

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean:L197-L215
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMatrix.phase_weightedDiagonal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_KervaireSpectral_hasSum_spectralLog
import Theorems.Thm_OAI_KervaireSpectral_tendsto_smoothTrace_vectorCLM

-- ---- from OAI.GroupTheory.Kervaire.ScalarPhase ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireScalarPhase

theorem norm_cutApproach_lt_one {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) :
    ‖cutApproach ε‖ < 1 := by
  apply (sq_lt_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)).mp
  rw [← Complex.normSq_eq_norm_sq]
  have hsq : ε ^ 2 < 1 := by nlinarith [mul_pos hε (sub_pos.mpr hε')]
  simp only [cutApproach, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, one_pow]
  nlinarith [mul_pos (sq_pos_of_pos hε) (sub_pos.mpr hsq)]

theorem cutTime_pos (n : ℕ) : 0 < cutTime n := by
  unfold cutTime
  positivity

theorem cutTime_lt_one (n : ℕ) : cutTime n < 1 := by
  unfold cutTime
  apply (div_lt_one (by positivity)).mpr
  have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem norm_cutApproach_cutTime_lt_one (n : ℕ) : ‖cutApproach (cutTime n)‖ < 1 :=
  norm_cutApproach_lt_one (cutTime_pos n) (cutTime_lt_one n)

end KervaireScalarPhase

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.SpectralApproximation ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Applying any continuous functional to the convergent spectral logarithm
 commutes with its Mercator expansion. -/
theorem traceLog_eq_calculus (U : Operator H) (hU : U ∈ unitary (Operator H))
    (τ : Operator H →L[ℂ] ℂ) {a : ℂ} (ha : ‖a‖ < 1) :
    let hN := isStarNormal_of_mem_unitary hU
    traceLog τ a U = τ (cfcHom hN (spectralLog U hU a ha)) := by
  let hN := isStarNormal_of_mem_unitary hU
  have hc := (hasSum_spectralLog U hU ha).map (cfcHom hN) (cfcHom_continuous hN)
  have ht := hc.map τ τ.continuous
  apply HasSum.tsum_eq
  convert ht using 1
  ext n
  simp [map_smul, map_pow, cfcHom_id]

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.PhaseSubadditivity ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder

namespace KervaireCentralizer
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] OAI.KervaireCentralizer.instContinuousFunctionalCalculusRealOperatorIsSelfAdjoint
end KervaireCentralizer

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- Regularized tracial phases distribute over a finite vector family. -/
theorem smoothTrace_vectorSum (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : ι → H) {a : ℂ} (ha : ‖a‖ < 1) :
    smoothTrace (vectorSum ξ) a U = ∑ j, smoothTrace (vectorCLM (ξ j)) a U := by
  let hN := isStarNormal_of_mem_unitary hU
  simp_rw [smoothTrace, traceLog_eq_calculus U hU _ ha, vectorSum_apply]
  simp only [Complex.re_sum, Complex.im_sum, Finset.sum_div, Finset.sum_sub_distrib]

/-- Bounded convergence for the precise matrix-trace phase. -/
theorem tendsto_smoothTrace_vectorSum (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : ι → H) :
    let _ := isStarNormal_of_mem_unitary hU
    Tendsto (fun n => smoothTrace (vectorSum ξ) (cutApproach (cutTime n)) U)
      atTop (𝓝 (sumPhase U ξ)) := by
  let hN := isStarNormal_of_mem_unitary hU
  simp_rw [smoothTrace_vectorSum U hU ξ (norm_cutApproach_cutTime_lt_one _)]
  exact tendsto_finsetSum _ (fun j _ => tendsto_smoothTrace_vectorCLM U hU (ξ j))

end KervaireSpectral

namespace KervaireCentralizer
open KervaireTraceCalculus KervaireSpectral KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

end KervaireCentralizer

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.PhaseGrids ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder

namespace KervaireSpectral

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

open KervaireTraceCalculus KervaireScalarPhase
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Positive integral moments, including mass, determine the cut-sensitive phase.
This avoids assuming any Borel functional calculus naturality theorem. -/
theorem sumPhase_eq_of_moments
    (U : Operator H) (V : Operator K)
    (hU : U ∈ unitary (Operator H)) (hV : V ∈ unitary (Operator K))
    (ξ : ι → H) (η : κ → K)
    (hm : ∀ n : ℕ, vectorSum ξ (U ^ n) = vectorSum η (V ^ n)) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary hV
    sumPhase U ξ = sumPhase V η := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary hV
  have hs (a : ℂ) : smoothTrace (vectorSum ξ) a U = smoothTrace (vectorSum η) a V := by
    have hmass := hm 0
    simp only [pow_zero] at hmass
    unfold smoothTrace traceLog
    rw [hmass]
    simp_rw [hm]
  exact tendsto_nhds_unique (tendsto_smoothTrace_vectorSum U hU ξ)
    (by simpa only [hs] using tendsto_smoothTrace_vectorSum V hV η)

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.WeightedCycles ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {A : Type*} [Group A]

end KervaireMatrix
namespace KervaireSpectral
open KervaireTraceCalculus
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem vectorPhase_eq_of_moments (U : Operator H) (V : Operator K)
    (hU : U ∈ unitary (Operator H)) (hV : V ∈ unitary (Operator K))
    (ξ : H) (η : K)
    (hm : ∀ n : ℕ, inner ℂ ξ ((U^n) ξ) = inner ℂ η ((V^n) η)) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary hV
    vectorPhase U ξ = vectorPhase V η := by
  simpa only [sumPhase, vectorSum_apply, Fintype.sum_unique] using
    sumPhase_eq_of_moments U V hU hV (fun _ : Unit => ξ) (fun _ : Unit => η)
      (fun n => by simpa only [vectorSum_apply, Fintype.sum_unique, vectorCLM_apply] using hm n)
end KervaireSpectral

namespace KervaireRegular
open KervaireSpectral
open scoped Classical
variable {A : Type*} [Group A]

/-- Scalar moments really are the coefficients of the left-regular circuit word. -/
theorem moment_group_weight (z : ℂ) (a : A) (n : ℕ) :
    inner ℂ (delta (1 : A)) (((z • leftOperator a)^n) (delta 1)) =
      if a^n = 1 then z^n else 0 := by
  classical
  rw [smul_pow, ← leftOperator_pow]
  simp only [smul_apply, leftOperator_delta, mul_one, inner_smul_right, inner_delta_left]
  simp [delta, Pi.single_apply, eq_comm]

end KervaireRegular

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

theorem weightedDiagonal_pow_delta (u : D → ℂ) (a : D → A)
    (n : ℕ) (i : D) (x : A) :
    (weightedShift (Equiv.refl D) u a ^ n) (delta (i,x)) =
      u i ^ n • delta (i,a i ^ n * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, weightedShift_delta]
    simp only [Equiv.refl_apply, smul_smul, pow_succ', mul_assoc]
    congr 1
    ring

/-- The phase of the diagonal circuit power is the sum of the literal regular phases. -/
theorem phase_weightedDiagonal (u : D → ℂ) (a : D → A)
    (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (Equiv.refl D) u a hu)
    phase (weightedShift (Equiv.refl D) u a) = ∑ i, groupPhase (u i) (hu i) (a i) := by
  let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (Equiv.refl D) u a hu)
  apply Finset.sum_congr rfl
  intro i _
  apply vectorPhase_eq_of_moments _ _
    (weightedShift_unitary (Equiv.refl D) u a hu)
    (Unitary.smul_mem ⟨u i,hu i⟩ (leftOperator_unitary (a i)))
    (delta (i,(1 : A))) (delta 1)
  intro n
  classical
  change inner ℂ (delta (i,1)) ((weightedShift (Equiv.refl D) u a ^ n) (delta (i,1))) =
    inner ℂ (delta 1) (((u i • leftOperator (a i)) ^ n) (delta 1))
  rw [weightedDiagonal_pow_delta, moment_group_weight]
  simp only [mul_one, inner_smul_right, inner_delta_left]
  simp [delta, Pi.single_apply, eq_comm]

end KervaireMatrix
namespace KervaireCycle
open Fin.NatCast
variable {D B : Type*} [Monoid B]

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireCycle
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix
namespace KervaireCycle
variable {D B : Type*} [Monoid B]

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireCycle
open Fin.NatCast
variable {A : Type*} [Group A]

end KervaireMatrix

end

end OAI

-- ---- platform node ----
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
open KervaireRegular KervaireSpectral


theorem solution : type_of% @_root_.OAI.KervaireMatrix.phase_weightedDiagonal := @_root_.OAI.KervaireMatrix.phase_weightedDiagonal
