-- Prove2me | solution 1 for OAI.KervaireCentralizer.phase_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:07:33.858055+00:00
-- url     : https://prove2.me/submissions/4b7b7dbd-018e-4fed-b4ac-532ec97ff83d

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseSubadditivity.lean:L186-L213
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireCentralizer.phase_subadditive. The node keeps its source
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
import Theorems.Thm_OAI_KervaireCentralizer_exists_phaseOperator_mem
import Theorems.Thm_OAI_KervaireSpectral_hasSum_spectralLog
import Theorems.Thm_OAI_KervaireSpectral_tendsto_smoothTrace_vectorCLM
import Theorems.Thm_OAI_KervaireTraceCalculus_geometricPart_trace_bound
import Theorems.Thm_OAI_KervaireTraceCalculus_hasDerivAt_smoothTrace_path

-- ---- from OAI.GroupTheory.Kervaire.SpectralLogarithm ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open KervaireStrong

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The vector functional respects the star, without a trace assumption. -/
theorem vectorCLM_star (ξ : H) (T : Operator H) :
    vectorCLM ξ (star T) = star (vectorCLM ξ T) := by
  simp only [vectorCLM_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

end KervaireSpectral

end

end OAI

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

-- ---- from OAI.GroupTheory.Kervaire.TraceCalculus ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireTraceCalculus
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Complex
variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

end Complex

section PositiveTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder

attribute [local instance] OAI.KervaireTraceCalculus.instContinuousFunctionalCalculusRealIsSelfAdjoint_oAI
end PositiveTrace
section RealPath
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

end RealPath
section Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end Cayley
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]

omit [Nontrivial A] in
/-- Positive generators give a unitary path at all real times. -/
theorem exp_phaseVelocity_mem_unitary {B : A} (hB : 0 ≤ B) (t : ℝ) :
    NormedSpace.exp (t • phaseVelocity B) ∈ unitary A := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp [phaseVelocity, star_smul, hB.star_eq]

/-- The one-sided derivative estimate for the smooth regularization. -/
theorem deriv_smoothTrace_path_le (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    (hs : ∀ X : A, τ (star X) = star (τ X))
    {U B : A} (hU : U ∈ unitary A) (hB : 0 ≤ B)
    {a : ℂ} (ha : ‖a‖ < 1) (t : ℝ) :
    deriv (fun t : ℝ => smoothTrace τ a
      (U * NormedSpace.exp (t • phaseVelocity B))) t ≤ (τ B).re := by
  rw [(hasDerivAt_smoothTrace_path τ ht hU hB ha t).deriv]
  apply geometricPart_trace_bound τ ht hp hs hB
  rw [norm_smul, CStarRing.norm_of_mem_unitary ((unitary A).mul_mem hU
    (exp_phaseVelocity_mem_unitary hB t)), mul_one]
  exact ha

/-- Integrating the regularized derivative bound over the unit path. -/
theorem smoothTrace_mul_exp_le (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    (hs : ∀ X : A, τ (star X) = star (τ X))
    {U B : A} (hU : U ∈ unitary A) (hB : 0 ≤ B)
    {a : ℂ} (ha : ‖a‖ < 1) :
    smoothTrace τ a (U * NormedSpace.exp (phaseVelocity B)) ≤
      smoothTrace τ a U + (τ B).re := by
  have hd := fun t => hasDerivAt_smoothTrace_path τ ht hU hB ha t
  have hc : Continuous (fun t : ℝ => smoothTrace τ a
      (U * NormedSpace.exp (t • phaseVelocity B))) :=
    continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hh := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    hc.continuousOn (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (fun t _ => deriv_smoothTrace_path_le τ ht hp hs hU hB ha t)
    0 (by simp) 1 (by simp) (by norm_num)
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one, one_smul, sub_zero,
    sub_le_iff_le_add, add_comm] using hh

end KervaireTraceCalculus

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

/-- Finite vector functionals are positive on squares. -/
theorem vectorSum_star_mul_nonneg (ξ : ι → H) (T : Operator H) :
    0 ≤ (vectorSum ξ (star T * T)).re := by
  rw [vectorSum_apply, Complex.re_sum]
  apply Finset.sum_nonneg
  intro j _
  change 0 ≤ (inner ℂ (ξ j) (star T (T (ξ j)))).re
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change 0 ≤ RCLike.re (inner ℂ (T (ξ j)) (T (ξ j)))
  rw [inner_self_eq_norm_sq]
  positivity

/-- Finite vector functionals respect adjoints. -/
theorem vectorSum_star (ξ : ι → H) (T : Operator H) :
    vectorSum ξ (star T) = star (vectorSum ξ T) := by
  simp only [vectorSum_apply, star_sum]
  exact Finset.sum_congr rfl (fun j _ => vectorCLM_star (ξ j) T)

end KervaireSpectral

namespace KervaireCentralizer
open KervaireTraceCalculus KervaireSpectral KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The logarithm trace commutes with the centralizer inclusion. -/
theorem traceLog_inclusion (S : Set (Operator (H := H))) (ξ : ι → H)
    (a : ℂ) (X : algebra S) :
    traceLog (trace S ξ) a X = traceLog (vectorSum ξ) a (X : Operator (H := H)) := by
  unfold traceLog
  apply tsum_congr
  intro n
  simp

/-- The smooth trace computed internally is the same operator trace. -/
theorem smoothTrace_inclusion (S : Set (Operator (H := H))) (ξ : ι → H)
    (a : ℂ) (X : algebra S) :
    smoothTrace (trace S ξ) a X = smoothTrace (vectorSum ξ) a (X : Operator (H := H)) := by
  simp [smoothTrace, traceLog_inclusion]

/-- Spectral phase subadditivity in a finite-vector tracial centralizer.
 The trace property will be proved for the arbitrary-group matrix representation. -/
theorem phase_subadditive [Nontrivial H] (S : Set (Operator (H := H))) (ξ : ι → H)
    (ht : ∀ X Y : algebra S, trace S ξ (X * Y) = trace S ξ (Y * X))
    (U V : algebra S) (hU : U ∈ unitary (algebra S)) (hV : V ∈ unitary (algebra S)) :
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S U).mp hU)
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S V).mp hV)
    let _ := isStarNormal_of_mem_unitary ((unitary_iff S (U*V)).mp ((unitary _).mul_mem hU hV))
    sumPhase ((U*V : algebra S) : Operator (H := H)) ξ ≤
      sumPhase (U : Operator (H := H)) ξ + sumPhase (V : Operator (H := H)) ξ := by
  have hU' := (unitary_iff S U).mp hU
  have hV' := (unitary_iff S V).mp hV
  have hUV' := (unitary_iff S (U*V)).mp ((unitary _).mul_mem hU hV)
  let hVN := isStarNormal_of_mem_unitary hV'
  obtain ⟨B,hB,hBV,hvec⟩ := exists_phaseOperator_mem S V hV
  have htrace : (trace S ξ B).re = sumPhase (V : Operator (H := H)) ξ := by
    simp only [trace_apply, vectorSum_apply, Complex.re_sum, hvec, sumPhase]
  have hp (X : algebra S) : 0 ≤ (trace S ξ (star X * X)).re :=
    vectorSum_star_mul_nonneg ξ (X : Operator (H := H))
  have hs (X : algebra S) : trace S ξ (star X) = star (trace S ξ X) :=
    vectorSum_star ξ (X : Operator (H := H))
  have hbound (n : ℕ) := smoothTrace_mul_exp_le (trace S ξ) ht hp hs hU hB
    (norm_cutApproach_cutTime_lt_one n)
  simp only [hBV, htrace, smoothTrace_inclusion] at hbound
  exact le_of_tendsto_of_tendsto
    (tendsto_smoothTrace_vectorSum _ hUV' ξ)
    ((tendsto_smoothTrace_vectorSum _ hU' ξ).add tendsto_const_nhds)
    (Filter.Eventually.of_forall hbound)

end KervaireCentralizer

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireCentralizer
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open KervaireTraceCalculus KervaireSpectral KervaireScalarPhase


theorem solution : type_of% @_root_.OAI.KervaireCentralizer.phase_subadditive := @_root_.OAI.KervaireCentralizer.phase_subadditive
