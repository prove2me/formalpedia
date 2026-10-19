-- Prove2me | solution 1 for OAI.KervaireSpectral.sumPhase_le_half_codim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:43:39.189826+00:00
-- url     : https://prove2.me/submissions/3678e9de-6ce9-4b4a-9c01-fb455fc7e4e0

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseDimension.lean:L174-L192
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.sumPhase_le_half_codim. The node keeps its source
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
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Theorems.Thm_OAI_KervaireSpectral_hasSum_spectralLog
import Theorems.Thm_OAI_KervaireSpectral_sumPhase_add_star_le_codim
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

-- ---- from OAI.GroupTheory.Kervaire.PhaseDimension ----
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
open scoped ComplexOrder

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

end

section
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℂ H] in
/-- The sum of vector functionals over an ONB is precisely algebraic trace. -/
theorem vectorSum_onb (b : OrthonormalBasis ι ℂ H) (T : Operator H) :
    vectorSum b T = LinearMap.trace ℂ H T.toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ b, vectorSum_apply]
  rfl

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι]

/-- Powers telescope under a unitary conjugation. -/
theorem unitary_conj_pow (U Q : Operator H) (hQ : Q ∈ unitary (Operator H)) (n : ℕ) :
    (Q * U * star Q)^n = Q * U^n * star Q := by
  induction n with
  | zero => simpa using (Unitary.mem_iff.mp hQ).2.symm
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    have h := (Unitary.mem_iff.mp hQ).1
    calc (Q * U^n * star Q) * (Q * U * star Q) =
        Q * U^n * (star Q * Q) * U * star Q := by noncomm_ring
         _ = Q * (U^n * U) * star Q := by rw [h]; noncomm_ring

omit [FiniteDimensional ℂ H] in
/-- The finite-vector trace of an ONB is cyclic. -/
theorem vectorSum_onb_mul_comm (b : OrthonormalBasis ι ℂ H) (T S : Operator H) :
    vectorSum b (T*S) = vectorSum b (S*T) := by
  rw [vectorSum_onb, vectorSum_onb]
  exact LinearMap.trace_mul_comm ℂ T.toLinearMap S.toLinearMap

/-- Conjugation preserves the exact, possibly discontinuous, spectral phase. -/
theorem sumPhase_unitary_conj (U Q : Operator H)
    (hU : U ∈ unitary (Operator H)) (hQ : Q ∈ unitary (Operator H))
    (b : OrthonormalBasis ι ℂ H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (mul_mem (mul_mem hQ hU) (Unitary.star_mem hQ))
    sumPhase (Q*U*star Q) b = sumPhase U b := by
  apply sumPhase_eq_of_moments _ _
    (mul_mem (mul_mem hQ hU) (Unitary.star_mem hQ)) hU b b
  intro n
  rw [unitary_conj_pow U Q hQ n,
    vectorSum_onb_mul_comm b (Q * U^n) (star Q), ← mul_assoc,
    (Unitary.mem_iff.mp hQ).1, one_mul]

/-- Inverse-symmetric spectrum divides the codimension bound by two. -/
theorem sumPhase_le_half_codim (U Q : Operator H)
    (hU : U ∈ unitary (Operator H)) (hQ : Q ∈ unitary (Operator H))
    (hconj : Q*U*star Q = star U)
    (b : OrthonormalBasis ι ℂ H) (E : Submodule ℂ H)
    (hE : ∀ v : E, U (v : H) = (v : H)) :
    let _ := isStarNormal_of_mem_unitary hU
    sumPhase U b ≤ ((Module.finrank ℂ H : ℝ) - Module.finrank ℂ E) / 2 := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
  change sumPhase U b ≤ _
  have heq : sumPhase (star U) b = sumPhase U b := by
    simpa only [hconj] using sumPhase_unitary_conj U Q hU hQ b
  have hb := sumPhase_add_star_le_codim U hU b E hE
  change sumPhase U b + sumPhase (star U) b ≤ (Module.finrank ℂ Eᗮ : ℝ) at hb
  rw [heq] at hb
  have hd : (Module.finrank ℂ E : ℝ) + Module.finrank ℂ Eᗮ = Module.finrank ℂ H := by
    exact_mod_cast E.finrank_add_finrank_orthogonal
  linarith

end KervaireSpectral

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

end KervaireSpectral

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireSpectral
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


theorem solution : type_of% @_root_.OAI.KervaireSpectral.sumPhase_le_half_codim := @_root_.OAI.KervaireSpectral.sumPhase_le_half_codim
