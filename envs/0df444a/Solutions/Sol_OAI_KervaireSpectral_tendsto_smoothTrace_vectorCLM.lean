-- Prove2me | solution 1 for OAI.KervaireSpectral.tendsto_smoothTrace_vectorCLM
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:04:15.240987+00:00
-- url     : https://prove2.me/submissions/f17cfe7a-0e6a-4eb1-ba13-2fb4a0e927ff

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralApproximation.lean:L131-L155
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.tendsto_smoothTrace_vectorCLM. The node keeps its source
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
import Theorems.Thm_OAI_KervaireScalarPhase_tendsto_smoothPhase_cut
import Theorems.Thm_OAI_KervaireSpectral_smoothTrace_vectorCLM

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

theorem smoothPhase_mem_Icc {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    smoothPhase a z ∈ Set.Icc (0 : ℝ) 1 := by
  have h := Complex.abs_arg_le_pi_div_two_iff.mpr (re_one_sub_mul_pos ha hz).le
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have hl' : -(1/2:ℝ) ≤ (1-a*z).arg / Real.pi :=
    (le_div_iff₀ Real.pi_pos).mpr (by linarith)
  have hu' : (1-a*z).arg / Real.pi ≤ (1/2:ℝ) :=
    (div_le_iff₀ Real.pi_pos).mpr (by linarith)
  dsimp [smoothPhase]
  constructor <;> linarith

theorem cutTime_pos (n : ℕ) : 0 < cutTime n := by
  unfold cutTime
  positivity

theorem cutTime_lt_one (n : ℕ) : cutTime n < 1 := by
  unfold cutTime
  apply (div_lt_one (by positivity)).mpr
  have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem tendsto_cutTime : Tendsto cutTime atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Filter.Eventually.of_forall cutTime_pos⟩
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0)
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 2)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h

theorem norm_cutApproach_cutTime_lt_one (n : ℕ) : ‖cutApproach (cutTime n)‖ < 1 :=
  norm_cutApproach_lt_one (cutTime_pos n) (cutTime_lt_one n)

theorem tendsto_smoothPhase_cutTime {z : ℂ} (hz : ‖z‖ = 1) :
    Tendsto (fun n : ℕ => smoothPhase (cutApproach (cutTime n)) z) atTop (𝓝 (phase z)) :=
  (tendsto_smoothPhase_cut hz).comp tendsto_cutTime

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

/-- Dominated convergence reaches the exact value zero at the phase cut. -/
theorem tendsto_smoothTrace_vectorCLM (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    Tendsto (fun n => smoothTrace (vectorCLM ξ) (cutApproach (cutTime n)) U)
      atTop (𝓝 (vectorPhase U ξ)) := by
  let hN := isStarNormal_of_mem_unitary hU
  have he (n : ℕ) := smoothTrace_vectorCLM U hU ξ (norm_cutApproach_cutTime_lt_one n)
  simp_rw [he]
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (spectralSmooth U hU _ (norm_cutApproach_cutTime_lt_one n)).continuous.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply Filter.Eventually.of_forall
    intro z
    have hz := CStarRing.norm_of_mem_unitary
      (spectrum_subset_unitary_of_mem_unitary hU z.property)
    rw [Real.norm_eq_abs, abs_of_nonneg
      ((smoothPhase_mem_Icc (norm_cutApproach_cutTime_lt_one n) hz.le).1)]
    exact (smoothPhase_mem_Icc (norm_cutApproach_cutTime_lt_one n) hz.le).2
  · apply Filter.Eventually.of_forall
    intro z
    exact tendsto_smoothPhase_cutTime (CStarRing.norm_of_mem_unitary
      (spectrum_subset_unitary_of_mem_unitary hU z.property))

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
open KervaireTraceCalculus KervaireScalarPhase


theorem solution : type_of% @_root_.OAI.KervaireSpectral.tendsto_smoothTrace_vectorCLM := @_root_.OAI.KervaireSpectral.tendsto_smoothTrace_vectorCLM
