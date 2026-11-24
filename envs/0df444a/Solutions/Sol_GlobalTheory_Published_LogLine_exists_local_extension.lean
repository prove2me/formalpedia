-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.exists_local_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:18.015862+00:00
-- url     : https://prove2.me/submissions/1b9c4fbe-8c67-4807-bb18-7263f1f5aa69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
import Theorems.Thm_GlobalTheory_Published_LogLine_offDivisor_subset
import Theorems.Thm_GlobalTheory_Published_LogLine_isOpen_offDivisor
import Theorems.Thm_GlobalTheory_Published_LogLine_subset_closure_offDivisor
import Theorems.Thm_GlobalTheory_Published_LogLine_eqOn_of_eqOn_offDivisor
import Theorems.Thm_GlobalTheory_Published_LogLine_isPreconnected_offDivisor_ball
import Theorems.Thm_GlobalTheory_Published_LogLine_oneForm_single
import Theorems.Thm_GlobalTheory_Published_LogLine_clm_ext_single
import Theorems.Thm_GlobalTheory_Published_LogLine_fderiv_symm_of_fderiv_eq
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}
namespace GlobalTheory.Published.LogLine
theorem _root_.solution {c : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (S : Finset (Fin n))
    {b : Fin n → (Fin n → ℂ) → ℂ} (hb : ∀ i, DifferentiableOn ℂ (b i) (ball c r))
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (offDivisor (ball c r) S))
    (hne : ∀ z ∈ offDivisor (ball c r) S, f z ≠ 0)
    (h : ∀ z ∈ offDivisor (ball c r) S, ∀ i, fderiv ℂ f z (Pi.single i 1) = -(f z * b i z)) :
    ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (ball c r) ∧
      EqOn F f (offDivisor (ball c r) S) ∧ ∀ z ∈ ball c r, F z ≠ 0 := by
  set V := offDivisor (ball c r) S with hV
  have hVo : IsOpen V := isOpen_offDivisor isOpen_ball S
  have hVs : V ⊆ ball c r := offDivisor_subset _ _
  have hβ : DifferentiableOn ℂ (oneForm b) (ball c r) :=
    DifferentiableOn.fun_sum fun i _ => (hb i).smul_const _
  have hfd : ∀ z ∈ V, fderiv ℂ f z = -(f z • oneForm b z) := fun z hz =>
    clm_ext_single fun i => by simp [h z hz i, oneForm_single]
  have hc := (GlobalTheory.SCV.differentiableOn_fderiv isOpen_ball hβ).continuousOn
  have hsym : ∀ x y, EqOn (fun z => fderiv ℂ (oneForm b) z x y)
      (fun z => fderiv ℂ (oneForm b) z y x) (ball c r) := fun x y =>
    eqOn_of_eqOn_offDivisor isOpen_ball S
      ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const)
      ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const)
      fun z hz => fderiv_symm_of_fderiv_eq hVo (hβ.mono hVs) hf hne hfd hz x y
  obtain ⟨g, hg⟩ := (convex_ball c r).exists_forall_hasFDerivAt_of_fderiv_symmetric (𝕜 := ℂ)
    (ω := oneForm b) isOpen_ball (hβ.restrictScalars ℝ) fun z hz x y => by
      rw [(hβ.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
      exact hsym x y hz
  have hprod : ∀ z ∈ V, HasFDerivAt (fun w => f w * Complex.exp (g w))
      (0 : (Fin n → ℂ) →L[ℂ] ℂ) z := by
    intro z hz
    have h1 := ((hf.differentiableAt (hVo.mem_nhds hz)).hasFDerivAt).mul (hg z (hVs hz)).cexp
    refine h1.congr_fderiv ?_
    rw [hfd z hz]
    ext v
    simp
    ring
  obtain ⟨k, hk⟩ := hVo.exists_is_const_of_fderiv_eq_zero (𝕜 := ℂ)
    (isPreconnected_offDivisor_ball c hr S)
    (fun z hz => (hprod z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hprod z hz).fderiv)
  obtain ⟨z₀, hz₀⟩ : V.Nonempty :=
    closure_nonempty_iff.mp ⟨c, subset_closure_offDivisor isOpen_ball S (mem_ball_self hr)⟩
  have hk0 : k ≠ 0 := hk z₀ hz₀ ▸ mul_ne_zero (hne z₀ hz₀) (Complex.exp_ne_zero _)
  refine ⟨fun z => k * Complex.exp (-g z), fun z hz => ?_, fun z hz => ?_,
    fun z _ => mul_ne_zero hk0 (Complex.exp_ne_zero _)⟩
  · exact (((hg z hz).neg.cexp).const_mul k).differentiableAt.differentiableWithinAt
  · simp only
    rw [← hk z hz, mul_assoc, ← Complex.exp_add]
    simp
end GlobalTheory.Published.LogLine
