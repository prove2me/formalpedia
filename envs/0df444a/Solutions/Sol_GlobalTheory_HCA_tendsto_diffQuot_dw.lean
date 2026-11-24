-- Prove2me | solution 1 for GlobalTheory.HCA.tendsto_diffQuot_dw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:42.328045+00:00
-- url     : https://prove2.me/submissions/26b92466-8e2b-45a7-af74-c08c31375c65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDeriv
import Theorems.Thm_GlobalTheory_HCA_contDiffOn_dw_of_isOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory Filter Topology
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (f : E d → ℂ)
    (hf : ContDiffOn ℝ ∞ f U) (w : List (Fin d)) (j : Fin d) {x : E d} (hx : x ∈ U) :
    Tendsto (fun n : ℕ => ((n : ℂ) + 1) * (dw w f (x + (1 / ((n : ℝ) + 1)) • ev j) - dw w f x))
      atTop (𝓝 (dw (j :: w) f x)) := by
  have hn := hU.mem_nhds hx
  have hd : DifferentiableAt ℝ (dw w f) x :=
    ((contDiffOn_dw_of_isOpen hU w f hf).contDiffAt hn).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => dw w f (x + t • ev j)) (fderiv ℝ (dw w f) x (ev j)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • ev j) (ev j) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (ev j)).const_add x
    have h2 : HasFDerivAt (dw w f) (fderiv ℝ (dw w f) x) (x + (0:ℝ) • ev j) := by
      simpa using hd.hasFDerivAt
    exact h2.comp_hasDerivAt (0:ℝ) h1
  have hs := hasDerivAt_iff_tendsto_slope.1 hline
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    positivity
  have h3 := hs.comp ht
  show Tendsto _ atTop (𝓝 (fderiv ℝ (dw w f) x (ev j)))
  refine h3.congr (fun n => ?_)
  simp only [Function.comp, slope_def_module, zero_smul, add_zero, sub_zero, Complex.real_smul]
  push_cast
  field_simp
end GlobalTheory.HCA
