-- Prove2me | solution 1 for GlobalTheory.SCV.iteratedDeriv_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:16:28.011624+00:00
-- url     : https://prove2.me/submissions/eb2e08c6-dc1a-4625-8afc-f073563db094

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_contDiffOn_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : E} (hc : c ∈ U) (y : E) (n : ℕ) :
    iteratedDeriv n (fun t : ℂ => f (c + t • y)) 0 = iteratedFDeriv ℂ n f c (fun _ => y) := by
  set L : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ y with hL
  set s : Set E := (fun w => c + w) ⁻¹' U with hs
  have hso : IsOpen s := hU.preimage (by fun_prop)
  have hso' : IsOpen (L ⁻¹' s) := hso.preimage L.continuous
  have hg : DifferentiableOn ℂ (fun w => f (c + w)) s :=
    hf.comp (by fun_prop) fun w hw => hw
  have h0 : L 0 ∈ s := by simpa [hs] using hc
  have key := L.iteratedFDerivWithin_comp_right (contDiffOn_nat hso n hg) hso.uniqueDiffOn
    hso'.uniqueDiffOn h0 le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hso' (show (0 : ℂ) ∈ L ⁻¹' s from h0),
    iteratedFDerivWithin_of_isOpen n hso h0, iteratedFDeriv_comp_add_left] at key
  have e : (fun t : ℂ => f (c + t • y)) = (fun w => f (c + w)) ∘ L := by
    ext t
    simp [hL]
  rw [iteratedDeriv_eq_iteratedFDeriv, e, key]
  simp [hL]
end GlobalTheory.SCV
