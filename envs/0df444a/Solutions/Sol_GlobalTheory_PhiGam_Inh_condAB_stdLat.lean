-- Prove2me | solution 1 for GlobalTheory.PhiGam.Inh.condAB_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:07:37.565796+00:00
-- url     : https://prove2.me/submissions/ba9f42c4-6ead-4f45-a1eb-2592ed1858dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_GlobalTheory_PhiGam_sh_zero_eq
import Theorems.Thm_GlobalTheory_PhiGam_Inh_pull_stdLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam.Inh
variable {k : Type} [Field k]
namespace GlobalTheory.PhiGam.Inh
theorem _root_.solution {l : ℕ} (R : RingPG k l) (hγ : Function.Bijective R.γ) (n : ℕ) :
    CondAB (unitMod R hγ n).φ (fun _ => 0) (fun _ => 0) (fun _ => stdLat k) := by
  intro i
  change pull (lin R.φ) _ ≤ _ ∧ _ ≤ pull (lin R.φ) _
  simp [pull_stdLat, sh_zero_eq]
end GlobalTheory.PhiGam.Inh
