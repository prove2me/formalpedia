-- Prove2me | solution 1 for GlobalTheory.PhiGam.Inh.nab_vv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:07:40.299554+00:00
-- url     : https://prove2.me/submissions/09bb1dd3-71d6-4983-8138-172f8456c8cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Theorems.Thm_GlobalTheory_PhiGam_vv_ne_zero
import Theorems.Thm_GlobalTheory_PhiGam_nab_apply_eq

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
theorem _root_.solution {l : ℕ} (R : RingPG k l) :
    ∃ κ : k⟦X⟧, PowerSeries.constantCoeff κ = 1 ∧ nab (lin R.γ) (vv k) = -((κ : k⸨X⸩) * vv k) := by
  obtain ⟨κ, h1, h2⟩ := R.γ_v
  refine ⟨κ, h1, ?_⟩
  have hv := vv_ne_zero k
  rw [nab_apply_eq, lin_apply, h2, smul_eq_mul]
  field_simp
  ring
end GlobalTheory.PhiGam.Inh
