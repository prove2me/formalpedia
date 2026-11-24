-- Prove2me | solution 1 for GlobalTheory.DiffVanish.sub_form_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:28.453638+00:00
-- url     : https://prove2.me/submissions/903aa0dd-6f15-4877-a432-05053f3069c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_multiDiff_sub
import Theorems.Thm_GlobalTheory_multiDiff_map
import Theorems.Thm_GlobalTheory_DiffVanish_form_apply
import Theorems.Thm_GlobalTheory_DiffVanish_multiDiff_form_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G K : Type*} [AddCommGroup G] [Field K] [CharZero K]
namespace GlobalTheory
namespace DiffVanish
theorem _root_.solution {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ) :
    DiffVanish d (φ - fun y ↦ (d.factorial : K)⁻¹ * h.form fun _ ↦ y) := fun g ↦ by
  ext x
  have := congrFun (multiDiff_map (AddMonoidHom.mulLeft (d.factorial : K)⁻¹) g
    (fun y ↦ h.form fun _ ↦ y)) x
  simp only [Function.comp_def, AddMonoidHom.coe_mulLeft] at this
  have hd : (d.factorial : K) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  rw [multiDiff_sub, Pi.sub_apply, this, h.multiDiff_form_diag, ← h.form_apply, nsmul_eq_mul,
    inv_mul_cancel_left₀ hd, sub_self, Pi.zero_apply]
end DiffVanish
end GlobalTheory
