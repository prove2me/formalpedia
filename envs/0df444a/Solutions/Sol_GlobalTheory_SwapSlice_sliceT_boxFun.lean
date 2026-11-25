-- Prove2me | solution 1 for GlobalTheory.SwapSlice.sliceT_boxFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:11:20.073715+00:00
-- url     : https://prove2.me/submissions/15fd8b21-dcfd-42fe-99f2-e0bfe04df7b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SwapNegApply
import Theorems.Thm_GlobalTheory_SwapSlice_sliceT_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SwapSlice
open GlobalTheory.WeilM
variable {k κ Y : Type}
namespace GlobalTheory.SwapSlice
theorem _root_.solution [CommRing k] (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ₁ φ₂ : (κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι (boxFun φ₁ φ₂) Z = ι φ₁ Z.1 * barL ι φ₂ Z.2 := by
  have e : (fun x₂ => ι (fun x₁ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) Z.1) = ι φ₁ Z.1 • φ₂ := by
    funext x₂
    have e' : (fun x₁ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₂ x₂ • φ₁ := by
      funext x₁; simp [boxFun, Function.comp_def, mul_comm]
    rw [e', map_smul]
    simp [mul_comm]
  rw [sliceT_apply, e, map_smul]
  simp
end GlobalTheory.SwapSlice
