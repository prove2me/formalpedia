-- Prove2me | solution 1 for GlobalTheory.Hk.RayForm.exists_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:51:53.021965+00:00
-- url     : https://prove2.me/submissions/69e2b63c-48eb-4adb-9544-d6ce3ed8d4bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryForm
import Theorems.Thm_GlobalTheory_Hk_RayForm_comb_injective
import Theorems.Thm_GlobalTheory_Hk_RayForm_range_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayForm
open GlobalTheory.Mem.PartialZeta
namespace GlobalTheory.Hk.RayForm
theorem _root_.solution (f₁ f₂ e₁ e₂ : ℂ) (hf : ((starRingEnd ℂ) f₁ * f₂).im ≠ 0)
    (he : ((starRingEnd ℂ) e₁ * e₂).im ≠ 0)
    (h : Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂}) :
    ∃ σ : ℤ × ℤ ≃ ℤ × ℤ, ∀ v, (v.1 : ℂ) * f₁ + v.2 * f₂ = (σ v).1 * e₁ + (σ v).2 * e₂ := by
  have hr : Set.range (fun v : ℤ × ℤ => (v.1 : ℂ) * f₁ + v.2 * f₂) =
      Set.range (fun v : ℤ × ℤ => (v.1 : ℂ) * e₁ + v.2 * e₂) := by
    rw [range_comb, range_comb, h]
  refine ⟨(Equiv.ofInjective _ (comb_injective f₁ f₂ hf)).trans
    ((Equiv.setCongr hr).trans (Equiv.ofInjective _ (comb_injective e₁ e₂ he)).symm), fun v => ?_⟩
  have key := Equiv.apply_ofInjective_symm (comb_injective e₁ e₂ he)
    (Equiv.setCongr hr (Equiv.ofInjective _ (comb_injective f₁ f₂ hf) v))
  simp only [Equiv.setCongr_apply, Equiv.ofInjective_apply] at key
  simp only [Equiv.trans_apply, Equiv.setCongr_apply, Equiv.ofInjective_apply]
  exact key.symm
end GlobalTheory.Hk.RayForm
