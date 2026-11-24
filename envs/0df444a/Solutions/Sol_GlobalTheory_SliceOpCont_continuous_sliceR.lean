-- Prove2me | solution 1 for GlobalTheory.SliceOpCont.continuous_sliceR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:41:26.201806+00:00
-- url     : https://prove2.me/submissions/acc7ef02-6fee-4d37-8669-db964eb8d157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowNormMulSeminormSliceRLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SeminormSliceRLe
import Theorems.Thm_GlobalTheory_SliceOpCont_norm_padL_le
import Theorems.Thm_GlobalTheory_SliceOpCont_sliceR_sub_eq
import Theorems.Thm_GlobalTheory_SliceOpCont_seminorm_sliceR_le
import Theorems.Thm_GlobalTheory_SchwartzTranslateLip_seminorm_translate_sub_le
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SliceSchwartz.sliceR_apply



set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOpCont
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.SliceOpCont
theorem _root_.solution (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun x : κ → V => sliceR f x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  refine ((schwartz_withSeminorms ℂ (κ' → V) ℂ).tendsto_nhds _ _).2 fun i ε hε => ?_
  obtain ⟨k, n⟩ := i
  set C : ℝ := 2 ^ k * ((Finset.Iic (k, n + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f
  have hcont : Continuous (fun x : κ → V => ‖x - x₀‖ * (1 + ‖x - x₀‖) ^ k * C) := by fun_prop
  have h0 : ‖x₀ - x₀‖ * (1 + ‖x₀ - x₀‖) ^ k * C = 0 := by simp
  have hev : ∀ᶠ x in nhds x₀, ‖x - x₀‖ * (1 + ‖x - x₀‖) ^ k * C < ε := by
    have := hcont.continuousAt (x := x₀)
    rw [ContinuousAt, h0] at this
    exact this (Iio_mem_nhds hε)
  filter_upwards [hev] with x hx
  refine lt_of_le_of_lt ?_ hx
  change SchwartzMap.seminorm ℂ k n (sliceR f x - sliceR f x₀) ≤ _
  rw [sliceR_sub_eq]
  refine (seminorm_sliceR_le V _ x₀ k n).trans ?_
  refine (GlobalTheory.SchwartzTranslateLip.seminorm_translate_sub_le k n k n le_rfl le_rfl _ f).trans ?_
  have hC : 0 ≤ C := by positivity
  have hp := norm_padL_le (κ' := κ') (x - x₀)
  gcongr
end GlobalTheory.SliceOpCont
