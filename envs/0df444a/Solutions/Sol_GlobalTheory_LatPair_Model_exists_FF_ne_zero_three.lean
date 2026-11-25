-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.exists_FF_ne_zero_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:23.777918+00:00
-- url     : https://prove2.me/submissions/3b4aecf0-34f0-45f5-9d89-37a1c1f6bf38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_Model_exists_FF_ne_zero
import Theorems.Thm_GlobalTheory_SplitWeil_Model_padic_localField
import Theorems.Thm_GlobalTheory_SplitWeil_Model_padic_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.LatPair.Model
theorem _root_.solution :
    letI := SplitWeil.Model.padic_localField 3
    ∃ (q : Unif ℚ_[3]) (ψ : AddChar ℚ_[3] Circle) (hψ : SplitWeil.HasConductor ψ 1) (φ : Form ℚ_[3] (Fin 2) ℂ),
      φ ∈ Mram ℚ_[3] (Fin 2) ℂ ∧ FF q (resChar ψ hψ q) φ ≠ 0 := by
  letI := SplitWeil.Model.padic_localField 3
  refine exists_FF_ne_zero (c := -1) fun h => ?_
  have h1 : (-1 : 𝓀[ℚ_[3]]) = 1 := by simpa using congrArg Units.val h
  have h3 : residue 𝒪[ℚ_[3]] 3 = 0 := by
    rw [residue_eq_zero_iff, ← not_not (a := _ ∈ _), notMem_maximalIdeal]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : (3 : ℚ_[3]) * v = 1 := congrArg Subtype.val hv
    have hle : ¬ valuation ℚ_[3] 1 < valuation ℚ_[3] v := by
      simpa using (Valuation.mem_integer_iff _ _).1 v.2
    rw [SplitWeil.Model.padic_lt] at hle
    have hn := congrArg norm hv'
    have h3 : ‖(3 : ℚ_[3])‖ < 1 := by simpa using Padic.norm_p_lt_one (p := 3)
    rw [norm_mul, norm_one] at hn
    rw [norm_one, not_lt] at hle
    nlinarith [norm_nonneg (3 : ℚ_[3]), norm_nonneg (v : ℚ_[3])]
  rw [map_ofNat] at h3
  exact one_ne_zero (α := 𝓀[ℚ_[3]]) (by linear_combination h3 + h1)
end GlobalTheory.LatPair.Model
