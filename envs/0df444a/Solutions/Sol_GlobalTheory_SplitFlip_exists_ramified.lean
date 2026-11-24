-- Prove2me | solution 1 for GlobalTheory.SplitFlip.exists_ramified
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:32.099303+00:00
-- url     : https://prove2.me/submissions/a398ca23-7837-4a60-b9ae-9122eae984a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitWeil_Model_ratCircle_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ ν : kˣ →* ℂˣ, ¬ IsUnram ν ∧ CondLE ϖ 2 ν ∧ ∀ x, ‖(ν x : ℂ)‖ = 1 := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have h1 : valuation k (1 + (ϖ : k)) = 1 := (valuation k).map_one_add_of_lt hlt
  let u : kˣ := Units.mk0 (1 + ϖ) (by intro h; simp [h] at h1)
  let Q := kˣ ⧸ unitCong (ϖ ^ 2)
  have hne : (Additive.ofMul (QuotientGroup.mk u : Q)) ≠ 0 := by
    intro h
    have h2 := ((QuotientGroup.eq_one_iff u).1 h).2
    simp only [u, Units.val_mk0, add_sub_cancel_left, Units.val_pow_eq_pow_val, map_pow] at h2
    have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
    exact absurd h2 (not_le.2 (by rw [pow_two]; exact mul_lt_of_lt_one_right h0 hlt))
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  let c' : Additive Q →+ AddCircle (1 : ℚ) := c
  let f : kˣ →* ℂˣ :=
    { toFun := fun x => Circle.toUnits (AddCircle.toCircle (ratCircle (c' (Additive.ofMul (QuotientGroup.mk x)))))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [QuotientGroup.mk_mul, ofMul_mul, map_add, map_add, AddCircle.toCircle_add, map_mul] }
  refine ⟨f, fun h => hc (ratCircle_eq_zero _ (AddCircle.injective_toCircle one_ne_zero ?_)), fun x hx => ?_,
    fun x => Circle.norm_coe _⟩
  · have := congrArg Units.val (h u h1)
    rw [AddCircle.toCircle_zero]
    exact Circle.ext this
  · show Circle.toUnits (AddCircle.toCircle (ratCircle (c' (Additive.ofMul (QuotientGroup.mk x))))) = 1
    rw [(QuotientGroup.eq_one_iff x).2 hx]; simp
end GlobalTheory.SplitFlip
