-- Prove2me | solution 1 for GlobalTheory.isSiegel_fromBlocks_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:40:03.561639+00:00
-- url     : https://prove2.me/submissions/7703a609-e6fe-4ca3-9fcd-dead3c2792c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_IsSiegel_dotProduct_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
namespace GlobalTheory
theorem _root_.solution [Finite ι] [Finite κ] {Ω₁ : Matrix ι ι ℂ} {Ω₂ : Matrix κ κ ℂ} :
    IsSiegel (fromBlocks Ω₁ 0 0 Ω₂) ↔ IsSiegel Ω₁ ∧ IsSiegel Ω₂ := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  refine ⟨fun h => ⟨h.submatrix Sum.inl_injective, h.submatrix Sum.inr_injective⟩,
    fun ⟨h₁, h₂⟩ => IsSiegel.of_dotProduct_pos ?_ fun x hx => ?_⟩
  · exact IsSymm.fromBlocks h₁.isSymm (by simp) h₂.isSymm
  · have e : x ⬝ᵥ ((fromBlocks Ω₁ 0 0 Ω₂).map Complex.im *ᵥ x) =
        (x ∘ Sum.inl) ⬝ᵥ (Ω₁.map Complex.im *ᵥ (x ∘ Sum.inl)) +
        (x ∘ Sum.inr) ⬝ᵥ (Ω₂.map Complex.im *ᵥ (x ∘ Sum.inr)) := by
      simp [dotProduct, mulVec, Fintype.sum_sum_type]
    have n₁ := h₁.posDef.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have n₂ := h₂.posDef.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    simp only [star_trivial] at n₁ n₂
    rw [e]
    by_cases hl : x ∘ Sum.inl = 0
    · have hr : x ∘ Sum.inr ≠ 0 := fun hr => hx (by
        funext i
        rcases i with i | i
        · exact congrFun hl i
        · exact congrFun hr i)
      linarith [h₂.dotProduct_pos hr]
    · linarith [h₁.dotProduct_pos hl]
end GlobalTheory
