-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_apply_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:39.108998+00:00
-- url     : https://prove2.me/submissions/5b29f489-6347-4259-92f0-1dc3488052b0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {G H K : Type*} [Group G] [Group H] [Group K] [Fintype G] [Fintype H] [Fintype K]
namespace GroundTheory.LocalField
theorem _root_.solution (φ : H →* G) (hφ : Function.Injective φ) (ψ : H → ℂ) :
    indFun φ ψ 1 = (Nat.card G : ℂ) / Nat.card H * ψ 1 := by
  classical
  rw [indFun_apply]
  have h1 : ∀ t : G, ∑ h : H, (if φ h = t⁻¹ * 1 * t then ψ h else 0) = ψ 1 := by
    intro t
    have hiff : ∀ h : H, φ h = t⁻¹ * 1 * t ↔ h = 1 := fun h ↦ by
      rw [show t⁻¹ * 1 * t = 1 by group, ← map_one φ]
      exact hφ.eq_iff
    simp_rw [hiff]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  ring
end GroundTheory.LocalField
