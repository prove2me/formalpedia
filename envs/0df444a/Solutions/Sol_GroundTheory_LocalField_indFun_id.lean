-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:40.758567+00:00
-- url     : https://prove2.me/submissions/c4da1d11-c30e-4f77-8f95-8334a8bd88de

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford

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
variable {G H H' : Type*} [Group G] [Group H] [Group H'] [Fintype G] [Fintype H] [Fintype H']
namespace GroundTheory.LocalField
theorem _root_.solution {ψ : G → ℂ} (hψ : IsClassFun ψ) : indFun (MonoidHom.id G) ψ = ψ := by
  classical
  funext s
  rw [indFun_apply]
  simp only [MonoidHom.id_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h : ∀ t : G, ψ (t⁻¹ * s * t) = ψ s := fun t ↦ by simpa using hψ s t⁻¹
  simp_rw [h]
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, ← mul_assoc,
    inv_mul_cancel₀ hG, one_mul]
end GroundTheory.LocalField
