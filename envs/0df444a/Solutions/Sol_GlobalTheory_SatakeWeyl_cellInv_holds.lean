-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.cellInv_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:31:35.062713+00:00
-- url     : https://prove2.me/submissions/8838a49a-798c-498d-b042-aeea21c3fd5a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CellSumLeftRightInvarianceNormaliser
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution : CellInv := by
  classical
  intro G _ K N h g k₁ k₂ hh hk₁ hk₂ hN hN'
  unfold cellSum
  rw [← finsum_comp_equiv (MulAction.toPerm k₁ : Equiv.Perm (G ⧸ K))]
  refine finsum_congr fun x => ?_
  obtain ⟨k, hk⟩ : ∃ k : K, (k₁ • x).out = k₁ * x.out * k := by
    rw [← MulAction.Quotient.mk_smul_out]
    exact QuotientGroup.mk_out_eq_mul K _
  rw [MulAction.toPerm_apply, hk]
  have e : h (k₁ * x.out * k) = h x.out := hh ⟨k₁, hk₁⟩ k _
  rw [e]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨u, hu, k', hk', e'⟩
    refine ⟨k₂ * u * k₂⁻¹, hN u hu, k₂ * k' * (k : G)⁻¹, K.mul_mem (K.mul_mem hk₂ hk') (K.inv_mem k.2), ?_⟩
    have : x.out = k₁⁻¹ * (k₁ * x.out * k) * (k : G)⁻¹ := by group
    rw [this, e']; group
  · rintro ⟨u, hu, k', hk', e'⟩
    refine ⟨k₂⁻¹ * u * k₂, hN' u hu, k₂⁻¹ * k' * k, K.mul_mem (K.mul_mem (K.inv_mem hk₂) hk') k.2, ?_⟩
    rw [e']; group
end GlobalTheory.SatakeWeyl
