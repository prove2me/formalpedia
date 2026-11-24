-- Prove2me | solution 1 for GlobalTheory.InertZeta.relIndex_scaledInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:07.839794+00:00
-- url     : https://prove2.me/submissions/5c40208c-68b2-45aa-8bbd-4731b54ae992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralLatticeInverseIndexOfElementaryDivisors
import Theorems.Thm_GlobalTheory_InertZeta_mem_scaledInt
import Theorems.Thm_GlobalTheory_InertZeta_mulLeft_surjective
import Theorems.Thm_GlobalTheory_InertZeta_mulLeft_injective
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_SatakeWeyl_intIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.InertZeta
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (d : ℕ) :
    (intL L).toAddSubgroup.relIndex (scaledInt (ϖ ^ d)) = q ^ (2 * d) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hϖ : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

  have h1 : (intL L).toAddSubgroup.relIndex (scaledInt ϖ) = q ^ 2 := by
    have hm : ((scaledInt ϖ).map (AddMonoidHom.mulLeft ϖ)) = (intL L).toAddSubgroup :=
      AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective h0) _
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (mulLeft_injective h0), hm]
    exact intIndex L ϖ σ q hU
  induction d with
  | zero =>
    have : scaledInt (ϖ ^ 0) = (intL L).toAddSubgroup := by
      ext x; simp [mem_scaledInt]
    rw [this, AddSubgroup.relIndex_self]; simp
  | succ d ih =>
    have hle1 : (intL L).toAddSubgroup ≤ scaledInt (ϖ ^ d) := fun x hx =>
      mul_mem (pow_mem hϖ d) hx
    have hle2 : scaledInt (ϖ ^ d) ≤ scaledInt (ϖ ^ (d + 1)) := fun x hx => by
      rw [mem_scaledInt] at hx ⊢
      rw [pow_succ, mul_comm _ ϖ, mul_assoc]
      exact mul_mem hϖ hx
    have hc : scaledInt (ϖ ^ (d + 1)) = (scaledInt ϖ).comap (AddMonoidHom.mulLeft (ϖ ^ d)) := by
      ext x
      simp only [AddSubgroup.mem_comap, mem_scaledInt]
      rw [pow_succ, mul_comm _ ϖ, mul_assoc]
      exact Iff.rfl
    have hstep : (scaledInt (ϖ ^ d)).relIndex (scaledInt (ϖ ^ (d + 1))) = q ^ 2 := by
      rw [hc, scaledInt, AddSubgroup.relIndex_comap,
        AddSubgroup.map_comap_eq_self_of_surjective (mulLeft_surjective (pow_ne_zero d h0)), h1]
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, ih, hstep]
    ring
end GlobalTheory.InertZeta
