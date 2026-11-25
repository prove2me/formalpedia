-- Prove2me | solution 1 for GroundTheory.Global.exists_valuation_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:15.332555+00:00
-- url     : https://prove2.me/submissions/4eb4d188-0e83-4f40-abc6-a9d0d807a2b9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
import Theorems.Thm_GroundTheory_Global_mem_inv_pow_iff
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {M : Type*} [Field M] [NumberField M]
namespace GroundTheory.Global
theorem _root_.solution (w : HeightOneSpectrum (𝓞 M)) (n : ℕ) :
    ∃ x : M, w.valuation M x = WithZero.exp (n : ℤ) ∧
      ∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M x ≤ 1 := by
  cases n with
  | zero => exact ⟨1, by simp, fun u _ ↦ by simp⟩
  | succ k =>
    by_contra H
    push Not at H
    have hle : ((w.asIdeal ^ (k + 1) : Ideal (𝓞 M)) :
        FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ≤
        ((w.asIdeal ^ k : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ := by
      intro x hx
      obtain ⟨hxw, hxu⟩ := (mem_inv_pow_iff w (k + 1) x).1 hx
      refine (mem_inv_pow_iff w k x).2 ⟨?_, hxu⟩
      have hne : w.valuation M x ≠ WithZero.exp ((k + 1 : ℕ) : ℤ) := by
        intro heq
        obtain ⟨u, hu, hlt⟩ := H x heq
        exact absurd (hxu u hu) (not_le.2 hlt)
      have hlt : w.valuation M x < WithZero.exp (k : ℤ) * WithZero.exp 1 := by
        rw [← WithZero.exp_add]
        have := lt_of_le_of_ne hxw hne
        push_cast at this
        exact this
      exact (WithZero.lt_mul_exp_iff_le (by simp)).1 hlt
    have hge : ((w.asIdeal ^ k : Ideal (𝓞 M)) :
        FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ≤
        ((w.asIdeal ^ (k + 1) : Ideal (𝓞 M)) :
          FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ := by
      intro x hx
      obtain ⟨hxw, hxu⟩ := (mem_inv_pow_iff w k x).1 hx
      refine (mem_inv_pow_iff w (k + 1) x).2 ⟨hxw.trans ?_, hxu⟩
      rw [WithZero.exp_le_exp]
      push_cast
      omega
    have heq := inv_inj.1 (le_antisymm hle hge)
    rw [FractionalIdeal.coeIdeal_inj] at heq
    exact (Ideal.pow_succ_lt_pow w.ne_bot k).ne heq
end GroundTheory.Global
