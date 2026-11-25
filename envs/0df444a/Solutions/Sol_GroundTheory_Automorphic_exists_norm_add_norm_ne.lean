-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_norm_add_norm_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:33.109944+00:00
-- url     : https://prove2.me/submissions/309fa7a5-7d3e-4de1-93d1-4bc2c80cb813

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Theorems.Thm_GroundTheory_Automorphic_mem_or_mul_inv_mem_of_natCard_eq_two
import Theorems.Thm_GroundTheory_Automorphic_norm_algebraMap_quadratic
import Theorems.Thm_GroundTheory_Automorphic_norm_inv_quadratic
import Theorems.Thm_GroundTheory_Automorphic_mem_range_normUnits_iff
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
namespace GroundTheory.Automorphic
theorem _root_.solution (hN : Nat.card (Fˣ ⧸ (normUnits F E).range) = 2)
    (hsq : ∃ m : ℕ, 0 < m ∧ ∃ s : F, s ^ 2 = -(m : F)) :
    ∃ x y : E, ∀ z : E, Algebra.norm F x + Algebra.norm F y ≠ Algebra.norm F z := by
  by_contra H
  push Not at H

  have hmul : ∀ a b : F, (∃ z : E, Algebra.norm F z = a) → (∃ z : E, Algebra.norm F z = b) →
      ∃ z : E, Algebra.norm F z = a * b := by
    rintro a b ⟨z, rfl⟩ ⟨w, rfl⟩
    exact ⟨z * w, map_mul _ _ _⟩
  have hinv : ∀ a : F, (∃ z : E, Algebra.norm F z = a) → ∃ z : E, Algebra.norm F z = a⁻¹ := by
    rintro a ⟨z, rfl⟩
    exact ⟨z⁻¹, norm_inv_quadratic z⟩
  have hadd : ∀ a b : F, (∃ z : E, Algebra.norm F z = a) → (∃ z : E, Algebra.norm F z = b) →
      ∃ z : E, Algebra.norm F z = a + b := by
    rintro a b ⟨z, rfl⟩ ⟨w, rfl⟩
    obtain ⟨u, hu⟩ := H z w
    exact ⟨u, hu.symm⟩
  by_cases hm1 : ∃ w : E, Algebra.norm F w = -1
  ·
    obtain ⟨y, hy1, -⟩ := (Nat.card_eq_two_iff' (1 : Fˣ ⧸ (normUnits F E).range)).1 hN
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
    have ht : t ∉ (normUnits F E).range := by rwa [Ne, QuotientGroup.eq_one_iff] at hy1
    have htR : ¬ ∃ z : E, Algebra.norm F z = t := fun H' => ht ((mem_range_normUnits_iff t).2 H')
    have h1t : (1 : F) + t ≠ 0 := by
      intro h0
      apply htR
      obtain ⟨w, hw⟩ := hm1
      exact ⟨w, by rw [hw]; linear_combination -h0⟩
    rcases mem_or_mul_inv_mem_of_natCard_eq_two hN ht (Units.mk0 _ h1t) with h | h
    · obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 h
      apply htR
      obtain ⟨z', hz'⟩ := hadd _ _ ⟨z, hz⟩ hm1
      exact ⟨z', by rw [hz', Units.val_mk0]; ring⟩
    · obtain ⟨z, hz⟩ := (mem_range_normUnits_iff _).1 h
      rw [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val] at hz
      obtain ⟨z', hz'⟩ := hadd _ _ ⟨z, hz⟩ hm1
      obtain ⟨z'', hz''⟩ := hinv _ ⟨z', hz'⟩
      apply htR
      refine ⟨z'', ?_⟩
      rw [hz'']
      have ht0 : (t : F) ≠ 0 := t.ne_zero
      field_simp
      ring
  ·
    have hk : ∀ k : ℕ, ∃ z : E, Algebra.norm F z = ((k + 1 : ℕ) : F) := by
      intro k
      induction k with
      | zero => exact ⟨1, by simp⟩
      | succ k ih =>
        obtain ⟨z, hz⟩ := hadd _ _ ih ⟨1, map_one _⟩
        exact ⟨z, by rw [hz]; push_cast; ring⟩
    obtain ⟨m, hm, s, hs⟩ := hsq
    apply hm1
    by_cases hm0 : (m : F) = 0
    · have hm2 : 2 ≤ m := by
        rcases Nat.lt_or_ge m 2 with h | h
        · interval_cases m; simp at hm0
        · exact h
      obtain ⟨z, hz⟩ := hk (m - 2)
      refine ⟨z, ?_⟩
      rw [hz]
      have : ((m - 2 + 1 : ℕ) : F) = (m : F) - 1 := by
        rw [show m - 2 + 1 = m - 1 by omega, Nat.cast_sub (by omega), Nat.cast_one]
      rw [this, hm0, zero_sub]
    · obtain ⟨z, hz⟩ := hk (m - 1)
      rw [show m - 1 + 1 = m by omega] at hz
      obtain ⟨w, hw⟩ := hinv _ ⟨z, hz⟩
      refine ⟨algebraMap F E s * w, ?_⟩
      rw [map_mul, norm_algebraMap_quadratic, hs, hw]
      field_simp
end GroundTheory.Automorphic
