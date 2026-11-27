-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.isometric_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:34.694917+00:00
-- url     : https://prove2.me/submissions/83cc4224-c017-48d0-abd8-ec9ed35e34b3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_toSesq_self_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_eq_of_isometric_prod_ofUnit
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_disc_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_finrank_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_refl
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_of_finrank_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_apply_self_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_isometric_prod_ofUnit
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_self_mem_range
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_left
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_mul_conj
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
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
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
open GroundTheory.Automorphic.HermitianForm
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [FiniteDimensional E V] [FiniteDimensional E V'] (h : HermitianForm F E V)
    (h' : HermitianForm F E V') :
    Isometric h h' ↔ finrank E V = finrank E V' ∧ h.disc = h'.disc := by
  refine ⟨fun H => ⟨H.finrank_eq, H.disc_eq⟩, fun ⟨hdim, hdisc⟩ => ?_⟩
  suffices key : ∀ n : ℕ, ∀ (U : Type _) (U' : Type _) [AddCommGroup U] [Module E U]
      [FiniteDimensional E U] [AddCommGroup U'] [Module E U'] [FiniteDimensional E U'],
      finrank E U = n → finrank E U' = n → ∀ (k : HermitianForm F E U)
      (k' : HermitianForm F E U'), k.disc = k'.disc → Isometric k k' from
    key _ V V' rfl hdim.symm h h' hdisc
  intro n
  induction n with
  | zero =>
    intro U U' _ _ _ _ _ _ hU hU' k k' _
    have : Subsingleton U := Module.finrank_zero_iff.1 hU
    refine ⟨LinearEquiv.ofFinrankEq U U' (hU.trans hU'.symm), fun x y => ?_⟩
    rw [Subsingleton.elim x 0, Subsingleton.elim y 0]
    simp only [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
  | succ n ih =>
    intro U U' _ _ _ _ _ _ hU hU' k k' hkk

    obtain ⟨c, ⟨v, hv⟩, ⟨v', hv'⟩⟩ : ∃ c : Fˣ, (∃ v, k.toSesq v v = algebraMap F E c) ∧
        (∃ v', k'.toSesq v' v' = algebraMap F E c) := by
      rcases Nat.lt_or_ge n 1 with hn | hn
      · have hn0 : n = 0 := by omega
        subst hn0
        have : Nontrivial U := Module.nontrivial_of_finrank_eq_succ hU
        have : Nontrivial U' := Module.nontrivial_of_finrank_eq_succ hU'
        obtain ⟨v, hv⟩ := k.exists_apply_self_ne_zero
        obtain ⟨a, ha⟩ := k.toSesq_self_mem_range v
        have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero] at ha; exact hv ha.symm
        obtain ⟨v', hv'⟩ := k'.exists_apply_self_ne_zero
        obtain ⟨a', ha'⟩ := k'.toSesq_self_mem_range v'
        have ha0' : a' ≠ 0 := by rintro rfl; rw [map_zero] at ha'; exact hv' ha'.symm
        obtain ⟨W, k₀, Hk, hW⟩ := k.exists_isometric_prod_ofUnit (a := Units.mk0 a ha0) ha.symm
        obtain ⟨W', k₀', Hk', hW'⟩ :=
          k'.exists_isometric_prod_ofUnit (a := Units.mk0 a' ha0') ha'.symm
        have d1 : k.disc = QuotientGroup.mk (Units.mk0 a ha0) := by
          rw [k.disc_eq_of_isometric_prod_ofUnit Hk,
            k₀.disc_of_finrank_eq_zero (by have := hW inferInstance; omega)]
          exact mul_one (M := Fˣ ⧸ (normUnits F E).range) _
        have d2 : k'.disc = QuotientGroup.mk (Units.mk0 a' ha0') := by
          rw [k'.disc_eq_of_isometric_prod_ofUnit Hk',
            k₀'.disc_of_finrank_eq_zero (by have := hW' inferInstance; omega)]
          exact mul_one (M := Fˣ ⧸ (normUnits F E).range) _
        rw [d1, d2] at hkk
        obtain ⟨u, hu⟩ := QuotientGroup.eq.1 hkk.symm
        refine ⟨Units.mk0 a ha0, ⟨v, ha.symm⟩, ⟨(u : E) • v', ?_⟩⟩
        rw [k'.toSesq_smul_left, k'.toSesq_smul_right, ← ha', ← mul_assoc,
          mul_comm (conj F E (u : E)), mul_conj, ← map_mul, ← coe_normUnits, hu]
        congr 1
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        field_simp
      · refine ⟨1, k.exists_toSesq_self_eq (by omega) 1, k'.exists_toSesq_self_eq (by omega) 1⟩
    obtain ⟨W, k₀, Hk, hW⟩ := k.exists_isometric_prod_ofUnit hv
    obtain ⟨W', k₀', Hk', hW'⟩ := k'.exists_isometric_prod_ofUnit hv'
    have hWn : finrank E W = n := by have := hW inferInstance; omega
    have hWn' : finrank E W' = n := by have := hW' inferInstance; omega
    have hd : k₀.disc = k₀'.disc := by
      have d1 := k.disc_eq_of_isometric_prod_ofUnit Hk
      have d2 := k'.disc_eq_of_isometric_prod_ofUnit Hk'
      rw [d1, d2] at hkk
      have := congrArg ((QuotientGroup.mk c : Fˣ ⧸ (normUnits F E).range)⁻¹ * ·) hkk
      simpa only [inv_mul_cancel_left] using this
    exact (Hk.symm.trans ((Isometric.refl _).prod (ih W W' hWn hWn' k₀ k₀' hd))).trans Hk'
end GroundTheory.Automorphic.HermitianForm
