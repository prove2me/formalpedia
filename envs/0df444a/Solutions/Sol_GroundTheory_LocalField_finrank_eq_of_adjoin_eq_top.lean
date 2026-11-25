-- Prove2me | solution 1 for GroundTheory.LocalField.finrank_eq_of_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:05:29.028397+00:00
-- url     : https://prove2.me/submissions/8fc31119-bb2d-405a-8e74-278291988055

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_eq_one_of_adjoin_eq_top
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_orderOf_frobenius
import Theorems.Thm_GroundTheory_LocalField_frobenius_apply_of_pow_eq_one
import Theorems.Thm_GroundTheory_LocalField_natCast_card_pow_sub_one_ne_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (htop : K⟮ζ⟯ = ⊤) :
    Module.finrank K L = n := by
  set q := Nat.card 𝓀[K] with hq_def
  have hq : 1 < q := one_lt_card_residueField K
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have h := ramificationIndex_eq_one_of_adjoin_eq_top hζ hm htop
  set F := frobenius K L h
  have hF : F ζ = ζ ^ q := frobenius_apply_of_pow_eq_one h hm hζ.pow_eq_one
  have hFk : ∀ k : ℕ, (F ^ k) ζ = ζ ^ (q ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hF, ← pow_mul, ← pow_succ']
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by
    have : 1 < q ^ n := Nat.one_lt_pow hn hq
    omega)
  have hpow : ∀ k : ℕ, ζ ^ (q ^ k) = ζ ↔ ζ ^ (q ^ k - 1) = 1 := by
    intro k
    have h1 : q ^ k = q ^ k - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    conv_lhs => rw [h1, pow_succ]
    constructor
    · intro h2
      exact mul_left_cancel₀ hζ0 (by rw [mul_one, mul_comm]; exact h2)
    · intro h2
      rw [h2, one_mul]
  have hd := orderOf_frobenius K L h
  have hfin := Module.finrank_pos (R := K) (M := L)
  apply le_antisymm
  ·
    have hFn : F ^ n = 1 := by
      apply algEquiv_eq_one_of_apply_eq htop
      rw [hFk, hpow]
      exact hζ.pow_eq_one
    rw [← hd]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (orderOf_dvd_of_pow_eq_one hFn)
  ·
    have h1 : ζ ^ (q ^ Module.finrank K L - 1) = 1 := by
      rw [← hpow, ← hFk, ← hd, pow_orderOf_eq_one, AlgEquiv.one_apply]
    have hdvd := hζ.dvd_of_pow_eq_one _ h1
    have hlt : 1 < q ^ Module.finrank K L := Nat.one_lt_pow hfin.ne' hq
    have hle := Nat.le_of_dvd (by omega) hdvd
    have : q ^ n ≤ q ^ Module.finrank K L := by
      have := Nat.one_le_pow n q (by omega)
      omega
    exact (Nat.pow_le_pow_iff_right hq).mp this
end GroundTheory.LocalField
