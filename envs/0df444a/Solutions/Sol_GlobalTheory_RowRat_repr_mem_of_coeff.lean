-- Prove2me | solution 1 for GlobalTheory.RowRat.repr_mem_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:58.108396+00:00
-- url     : https://prove2.me/submissions/8ccd3187-6457-4e0d-b56f-1b828ffabc48

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ReprMemOfCoeff
import Theorems.Thm_GlobalTheory_RowRat_exists_proj
import Theorems.Thm_GlobalTheory_RowRat_val_eq_sum_repr
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_DIV_bVVfun_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism.L2.DIV MvPolynomial
open GlobalTheory GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial
namespace GlobalTheory.RowRat
theorem _root_.solution {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ m, coeff m v.1 ∈ Set.range κ) (a : VVIdx lam) :
    (bVV ℂ lam).repr v a ∈ Set.range κ := by
  set K' := κ.fieldRange
  obtain ⟨φ, hφ1, hφ2⟩ := exists_proj K'
  set c := fun a => (bVV ℂ lam).repr v a
  have hK : ∀ a m, coeff m (bVVfun ℂ lam a) ∈ K' := fun a m => by
    obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
    rw [hP, coeff_map]
    exact ⟨((coeff m P : ℤ) : L), by simp⟩
  have key : ∑ b, (c b - φ (c b)) • bVVfun ℂ lam b = 0 := by
    ext m
    have e1 : coeff m v.1 = ∑ b, c b * coeff m (bVVfun ℂ lam b) := by
      rw [val_eq_sum_repr, coeff_sum]; simp [c]
    have e2 : φ (coeff m v.1) = coeff m v.1 := hφ1 ⟨_, RingHom.mem_fieldRange.2 (h m)⟩
    have e3 : φ (coeff m v.1) = ∑ b, φ (c b) * coeff m (bVVfun ℂ lam b) := by
      rw [e1, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : c b * coeff m (bVVfun ℂ lam b) = (⟨_, hK b m⟩ : K') • c b := by
        rw [Subfield.smul_def, smul_eq_mul, mul_comm]
      rw [this, map_smul, Subfield.smul_def, smul_eq_mul, mul_comm]
    rw [coeff_sum, coeff_zero]
    simp only [coeff_smul, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e3, e2, sub_self]
  have hz := Fintype.linearIndependent_iff.1 (bVVfun_spec ℂ lam).1 _ key a
  rw [sub_eq_zero] at hz
  have hc : c a ∈ K' := by rw [hz]; exact hφ2 _
  exact RingHom.mem_fieldRange.1 hc
end GlobalTheory.RowRat
