-- Prove2me | solution 1 for GlobalTheory.RowRat.coeff_mem_of_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:38.475784+00:00
-- url     : https://prove2.me/submissions/c84e917a-c5ac-4289-b240-e2173c839b60

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ReprMemOfCoeff
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
namespace GlobalTheory.RowRat
theorem _root_.solution {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ a, (bVV ℂ lam).repr v a ∈ Set.range κ) (m : ι × Fin n × Fin n →₀ ℕ) :
    coeff m v.1 ∈ Set.range κ := by
  rw [val_eq_sum_repr, coeff_sum, ← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun a _ => ?_
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
  rw [coeff_smul, hP, coeff_map, smul_eq_mul]
  obtain ⟨x, hx⟩ := h a
  exact ⟨x * P.coeff m, by simp [hx]⟩
end GlobalTheory.RowRat
