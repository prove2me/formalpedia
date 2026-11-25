-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:39.523832+00:00
-- url     : https://prove2.me/submissions/86d197e4-f04e-4afc-87d0-53f4488a8398

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_P2M_GlobalTheory_UnitaryZariskiDense_eval_bind__subst_f04b094ac84b
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eq_zero_of_eval_real
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_tr_tr
import Theorems.Thm_P2M_GlobalTheory_UnitaryZariskiDense_conj_c__480c94d4cfbd
import Theorems.Thm_P2M_GlobalTheory_UnitaryZariskiDense_conj_c__61702cfdeecf
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_c_one
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_c_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution (R : MvPolynomial (ι × Fin a × Fin a) ℂ)
    (h : ∀ x : ι × Fin a × Fin a → ℂ, (∀ v, star (x (tr v)) = - x v) → eval x R = 0) : R = 0 := by
  have hev : ∀ y : ι × Fin a × Fin a → ℂ,
      eval y (bind₁ (fun v => C cα * X v + C cβ * X (tr v)) R) =
        eval (fun v => cα * y v + cβ * y (tr v)) R := by
    intro y
    rw [eval_bind₁_subst]
    congr 2
    funext v
    simp
  have hS0 : bind₁ (fun v => C cα * X v + C cβ * X (tr v)) R = 0 := by
    apply eq_zero_of_eval_real
    intro u
    rw [hev]
    apply h
    intro v
    simp only [tr_tr, star_add, star_mul', Complex.star_def, Complex.conj_ofReal, conj_cα, conj_cβ]
    ring
  apply MvPolynomial.funext
  intro x
  have := hev (fun v => cγ * x v + cδ * x (tr v))
  rw [hS0, map_zero] at this
  rw [map_zero, this]
  congr 2
  funext v
  simp only [tr_tr]
  linear_combination (-(x v)) * c_one - x (tr v) * c_zero
end GlobalTheory.UnitaryZariskiDense
