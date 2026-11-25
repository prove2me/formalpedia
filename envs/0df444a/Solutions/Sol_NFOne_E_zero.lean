-- Prove2me | solution 1 for NFOne.E_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:14:33.233584+00:00
-- url     : https://prove2.me/submissions/ececb061-9b05-4ee5-ab56-8c92c46c4730

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Theorems.Thm_NFOne_K_iso
import Theorems.Thm_NFOne_HP_apply
import Theorems.Thm_NFOne_PHP_apply
import Theorems.Thm_NFOne_PH_apply
import Theorems.Thm_NFOne_P_WS
import Theorems.Thm_NFOne_P_XS
import Theorems.Thm_NFOne_P_XW
import Theorems.Thm_NFOne_P_colX
import Theorems.Thm_NFOne_P_rowS
import Theorems.Thm_NFOne_P_rowWS_colW
import Theorems.Thm_NFOne_sg_val
import Theorems.Thm_NFOne_star_dW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] NFOne.sg_val



set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants
noncomputable section
open NFOne
namespace NFOne
theorem _root_.solution (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0)
    (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * Hpk k r) p q + (Hpk k r * Pm k r j V) p q +
      ((Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) p q = 0 := by
  have hp2 := p.isLt
  have hq2 := q.isLt
  rw [PH_apply, HP_apply, PHP_apply]
  have hC : ¬ (r + k < p.val ∧ r + k < q.val) →
      ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
        dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) = 0 := by
    intro hpq
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with hi
    · by_cases hp : r + k < p.val
      · rw [P_rowWS_colW k r j V i q hi.1 (by omega), mul_zero]
      · rw [P_rowWS_colW k r j V i p hi.1 (by omega), star_zero, mul_zero, zero_mul]
    · rfl
  by_cases hpX : p.val < r
  · have hpW : ¬ (r ≤ p.val ∧ p.val ≤ r + k) := by omega
    have hA : ∀ x : Fin (2 * r + k + 1), Pm k r j V x p = 0 := fun x => P_colX k r j V x p hpX
    have hB : Pm k r j V (sg k r p) q = 0 := P_rowS k r j V (sg k r p) q (by rw [sg_val]; omega)
    rw [if_neg hpW, hB, hC (by omega), hA, hA]
    simp
  · by_cases hpW : r ≤ p.val ∧ p.val ≤ r + k
    · rw [if_pos hpW, hC (by omega), add_zero]
      by_cases hqX : q.val < r
      · have hqW : ¬ (r ≤ q.val ∧ q.val ≤ r + k) := by omega
        rw [if_neg hqW, P_rowS k r j V (sg k r q) p (by rw [sg_val]; omega), P_colX k r j V p q hqX]
        simp
      · by_cases hqW : r ≤ q.val ∧ q.val ≤ r + k
        · rw [if_pos hqW, P_rowWS_colW k r j V q p hqW.1 hpW.2, P_rowWS_colW k r j V p q hpW.1 hqW.2]
          simp
        · have hqS : r + k < q.val := by omega
          rw [if_neg hqW, P_XW k r j V (sg k r q) p (by rw [sg_val]; omega) hpW.1 hpW.2,
            P_WS k r j V p q hpW.1 hpW.2 hqS, star_neg, star_mul', star_star, star_dW]
          ring
    · have hpS : r + k < p.val := by omega
      rw [if_neg hpW]
      by_cases hqX : q.val < r
      · have hqW : ¬ (r ≤ q.val ∧ q.val ≤ r + k) := by omega
        rw [if_neg hqW, P_rowS k r j V (sg k r q) p (by rw [sg_val]; omega),
          P_colX k r j V (sg k r p) q hqX, hC (by omega)]
        simp
      · by_cases hqW : r ≤ q.val ∧ q.val ≤ r + k
        · rw [if_pos hqW, P_WS k r j V q p hqW.1 hqW.2 hpS,
            P_XW k r j V (sg k r p) q (by rw [sg_val]; omega) hqW.1 hqW.2, hC (by omega)]
          ring
        · have hqS : r + k < q.val := by omega
          rw [if_neg hqW]
          have hC' : ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
              dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) =
              ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
                dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs with hi
            · rw [P_WS k r j V i p hi.1 hi.2 hpS, P_WS k r j V i q hi.1 hi.2 hqS]
            · rfl
          rw [hC', P_XS k r j V (sg k r q) p (by rw [sg_val]; omega) hpS,
            P_XS k r j V (sg k r p) q (by rw [sg_val]; omega) hqS]
          by_cases hbp : (sg k r p).val < j
          · by_cases hbq : (sg k r q).val < j
            · rw [if_pos hbp, if_pos hbq]
              have hK := K_iso k r j V Vs p q hpS hqS hbq hbp
              rw [Viso _ _ hbq hbp] at hK
              exact hK.symm
            · have h0 := V0 _ (Nat.le_of_not_lt hbq)
              rw [if_pos hbp, if_neg hbq, h0]
              simp
          · have h0 := V0 _ (Nat.le_of_not_lt hbp)
            rw [if_neg hbp, h0]
            by_cases hbq : (sg k r q).val < j
            · rw [if_pos hbq]
              simp
            · have h0' := V0 _ (Nat.le_of_not_lt hbq)
              rw [if_neg hbq, h0']
              simp
end NFOne
