-- Prove2me | solution 1 for NFOne.K_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:25.853547+00:00
-- url     : https://prove2.me/submissions/93c4c5c1-4ee7-41e4-bea1-b4da6a47eb7b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Theorems.Thm_NFOne_Hpk_mulVec
import Theorems.Thm_NFOne_herm_eq
import Theorems.Thm_NFOne_sg_sg
import Theorems.Thm_NFOne_sg_val
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
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (p q : Fin (2 * r + k + 1)) (hp : r + k < p.val) (hq : r + k < q.val)
    (hb : (sg k r q).val < j) (hc : (sg k r p).val < j) :
    herm (Hpk k r) (V (sg k r q).val) (V (sg k r p).val) =
      star (V (sg k r p).val (sg k r q)) + V (sg k r q).val (sg k r p) +
      ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
        dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
  have hp' := p.isLt; have hq' := q.isLt
  rw [herm_eq]
  have pt : ∀ i : Fin (2 * r + k + 1),
      star (V (sg k r p).val i) * (Hpk k r *ᵥ V (sg k r q).val) i =
        (if i = sg k r q then star (V (sg k r p).val (sg k r q)) else 0) +
        (if i = p then V (sg k r q).val (sg k r p) else 0) +
        (if r ≤ i.val ∧ i.val ≤ r + k then
          dW k r i * star (V (sg k r p).val i) * V (sg k r q).val i else 0) := by
    intro i
    have hi := i.isLt
    rw [Hpk_mulVec]
    by_cases h1 : i.val < r
    · rw [if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
        if_neg (show ¬ (i = p) from fun h => by rw [h] at h1; omega),
        if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega), add_zero, add_zero]
      rw [Vs _ hb (sg k r i) (by simp only [sg_val]; omega)]
      by_cases h2 : i = sg k r q
      · rw [if_pos (show (sg k r (sg k r i)).val = (sg k r q).val by rw [h2, sg_sg]), if_pos h2,
          mul_one, h2]
      · rw [if_neg (show ¬ ((sg k r (sg k r i)).val = (sg k r q).val) by
            intro h; apply h2; ext; simp only [sg_val] at h ⊢; omega), if_neg h2, mul_zero]
    · by_cases h3 : i.val ≤ r + k
      · rw [if_pos (show r ≤ i.val ∧ i.val ≤ r + k from ⟨by omega, h3⟩),
          if_neg (show ¬ (i = sg k r q) from fun h => by rw [h] at h1; simp only [sg_val] at h1; omega),
          if_neg (show ¬ (i = p) from fun h => by rw [h] at h3; omega),
          if_pos (show r ≤ i.val ∧ i.val ≤ r + k from ⟨by omega, h3⟩)]
        ring
      · rw [if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
          if_neg (show ¬ (r ≤ i.val ∧ i.val ≤ r + k) by omega),
          if_neg (show ¬ (i = sg k r q) from fun h => by rw [h] at h3; simp only [sg_val] at h3; omega),
          zero_add, add_zero]
        rw [Vs _ hc i (by omega)]
        by_cases h2 : i = p
        · rw [if_pos (show (sg k r i).val = (sg k r p).val by rw [h2]), if_pos h2, h2]; simp
        · rw [if_neg (show ¬ ((sg k r i).val = (sg k r p).val) by
            intro h; apply h2; ext; simp only [sg_val] at h; omega), if_neg h2]; simp
  rw [Finset.sum_congr rfl (fun i _ => pt i), Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
end NFOne
