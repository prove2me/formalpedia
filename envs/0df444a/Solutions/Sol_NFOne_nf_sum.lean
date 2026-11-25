-- Prove2me | solution 1 for NFOne.nf_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:45.040774+00:00
-- url     : https://prove2.me/submissions/99d72043-61e7-4351-9ada-34c78877fe6c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Theorems.Thm_NFOne_y_esI_zero
import Theorems.Thm_NFOne_P_WS
import Theorems.Thm_NFOne_P_XS
import Theorems.Thm_NFOne_P_rowS
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
open Matrix Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
noncomputable section
open NFOne
namespace NFOne
theorem _root_.solution (k r j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (N : Matrix (Fin j) (Fin j) ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hMN : (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) * N = 1)
    (a : Fin j) (p : Fin (2 * r + k + 1)) :
    (Pm k r j (Vv y N) *ᵥ (fun q => if r + k < q.val then y a q else 0)) p =
      if r + k < p.val then 0 else y a p := by
  have hp2 := p.isLt
  have hsRv : ∀ l : Fin j, (sR k r j hj l).val = 2 * r + k - l.val := fun l => rfl
  rw [show (Pm k r j (Vv y N) *ᵥ (fun q => if r + k < q.val then y a q else 0)) p =
    ∑ q, Pm k r j (Vv y N) p q * (if r + k < q.val then y a q else 0) from rfl]
  split_ifs with hp
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [P_rowS k r j _ p q hp, zero_mul]
  · have key : ∀ q : Fin (2 * r + k + 1),
        Pm k r j (Vv y N) p q * (if r + k < q.val then y a q else 0) =
          if r + k < q.val ∧ (sg k r q).val < j then Vv y N (sg k r q).val p * y a q else 0 := by
      intro q
      by_cases hq : r + k < q.val
      · rw [if_pos hq]
        by_cases hs : (sg k r q).val < j
        · rw [if_pos ⟨hq, hs⟩]
          congr 1
          by_cases hpr : p.val < r
          · rw [P_XS k r j _ p q hpr hq, if_pos hs]
          · exact P_WS k r j _ p q (by omega) (by omega) hq
        · rw [if_neg (fun h => hs h.2), y_esI_zero k r j y hy2 a q hq hs, mul_zero]
      · rw [if_neg hq, mul_zero, if_neg (fun h => hq h.1)]
    simp only [key]
    have hinj : Function.Injective (sR k r j hj) := by
      intro l1 l2 h
      have h' := congrArg Fin.val h
      rw [hsRv, hsRv] at h'
      have := l1.isLt
      have := l2.isLt
      exact Fin.ext (by omega)
    have hzero : ∀ q ∉ Set.range (sR k r j hj),
        (if r + k < q.val ∧ (sg k r q).val < j then Vv y N (sg k r q).val p * y a q else 0) = 0 := by
      intro q hq
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hq
      refine ⟨⟨(sg k r q).val, h2⟩, Fin.ext ?_⟩
      rw [hsRv]
      have := q.isLt
      simp only [sg_val]
      omega
    have hval : ∀ l : Fin j, Vv y N l.val p * y a (sR k r j hj l) =
        (if r + k < (sR k r j hj l).val ∧ (sg k r (sR k r j hj l)).val < j then
          Vv y N (sg k r (sR k r j hj l)).val p * y a (sR k r j hj l) else 0) := by
      intro l
      have hl := l.isLt
      have e : (sg k r (sR k r j hj l)).val = l.val := by rw [sg_val, hsRv]; omega
      rw [if_pos ⟨by rw [hsRv]; omega, by omega⟩, e]
    rw [← Fintype.sum_of_injective (sR k r j hj) hinj _ _ hzero hval]
    have hV : ∀ l : Fin j, Vv y N l.val p = ∑ a', N l a' * y a' p := by
      intro l
      unfold Vv
      rw [dif_pos l.isLt]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.eta]
    simp only [hV]
    have h1 : y a p = ∑ a', (∑ l, y a (sR k r j hj l) * N l a') * y a' p := by
      have := fun a' => congrFun (congrFun hMN a) a'
      simp only [Matrix.mul_apply, Matrix.of_apply] at this
      simp only [this, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [h1]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun l _ => by ring
end NFOne
