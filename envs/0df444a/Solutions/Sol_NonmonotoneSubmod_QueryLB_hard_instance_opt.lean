-- Prove2me | solution 1 for NonmonotoneSubmod.QueryLB.hard_instance_opt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:38:20.732896+00:00
-- url     : https://prove2.me/submissions/e04a906e-abc3-4708-bd7c-2dc52ca7d5ee

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance

namespace NonmonotoneSubmod.QueryLB

lemma aux_hio_fkl_le (n m h k l : ℕ) (hnh : (n : ℝ) = 2 * h) (hm : 1 ≤ m) (hmh : m ≤ h)
    (hk : k ≤ h) (hl : l ≤ h) :
    fkl n m k l ≤ (n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2 := by
  have hk' : (k : ℝ) ≤ h := by exact_mod_cast hk
  have hl' : (l : ℝ) ≤ h := by exact_mod_cast hl
  have hmh' : (m : ℝ) ≤ h := by exact_mod_cast hmh
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hl0 : (0 : ℝ) ≤ l := by positivity
  unfold fkl
  rw [hnh]
  split_ifs with H
  · nlinarith [sq_nonneg ((k : ℝ) + l - h), sq_nonneg ((h : ℝ) - m)]
  · push Not at H
    rcases le_total (l : ℝ) k with hkl | hkl
    · rw [abs_of_nonneg (by linarith)] at H ⊢
      nlinarith [sq_nonneg ((k : ℝ) + l - h), sq_nonneg ((h : ℝ) - m),
        mul_nonneg (by linarith : (0 : ℝ) ≤ h - (k - l)) (by linarith : (0 : ℝ) ≤ h + (k - l) - 2 * m)]
    · rw [abs_of_nonpos (by linarith)] at H ⊢
      nlinarith [sq_nonneg ((k : ℝ) + l - h), sq_nonneg ((h : ℝ) - m),
        mul_nonneg (by linarith : (0 : ℝ) ≤ h - (l - k)) (by linarith : (0 : ℝ) ≤ h + (l - k) - 2 * m)]

end NonmonotoneSubmod.QueryLB

open NonmonotoneSubmod.QueryLB

theorem solution (n m : ℕ) (hn : Even n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (C : Finset (Fin n)) (hC : C.card = n / 2) :
    NonmonotoneSubmod.Shared.OPT (fC n m C) = (n : ℝ) ^ 2 / 2 - (m : ℝ) * n + (m : ℝ) ^ 2 ∧
      fC n m C C = NonmonotoneSubmod.Shared.OPT (fC n m C) := by
  obtain ⟨h, rfl⟩ := hn
  have hh : (h + h) / 2 = h := by omega
  rw [hh] at hC
  have hnh : ((h + h : ℕ) : ℝ) = 2 * h := by push_cast; ring
  have hmh : m ≤ h := by omega
  have hCc : Cᶜ.card = h := by
    rw [Finset.card_compl, Fintype.card_fin, hC]; omega
  have hub : ∀ S : Finset (Fin (h + h)), fC (h + h) m C S ≤
      ((h + h : ℕ) : ℝ) ^ 2 / 2 - (m : ℝ) * ((h + h : ℕ) : ℝ) + (m : ℝ) ^ 2 := by
    intro S
    unfold fC
    apply aux_hio_fkl_le (h + h) m h _ _ hnh hm hmh
    · exact (Finset.card_le_card Finset.inter_subset_right).trans hC.le
    · exact (Finset.card_le_card Finset.inter_subset_right).trans hCc.le
  have hval : fC (h + h) m C C =
      ((h + h : ℕ) : ℝ) ^ 2 / 2 - (m : ℝ) * ((h + h : ℕ) : ℝ) + (m : ℝ) ^ 2 := by
    unfold fC fkl
    rw [Finset.inter_self, Finset.inter_compl, Finset.card_empty, hC, hnh]
    have hm' : (m : ℝ) ≤ h := by exact_mod_cast hmh
    have habs : |(h : ℝ) - ((0 : ℕ) : ℝ)| = h := by
      rw [Nat.cast_zero, sub_zero, abs_of_nonneg (by positivity)]
    split_ifs with H
    · rw [habs] at H
      have : (m : ℝ) = h := le_antisymm hm' H
      rw [this]; push_cast; ring
    · rw [habs]; push_cast; ring
  have hopt : NonmonotoneSubmod.Shared.OPT (fC (h + h) m C) =
      ((h + h : ℕ) : ℝ) ^ 2 / 2 - (m : ℝ) * ((h + h : ℕ) : ℝ) + (m : ℝ) ^ 2 := by
    unfold NonmonotoneSubmod.Shared.OPT
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun S _ => hub S)
    · rw [← hval]; exact Finset.le_sup' _ (Finset.mem_univ C)
  exact ⟨hopt, by rw [hopt, hval]⟩
