-- Prove2me | solution 1 for LeiBR.Async.normInf_Gamma_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:40:42.814753+00:00
-- url     : https://prove2.me/submissions/4209f9d6-9291-4af7-9143-9620219ac785

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model

open LeiBR.Async in
theorem solution {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ) (μ : ℝ) (hμ : 0 < μ) (hA5 : Assumption5 X f) :
    normInf (LeiBR.Sync.Gamma X f μ) < 1 := by
  have hzmax : ∀ i j, 0 ≤ LeiBR.Sync.zetaMax X f i j := by
    intro i j
    apply Real.sSup_nonneg
    rintro x ⟨_, _, _, _, _, _, rfl⟩
    exact abs_nonneg _
  have key : ∀ i, (∑ j, ‖LeiBR.Sync.Gamma X f μ i j‖₊) < 1 := by
    intro i
    have hsum_nn : 0 ≤ ∑ j ∈ Finset.univ.erase i, LeiBR.Sync.zetaMax X f i j :=
      Finset.sum_nonneg (fun j _ => hzmax i j)
    have h5 := hA5 i
    have hD : 0 < μ + LeiBR.Sync.zetaMin X f i := by linarith
    rw [← NNReal.coe_lt_coe, NNReal.coe_sum, NNReal.coe_one]
    simp only [coe_nnnorm, Real.norm_eq_abs]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hdiag : |LeiBR.Sync.Gamma X f μ i i| = μ / (μ + LeiBR.Sync.zetaMin X f i) := by
      unfold LeiBR.Sync.Gamma
      rw [if_pos rfl, abs_of_nonneg (div_nonneg hμ.le hD.le)]
    have hoff : ∀ j ∈ Finset.univ.erase i, |LeiBR.Sync.Gamma X f μ i j| =
        LeiBR.Sync.zetaMax X f i j / (μ + LeiBR.Sync.zetaMin X f i) := by
      intro j hj
      have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      unfold LeiBR.Sync.Gamma
      rw [if_neg hne, abs_of_nonneg (div_nonneg (hzmax i j) hD.le)]
    rw [hdiag, Finset.sum_congr rfl hoff, ← Finset.sum_div, ← add_div, div_lt_one hD]
    linarith
  unfold normInf
  rw [← NNReal.coe_one, NNReal.coe_lt_coe]
  exact (Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr one_ne_zero)).mpr (fun i _ => key i)
