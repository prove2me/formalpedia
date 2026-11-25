-- Prove2me | solution 1 for GlobalTheory.WigSh.inv_sq_le_wP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:38.270288+00:00
-- url     : https://prove2.me/submissions/373d1ce5-ed06-4a7f-8ee1-4727f33ccbc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqRaising
import Theorems.Thm_GlobalTheory_WigSh_prod_other_neighbour_raise
import Theorems.Thm_GlobalTheory_WigSh_Model_placeWeight_nonneg
import Theorems.Thm_GlobalTheory_WigSh_Model_prod_erase_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh
namespace GlobalTheory.WigSh
theorem _root_.solution (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hL : StrictAnti L) (hM : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l + 1) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hn : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ wP L M l := by
  set e : Fin (n + 1) → ℤ := fun i => max |L i - L l| 1 with he
  set d : Fin (n + 1) → ℝ := fun i => (e i : ℝ) with hd
  have hdpos : ∀ i, 0 < d i := fun i => by
    have : 0 < e i := lt_of_lt_of_le one_pos (le_max_right _ _)
    simp only [hd]; exact_mod_cast this
  have hdl : d l = 1 := by simp [hd, he]
  have key := prod_other_neighbour_raise d l hdpos hdl
  have hd0 : d 0 ≤ D := by
    have a : L l ≤ L 0 := hL.antitone (Fin.zero_le _)
    have a' : (L l : ℝ) ≤ L 0 := by exact_mod_cast a
    simp only [hd, he]
    push_cast
    exact max_le (by rw [abs_of_nonneg (by linarith)]; exact h0) hD
  have hdn : d (Fin.last n) ≤ D := by
    have a : L (Fin.last n) ≤ L l := hL.antitone (Fin.le_last _)
    have a' : (L (Fin.last n) : ℝ) ≤ L l := by exact_mod_cast a
    simp only [hd, he]
    push_cast
    exact max_le (by rw [abs_of_nonpos (by linarith)]; linarith) hD
  have hden : ∏ j : Fin n, |(L (l.succAbove j) : ℝ) - L l| = ∏ j : Fin n, d (l.succAbove j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    have a : L (l.succAbove j) ≠ L l := fun h => Fin.succAbove_ne l j (hL.injective h)
    have b : 1 ≤ |L (l.succAbove j) - L l| := Int.one_le_abs (sub_ne_zero.2 a)
    simp only [hd, he, max_eq_left b]
    push_cast
    rfl
  have hnum : (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      ≤ ∏ j : Fin n, |(M j : ℝ) - 1 - L l| := by
    refine Finset.prod_le_prod (fun j _ => (hdpos _).le) fun j _ => ?_
    obtain ⟨h1, h2⟩ := hM j
    have h3 := hne j
    have : e (if j.castSucc < l then j.succ else j.castSucc) ≤ |M j - 1 - L l| := by
      split_ifs with hl
      · have a2 : L l ≤ L j.succ := hL.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)
        simp only [he]
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
        omega
      · have a2 : L j.castSucc ≤ L l := hL.antitone (not_lt.1 hl)
        simp only [he]
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
        omega
    simp only [hd]
    exact_mod_cast this
  rw [← abs_of_nonneg (Model.placeWeight_nonneg hM l)]
  unfold wP
  rw [Model.prod_erase_eq, abs_div, Finset.abs_prod, Finset.abs_prod, hden, ← key]
  have hQ : 0 < ∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc) :=
    Finset.prod_pos fun j _ => hdpos _
  have hm : d 0 * d (Fin.last n) ≤ D ^ 2 := by
    rw [sq]; exact mul_le_mul hd0 hdn (hdpos _).le (by linarith)
  have hmpos : 0 < d 0 * d (Fin.last n) := mul_pos (hdpos _) (hdpos _)
  calc (D ^ 2)⁻¹ ≤ (d 0 * d (Fin.last n))⁻¹ := inv_anti₀ hmpos hm
    _ = (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) /
        ((∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
          * (d 0 * d (Fin.last n))) := by
      rw [div_mul_eq_div_div, div_self hQ.ne', one_div]
    _ ≤ _ := div_le_div_of_nonneg_right hnum (mul_pos hQ hmpos).le
end GlobalTheory.WigSh
