-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.forcing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:15:16.715019+00:00
-- url     : https://prove2.me/submissions/d063984c-618c-47bf-8a98-478fc3fc134e

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Certificate

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
variable {n u v w : ℕ}
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution {a b l x : ℕ} (ha : a < n) (hb : b < n) (hl : l < n) (hx : x < n)
    (hab : ¬ IsLowEnd n a b) (hlb : l ≠ b) (hxl : x ≠ l) (hxa : x ≠ a)
    (hk : ¬ Precedes n a l a b)
    (hsum : localRank n l x + localRank n a b = targetDegree n a l) :
    Precedes n l x a b := by
  have hn2 : 2 ≤ n := by omega
  have hlab : localRank n a b = targetDegree n a b - diagIndex n a b / 2 := by
    unfold localRank; rw [if_neg hab]
  have hlow_ab : lowEnd n a b = b := by
    unfold lowEnd; rw [if_neg hab]
  have hab_e : ¬ (diagIndex n a b % 2 = 0 ↔ b < a) := hab
  have hk_ge : diagIndex n a b / 2 ≤ diagIndex n a l / 2 := by
    unfold Precedes at hk; omega
  have hk_eq : diagIndex n a l / 2 = diagIndex n a b / 2 → lowEnd n a l ≤ b := by
    unfold Precedes at hk; rw [hlow_ab] at hk; omega
  have h_abl : targetDegree n a l ≤ targetDegree n a b ∧
      (targetDegree n a l = targetDegree n a b → b < l) := by
    clear hab hk hsum
    have h1 : (n - 1 ≤ a + b ∧ diagIndex n a b = a + b - (n - 1) ∧ targetDegree n a b = n - 1) ∨
        (a + b < n - 1 ∧ diagIndex n a b = a + b ∧ targetDegree n a b = n - 2) := by
      unfold diagIndex targetDegree; split_ifs <;> omega
    have h2 : (n - 1 ≤ a + l ∧ diagIndex n a l = a + l - (n - 1) ∧ targetDegree n a l = n - 1) ∨
        (a + l < n - 1 ∧ diagIndex n a l = a + l ∧ targetDegree n a l = n - 2) := by
      unfold diagIndex targetDegree; split_ifs <;> omega
    by_cases hal : IsLowEnd n a l
    · have hlow_al : lowEnd n a l = a := by unfold lowEnd; rw [if_pos hal]
      have hal' : diagIndex n a l % 2 = 0 ↔ l < a := hal
      clear hal
      rcases h1 with ⟨_, hdab, htab⟩ | ⟨_, hdab, htab⟩ <;>
        rcases h2 with ⟨_, hdal, htal⟩ | ⟨_, hdal, htal⟩ <;>
        (rw [hdab] at hab_e hk_ge hk_eq; rw [hdal] at hal' hk_ge hk_eq;
         rw [hlow_al] at hk_eq; rw [htab, htal]; omega)
    · have hlow_al : lowEnd n a l = l := by unfold lowEnd; rw [if_neg hal]
      have hal' : ¬ (diagIndex n a l % 2 = 0 ↔ l < a) := hal
      clear hal
      rcases h1 with ⟨_, hdab, htab⟩ | ⟨_, hdab, htab⟩ <;>
        rcases h2 with ⟨_, hdal, htal⟩ | ⟨_, hdal, htal⟩ <;>
        (rw [hdab] at hab_e hk_ge hk_eq; rw [hdal] at hal' hk_ge hk_eq;
         rw [hlow_al] at hk_eq; rw [htab, htal]; omega)
  have hdlx_le : diagIndex n l x ≤ n - 2 := by unfold diagIndex; split_ifs <;> omega
  have hdab_le : diagIndex n a b ≤ n - 1 := by unfold diagIndex; split_ifs <;> omega
  have htab_ge : n - 2 ≤ targetDegree n a b := by unfold targetDegree; split_ifs <;> omega
  have htlx_ge : n - 2 ≤ targetDegree n l x := by unfold targetDegree; split_ifs <;> omega
  unfold Precedes
  rw [hlow_ab]
  rw [hlab] at hsum
  by_cases hlx : IsLowEnd n l x
  · have hllx : localRank n l x = diagIndex n l x / 2 := by unfold localRank; rw [if_pos hlx]
    have hlow_lx : lowEnd n l x = l := by unfold lowEnd; rw [if_pos hlx]
    rw [hllx] at hsum
    rw [hlow_lx]
    by_cases heq : targetDegree n a l = targetDegree n a b
    · right; exact ⟨by omega, h_abl.2 heq⟩
    · left; omega
  · have hllx : localRank n l x = targetDegree n l x - diagIndex n l x / 2 := by
      unfold localRank; rw [if_neg hlx]
    have hlow_lx : lowEnd n l x = x := by unfold lowEnd; rw [if_neg hlx]
    have hlx' : ¬ (diagIndex n l x % 2 = 0 ↔ x < l) := hlx
    rw [hllx] at hsum
    rw [hlow_lx]
    by_cases hlt : diagIndex n l x / 2 < diagIndex n a b / 2
    · exact Or.inl hlt
    · have htlx_eq : targetDegree n l x = n - 2 := by omega
      have htab_eq : targetDegree n a l = targetDegree n a b := by omega
      have hbl : b < l := h_abl.2 htab_eq
      right
      exact ⟨by omega, by omega⟩
end LeanPool.ListEdgeColoringComplete
