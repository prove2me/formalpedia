-- Prove2me | solution 1 for GlobalTheory.WigSh.inv_sq_le_wM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:18.09101+00:00
-- url     : https://prove2.me/submissions/2d1db8b1-2ba8-4413-acc6-a4a97484a0d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqLowering
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace GlobalTheory.WigSh.LowerBound
private theorem prod_erase_succAbove {n : ℕ} (f : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∏ j ∈ univ.erase l, f j = ∏ j : Fin n, f (l.succAbove j) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ]
  · rw [Finset.prod_image]
    intro a _ b _ hab
    exact Fin.succAbove_right_injective hab
private theorem ratio_pos_case {a b c : ℝ} (hb : 0 < b) (h : c ≤ a) :
    c * b / b ^ 2 ≤ a / b := by
  have : c * b / b ^ 2 = c / b := by field_simp
  rw [this]
  exact div_le_div_of_nonneg_right h hb.le
private theorem factor_lower {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (l : Fin (n + 1))
    (hs : StrictAnti L) (j : Fin n) (h1 : L j.succ < M j) (h2 : M j ≤ L j.castSucc)
    (h3 : M j ≠ L l) (G : Fin (n + 1) → ℤ)
    (hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i))) :
    (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2 ≤
      ((M j : ℝ) - L l) / ((L (l.succAbove j) : ℝ) - L l) := by
  have g1 := hG j.succ
  have g2 := hG j.castSucc
  rcases lt_or_ge j.castSucc l with hl | hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ hl]
    have a1 : L l < L j.castSucc := hs hl
    have a2 : L l ≤ L j.succ := hs.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)
    have e : G j.castSucc = L j.castSucc - L l := by omega
    have e' : (L j.castSucc : ℝ) - L l = G j.castSucc := by rw [e]; push_cast; ring
    rw [e']
    apply ratio_pos_case
    · have : (0 : ℤ) < G j.castSucc := by omega
      exact_mod_cast this
    · have : G j.succ ≤ M j - L l := by omega
      exact_mod_cast this
  · rw [Fin.succAbove_of_le_castSucc _ _ hl]
    have a2 : L j.castSucc ≤ L l := hs.antitone hl
    have e : G j.succ = L l - L j.succ := by omega
    have e' : (L j.succ : ℝ) - L l = -G j.succ := by rw [e]; push_cast; ring
    rw [e', div_neg, ← neg_div, mul_comm]
    apply ratio_pos_case
    · have : (0 : ℤ) < G j.succ := by omega
      exact_mod_cast this
    · have : G j.castSucc ≤ -(M j - L l) := by omega
      exact_mod_cast this
end GlobalTheory.WigSh.LowerBound
namespace GlobalTheory.WigSh
open LowerBound
end GlobalTheory.WigSh
end
end

set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh
open LowerBound
namespace GlobalTheory.WigSh
theorem _root_.solution (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hs : StrictAnti L) (hbox : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hlast : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by
  set G : Fin (n + 1) → ℤ := fun i => max 1 (max (L i - L l) (L l - L i)) with hGdef
  have hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i)) := fun i => rfl
  have hpos : ∀ i, (0 : ℝ) < G i := fun i => by
    have : (0 : ℤ) < G i := by rw [hG]; omega
    exact_mod_cast this
  have hl : G l = 1 := by rw [hG]; omega
  have hG0 : (G 0 : ℝ) ≤ D := by
    have a : L l ≤ L 0 := hs.antitone (Fin.zero_le l)
    have : G 0 = 1 ∨ G 0 = L 0 - L l := by rw [hG]; omega
    rcases this with e | e <;> rw [e] <;> push_cast <;> assumption
  have hGl : (G (Fin.last n) : ℝ) ≤ D := by
    have a : L (Fin.last n) ≤ L l := hs.antitone (Fin.le_last l)
    have : G (Fin.last n) = 1 ∨ G (Fin.last n) = L l - L (Fin.last n) := by rw [hG]; omega
    rcases this with e | e <;> rw [e] <;> push_cast <;> assumption
  set P : ℝ := ∏ i, (G i : ℝ) with hP
  have hPpos : 0 < P := Finset.prod_pos fun i _ => hpos i
  have p1 : ∏ j : Fin n, (G j.succ : ℝ) = P / G 0 := by
    rw [eq_div_iff (hpos 0).ne', hP, Fin.prod_univ_succ, mul_comm]
  have p2 : ∏ j : Fin n, (G j.castSucc : ℝ) = P / G (Fin.last n) := by
    rw [eq_div_iff (hpos _).ne', hP, Fin.prod_univ_castSucc]
  have p3 : ∏ j : Fin n, (G (l.succAbove j) : ℝ) = P := by
    rw [hP, Fin.prod_univ_succAbove _ l, hl]; simp
  unfold wM
  rw [prod_erase_succAbove, ← Finset.prod_div_distrib]
  refine le_trans ?_ (Finset.prod_le_prod
    (f := fun j : Fin n => (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2)
    (fun j _ => ?_) (fun j _ => factor_lower l hs j (hbox j).1 (hbox j).2 (hne j) G hG))
  · rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow, p1, p2, p3]
    have q0 := hpos 0
    have ql := hpos (Fin.last n)
    have : P / G 0 * (P / G (Fin.last n)) / P ^ 2 = ((G 0 : ℝ) * G (Fin.last n))⁻¹ := by
      field_simp
    rw [this]
    apply inv_anti₀ (mul_pos q0 ql)
    rw [sq]
    exact mul_le_mul hG0 hGl ql.le (by linarith)
  · have := hpos j.succ
    have := hpos j.castSucc
    positivity
end GlobalTheory.WigSh
