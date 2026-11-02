-- Prove2me | solution 1 for LiqProvision.Oligopoly.theorem_3_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:42:48.648214+00:00
-- url     : https://prove2.me/submissions/ba37d8df-30fa-498f-b5ed-4a2895339183
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model
import Theorems.Thm_LiqProvision_Oligopoly_lemma_2_5_a
import Theorems.Thm_LiqProvision_Oligopoly_lemma_3_6
import Theorems.Thm_LiqProvision_Oligopoly_theorem_3_8
import Theorems.Thm_LiqProvision_Oligopoly_theorem_3_11_existence

open Set MeasureTheory
open LiqProvision.Oligopoly

namespace LiqT311Aux

/-- Fundamental theorem of calculus across the kink at `0`. -/
theorem ftc (P p : ℝ → ℝ) (hPc : Continuous P) (hP0 : P 0 = 0)
    (hd : ∀ x, x ≠ 0 → HasDerivAt P (p x) x) (hmono : StrictMonoOn p {0}ᶜ) (n : ℝ) :
    P n = ∫ x in (0:ℝ)..n, p x := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [ae_iff]; simp
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · set q := Function.update p 0 (p 1) with hq
    have hqm : MonotoneOn q (uIcc n 0) := by
      rw [uIcc_of_le hn.le]
      intro a ha b hb hab
      by_cases hb0 : b = 0
      · subst hb0
        by_cases ha0 : a = 0
        · subst ha0; exact le_rfl
        · simp only [hq, Function.update_self, Function.update_of_ne ha0]
          exact (hmono ha0 (one_ne_zero) (by linarith [lt_of_le_of_ne ha.2 ha0])).le
      · have ha0 : a ≠ 0 := by
          intro h; subst h; exact hb0 (le_antisymm hb.2 hab)
        simp only [hq, Function.update_of_ne ha0, Function.update_of_ne hb0]
        exact hmono.monotoneOn ha0 hb0 hab
    have hqi : IntervalIntegrable q volume n 0 := hqm.intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hn.le hPc.continuousOn
      (fun x hx => by
        have hx0 : x ≠ 0 := hx.2.ne
        simpa [hq, Function.update_of_ne hx0] using hd x hx0) hqi
    have hpq : ∫ x in n..0, q x = ∫ x in n..0, p x :=
      intervalIntegral.integral_congr_ae (hae.mono fun x hx _ => by
        simp [hq, Function.update_of_ne hx])
    rw [intervalIntegral.integral_symm, ← hpq, hftc, hP0]; ring
  · simp [hP0]
  · set q := Function.update p 0 (p (-1)) with hq
    have hqm : MonotoneOn q (uIcc 0 n) := by
      rw [uIcc_of_le hn.le]
      intro a ha b hb hab
      by_cases ha0 : a = 0
      · subst ha0
        by_cases hb0 : b = 0
        · subst hb0; exact le_rfl
        · simp only [hq, Function.update_self, Function.update_of_ne hb0]
          exact (hmono (by norm_num : (-1:ℝ) ≠ 0) hb0
            (by linarith [lt_of_le_of_ne hb.1 (Ne.symm hb0)])).le
      · have hb0 : b ≠ 0 := by
          intro h; subst h; exact ha0 (le_antisymm hab ha.1)
        simp only [hq, Function.update_of_ne ha0, Function.update_of_ne hb0]
        exact hmono.monotoneOn ha0 hb0 hab
    have hqi : IntervalIntegrable q volume 0 n := hqm.intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hn.le hPc.continuousOn
      (fun x hx => by
        have hx0 : x ≠ 0 := hx.1.ne'
        simpa [hq, Function.update_of_ne hx0] using hd x hx0) hqi
    have hpq : ∫ x in (0:ℝ)..n, q x = ∫ x in (0:ℝ)..n, p x :=
      intervalIntegral.integral_congr_ae (hae.mono fun x hx _ => by
        simp [hq, Function.update_of_ne hx])
    rw [← hpq, hftc, hP0]; ring

end LiqT311Aux

open LiqT311Aux in
theorem solution (M : Params) (hS : M.Standing) (h21 : M.Assumption21)
    (h37 : M.Assumption37) (p : ℝ → ℝ) (hp : IsODESol M p) (h310 : Assumption310 M p)
    (P : ℝ → ℝ) :
    IsSymNE M P ↔ ∀ n, P n = ∫ x in (0 : ℝ)..n, p x := by
  constructor
  · intro hNE
    obtain ⟨hPS, hsc⟩ := (lemma_2_5_a M hS.1 hS.2.1 P).1 hNE.1
    have hopen : IsOpen ({0}ᶜ : Set ℝ) := isOpen_compl_singleton
    have hdiffAt : ∀ x, x ≠ 0 → DifferentiableAt ℝ P x := fun x hx =>
      (hPS.2.2.differentiableOn (by norm_num) x hx).differentiableAt (hopen.mem_nhds hx)
    have hODE : IsODESol M (deriv P) := by
      refine ⟨?_, hPS.2.2.deriv_of_isOpen hopen (by norm_num), lemma_3_6 M hS h21 P hNE⟩
      intro x hx y hy hxy
      exact (hsc.deriv_lt_slope (mem_univ _) (mem_univ _) hxy (hdiffAt x hx)).trans
        (hsc.slope_lt_deriv (mem_univ _) (mem_univ _) hxy (hdiffAt y hy))
    obtain ⟨p₀, -, huniq⟩ := theorem_3_8 M hS h21 h37
    have heq : ∀ x, x ≠ 0 → deriv P x = p x := fun x hx =>
      (huniq _ hODE hx).trans (huniq _ hp hx).symm
    intro n
    exact ftc P p hPS.1 hPS.2.1 (fun x hx => heq x hx ▸ (hdiffAt x hx).hasDerivAt) hp.1 n
  · intro h
    have : P = fun n => ∫ x in (0 : ℝ)..n, p x := funext h
    rw [this]; exact theorem_3_11_existence M hS h21 h37 p hp h310
