-- Prove2me | solution 1 for Helfgott.moebius_initial_integral_le_303
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:29:17.322721+00:00
-- url     : https://prove2.me/submissions/bd1040f6-da90-449e-8c6b-70e37494fa54

import Theorems.Thm_Helfgott_mobiusTable1200001_checked
import Theorems.Thm_Helfgott_mobiusHarmonic1078853_checked
import Theorems.Thm_Helfgott_moebius_initial_integral_of_finite_certificate
import Mathlib.Tactic


set_option autoImplicit false
namespace Helfgott

lemma mobiusLeafCheck_mono (g : ℕ → ℤ) (Bsmall Bbig offset digits : ℕ)
    (hB : Bsmall ≤ Bbig) (h : mobiusLeafCheck g Bbig offset digits = true) :
    mobiusLeafCheck g Bsmall offset digits = true := by
  rw [mobiusLeafCheck, List.all_eq_true] at h ⊢
  intro k hk
  by_cases hsmall : offset + k < Bsmall
  · have hbig : offset + k < Bbig := lt_of_lt_of_le hsmall hB
    simpa only [hsmall, hbig, if_pos] using h k hk
  · simp only [hsmall, if_false]

lemma mobiusTreeCheck_mono (g : ℕ → ℤ) (Bsmall Bbig d offset : ℕ)
    (tree : MobiusCertTree) (hB : Bsmall ≤ Bbig)
    (h : mobiusTreeCheck g Bbig d offset tree = true) :
    mobiusTreeCheck g Bsmall d offset tree = true := by
  induction d generalizing offset tree with
  | zero =>
      by_cases hs : Bsmall ≤ offset
      · unfold mobiusTreeCheck
        simp only [hs, if_pos]
      · have hb : ¬Bbig ≤ offset := by omega
        cases tree with
        | leaf mu digits =>
            simp only [mobiusTreeCheck, hs, hb, if_false] at h ⊢
            exact mobiusLeafCheck_mono g Bsmall Bbig offset digits hB h
        | branch l r =>
            unfold mobiusTreeCheck at h
            simp only [hb, if_false] at h
            contradiction
  | succ d ih =>
      by_cases hs : Bsmall ≤ offset
      · unfold mobiusTreeCheck
        simp only [hs, if_pos]
      · have hb : ¬Bbig ≤ offset := by omega
        cases tree with
        | leaf mu digits =>
            unfold mobiusTreeCheck at h
            simp only [hb, if_false] at h
            contradiction
        | branch l r =>
            simp only [mobiusTreeCheck, hs, hb, if_false, Bool.and_eq_true] at h ⊢
            exact ⟨ih offset l h.1, ih (offset + 32 * 2 ^ d) r h.2⟩

end Helfgott
open Helfgott Finset Nat ArithmeticFunction Real MeasureTheory
open scoped BigOperators Classical Interval
set_option Elab.async false

theorem solution :
    (∫ t in (1 : ℝ)..(1078853 : ℝ),
      |∑ d ∈ Finset.Icc 1 ⌊t⌋₊, ((moebius d : ℤ) : ℝ)| / t) ≤ 303 := by
  have hm := Helfgott.mobiusTreeCheck_mono (mobiusTreeValue 16 mobiusTable1200001)
    1078853 1200001 16 0 mobiusTable1200001 (by decide) mobiusTable1200001_checked
  have hi := moebius_initial_integral_of_finite_certificate 1078853 16 16 1000000000
    mobiusTable1200001 mobiusHarmonic1078853 (by decide) (by decide)
    (by decide) (by decide) (by decide) hm mobiusHarmonic1078853_checked
  have hu : (mobiusHarmonicUpper mobiusHarmonic1078853 : ℝ) / (1000000000 : ℝ) ≤ 303 := by
    change (302481031385 : ℝ) / (1000000000 : ℝ) ≤ 303
    norm_num
  exact hi.trans hu

#print axioms solution
