-- Prove2me | solution 1 for Kyprianou.Ch04.idleRegulatorCrossingFromFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:16:49.206528+00:00
-- url     : https://prove2.me/submissions/e25c3afc-1bc3-431b-bfb1-e68594194fed

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : NNReal → Real) (d w : Real) (hd : 0 < d) (hw : 0 ≤ w)
    (hf0 : f 0 = 0)
    (hf : ∀ s t : NNReal, s ≤ t → f t - f s ≤ d * ((t : Real) - (s : Real)))
    (I : Nat → ENNReal)
    (hI : ∀ n : Nat, ENNReal.ofReal (max w (sSup (f '' Iic (n : NNReal))) - w) =
      ENNReal.ofReal d * I n) :
    ∀ x : Real, 0 ≤ x → (ENNReal.ofReal x < ⨆ n, I n ↔
      ∃ t : NNReal, w + d * x < f t) := by
  have hbdd (t : NNReal) : BddAbove (f '' Iic t) := by
    refine ⟨d * (t : Real), ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hh := hf 0 s zero_le
    have hs' : (s : Real) ≤ (t : Real) := hs
    simp only [hf0, NNReal.coe_zero, sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hs' hd.le)
  intro x hx
  have hd0 : ENNReal.ofReal d ≠ 0 := by positivity
  have hscl (n : Nat) : ENNReal.ofReal x < I n ↔
      w + d * x < max w (sSup (f '' Iic (n : NNReal))) := by
    rw [← ENNReal.mul_lt_mul_iff_left hd0 ENNReal.ofReal_ne_top,
      mul_comm (ENNReal.ofReal x), mul_comm (I n), ← ENNReal.ofReal_mul hd.le, ← hI n]
    rw [← not_le, ← not_le, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hd.le hx)]
    constructor <;> intro h <;> linarith
  rw [lt_iSup_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hr := (hscl n).mp hn
    have hlevel : w ≤ w + d * x := by linarith [mul_nonneg hd.le hx]
    have hsup : w + d * x < sSup (f '' Iic (n : NNReal)) := by
      by_contra! hh
      exact (not_lt_of_ge (max_le hlevel hh)) hr
    obtain ⟨_, ⟨t, ht, rfl⟩, ht'⟩ := (lt_csSup_iff (hbdd _) ⟨f 0, 0, mem_Iic.mpr zero_le, rfl⟩).mp hsup
    exact ⟨t, ht'⟩
  · rintro ⟨t, ht⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (t : Real)
    have htn : t ≤ (n : NNReal) := by exact_mod_cast hn
    exact ⟨n, (hscl n).mpr (ht.trans_le
      ((le_csSup (hbdd _) ⟨t, mem_Iic.mpr htn, rfl⟩).trans (le_max_right _ _)))⟩
