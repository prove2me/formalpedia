-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.isClique_range_fractionGraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:41.232777+00:00
-- url     : https://prove2.me/submissions/8a55eb0b-4589-4fe1-9c7d-193d8142e0ba

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs

set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (p q : ℕ) [NeZero p] (hq : 0 < q) (h2q : 2 * q ≤ p) :
    (fractionGraph p q).IsClique ((Finset.range q).image (fun i : ℕ => (i : ZMod p))) := by
  rw [SimpleGraph.isClique_iff]
  intro u hu v hv huv
  rw [Finset.mem_coe, Finset.mem_image] at hu hv
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hv
  rw [Finset.mem_range] at ha hb
  simp only [fractionGraph]
  constructor
  · exact huv
  · -- distMod (a : ZMod p) (b : ZMod p) < q
    simp only [distMod]
    have hq_le_p : q ≤ p := by omega
    have ha_lt_p : a < p := Nat.lt_of_lt_of_le ha hq_le_p
    have hb_lt_p : b < p := Nat.lt_of_lt_of_le hb hq_le_p
    by_cases hab : a ≤ b
    · -- Case a ≤ b
      have hval : ((a : ZMod p) - (b : ZMod p)).val =
          if a = b then 0 else p - (b - a) := by
        by_cases heq : a = b
        · simp [heq]
        · have hlt : a < b := Nat.lt_of_le_of_ne hab heq
          have hba_pos : 0 < b - a := Nat.sub_pos_of_lt hlt
          have hba_lt_p : b - a < p := by omega
          simp only [heq, ↓reduceIte]
          have h : (a : ZMod p) - (b : ZMod p) = -((b - a : ℕ) : ZMod p) := by
            simp only [Nat.cast_sub (Nat.le_of_lt hlt), neg_sub]
          rw [h]
          have hne : ((b - a : ℕ) : ZMod p) ≠ 0 := by
            rw [ne_eq, ZMod.natCast_eq_zero_iff]
            intro hdvd
            have := Nat.eq_zero_of_dvd_of_lt hdvd hba_lt_p
            omega
          rw [ZMod.neg_val, if_neg hne, ZMod.val_natCast_of_lt hba_lt_p]
      simp only [hval]
      split_ifs with heq
      · -- If a = b, then u = v, contradicting huv
        exfalso; apply huv; simp [heq]
      · have hlt : a < b := Nat.lt_of_le_of_ne hab heq
        have hba : b - a < q := by omega
        simp only [Nat.min_def]
        split_ifs with h <;> omega
    · -- Case b < a
      push_neg at hab
      have hval : ((a : ZMod p) - (b : ZMod p)).val = a - b := by
        have hab' : (a : ZMod p) - (b : ZMod p) = ((a - b : ℕ) : ZMod p) := by
          simp only [Nat.cast_sub (Nat.le_of_lt hab)]
        rw [hab']
        have hab_lt_p : a - b < p := by omega
        exact ZMod.val_natCast_of_lt hab_lt_p
      rw [hval]
      have hab_lt_q : a - b < q := by omega
      simp only [Nat.min_def]
      split_ifs with h
      · exact hab_lt_q
      · omega
end GroupTheoreticShannonCapacity
