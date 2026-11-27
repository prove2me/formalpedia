-- Prove2me | solution 1 for MLRPCake.EnvyFree.Supplement.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:51.713399+00:00
-- url     : https://prove2.me/submissions/e210d239-d60c-4a8c-a9a6-100d30baffc0

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_SwitchPoints

open MLRPCake
open MLRPCake.EnvyFree
open MLRPCake.EnvyFree.Supplement

/-- Lemma 6, p. 18: for two value densities bearing MLRP (strictly positive on `[0,1]`, `f_j/f_i`
nondecreasing on `[0,1]`) with switching point `p_{ij} = inf {x ∈ [0,1] : f_j(x) ≥ f_i(x)}`:
(a) `f_j(y)/f_i(y) < 1` for all `y ∈ [0, p_{ij})`, and (b) `f_j(z)/f_i(z) ≥ 1` for all
`z ∈ (p_{ij}, 1]`. -/
theorem solution (fi fj : ℝ → ℝ) (hi : IsDensity fi) (hj : IsDensity fj)
    (hpos_i : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < fi x) (hpos_j : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < fj x)
    (hmlrp : ∀ b c : ℝ, 0 ≤ b → b ≤ c → c ≤ 1 → fj b / fi b ≤ fj c / fi c) :
    (∀ y : ℝ, 0 ≤ y → y < switchPt fi fj → fj y / fi y < 1) ∧
    (∀ z : ℝ, switchPt fi fj < z → z ≤ 1 → 1 ≤ fj z / fi z) := by
      set S : Set ℝ := {x | x ∈ Set.Icc (0:ℝ) 1 ∧ fi x ≤ fj x} with hS
      have hp : switchPt fi fj = sInf S := rfl
      have hbdd : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
      have hne : S.Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        have hlt : ∀ x ∈ Set.Icc (0:ℝ) 1, fj x < fi x := by
          intro x hx
          by_contra h
          push_neg at h
          have : x ∈ S := ⟨hx, h⟩
          rw [hemp] at this
          exact this
        have hint : IntervalIntegrable (fun x => fi x - fj x) MeasureTheory.volume 0 1 :=
          hi.2.2.1.sub hj.2.2.1
        have hposI : 0 < ∫ x in (0:ℝ)..1, (fi x - fj x) :=
          intervalIntegral.intervalIntegral_pos_of_pos_on hint
            (fun x hx => sub_pos.mpr (hlt x (Set.Ioo_subset_Icc_self hx))) one_pos
        rw [intervalIntegral.integral_sub hi.2.2.1 hj.2.2.1, hi.2.2.2, hj.2.2.2] at hposI
        simp at hposI
      refine ⟨?_, ?_⟩
      · intro y hy0 hyp
        obtain ⟨s, hs⟩ := hne
        have hp1 : sInf S ≤ 1 := le_trans (csInf_le hbdd hs) hs.1.2
        rw [hp] at hyp
        have hy1 : y ≤ 1 := by linarith
        have hfi := hpos_i y ⟨hy0, hy1⟩
        rw [div_lt_one hfi]
        by_contra h
        push_neg at h
        have : y ∈ S := ⟨⟨hy0, hy1⟩, h⟩
        have := csInf_le hbdd this
        linarith
      · intro z hpz hz1
        rw [hp] at hpz
        obtain ⟨s, hs, hsz⟩ := exists_lt_of_csInf_lt hne hpz
        have hfs := hpos_i s hs.1
        have h1 : 1 ≤ fj s / fi s := by rw [le_div_iff₀ hfs]; linarith [hs.2]
        exact le_trans h1 (hmlrp s z hs.1.1 hsz.le hz1)
