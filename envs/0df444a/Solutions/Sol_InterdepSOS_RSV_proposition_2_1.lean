-- Prove2me | solution 1 for InterdepSOS.RSV.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:46:54.487788+00:00
-- url     : https://prove2.me/submissions/f45d12fb-8970-4e5e-beb6-ac287559dbfb

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting
set_option autoImplicit false
open InterdepSOS.RSV

/-- threshold signal of agent `i` against the other signals of `s` -/
noncomputable def eeThr {n : ℕ} (x : Allocation n) (i : Fin n) (s : Signal n) : NNReal :=
  sInf {y : NNReal | i ∈ x (Function.update s i y)}

theorem eeThr_update {n : ℕ} (x : Allocation n) (i : Fin n) (s : Signal n) (y : NNReal) :
    eeThr x i (Function.update s i y) = eeThr x i s := by
  unfold eeThr
  simp [Function.update_idem]

theorem eeThr_le {n : ℕ} (x : Allocation n) (i : Fin n) (s : Signal n) (y : NNReal)
    (h : i ∈ x (Function.update s i y)) : eeThr x i s ≤ y :=
  csInf_le (OrderBot.bddBelow _) h

theorem eeThr_lt {n : ℕ} (x : Allocation n) (hx : IsMonotoneAlloc x) (i : Fin n) (s : Signal n)
    (y : NNReal) (h : eeThr x i s < y) (hne : {y : NNReal | i ∈ x (Function.update s i y)}.Nonempty) :
    i ∈ x (Function.update s i y) := by
  obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne h
  have := hx i s z y hzy.le hz
  exact this

theorem solution {n : ℕ} (v : Valuation n) (hv : IsValuation v)
    (x : Allocation n) :
    (∃ p : Payment n, IsExPostIC v x p ∧ IsExPostIR v x p) ↔
      IsMonotoneAlloc x := by
  obtain ⟨hv0, hvm, hvs⟩ := hv
  constructor
  · rintro ⟨p, hic, _⟩ i s a b hab ha
    by_contra hb
    rcases hab.lt_or_eq with hlt | heq
    · -- IC at true signal b reporting a, and at true signal a reporting b
      have h1 := hic i (Function.update s i b) a
      have h2 := hic i (Function.update s i a) b
      simp only [utility, Function.update_idem, Function.update_self] at h1 h2
      rw [if_pos ha, if_neg hb] at h1
      rw [if_neg hb] at h2
      have h3 := hvs i s a b hlt
      rw [if_pos ha] at h2
      linarith
    · subst heq; exact absurd ha hb
  · intro hx
    classical
    refine ⟨fun s i => if i ∈ x s then v i (Function.update s i (eeThr x i s)) else 0, ?_, ?_⟩
    · intro i s y
      have hT : ∀ z, eeThr x i (Function.update s i z) = eeThr x i s := fun z => eeThr_update x i s z
      simp only [utility, Function.update_idem, Function.update_self, hT]
      -- notation
      set t := eeThr x i s with ht
      have hsi : Function.update s i (s i) = s := Function.update_eq_self i s
      rw [hsi]
      by_cases hy : i ∈ x (Function.update s i y)
      · by_cases hs : i ∈ x s
        · simp [hy, hs]
        · have hne : i ∈ x s → False := hs
          have h1 : t ≤ y := eeThr_le x i s y hy
          have h2 : s i ≤ t := by
            by_contra hlt
            push_neg at hlt
            have hne' : {y : NNReal | i ∈ x (Function.update s i y)}.Nonempty := ⟨y, hy⟩
            have := eeThr_lt x hx i s (s i) hlt hne'
            rw [hsi] at this
            exact hs this
          have h3 : v i s ≤ v i (Function.update s i t) := by
            have : v i (Function.update s i (s i)) ≤ v i (Function.update s i t) :=
              hvm i (fun j => by
                by_cases hj : j = i
                · subst hj; simp [h2]
                · simp [Function.update_of_ne hj])
            rwa [hsi] at this
          simp [hy, hs]
          linarith
      · by_cases hs : i ∈ x s
        · have h1 : t ≤ s i := by
            have := eeThr_le x i s (s i) (by rw [hsi]; exact hs)
            exact this
          have h3 : v i (Function.update s i t) ≤ v i s := by
            have : v i (Function.update s i t) ≤ v i (Function.update s i (s i)) :=
              hvm i (fun j => by
                by_cases hj : j = i
                · subst hj; simp [h1]
                · simp [Function.update_of_ne hj])
            rwa [hsi] at this
          simp [hy, hs]
          linarith
        · simp [hy, hs]
    · intro i s
      simp only [utility, Function.update_self]
      have hsi : Function.update s i (s i) = s := Function.update_eq_self i s
      rw [hsi]
      by_cases hs : i ∈ x s
      · have h1 : eeThr x i s ≤ s i := by
          have := eeThr_le x i s (s i) (by rw [hsi]; exact hs)
          exact this
        have h3 : v i (Function.update s i (eeThr x i s)) ≤ v i s := by
          have : v i (Function.update s i (eeThr x i s)) ≤ v i (Function.update s i (s i)) :=
            hvm i (fun j => by
              by_cases hj : j = i
              · subst hj; simp [h1]
              · simp [Function.update_of_ne hj])
          rwa [hsi] at this
        simp [hs]
        linarith
      · simp [hs]
