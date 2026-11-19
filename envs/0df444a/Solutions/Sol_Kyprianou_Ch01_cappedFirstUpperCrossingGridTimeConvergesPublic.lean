-- Prove2me | solution 1 for Kyprianou.Ch01.cappedFirstUpperCrossingGridTimeConvergesPublic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:17:53.374127+00:00
-- url     : https://prove2.me/submissions/0367ec25-79be-4016-a946-a01216cfbdbe

import Mathlib
import Mathlib.Topology.Bornology.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Find
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (x : ℝ)
    (hx : 0 < x) (hcont : Continuous (fun t : ℝ≥0 => X t ω))
    (hzero : X 0 ω = 0) (T : ℝ≥0) :
    Tendsto (fun N : ℕ =>
      let K : ℕ := N + 1
      let delta : ℝ≥0 := T / (K : ℝ≥0)
      let tau : ℕ := by
        classical
        exact Nat.find (show ∃ k : ℕ,
          k = K ∨ x < X ((k : ℝ≥0) * delta) ω from ⟨K, Or.inl rfl⟩)
      (tau : ℝ≥0) * delta) atTop
      (nhds (match firstUpperPassage X x ω with
        | none => T
        | some t => min t T)) := by
  classical
  dsimp only
  set f : ℝ≥0 → ℝ := fun t => X t ω with hf
  -- generic facts about the grid index
  have hK : ∀ N : ℕ, ((N + 1 : ℕ) : ℝ≥0) ≠ 0 := fun N => by positivity
  have F1 : ∀ N (h : ∃ k : ℕ, k = N + 1 ∨ x < X ((k : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0))) ω),
      Nat.find h ≤ N + 1 := fun N h => Nat.find_min' h (Or.inl rfl)
  have F2 : ∀ N (h : ∃ k : ℕ, k = N + 1 ∨ x < X ((k : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0))) ω),
      (Nat.find h : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0)) ≤ T := by
    intro N h
    calc (Nat.find h : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0))
        ≤ ((N + 1 : ℕ) : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0)) := by
          gcongr; exact_mod_cast F1 N h
      _ = T := by rw [mul_div_cancel₀ _ (hK N)]
  have F3 : ∀ N (h : ∃ k : ℕ, k = N + 1 ∨ x < X ((k : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0))) ω),
      Nat.find h = N + 1 ∨ x < f ((Nat.find h : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0))) :=
    fun N h => Nat.find_spec h
  have F4 : ∀ N (h : ∃ k : ℕ, k = N + 1 ∨ x < X ((k : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0))) ω)
      (k : ℕ), x < f ((k : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0))) → Nat.find h ≤ k :=
    fun N h k hk => Nat.find_min' h (Or.inr hk)
  have Fval : ∀ N (h : ∃ k : ℕ, k = N + 1 ∨ x < X ((k : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0))) ω),
      Nat.find h = N + 1 → (Nat.find h : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0)) = T := by
    intro N h e
    rw [e, mul_div_cancel₀ _ (hK N)]
  by_cases hS : ∃ t : ℝ≥0, 0 < t ∧ x < X t ω
  · set S : Set ℝ≥0 := {t : ℝ≥0 | 0 < t ∧ x < X t ω} with hSdef
    have hFP : firstUpperPassage X x ω = ((sInf S : ℝ≥0) : WithTop ℝ≥0) := by
      unfold firstUpperPassage; rw [if_pos hS]
    rw [hFP]
    show Tendsto _ atTop (nhds (min (sInf S) T))
    have hne : S.Nonempty := hS
    -- lower bound
    have lower : ∀ N (h : ∃ k : ℕ, k = N + 1 ∨ x < X ((k : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0))) ω),
        min (sInf S) T ≤ (Nat.find h : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0)) := by
      intro N h
      rcases F3 N h with e | hlt
      · rw [Fval N h e]; exact min_le_right _ _
      · refine (min_le_left _ _).trans (csInf_le (OrderBot.bddBelow S) ⟨?_, hlt⟩)
        by_cases h0 : (Nat.find h : ℝ≥0) * (T / ((N + 1 : ℕ) : ℝ≥0)) = 0
        · exfalso; rw [h0] at hlt; simp only [hf, hzero] at hlt; linarith
        · exact pos_iff_ne_zero.2 h0
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun N => lt_of_lt_of_le ha (lower N _),
      fun b hb => ?_⟩
    by_cases hbT : T < b
    · exact Eventually.of_forall fun N => lt_of_le_of_lt (F2 N _) hbT
    rw [not_lt] at hbT
    have hτb : sInf S < b := by
      rcases min_lt_iff.1 hb with h | h
      · exact h
      · exact absurd hbT (not_le.2 h)
    obtain ⟨t, ⟨ht0, htx⟩, htb⟩ := exists_lt_of_csInf_lt hne hτb
    have hopen : IsOpen {s : ℝ≥0 | x < f s} := isOpen_lt continuous_const hcont
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen t htx
    have hTpos : (0 : ℝ) < T := by
      have : (0:ℝ≥0) < T := lt_of_lt_of_le (lt_trans ht0 htb) hbT
      exact_mod_cast this
    set ε : ℝ := min η ((b : ℝ) - t) with hε
    have hεpos : 0 < ε := lt_min hη (by have : (t:ℝ) < b := by exact_mod_cast htb
                                        linarith)
    have hlim : Tendsto (fun N : ℕ => (T : ℝ) * (1 / ((N : ℝ) + 1))) atTop (nhds ((T:ℝ) * 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _
    rw [mul_zero] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds hεpos)] with N hN
    set δ : ℝ≥0 := T / ((N + 1 : ℕ) : ℝ≥0) with hδ
    have hδr : (δ : ℝ) = (T : ℝ) * (1 / ((N : ℝ) + 1)) := by
      rw [hδ]; push_cast; ring
    have hδpos : (0 : ℝ) < δ := by rw [hδr]; positivity
    have hδpos' : (0 : ℝ≥0) < δ := by exact_mod_cast hδpos
    have hδε : (δ : ℝ) < ε := by rw [hδr]; exact hN
    set k : ℕ := ⌈t / δ⌉₊ with hk
    have hk1 : (t : ℝ) ≤ (k : ℝ) * δ := by
      have : t / δ ≤ (k : ℝ≥0) := Nat.le_ceil _
      have h2 : t ≤ (k : ℝ≥0) * δ := by
        rwa [div_le_iff₀ hδpos'] at this
      exact_mod_cast h2
    have hk2 : (k : ℝ) * δ < t + δ := by
      have : (k : ℝ≥0) < t / δ + 1 := Nat.ceil_lt_add_one zero_le
      have h2 : (k : ℝ≥0) * δ < (t / δ + 1) * δ := mul_lt_mul_of_pos_right this hδpos'
      rw [add_mul, div_mul_cancel₀ _ hδpos'.ne', one_mul] at h2
      exact_mod_cast h2
    have hkx : x < f ((k : ℝ≥0) * δ) := by
      apply hball
      rw [Metric.mem_ball, NNReal.dist_eq]
      push_cast
      rw [abs_lt]
      constructor <;> linarith [min_le_left η ((b : ℝ) - t)]
    have hb' : (k : ℝ≥0) * δ < b := by
      have : ((k : ℝ≥0) * δ : ℝ) < b := by
        push_cast
        linarith [min_le_right η ((b : ℝ) - t)]
      exact_mod_cast this
    refine lt_of_le_of_lt ?_ hb'
    gcongr
    exact_mod_cast F4 N _ k hkx
  · have hFP : firstUpperPassage X x ω = ⊤ := by
      unfold firstUpperPassage; rw [if_neg hS]
    rw [hFP]
    show Tendsto _ atTop (nhds T)
    refine tendsto_const_nhds.congr fun N => ?_
    symm
    apply Fval
    rcases F3 N _ with e | hlt
    · exact e
    · exfalso
      have hnot : ∀ s : ℝ≥0, ¬ x < f s := by
        intro s hs
        by_cases h0 : s = 0
        · rw [h0] at hs; simp only [hf, hzero] at hs; linarith
        · exact hS ⟨s, pos_iff_ne_zero.2 h0, hs⟩
      exact hnot _ hlt
