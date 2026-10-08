-- Prove2me | solution 1 for LawlerMoore.WeightedTardy.min_weighted_tardy_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:15:03.689004+00:00
-- url     : https://prove2.me/submissions/46c103f2-12ce-459a-8c1e-0e72edafcd7f

import Mathlib
import Definitions.Def_LawlerMoore_WeightedTardy_PrefixFeasible
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_LawlerMoore_WeightedTardy_weightedTardy
import Definitions.Def_LawlerMoore_WeightedTardy_eq3



namespace LawlerMoore.WeightedTardy

open MooreLateJobs.Shared MooreLateJobs.NumLate
open Finset

section eq3v
variable {n : ℕ}

def lmSS (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (t : ℤ) : Set ℝ :=
  {v | ∃ x : Fin n → Bool, (∀ i : Fin n, j ≤ i.val → x i = false) ∧
    (∀ k : Fin n, k.val < j → ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k) ∧
    ((∑ i, a' i * (x i).toNat : ℕ) : ℤ) ≤ t ∧ v = knapValue p x}

theorem lm_sum_update (c : Fin n → ℕ) (x : Fin n → Bool) (j : Fin n) (b : Bool)
    (s : Finset (Fin n)) (hj : j ∈ s) :
    ∑ i ∈ s, c i * (Function.update x j b i).toNat
      = c j * b.toNat + ∑ i ∈ s.erase j, c i * (x i).toNat := by
  rw [← Finset.add_sum_erase s _ hj]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem lm_knap_update (p : Fin n → ℝ) (x : Fin n → Bool) (j : Fin n) (b : Bool) :
    knapValue p (Function.update x j b)
      = p j * (b.toNat : ℝ) + ∑ i ∈ univ.erase j, p i * ((x i).toNat : ℝ) := by
  unfold knapValue
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ j)]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem lm_knap_split (p : Fin n → ℝ) (x : Fin n → Bool) (j : Fin n) :
    knapValue p x = p j * ((x j).toNat : ℝ) + ∑ i ∈ univ.erase j, p i * ((x i).toNat : ℝ) := by
  unfold knapValue
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ j)]

theorem lm_tot_split (c : Fin n → ℕ) (x : Fin n → Bool) (j : Fin n) :
    ∑ i, c i * (x i).toNat = c j * (x j).toNat + ∑ i ∈ univ.erase j, c i * (x i).toNat := by
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ j)]

theorem lm_T (a' : Fin n → ℕ) (x : Fin n → Bool) (j : ℕ) (k : Fin n) (hk : k.val = j)
    (hx : ∀ i : Fin n, j + 1 ≤ i.val → x i = false) :
    ∑ i, a' i * (x i).toNat = ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (x i).toNat := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i ≤ k
  · simp [h]
  · have : j + 1 ≤ i.val := by rw [Fin.le_def] at h; omega
    simp [h, hx i this]

theorem lm_sumTo_le (a' : Fin n → ℕ) (x : Fin n → Bool) (k : Fin n) :
    ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ ∑ i, a' i * (x i).toNat :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem lm_down1 (a' d : Fin n → ℕ) (j : ℕ) (hjn : j < n) (t : ℤ) (x : Fin n → Bool)
    (h1 : ∀ i : Fin n, j + 1 ≤ i.val → x i = false)
    (h2 : ∀ k : Fin n, k.val < j + 1 → ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k)
    (h3 : ((∑ i, a' i * (x i).toNat : ℕ) : ℤ) ≤ t) (hxj : x ⟨j, hjn⟩ = false) :
    (∀ i : Fin n, j ≤ i.val → x i = false) ∧
    (∀ k : Fin n, k.val < j → ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k) ∧
    ((∑ i, a' i * (x i).toNat : ℕ) : ℤ) ≤ t := by
  refine ⟨?_, fun k hk => h2 k (by omega), h3⟩
  intro i hi
  by_cases h : i.val = j
  · have : i = ⟨j, hjn⟩ := Fin.ext h
    rw [this]; exact hxj
  · exact h1 i (by omega)

theorem lm_down2 (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hjn : j < n) (t : ℤ)
    (x : Fin n → Bool)
    (h1 : ∀ i : Fin n, j + 1 ≤ i.val → x i = false)
    (h2 : ∀ k : Fin n, k.val < j + 1 → ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k)
    (h3 : ((∑ i, a' i * (x i).toNat : ℕ) : ℤ) ≤ t) (hxj : x ⟨j, hjn⟩ = true) :
    (∀ i : Fin n, j ≤ i.val → Function.update x ⟨j, hjn⟩ false i = false) ∧
    (∀ k : Fin n, k.val < j → ∑ i ∈ univ.filter (fun i => i ≤ k),
        a' i * (Function.update x ⟨j, hjn⟩ false i).toNat ≤ d k) ∧
    ((∑ i, a' i * (Function.update x ⟨j, hjn⟩ false i).toNat : ℕ) : ℤ) ≤ t - (a' ⟨j, hjn⟩ : ℤ) ∧
    knapValue p x = p ⟨j, hjn⟩ + knapValue p (Function.update x ⟨j, hjn⟩ false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h : i.val = j
    · have : i = ⟨j, hjn⟩ := Fin.ext h
      rw [this]; simp
    · rw [Function.update_of_ne (fun h' => h (by rw [h']))]
      exact h1 i (by omega)
  · intro k hk
    have : ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (Function.update x ⟨j, hjn⟩ false i).toNat
        = ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (x i).toNat := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ k := (Finset.mem_filter.1 hi).2
      rw [Fin.le_def] at hi'
      rw [Function.update_of_ne (fun h' => by rw [h'] at hi'; simp at hi'; omega)]
    rw [this]; exact h2 k (by omega)
  · have e1 := lm_tot_split a' (Function.update x ⟨j, hjn⟩ false) ⟨j, hjn⟩
    have e2 := lm_tot_split a' x ⟨j, hjn⟩
    have e3 : ∑ i ∈ univ.erase (⟨j, hjn⟩ : Fin n), a' i * (Function.update x ⟨j, hjn⟩ false i).toNat
        = ∑ i ∈ univ.erase (⟨j, hjn⟩ : Fin n), a' i * (x i).toNat := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    simp only [hxj, Function.update_self] at e1 e2
    simp at e1 e2
    omega
  · rw [lm_knap_split p x ⟨j, hjn⟩, lm_knap_update]
    simp [hxj]

theorem lm_up (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hjn : j < n) (t : ℤ)
    (x : Fin n → Bool)
    (h1 : ∀ i : Fin n, j ≤ i.val → x i = false)
    (h2 : ∀ k : Fin n, k.val < j → ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k)
    (h3 : ((∑ i, a' i * (x i).toNat : ℕ) : ℤ) ≤ t - (a' ⟨j, hjn⟩ : ℤ))
    (htd : t ≤ (d ⟨j, hjn⟩ : ℤ)) :
    (∀ i : Fin n, j + 1 ≤ i.val → Function.update x ⟨j, hjn⟩ true i = false) ∧
    (∀ k : Fin n, k.val < j + 1 → ∑ i ∈ univ.filter (fun i => i ≤ k),
        a' i * (Function.update x ⟨j, hjn⟩ true i).toNat ≤ d k) ∧
    ((∑ i, a' i * (Function.update x ⟨j, hjn⟩ true i).toNat : ℕ) : ℤ) ≤ t ∧
    knapValue p (Function.update x ⟨j, hjn⟩ true) = p ⟨j, hjn⟩ + knapValue p x := by
  have hxj : x ⟨j, hjn⟩ = false := h1 _ le_rfl
  have htot : ((∑ i, a' i * (Function.update x ⟨j, hjn⟩ true i).toNat : ℕ) : ℤ) ≤ t := by
    have e1 := lm_tot_split a' (Function.update x ⟨j, hjn⟩ true) ⟨j, hjn⟩
    have e2 := lm_tot_split a' x ⟨j, hjn⟩
    have e3 : ∑ i ∈ univ.erase (⟨j, hjn⟩ : Fin n), a' i * (Function.update x ⟨j, hjn⟩ true i).toNat
        = ∑ i ∈ univ.erase (⟨j, hjn⟩ : Fin n), a' i * (x i).toNat := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    simp only [hxj, Function.update_self] at e1 e2
    simp at e1 e2
    omega
  refine ⟨?_, ?_, htot, ?_⟩
  · intro i hi
    rw [Function.update_of_ne (fun h' => by rw [h'] at hi; simp at hi)]
    exact h1 i (by omega)
  · intro k hk
    by_cases hkj : k.val = j
    · obtain rfl : k = ⟨j, hjn⟩ := Fin.ext hkj
      have := lm_sumTo_le a' (Function.update x ⟨j, hjn⟩ true) ⟨j, hjn⟩
      omega
    · have hk' : k.val < j := by omega
      have : ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (Function.update x ⟨j, hjn⟩ true i).toNat
          = ∑ i ∈ univ.filter (fun i => i ≤ k), a' i * (x i).toNat := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ≤ k := (Finset.mem_filter.1 hi).2
        rw [Fin.le_def] at hi'
        rw [Function.update_of_ne (fun h' => by rw [h'] at hi'; simp at hi'; omega)]
      rw [this]; exact h2 k hk'
  · rw [lm_knap_split p x ⟨j, hjn⟩, lm_knap_update]
    simp [hxj]


theorem lm_eq3_zero (a' d : Fin n → ℕ) (p : Fin n → ℝ) (t : ℤ) :
    (t < 0 → eq3 a' d p 0 t = ⊥) ∧ (0 ≤ t → ∃ V : ℝ, eq3 a' d p 0 t = (V : WithBot ℝ) ∧
      IsGreatest (lmSS a' d p 0 t) V) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩
  · rw [eq3]; simp [not_le.2 ht]
  · refine ⟨0, ?_, ?_, ?_⟩
    · rw [eq3]; simp [ht]
    · refine ⟨fun _ => false, ?_, ?_, ?_, ?_⟩
      · simp
      · intro k hk; omega
      · simpa using ht
      · simp [knapValue]
    · rintro v ⟨x, hx, _, _, rfl⟩
      have : ∀ i, x i = false := fun i => hx i (Nat.zero_le _)
      simp [knapValue, this]

theorem lm_eq3_step_eq (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hjn : j < n) (t : ℤ) :
    eq3 a' d p (j + 1) t =
      if t < 0 then ⊥ else
      if t ≤ (d ⟨j, hjn⟩ : ℤ) then
        max (max (eq3 a' d p (j + 1) (t - 1)) (eq3 a' d p j t))
          ((p ⟨j, hjn⟩ : WithBot ℝ) + eq3 a' d p j (t - (a' ⟨j, hjn⟩ : ℤ)))
      else eq3 a' d p (j + 1) (d ⟨j, hjn⟩ : ℤ) := by
  rw [eq3]
  simp [hjn]


theorem lm_mono_t (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) {t t' : ℤ} (h : t ≤ t') {v : ℝ}
    (hv : v ∈ lmSS a' d p j t) : v ∈ lmSS a' d p j t' := by
  obtain ⟨x, h1, h2, h3, h4⟩ := hv
  exact ⟨x, h1, h2, le_trans h3 h, h4⟩

theorem lm_cut (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hjn : j < n) (t : ℤ) {v : ℝ}
    (hv : v ∈ lmSS a' d p (j + 1) t) : v ∈ lmSS a' d p (j + 1) ((d ⟨j, hjn⟩ : ℕ) : ℤ) := by
  obtain ⟨x, h1, h2, h3, h4⟩ := hv
  refine ⟨x, h1, h2, ?_, h4⟩
  have := h2 ⟨j, hjn⟩ (by simp)
  rw [lm_T a' x j ⟨j, hjn⟩ rfl h1]
  exact_mod_cast this

theorem lm_split_mem (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hjn : j < n) (t : ℤ) {v : ℝ}
    (hv : v ∈ lmSS a' d p (j + 1) t) :
    v ∈ lmSS a' d p j t ∨ ∃ v' ∈ lmSS a' d p j (t - (a' ⟨j, hjn⟩ : ℤ)), v = p ⟨j, hjn⟩ + v' := by
  obtain ⟨x, h1, h2, h3, h4⟩ := hv
  cases hxj : x ⟨j, hjn⟩
  · left
    obtain ⟨g1, g2, g3⟩ := lm_down1 a' d j hjn t x h1 h2 h3 hxj
    exact ⟨x, g1, g2, g3, h4⟩
  · right
    obtain ⟨g1, g2, g3, g4⟩ := lm_down2 a' d p j hjn t x h1 h2 h3 hxj
    exact ⟨_, ⟨_, g1, g2, g3, rfl⟩, by rw [h4]; exact g4⟩

theorem lm_emb1 (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hjn : j < n) (t : ℤ)
    (htd : t ≤ (d ⟨j, hjn⟩ : ℤ)) {v : ℝ} (hv : v ∈ lmSS a' d p j t) :
    v ∈ lmSS a' d p (j + 1) t := by
  obtain ⟨x, h1, h2, h3, h4⟩ := hv
  refine ⟨x, fun i hi => h1 i (by omega), ?_, h3, h4⟩
  intro k hk
  by_cases hkj : k.val = j
  · obtain rfl : k = ⟨j, hjn⟩ := Fin.ext hkj
    have := lm_sumTo_le a' x ⟨j, hjn⟩
    omega
  · exact h2 k (by omega)

theorem lm_emb2 (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hjn : j < n) (t : ℤ)
    (htd : t ≤ (d ⟨j, hjn⟩ : ℤ)) {v : ℝ} (hv : v ∈ lmSS a' d p j (t - (a' ⟨j, hjn⟩ : ℤ))) :
    p ⟨j, hjn⟩ + v ∈ lmSS a' d p (j + 1) t := by
  obtain ⟨x, h1, h2, h3, h4⟩ := hv
  obtain ⟨g1, g2, g3, g4⟩ := lm_up a' d p j hjn t x h1 h2 h3 htd
  exact ⟨_, g1, g2, g3, by rw [g4, h4]⟩

theorem lm_eq3_main (a' d : Fin n → ℕ) (p : Fin n → ℝ) : ∀ j : ℕ, j ≤ n → ∀ t : ℤ,
    (t < 0 → eq3 a' d p j t = ⊥) ∧ (0 ≤ t → ∃ V : ℝ, eq3 a' d p j t = (V : WithBot ℝ) ∧
      IsGreatest (lmSS a' d p j t) V) := by
  intro j
  induction j with
  | zero => intro _ t; exact lm_eq3_zero a' d p t
  | succ j ih =>
    intro hj
    have hjn : j < n := by omega
    have ih' := ih (by omega)
    have neg : ∀ t : ℤ, t < 0 → eq3 a' d p (j + 1) t = ⊥ := by
      intro t ht
      rw [lm_eq3_step_eq a' d p j hjn, if_pos ht]
    have pos : ∀ m : ℕ, ∃ V : ℝ, eq3 a' d p (j + 1) (m : ℤ) = (V : WithBot ℝ) ∧
        IsGreatest (lmSS a' d p (j + 1) (m : ℤ)) V := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m IH =>
        rw [lm_eq3_step_eq a' d p j hjn, if_neg (by omega)]
        by_cases htd : (m : ℤ) ≤ (d ⟨j, hjn⟩ : ℤ)
        · rw [if_pos htd]
          obtain ⟨V1, hV1, hG1⟩ := (ih' (m : ℤ)).2 (by omega)
          have h3 : eq3 a' d p (j + 1) ((m : ℤ) - 1) = ⊥ ∨
              ∃ v ∈ lmSS a' d p (j + 1) (m : ℤ), eq3 a' d p (j + 1) ((m : ℤ) - 1) = (v : WithBot ℝ) := by
            by_cases hm : m = 0
            · left; apply neg; omega
            · right
              obtain ⟨V3, e3, g3⟩ := IH (m - 1) (by omega)
              refine ⟨V3, lm_mono_t a' d p (j + 1) (by omega) g3.1, ?_⟩
              have : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
              rw [← this]; exact e3
          have h2 : eq3 a' d p j ((m : ℤ) - (a' ⟨j, hjn⟩ : ℤ)) = ⊥ ∨
              ∃ v ∈ lmSS a' d p j ((m : ℤ) - (a' ⟨j, hjn⟩ : ℤ)),
                eq3 a' d p j ((m : ℤ) - (a' ⟨j, hjn⟩ : ℤ)) = (v : WithBot ℝ) := by
            by_cases ha : (a' ⟨j, hjn⟩ : ℤ) ≤ m
            · right
              obtain ⟨V2, e2, g2⟩ := (ih' ((m : ℤ) - (a' ⟨j, hjn⟩ : ℤ))).2 (by omega)
              exact ⟨V2, g2.1, e2⟩
            · left; exact (ih' ((m : ℤ) - (a' ⟨j, hjn⟩ : ℤ))).1 (by omega)
          have hub : ∀ v ∈ lmSS a' d p (j + 1) (m : ℤ), (v : WithBot ℝ) ≤
              max (max (eq3 a' d p (j + 1) ((m : ℤ) - 1)) (eq3 a' d p j (m : ℤ)))
                ((p ⟨j, hjn⟩ : WithBot ℝ) + eq3 a' d p j ((m : ℤ) - (a' ⟨j, hjn⟩ : ℤ))) := by
            intro v hv
            rcases lm_split_mem a' d p j hjn _ hv with h | ⟨v', hv', rfl⟩
            · have : v ≤ V1 := hG1.2 h
              calc (v : WithBot ℝ) ≤ (V1 : WithBot ℝ) := WithBot.coe_le_coe.2 this
                _ = eq3 a' d p j (m : ℤ) := hV1.symm
                _ ≤ _ := le_trans (le_max_right _ _) (le_max_left _ _)
            · have ha : (a' ⟨j, hjn⟩ : ℤ) ≤ m := by
                obtain ⟨x, _, _, h3, _⟩ := hv'
                have : (0 : ℤ) ≤ ((∑ i, a' i * (x i).toNat : ℕ) : ℤ) := by positivity
                omega
              obtain ⟨V2, e2, g2⟩ := (ih' ((m : ℤ) - (a' ⟨j, hjn⟩ : ℤ))).2 (by omega)
              have : v' ≤ V2 := g2.2 hv'
              calc ((p ⟨j, hjn⟩ + v' : ℝ) : WithBot ℝ)
                  = (p ⟨j, hjn⟩ : WithBot ℝ) + (v' : WithBot ℝ) := by rw [WithBot.coe_add]
                _ ≤ (p ⟨j, hjn⟩ : WithBot ℝ) + eq3 a' d p j ((m : ℤ) - (a' ⟨j, hjn⟩ : ℤ)) := by
                    rw [e2]; exact add_le_add le_rfl (WithBot.coe_le_coe.2 this)
                _ ≤ _ := le_max_right _ _
          rw [hV1]; rw [hV1] at hub
          generalize eq3 a' d p (j + 1) ((m : ℤ) - 1) = E3 at h3 hub ⊢
          generalize eq3 a' d p j ((m : ℤ) - (a' ⟨j, hjn⟩ : ℤ)) = E2 at h2 hub ⊢
          generalize hpp : (p ⟨j, hjn⟩ : WithBot ℝ) = P at hub ⊢
          have hM : max (max E3 (V1 : WithBot ℝ)) (P + E2) = E3 ∨ max (max E3 (V1 : WithBot ℝ)) (P + E2) = (V1 : WithBot ℝ) ∨
                max (max E3 (V1 : WithBot ℝ)) (P + E2) = P + E2 := by
            rcases max_choice (max E3 (V1 : WithBot ℝ)) (P + E2) with h | h
            · rcases max_choice E3 (V1 : WithBot ℝ) with h' | h'
              · left; rw [h, h']
              · right; left; rw [h, h']
            · right; right; exact h
          have hne : max (max E3 (V1 : WithBot ℝ)) (P + E2) ≠ ⊥ := by
            intro h
            have : (V1 : WithBot ℝ) ≤ max (max E3 (V1 : WithBot ℝ)) (P + E2) :=
              le_trans (le_max_right _ _) (le_max_left _ _)
            rw [h] at this
            simp at this
          have hatt : ∃ v ∈ lmSS a' d p (j + 1) (m : ℤ),
              max (max E3 (V1 : WithBot ℝ)) (P + E2) = (v : WithBot ℝ) := by
            rcases hM with h | h | h
            · rw [h] at hne ⊢
              rcases h3 with h3 | h3
              · exact absurd h3 hne
              · exact h3
            · rw [h]
              exact ⟨V1, lm_emb1 a' d p j hjn _ htd hG1.1, rfl⟩
            · rw [h] at hne ⊢
              rcases h2 with h2 | ⟨v, hv, e⟩
              · rw [h2] at hne; simp at hne
              · refine ⟨p ⟨j, hjn⟩ + v, lm_emb2 a' d p j hjn _ htd hv, ?_⟩
                rw [e, ← hpp, WithBot.coe_add]
          obtain ⟨v, hv, hvM⟩ := hatt
          refine ⟨v, hvM, hv, fun w hw => ?_⟩
          have := hub w hw
          rw [hvM] at this
          exact WithBot.coe_le_coe.1 this
        · rw [if_neg htd]
          obtain ⟨V, e, g⟩ := IH (d ⟨j, hjn⟩) (by omega)
          refine ⟨V, e, ?_⟩
          have hset : lmSS a' d p (j + 1) (m : ℤ) = lmSS a' d p (j + 1) ((d ⟨j, hjn⟩ : ℕ) : ℤ) := by
            ext v
            exact ⟨lm_cut a' d p j hjn _, lm_mono_t a' d p (j + 1) (by omega)⟩
          rw [hset]; exact g
    intro t
    refine ⟨neg t, fun ht => ?_⟩
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ht
    exact pos m

theorem eq3_core {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hj : j ≤ n) (t : ℕ) :
    ∃ V : ℝ, eq3 a' d p j (t : ℤ) = (V : WithBot ℝ) ∧
      IsGreatest
        {v : ℝ | ∃ x : Fin n → Bool,
          (∀ i : Fin n, j ≤ i.val → x i = false) ∧
          (∀ k : Fin n, k.val < j →
            ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k) ∧
          ∑ i, a' i * (x i).toNat ≤ t ∧
          v = knapValue p x}
        V := by
  obtain ⟨V, e, g⟩ := ((lm_eq3_main a' d p j hj (t : ℤ)).2 (by omega))
  refine ⟨V, e, ?_⟩
  obtain ⟨⟨x, h1, h2, h3, h4⟩, hub⟩ := g
  refine ⟨⟨x, h1, h2, by exact_mod_cast h3, h4⟩, ?_⟩
  rintro w ⟨y, k1, k2, k3, k4⟩
  exact hub ⟨y, k1, k2, by exact_mod_cast k3, k4⟩

end eq3v

section sched

theorem lm_ct_def {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (l : List ι) (j : ι) :
    completionTime t l j = ((l.take (l.idxOf j + 1)).map t).sum := rfl

theorem lm_ct_append_left {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (A B : List ι) (j : ι)
    (hj : j ∈ A) : completionTime t (A ++ B) j = completionTime t A j := by
  simp only [lm_ct_def, List.idxOf_append_of_mem hj]
  rw [List.take_append_of_le_length]
  have := List.idxOf_lt_length_of_mem hj
  omega

theorem lm_mem_lateSet {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (l : List ι) (j : ι) :
    j ∈ lateSet t D l ↔ j ∈ l ∧ D j < completionTime t l j := by
  simp [lateSet]

theorem lm_ct_split {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s u : List ι) (j : ι)
    (hnd : (s ++ j :: u).Nodup) :
    completionTime t (s ++ j :: u) j = (s.map t).sum + t j := by
  have hj : j ∉ s := by
    intro h
    have := List.nodup_append.1 hnd
    exact this.2.2 j h j (List.mem_cons_self) rfl
  have e : (s ++ j :: u).take (s.length + 1) = s ++ [j] := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  rw [lm_ct_def, List.idxOf_append_of_notMem hj, List.idxOf_cons_self, Nat.add_zero, e]
  simp

theorem lm_key {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (l : List ι)
    (hl : l.Nodup) (X : Finset ι) (hX : X.Nonempty) (hXl : ∀ i ∈ X, i ∈ l) :
    ∃ m ∈ X, ∑ i ∈ X, t i ≤ completionTime t l m := by
  obtain ⟨m, hmX, hmax⟩ := Finset.exists_max_image X (fun i => l.idxOf i) hX
  refine ⟨m, hmX, ?_⟩
  have hsub : X ⊆ (l.take (l.idxOf m + 1)).toFinset := by
    intro i hi
    rw [List.mem_toFinset]
    have hil := hXl i hi
    have h1 : l.idxOf i < l.length := List.idxOf_lt_length_of_mem hil
    have h2 : l.idxOf i < l.idxOf m + 1 := by have := hmax i hi; omega
    rw [List.mem_iff_getElem]
    refine ⟨l.idxOf i, by simp [List.length_take]; omega, ?_⟩
    simp [List.getElem_take]
  calc ∑ i ∈ X, t i ≤ ∑ i ∈ (l.take (l.idxOf m + 1)).toFinset, t i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => ht i)
    _ = ((l.take (l.idxOf m + 1)).map t).sum :=
        List.sum_toFinset t ((hl.sublist (List.take_sublist _ _)))
    _ = completionTime t l m := rfl


theorem lm_edd_core {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (l : List (Fin n)) (hl : IsSchedule Finset.univ l) :
    ∃ E : List (Fin n),
      E.Nodup ∧
      (∀ j, j ∈ E ↔ j ∉ lateSet (fun i => (a' i : ℝ)) (fun i => (d i : ℝ)) l) ∧
      E.Pairwise (fun i j => d i ≤ d j) ∧
      ∀ L : List (Fin n), IsSchedule Finset.univ (E ++ L) →
        (∀ j ∈ E, j ∉ lateSet (fun i => (a' i : ℝ)) (fun i => (d i : ℝ)) (E ++ L)) ∧
        weightedTardy a' d p (E ++ L) ≤ weightedTardy a' d p l := by
  set t : Fin n → ℝ := fun i => (a' i : ℝ) with ht_def
  set D : Fin n → ℝ := fun i => (d i : ℝ) with hD_def
  have ht0 : ∀ i, 0 ≤ t i := fun i => Nat.cast_nonneg _
  have hmem : ∀ j, j ∈ l := fun j => (hl.2 j).2 (Finset.mem_univ j)
  set A : List (Fin n) := l.filter (fun j => decide (j ∉ lateSet t D l)) with hA
  set E : List (Fin n) := A.mergeSort (fun i j => decide (d i ≤ d j)) with hE
  have hperm : E.Perm A := List.mergeSort_perm _ _
  have hAnd : A.Nodup := hl.1.filter _
  have hEnd : E.Nodup := hperm.nodup_iff.2 hAnd
  have hEmem : ∀ j, j ∈ E ↔ j ∉ lateSet t D l := by
    intro j
    rw [hperm.mem_iff, hA, List.mem_filter]
    simp [hmem j]
  have hEpw : E.Pairwise (fun i j => d i ≤ d j) := by
    have := List.pairwise_mergeSort (le := fun i j => decide (d i ≤ d j))
      (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) A
    simpa using this
  have hEok : ∀ j ∈ E, completionTime t E j ≤ D j := by
    intro j hj
    obtain ⟨s, u, hsu⟩ := List.append_of_mem hj
    have hnd : (s ++ j :: u).Nodup := hsu ▸ hEnd
    have hjs : j ∉ s := by
      intro h
      have := List.nodup_append.1 hnd
      exact this.2.2 j h j (List.mem_cons_self) rfl
    have hsnd : s.Nodup := (List.nodup_append.1 hnd).1
    rw [hsu, lm_ct_split t s u j hnd]
    set X : Finset (Fin n) := insert j s.toFinset with hX
    have hsum : ∑ i ∈ X, t i = (s.map t).sum + t j := by
      rw [hX, Finset.sum_insert (by simpa using hjs), List.sum_toFinset t hsnd]
      ring
    obtain ⟨m, hmX, hm⟩ := lm_key t ht0 l hl.1 X ⟨j, Finset.mem_insert_self _ _⟩
      (fun i _ => hmem i)
    have hmE : m ∈ E := by
      rw [hsu]
      rcases Finset.mem_insert.1 hmX with h | h
      · rw [h]; simp
      · simp at h; simp [h]
    have hmon : m ∉ lateSet t D l := (hEmem m).1 hmE
    have hmct : completionTime t l m ≤ D m := by
      rw [lm_mem_lateSet] at hmon
      push_neg at hmon
      exact hmon (hmem m)
    have hdm : d m ≤ d j := by
      rcases Finset.mem_insert.1 hmX with h | h
      · rw [h]
      · have hs : m ∈ s := by simpa using h
        have := hEpw
        rw [hsu, List.pairwise_append] at this
        exact this.2.2 m hs j (List.mem_cons_self)
    rw [← hsum]
    calc _ ≤ completionTime t l m := hm
      _ ≤ D m := hmct
      _ ≤ D j := by simp only [hD_def]; exact_mod_cast hdm
  refine ⟨E, hEnd, hEmem, hEpw, fun L _ => ?_⟩
  have hon : ∀ j ∈ E, j ∉ lateSet t D (E ++ L) := by
    intro j hj
    rw [lm_mem_lateSet, lm_ct_append_left t E L j hj]
    push_neg
    intro _
    exact hEok j hj
  refine ⟨hon, ?_⟩
  unfold weightedTardy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    by_contra hnot
    exact hon j ((hEmem j).2 hnot) hj
  · intro i _ _; exact hp i


theorem lm_sum_dec {ι : Type*} (S : Finset ι) (c : ι → ℕ) (q : ι → Prop) [DecidablePred q] :
    ∑ i ∈ S, c i * (decide (q i)).toNat = ∑ i ∈ S.filter q, c i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q i <;> simp [h]

theorem lm_sum_dec_real {ι : Type*} (S : Finset ι) (c : ι → ℝ) (q : ι → Prop) [DecidablePred q] :
    ∑ i ∈ S, c i * ((decide (q i)).toNat : ℝ) = ∑ i ∈ S.filter q, c i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q i <;> simp [h]

theorem lm_part1 {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ) (hd : Monotone d)
    (l : List (Fin n)) (hl : IsSchedule Finset.univ l) :
    ∃ x : Fin n → Bool, PrefixFeasible a' d x ∧
      (∑ j, p j) - knapValue p x ≤ weightedTardy a' d p l := by
  set t : Fin n → ℝ := fun i => (a' i : ℝ) with ht_def
  set D : Fin n → ℝ := fun i => (d i : ℝ) with hD_def
  have ht0 : ∀ i, 0 ≤ t i := fun i => Nat.cast_nonneg _
  have hmem : ∀ j, j ∈ l := fun j => (hl.2 j).2 (Finset.mem_univ j)
  set late := lateSet t D l with hlate
  refine ⟨fun j => decide (j ∉ late), ?_, ?_⟩
  · intro k
    set X : Finset (Fin n) := Finset.univ.filter (fun i => i ≤ k ∧ i ∉ late) with hX
    have hsumX : ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), a' i * (decide (i ∉ late)).toNat
        = ∑ i ∈ X, a' i := by
      rw [lm_sum_dec, Finset.filter_filter]
    rw [hsumX]
    by_cases hXe : X = ∅
    · rw [hXe]; simp
    · obtain ⟨m, hmX, hm⟩ := lm_key t ht0 l hl.1 X (Finset.nonempty_iff_ne_empty.2 hXe)
        (fun i _ => hmem i)
      have hmX' := (Finset.mem_filter.1 hmX).2
      have hmct : completionTime t l m ≤ D m := by
        have := hmX'.2
        rw [hlate, lm_mem_lateSet] at this
        push_neg at this
        exact this (hmem m)
      have hdm : d m ≤ d k := hd hmX'.1
      have : ∑ i ∈ X, t i ≤ (d k : ℝ) :=
        le_trans hm (le_trans hmct (by simp only [hD_def]; exact_mod_cast hdm))
      have h2 : ((∑ i ∈ X, a' i : ℕ) : ℝ) ≤ (d k : ℝ) := by
        push_cast; exact this
      exact_mod_cast h2
  · have h1 : knapValue p (fun j => decide (j ∉ late)) = ∑ j ∈ Finset.univ.filter (fun j => j ∉ late), p j := by
      unfold knapValue
      exact lm_sum_dec_real _ _ _
    have h2 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ late) p
    have h3 : Finset.univ.filter (fun j => j ∈ late) = late := by ext; simp
    unfold weightedTardy
    rw [h1]
    rw [h3] at h2
    simp only [← hlate] at *
    linarith


theorem lm_sum_bool {ι : Type*} (S : Finset ι) (c : ι → ℕ) (y : ι → Bool) :
    ∑ i ∈ S, c i * (y i).toNat = ∑ i ∈ S.filter (fun i => y i = true), c i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases h : y i <;> simp

theorem lm_sum_bool_real {ι : Type*} (S : Finset ι) (c : ι → ℝ) (y : ι → Bool) :
    ∑ i ∈ S, c i * ((y i).toNat : ℝ) = ∑ i ∈ S.filter (fun i => y i = true), c i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases h : y i <;> simp

theorem lm_part2 {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (x : Fin n → Bool) (hx : PrefixFeasible a' d x) :
    ∃ l : List (Fin n), IsSchedule Finset.univ l ∧
      weightedTardy a' d p l ≤ (∑ j, p j) - knapValue p x := by
  set t : Fin n → ℝ := fun i => (a' i : ℝ) with ht_def
  set D : Fin n → ℝ := fun i => (d i : ℝ) with hD_def
  set E : List (Fin n) := (List.finRange n).filter (fun j => x j) with hE
  set F : List (Fin n) := (List.finRange n).filter (fun j => !x j) with hF
  have hperm : (E ++ F).Perm (List.finRange n) := List.filter_append_perm _ _
  have hsch : IsSchedule Finset.univ (E ++ F) :=
    ⟨hperm.nodup_iff.2 (List.nodup_finRange n), fun j => by simp [hperm.mem_iff]⟩
  have hEs : E.Pairwise (· < ·) := (List.pairwise_lt_finRange n).filter _
  have hEnd : E.Nodup := (List.nodup_finRange n).filter _
  have hEmem : ∀ j, j ∈ E ↔ x j = true := by intro j; simp [hE]
  have hEok : ∀ j ∈ E, completionTime t (E ++ F) j ≤ D j := by
    intro j hj
    rw [lm_ct_append_left t E F j hj]
    obtain ⟨s, u, hsu⟩ := List.append_of_mem hj
    have hnd : (s ++ j :: u).Nodup := hsu ▸ hEnd
    have hsnd : s.Nodup := (List.nodup_append.1 hnd).1
    have hjs : j ∉ s := by
      intro h
      have := List.nodup_append.1 hnd
      exact this.2.2 j h j (List.mem_cons_self) rfl
    have hpw := hEs
    rw [hsu, List.pairwise_append] at hpw
    have hlts : ∀ i ∈ s, i < j := fun i hi => hpw.2.2 i hi j (List.mem_cons_self)
    have hltu : ∀ i ∈ u, j < i := fun i hi => (List.pairwise_cons.1 hpw.2.1).1 i hi
    rw [hsu, lm_ct_split t s u j hnd]
    have hY : insert j s.toFinset = Finset.univ.filter (fun i => i ≤ j ∧ x i = true) := by
      ext i
      simp only [Finset.mem_insert, List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | hi)
        · exact ⟨le_rfl, (hEmem i).1 hj⟩
        · refine ⟨le_of_lt (hlts i hi), (hEmem i).1 ?_⟩
          rw [hsu]; simp [hi]
      · rintro ⟨hij, hxi⟩
        have : i ∈ s ++ j :: u := by rw [← hsu]; exact (hEmem i).2 hxi
        rcases List.mem_append.1 this with h | h
        · right; exact h
        · rcases List.mem_cons.1 h with h | h
          · left; exact h
          · exact absurd (hltu i h) (not_lt.2 hij)
    have hsum : (s.map t).sum + t j = ∑ i ∈ insert j s.toFinset, t i := by
      rw [Finset.sum_insert (by simpa using hjs), List.sum_toFinset t hsnd]
      ring
    have h1 := hx j
    rw [lm_sum_bool, Finset.filter_filter] at h1
    rw [hsum, hY]
    have h2 : ((∑ i ∈ Finset.univ.filter (fun i => i ≤ j ∧ x i = true), a' i : ℕ) : ℝ) ≤ (d j : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    exact h2
  refine ⟨E ++ F, hsch, ?_⟩
  have hsub : lateSet t D (E ++ F) ⊆ Finset.univ.filter (fun j => ¬ (x j = true)) := by
    intro j hj
    rw [lm_mem_lateSet] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hxj
    have := hEok j ((hEmem j).2 hxj)
    linarith [hj.2]
  have h2 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => x j = true) p
  have h1 : knapValue p x = ∑ j ∈ Finset.univ.filter (fun j => x j = true), p j := by
    unfold knapValue; exact lm_sum_bool_real _ _ _
  unfold weightedTardy
  calc ∑ j ∈ lateSet t D (E ++ F), p j ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ (x j = true)), p j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hp i)
    _ = (∑ j, p j) - knapValue p x := by rw [h1]; linarith



theorem lm_goal {n : ℕ} (hn : 0 < n) (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hd : Monotone d) :
    ∃ V : ℝ, eq3 a' d p n (d ⟨n - 1, by omega⟩ : ℤ) = (V : WithBot ℝ) ∧
      IsLeast {w : ℝ | ∃ l : List (Fin n), IsSchedule Finset.univ l ∧ w = weightedTardy a' d p l}
        ((∑ j, p j) - V) := by
  obtain ⟨V, hV, hG⟩ := eq3_core a' d p n le_rfl (d ⟨n - 1, by omega⟩)
  refine ⟨V, hV, ?_⟩
  have hB : ∀ x : Fin n → Bool, PrefixFeasible a' d x → knapValue p x ≤ V := by
    intro x hx
    apply hG.2
    refine ⟨x, fun i hi => absurd i.isLt (by omega), fun k _ => hx k, ?_, rfl⟩
    rw [lm_T a' x (n - 1) ⟨n - 1, by omega⟩ rfl (fun i hi => absurd i.isLt (by omega))]
    exact hx _
  obtain ⟨x0, _, hx0, _, hx0v⟩ := hG.1
  have hx0' : PrefixFeasible a' d x0 := fun k => hx0 k k.isLt
  have hlow : ∀ l : List (Fin n), IsSchedule Finset.univ l →
      (∑ j, p j) - V ≤ weightedTardy a' d p l := by
    intro l hl
    obtain ⟨x, hxf, hxl⟩ := lm_part1 a' d p hd l hl
    have := hB x hxf
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hl, hlw⟩ := lm_part2 a' d p hp x0 hx0'
    refine ⟨l, hl, ?_⟩
    have := hlow l hl
    rw [← hx0v] at hlw
    linarith
  · rintro w ⟨l, hl, rfl⟩
    exact hlow l hl

end sched
end LawlerMoore.WeightedTardy

open LawlerMoore.WeightedTardy
open MooreLateJobs.Shared MooreLateJobs.NumLate

theorem solution {n : ℕ} (hn : 0 < n) (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hd : Monotone d) :
    ∃ V : ℝ, eq3 a' d p n (d ⟨n - 1, by omega⟩ : ℤ) = (V : WithBot ℝ) ∧
      IsLeast {w : ℝ | ∃ l : List (Fin n), IsSchedule Finset.univ l ∧ w = weightedTardy a' d p l}
        ((∑ j, p j) - V) := by
  exact lm_goal hn a' d p hp hd
