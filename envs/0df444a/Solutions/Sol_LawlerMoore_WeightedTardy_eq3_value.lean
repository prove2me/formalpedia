-- Prove2me | solution 1 for LawlerMoore.WeightedTardy.eq3_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:08:51.727445+00:00
-- url     : https://prove2.me/submissions/996729f1-cee3-4625-b124-9a2b576264cd

import Mathlib
import Definitions.Def_LawlerMoore_WeightedTardy_PrefixFeasible
import Definitions.Def_LawlerMoore_WeightedTardy_eq3



namespace LawlerMoore.WeightedTardy
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
end LawlerMoore.WeightedTardy

open LawlerMoore.WeightedTardy


theorem solution {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ) (j : ℕ) (hj : j ≤ n) (t : ℕ) :
    ∃ V : ℝ, eq3 a' d p j (t : ℤ) = (V : WithBot ℝ) ∧
      IsGreatest
        {v : ℝ | ∃ x : Fin n → Bool,
          (∀ i : Fin n, j ≤ i.val → x i = false) ∧
          (∀ k : Fin n, k.val < j →
            ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), a' i * (x i).toNat ≤ d k) ∧
          ∑ i, a' i * (x i).toNat ≤ t ∧
          v = knapValue p x}
        V := by
  exact eq3_core a' d p j hj t
