-- Prove2me | solution 1 for MaxPressure.ReversedLeontief.pressure_split_by_processor
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:22:15.66871+00:00
-- url     : https://prove2.me/submissions/76c227d3-c181-4463-ac82-0e6ca9d0b75d

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network



namespace MaxPressure.ReversedLeontief

open Classical

lemma rl_A_nonneg {I J K : ℕ} (N : Network I J K) (hN : N.Standing) (k : Fin K) (j : Fin J) :
    0 ≤ N.A k j := by
  rcases hN.1 k j with h | h <;> rw [h] <;> norm_num

lemma rl_le_one {I J K : ℕ} (N : Network I J K) (hN : N.Standing) {b : Fin J → ℝ}
    (hb : b ∈ allocSet N) (j : Fin J) : b j ≤ 1 := by
  obtain ⟨k, hk⟩ := hN.2.2.2.2.1 j
  have h1 := hb.2.1 k
  have h2 : N.A k j * b j ≤ ∑ j', N.A k j' * b j' :=
    Finset.single_le_sum (f := fun j' => N.A k j' * b j')
      (fun j' _ => mul_nonneg (rl_A_nonneg N hN k j') (hb.1 j')) (Finset.mem_univ j)
  rw [hk, one_mul] at h2
  linarith

lemma rl_int01 {I J K : ℕ} (N : Network I J K) (hN : N.Standing) {a : Fin J → ℝ}
    (ha : a ∈ intAllocs N) (j : Fin J) : a j = 0 ∨ a j = 1 := by
  obtain ⟨n, hn⟩ := ha.2 j
  have h1 := rl_le_one N hN ha.1 j
  rw [hn] at h1 ⊢
  have : n ≤ 1 := by exact_mod_cast h1
  interval_cases n <;> simp

theorem rl_int_sub_ext {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    intAllocs N ⊆ extremeAllocs N := by
  intro a ha
  rw [extremeAllocs, mem_extremePoints]
  refine ⟨ha.1, ?_⟩
  intro x1 hx1 x2 hx2 hseg
  obtain ⟨t, s, ht, hs, hts, hx⟩ := hseg
  have key : ∀ j, x1 j = a j ∧ x2 j = a j := by
    intro j
    have hj := congrFun hx j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
    have h1 := rl_le_one N hN hx1 j
    have h2 := rl_le_one N hN hx2 j
    have h3 := hx1.1 j
    have h4 := hx2.1 j
    rcases rl_int01 N hN ha j with h | h <;> rw [h] at hj ⊢
    · constructor
      · apply le_antisymm _ h3
        nlinarith [mul_nonneg hs.le h4]
      · apply le_antisymm _ h4
        nlinarith [mul_nonneg ht.le h3]
    · constructor
      · apply le_antisymm h1
        nlinarith [mul_nonneg hs.le (sub_nonneg.2 h2)]
      · apply le_antisymm h2
        nlinarith [mul_nonneg ht.le (sub_nonneg.2 h1)]
  exact ⟨funext fun j => (key j).1, funext fun j => (key j).2⟩

lemma rl_other_zero {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) {k k' : Fin K} {j : Fin J}
    (h : N.A k j = 1) (hk : k' ≠ k) : N.A k' j = 0 := by
  rcases hN.1 k' j with h' | h'
  · exact h'
  · exact absurd ((hRL j).unique h' h) hk

theorem rl_ext_sub_int {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) : extremeAllocs N ⊆ intAllocs N := by
  intro a ha
  rw [extremeAllocs, mem_extremePoints] at ha
  have haA := ha.1
  refine ⟨haA, ?_⟩
  suffices h01 : ∀ j, a j = 0 ∨ a j = 1 by
    intro j; rcases h01 j with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  intro j
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < a j := lt_of_le_of_ne (haA.1 j) (Ne.symm hcon.1)
  have hlt : a j < 1 := lt_of_le_of_ne (rl_le_one N hN haA j) hcon.2
  obtain ⟨k, hk⟩ := hN.2.2.2.2.1 j
  have pert : ∀ b c : Fin J → ℝ, b ∈ allocSet N → c ∈ allocSet N →
      (∀ j', b j' + c j' = 2 * a j') → b j ≠ a j → False := by
    intro b c hb hc hbc hne
    have h := (ha.2 b hb c hc ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith [hbc i]⟩).1
    exact hne (congrFun h j)
  have hs1 : ∑ j', N.A k j' * a j' ≤ 1 := haA.2.1 k
  rcases lt_or_eq_of_le hs1 with hslt | hseq
  · -- processor k has slack
    have hnin : ¬ N.inputProc k := fun hin => by linarith [haA.2.2 k hin]
    set δ := min (a j) (1 - ∑ j', N.A k j' * a j') with hδ
    have hδpos : 0 < δ := lt_min hpos (by linarith)
    have hδ1 : δ ≤ a j := min_le_left _ _
    have hδ2 : δ ≤ 1 - ∑ j', N.A k j' * a j' := min_le_right _ _
    have mem : ∀ c : ℝ, -δ ≤ c → c ≤ δ →
        (fun j' => a j' + c * (if j' = j then 1 else 0)) ∈ allocSet N := by
      intro c hc1 hc2
      have hsum : ∀ k', ∑ j', N.A k' j' * (a j' + c * (if j' = j then 1 else 0)) =
          ∑ j', N.A k' j' * a j' + c * N.A k' j := by
        intro k'
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
        simp [Finset.sum_ite_eq', mul_comm]
      refine ⟨?_, ?_, ?_⟩
      · intro j'
        by_cases h : j' = j
        · subst h; simp; linarith
        · simp [h]; exact haA.1 j'
      · intro k'
        rw [hsum]
        by_cases hkk : k' = k
        · subst hkk; rw [hk]; linarith
        · rw [rl_other_zero N hN hRL hk hkk]; simpa using haA.2.1 k'
      · intro k' hin
        rw [hsum]
        have hkk : k' ≠ k := fun h => hnin (h ▸ hin)
        rw [rl_other_zero N hN hRL hk hkk]; simpa using haA.2.2 k' hin
    exact pert _ _ (mem δ (by linarith) le_rfl) (mem (-δ) le_rfl (by linarith))
      (fun j' => by ring) (by simp; exact hδpos.ne')
  · -- processor k is saturated: find another active activity
    obtain ⟨j2, hj2ne, hj2k, hj2pos⟩ : ∃ j2, j2 ≠ j ∧ N.A k j2 = 1 ∧ 0 < a j2 := by
      by_contra hno
      push_neg at hno
      have : ∑ j', N.A k j' * a j' = N.A k j * a j := by
        apply Finset.sum_eq_single j
        · intro j' _ hj'
          rcases hN.1 k j' with h | h
          · rw [h, zero_mul]
          · have := hno j' hj' h
            have := haA.1 j'
            rw [h, one_mul]; linarith
        · simp
      rw [this, hk, one_mul] at hseq
      linarith
    set δ := min (a j) (a j2) with hδ
    have hδpos : 0 < δ := lt_min hpos hj2pos
    have hδ1 : δ ≤ a j := min_le_left _ _
    have hδ2 : δ ≤ a j2 := min_le_right _ _
    have mem : ∀ c : ℝ, -δ ≤ c → c ≤ δ →
        (fun j' => a j' + c * ((if j' = j then 1 else 0) - (if j' = j2 then 1 else 0)))
          ∈ allocSet N := by
      intro c hc1 hc2
      have hsum : ∀ k', ∑ j', N.A k' j' *
          (a j' + c * ((if j' = j then 1 else 0) - (if j' = j2 then 1 else 0))) =
          ∑ j', N.A k' j' * a j' := by
        intro k'
        have e : ∑ j', N.A k' j' *
            (a j' + c * ((if j' = j then 1 else 0) - (if j' = j2 then 1 else 0))) =
            ∑ j', N.A k' j' * a j' + c * (N.A k' j - N.A k' j2) := by
          simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
            mul_one, mul_zero]
          simp [Finset.sum_ite_eq', mul_comm, mul_sub]
        rw [e]
        by_cases hkk : k' = k
        · subst hkk; rw [hk, hj2k]; ring
        · rw [rl_other_zero N hN hRL hk hkk, rl_other_zero N hN hRL hj2k hkk]; ring
      refine ⟨?_, ?_, ?_⟩
      · intro j'
        by_cases h : j' = j
        · subst h; simp [hj2ne.symm]; linarith
        · by_cases h2 : j' = j2
          · subst h2; simp [h]; linarith
          · simp [h, h2]; exact haA.1 j'
      · intro k'
        rw [hsum]; exact haA.2.1 k'
      · intro k' hin
        rw [hsum]; exact haA.2.2 k' hin
    exact pert _ _ (mem δ (by linarith) le_rfl) (mem (-δ) le_rfl (by linarith))
      (fun j' => by ring) (by simp [hj2ne.symm]; exact hδpos.ne')

theorem extremeAllocs_eq_intAllocs_core {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) :
    extremeAllocs N = intAllocs N :=
  Set.Subset.antisymm (rl_ext_sub_int N hN hRL) (rl_int_sub_ext N hN)

lemma rl_atmost_one {I J K : ℕ} (N : Network I J K) (hN : N.Standing) {a : Fin J → ℝ}
    (ha : a ∈ intAllocs N) {k : Fin K} {j j' : Fin J} (hj : N.A k j = 1) (hj' : N.A k j' = 1)
    (haj : a j = 1) (haj' : a j' = 1) : j = j' := by
  by_contra hne
  have h1 := ha.1.2.1 k
  have h2 : ∑ x ∈ ({j, j'} : Finset (Fin J)), N.A k x * a x ≤ ∑ x, N.A k x * a x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => mul_nonneg (rl_A_nonneg N hN k x) (ha.1.1 x))
  rw [Finset.sum_pair hne, hj, hj', haj, haj'] at h2
  linarith

lemma rl_act_A {I J K : ℕ} (N : Network I J K) {a : Fin J → ℝ} {k : Fin K} {j : Fin J}
    (h : activityOf N a k = some j) : N.A k j = 1 ∧ a j = 1 := by
  unfold activityOf at h
  split_ifs at h with hex
  · cases h; exact hex.choose_spec

lemma rl_act_iff {I J K : ℕ} (N : Network I J K) (hN : N.Standing) {a : Fin J → ℝ}
    (ha : a ∈ intAllocs N) {k : Fin K} {j : Fin J} (hj : N.A k j = 1) :
    activityOf N a k = some j ↔ a j = 1 := by
  constructor
  · intro h; exact (rl_act_A N h).2
  · intro h
    unfold activityOf
    have hex : ∃ j, N.A k j = 1 ∧ a j = 1 := ⟨j, hj, h⟩
    rw [dif_pos hex]
    congr 1
    exact rl_atmost_one N hN ha hex.choose_spec.1 hj hex.choose_spec.2 h

lemma rl_unitVec_apply {J : ℕ} (o : Option (Fin J)) (j : Fin J) :
    unitVec o j = if o = some j then 1 else 0 := by
  cases o with
  | none => simp [unitVec]
  | some j' => simp [unitVec, Pi.single_apply, eq_comm]

lemma rl_decomp {I J K : ℕ} (N : Network I J K) (hN : N.Standing) (hRL : IsReversedLeontief N)
    {a : Fin J → ℝ} (ha : a ∈ intAllocs N) (j : Fin J) :
    a j = ∑ k, unitVec (activityOf N a k) j := by
  obtain ⟨k0, hk0⟩ := hN.2.2.2.2.1 j
  rw [Finset.sum_eq_single k0]
  · rw [rl_unitVec_apply]
    split_ifs with h
    · exact (rl_act_iff N hN ha hk0).1 h
    · rcases rl_int01 N hN ha j with h' | h'
      · exact h'
      · exact absurd ((rl_act_iff N hN ha hk0).2 h') h
  · intro k _ hk
    rw [rl_unitVec_apply, if_neg]
    intro h
    exact hk ((hRL j).unique (rl_act_A N h).1 hk0)
  · simp

lemma rl_pressure_eq {I J K : ℕ} (N : Network I J K) (a : Fin J → ℝ) (z : Fin I → ℝ) :
    pressure N a z = ∑ j, a j * actPressure N j z := by
  simp only [pressure, actPressure, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))

lemma rl_pressure_unitVec {I J K : ℕ} (N : Network I J K) (o : Option (Fin J)) (z : Fin I → ℝ) :
    pressure N (unitVec o) z = actPressure' N o z := by
  rw [rl_pressure_eq]
  cases o with
  | none => simp [unitVec, actPressure']
  | some j' => simp [unitVec, actPressure', Pi.single_apply]

theorem pressure_split_by_processor_core {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) (a : Fin J → ℝ) (ha : a ∈ extremeAllocs N) :
    (∀ k, activityOf N a k ∈ procActs N k) ∧
    ∀ z : Fin I → ℝ, pressure N a z = ∑ k, actPressure' N (activityOf N a k) z := by
  have hi := rl_ext_sub_int N hN hRL ha
  constructor
  · intro k
    by_cases hex : ∃ j, N.A k j = 1 ∧ a j = 1
    · have h : activityOf N a k = some hex.choose := by
        unfold activityOf; rw [dif_pos hex]
      rw [h]
      exact Or.inr ⟨hex.choose, rfl, hex.choose_spec.1⟩
    · have h : activityOf N a k = none := by
        unfold activityOf; rw [dif_neg hex]
      rw [h]
      refine Or.inl ⟨rfl, fun hin => ?_⟩
      have hs := hi.1.2.2 k hin
      have : ∑ j, N.A k j * a j = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rcases hN.1 k j with h1 | h1
        · rw [h1, zero_mul]
        · rcases rl_int01 N hN hi j with h2 | h2
          · rw [h2, mul_zero]
          · exact absurd ⟨j, h1, h2⟩ hex
      linarith
  · intro z
    rw [rl_pressure_eq]
    simp_rw [← rl_pressure_unitVec N _ z, rl_pressure_eq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_mul, ← rl_decomp N hN hRL hi j]

theorem single_processor_exchange_core {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) (a : Fin J → ℝ) (ha : a ∈ extremeAllocs N) (k : Fin K)
    (o : Option (Fin J)) (ho : o ∈ procActs N k) :
    a - unitVec (activityOf N a k) + unitVec o ∈ extremeAllocs N ∧
    ∀ z : Fin I → ℝ, pressure N (a - unitVec (activityOf N a k) + unitVec o) z =
      pressure N a z - actPressure' N (activityOf N a k) z + actPressure' N o z := by
  have hi := rl_ext_sub_int N hN hRL ha
  constructor
  · apply rl_int_sub_ext N hN
    set b := a - unitVec (activityOf N a k) + unitVec o with hb
    have hbk : ∀ j, N.A k j = 1 → b j = if o = some j then 1 else 0 := by
      intro j hj
      simp only [hb, Pi.add_apply, Pi.sub_apply, rl_unitVec_apply]
      have e : a j = if activityOf N a k = some j then 1 else 0 := by
        split_ifs with h
        · exact (rl_act_iff N hN hi hj).1 h
        · rcases rl_int01 N hN hi j with h' | h'
          · exact h'
          · exact absurd ((rl_act_iff N hN hi hj).2 h') h
      rw [e]; ring
    have hbo : ∀ j, N.A k j ≠ 1 → b j = a j := by
      intro j hj
      simp only [hb, Pi.add_apply, Pi.sub_apply, rl_unitVec_apply]
      rw [if_neg (fun h => hj (rl_act_A N h).1), if_neg]
      · ring
      · intro h
        subst h
        rcases ho with ⟨h1, _⟩ | ⟨j', h1, h2⟩
        · cases h1
        · cases h1; exact hj h2
    have hsum_other : ∀ k', k' ≠ k → ∑ j, N.A k' j * b j = ∑ j, N.A k' j * a j := by
      intro k' hk'
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hj : N.A k j = 1
      · rw [rl_other_zero N hN hRL hj hk']; ring
      · rw [hbo j hj]
    have hsum_k : ∑ j, N.A k j * b j = if o = none then 0 else 1 := by
      have : ∀ j, N.A k j * b j = N.A k j * (if o = some j then 1 else 0) := by
        intro j
        by_cases hj : N.A k j = 1
        · rw [hbk j hj]
        · rw [hbo j hj]
          rcases hN.1 k j with h | h
          · rw [h]; ring
          · exact absurd h hj
      simp_rw [this]
      rcases ho with ⟨h1, _⟩ | ⟨j', h1, h2⟩
      · subst h1; simp
      · subst h1; simp [h2]
    have hb01 : ∀ j, b j = 0 ∨ b j = 1 := by
      intro j
      by_cases hj : N.A k j = 1
      · rw [hbk j hj]; split_ifs <;> simp
      · rw [hbo j hj]; exact rl_int01 N hN hi j
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro j; rcases hb01 j with h | h <;> rw [h] <;> norm_num
    · intro k'
      by_cases hk' : k' = k
      · subst hk'; rw [hsum_k]; split_ifs <;> norm_num
      · rw [hsum_other k' hk']; exact hi.1.2.1 k'
    · intro k' hin
      by_cases hk' : k' = k
      · subst hk'; rw [hsum_k]
        rcases ho with ⟨_, h2⟩ | ⟨j', h1, _⟩
        · exact absurd hin h2
        · subst h1; simp
      · rw [hsum_other k' hk']; exact hi.1.2.2 k' hin
    · intro j
      rcases hb01 j with h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
  · intro z
    rw [← rl_pressure_unitVec N (activityOf N a k) z, ← rl_pressure_unitVec N o z]
    simp only [rl_pressure_eq, Pi.add_apply, Pi.sub_apply, add_mul, sub_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]

end MaxPressure.ReversedLeontief

open MaxPressure.ReversedLeontief


theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) (a : Fin J → ℝ) (ha : a ∈ extremeAllocs N) :
    (∀ k, activityOf N a k ∈ procActs N k) ∧
    ∀ z : Fin I → ℝ, pressure N a z = ∑ k, actPressure' N (activityOf N a k) z := by
  exact pressure_split_by_processor_core N hN hRL a ha
