-- Prove2me | solution 1 for JohnsonApprox.SubsetSum.lowerBoundInput_spec
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T18:00:22.475231+00:00
-- url     : https://prove2.me/submissions/2968fc82-f23f-492e-844b-087a38d4147b

import Mathlib
import Definitions.Def_JohnsonApprox_SubsetSum_Problem
import Definitions.Def_JohnsonApprox_SubsetSum_Ak
import Definitions.Def_JohnsonApprox_SubsetSum_LowerBoundInput



namespace JohnsonApprox.SubsetSum

open Finset

variable {α : Type}

lemma measure_nonneg (u : Input α) (X : Finset α) (hX : X ⊆ u.T) : 0 ≤ measure u X :=
  sum_nonneg (fun x hx => (u.s_pos x (hX hx)).le)

lemma measure_mono (u : Input α) {X Y : Finset α} (hXY : X ⊆ Y) (hY : Y ⊆ u.T) :
    measure u X ≤ measure u Y :=
  sum_le_sum_of_subset_of_nonneg hXY (fun x hx _ => (u.s_pos x (hY hx)).le)

lemma opt_le_b (u : Input α) : opt u ≤ u.b := by
  unfold opt
  apply Finset.sup'_le
  intro T' hT'
  unfold feasibleSet at hT'
  exact (mem_filter.1 hT').2

lemma le_opt (u : Input α) (T' : Finset α) (h : IsFeasible u T') : measure u T' ≤ opt u := by
  unfold opt
  exact Finset.le_sup' (measure u) (by
    unfold feasibleSet; exact mem_filter.2 ⟨mem_powerset.2 h.1, h.2⟩)

/-- Invariants along a run of `A_k`. -/
lemma run_inv [DecidableEq α] (k : ℕ) (u : Input α) (S : Finset α) (hS : IsStep1Choice k u S)
    (σ : State α) (hr : Relation.ReflTransGen (Step u) (initState u S) σ) :
    σ.SUB ⊆ u.T ∧ σ.LEFT = u.T \ σ.SUB ∧ σ.SUM = measure u σ.SUB ∧ S ⊆ σ.SUB ∧
      bigPart k u σ.SUB = S ∧ measure u σ.SUB ≤ u.b := by
  obtain ⟨hSbig, hSb, hSmax⟩ := hS
  have hST : S ⊆ u.T := fun x hx => (mem_filter.1 (hSbig hx)).1
  induction hr with
  | refl =>
    refine ⟨hST, rfl, rfl, le_rfl, ?_, hSb⟩
    unfold bigPart
    apply filter_true_of_mem
    intro x hx
    exact (mem_filter.1 (hSbig hx)).2
  | @tail σ₁ σ₂ _ hstep ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    obtain ⟨_, y, hy, hfit, _, rfl⟩ := hstep
    rw [h2] at hy
    have hyT : y ∈ u.T := (mem_sdiff.1 hy).1
    have hyS : y ∉ σ₁.SUB := (mem_sdiff.1 hy).2
    have hunion : σ₁.SUB ∪ {y} = insert y σ₁.SUB := by
      rw [union_comm]; rfl
    have hmeas : measure u (σ₁.SUB ∪ {y}) = σ₁.SUM + u.s y := by
      rw [hunion, measure, sum_insert hyS, h3, measure]; ring
    -- y is not big
    have hsmall : ¬ (u.b / ((k : ℚ) + 1) < u.s y) := by
      intro hbig
      have hyS0 : y ∉ S := fun h => hyS (h4 h)
      have hsub : insert y S ⊆ bigElems k u := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_filter.2 ⟨hyT, hbig⟩
        · exact hSbig hx
      have hm : measure u (insert y S) = u.s y + measure u S := by
        rw [measure, sum_insert hyS0]; rfl
      have hmS : measure u S ≤ measure u σ₁.SUB := measure_mono u h4 h1
      have := hSmax (insert y S) hsub (by rw [hm]; rw [h3] at hfit; linarith)
      rw [hm] at this
      have := u.s_pos y hyT
      linarith
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases mem_union.1 hx with hx | hx
      · exact h1 hx
      · rw [mem_singleton.1 hx]; exact hyT
    · show σ₁.LEFT.erase y = u.T \ (σ₁.SUB ∪ {y})
      rw [h2]
      ext x
      simp only [mem_erase, mem_sdiff, mem_union, mem_singleton]
      tauto
    · show σ₁.SUM + u.s y = measure u (σ₁.SUB ∪ {y})
      rw [hmeas]
    · exact fun x hx => mem_union_left _ (h4 hx)
    · show bigPart k u (σ₁.SUB ∪ {y}) = S
      unfold bigPart at h5 ⊢
      rw [filter_union, h5]
      have : filter (fun x => u.b / ((k : ℚ) + 1) < u.s x) {y} = ∅ := by
        apply filter_eq_empty_iff.2
        intro x hx
        rw [mem_singleton.1 hx]; exact hsmall
      rw [this, union_empty]
    · show measure u (σ₁.SUB ∪ {y}) ≤ u.b
      rw [hmeas]; linarith

theorem excluded_small_does_not_fit {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k)
    (u : Input α) (T₁ : Finset α) (hT₁ : Choosable k u T₁) (x : α) (hxT : x ∈ u.T)
    (hxT₁ : x ∉ T₁) (hsmall : u.s x ≤ u.b / ((k : ℚ) + 1)) :
    u.b < u.s x + measure u T₁ ∧
      (k : ℚ) * u.b < ((k : ℚ) + 1) * measure u T₁ ∧
      (k : ℚ) * opt u ≤ ((k : ℚ) + 1) * measure u T₁ := by
  obtain ⟨S, hS, σ, hr, hhalt, hsub⟩ := hT₁
  obtain ⟨_, h2, h3, _, _, _⟩ := run_inv k u S hS σ hr
  have hxL : x ∈ σ.LEFT := by rw [h2, hsub]; exact mem_sdiff.2 ⟨hxT, hxT₁⟩
  have h1 : u.b < u.s x + measure u T₁ := by
    have := hhalt x hxL; rwa [h3, hsub] at this
  have hk1 : (0 : ℚ) < (k : ℚ) + 1 := by positivity
  have h2' : (k : ℚ) * u.b < ((k : ℚ) + 1) * measure u T₁ := by
    have hs : ((k : ℚ) + 1) * u.s x ≤ u.b := by
      rw [le_div_iff₀ hk1] at hsmall; linarith
    nlinarith
  refine ⟨h1, h2', ?_⟩
  have := opt_le_b u
  have hk0 : (0 : ℚ) ≤ k := by positivity
  nlinarith

theorem step1_big_dominates {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (u : Input α)
    (T₀ T₁ : Finset α) (hT₁ : Choosable k u T₁) (hT₀ : IsFeasible u T₀) :
    measure u (bigPart k u T₀) ≤ measure u (bigPart k u T₁) := by
  obtain ⟨S, hS, σ, hr, _, hsub⟩ := hT₁
  obtain ⟨_, _, _, _, h5, _⟩ := run_inv k u S hS σ hr
  rw [← hsub, h5]
  obtain ⟨_, _, hSmax⟩ := hS
  apply hSmax
  · intro x hx
    unfold bigPart at hx
    exact mem_filter.2 ⟨hT₀.1 (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
  · have : measure u (bigPart k u T₀) ≤ measure u T₀ :=
      measure_mono u (filter_subset _ _) hT₀.1
    linarith [hT₀.2]

theorem choosable_opt_or_large {α : Type} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (u : Input α)
    (T₁ : Finset α) (hT₁ : Choosable k u T₁) :
    measure u T₁ = opt u ∨ (k : ℚ) * u.b ≤ ((k : ℚ) + 1) * measure u T₁ := by
  by_cases hex : ∃ x ∈ u.T, x ∉ T₁ ∧ u.s x ≤ u.b / ((k : ℚ) + 1)
  · obtain ⟨x, hxT, hxT₁, hsmall⟩ := hex
    right
    exact (excluded_small_does_not_fit k hk u T₁ hT₁ x hxT hxT₁ hsmall).2.1.le
  · left
    push Not at hex
    obtain ⟨S, hS, σ, hr, hhalt, hsub⟩ := hT₁
    obtain ⟨h1, _, _, _, h5, h6⟩ := run_inv k u S hS σ hr
    rw [hsub] at h1 h5 h6
    have hT₁feas : IsFeasible u T₁ := ⟨h1, h6⟩
    apply le_antisymm (le_opt u T₁ hT₁feas)
    unfold opt
    apply Finset.sup'_le
    intro T₀ hT₀
    unfold feasibleSet at hT₀
    have hT₀f : IsFeasible u T₀ := ⟨mem_powerset.1 (mem_filter.1 hT₀).1, (mem_filter.1 hT₀).2⟩
    have hbig := step1_big_dominates k hk u T₀ T₁ ⟨S, hS, σ, hr, hhalt, hsub⟩ hT₀f
    -- split into big and small parts
    set p : α → Prop := fun x => u.b / ((k : ℚ) + 1) < u.s x
    have hsplit : ∀ X : Finset α, measure u X = measure u (bigPart k u X)
        + measure u (X.filter (fun x => ¬ p x)) := by
      intro X
      unfold measure bigPart
      exact (sum_filter_add_sum_filter_not X p _).symm
    rw [hsplit T₀, hsplit T₁]
    have hsm : measure u (T₀.filter (fun x => ¬ p x)) ≤ measure u (T₁.filter (fun x => ¬ p x)) := by
      apply measure_mono u
      · intro x hx
        rw [mem_filter] at hx ⊢
        refine ⟨?_, hx.2⟩
        by_contra hxn
        have := hex x (hT₀f.1 hx.1) hxn
        exact hx.2 this
      · exact fun x hx => h1 (mem_filter.1 hx).1
    linarith

/-! ### The lower-bound instance, generically -/

/-- A generic lower-bound instance: `T` with a distinguished `a0` of size `1 + ε`, all other
elements of size `1`, `|T| = k + 2` and `b = k + 1`. -/
structure LB (k : ℕ) (ε : ℚ) (u : Input α) (a0 : α) : Prop where
  ha0 : a0 ∈ u.T
  hsa0 : u.s a0 = 1 + ε
  hs1 : ∀ x ∈ u.T, x ≠ a0 → u.s x = 1
  hcard : u.T.card = k + 2
  hb : u.b = (k : ℚ) + 1

lemma LB.opt_eq [DecidableEq α] {k : ℕ} {ε : ℚ} {u : Input α} {a0 : α} (h : LB k ε u a0) :
    opt u = (k : ℚ) + 1 := by
  apply le_antisymm (h.hb ▸ opt_le_b u)
  obtain ⟨W, hW, hWc⟩ := exists_subset_card_eq (s := u.T.erase a0) (n := k + 1)
    (by rw [card_erase_of_mem h.ha0, h.hcard]; omega)
  have hWm : measure u W = (k : ℚ) + 1 := by
    unfold measure
    rw [sum_congr rfl (fun x hx => h.hs1 x (mem_of_mem_erase (hW hx)) (ne_of_mem_erase (hW hx))),
      sum_const, hWc, nsmul_eq_mul, mul_one]
    push_cast; ring
  rw [← hWm]
  exact le_opt u W ⟨fun x hx => mem_of_mem_erase (hW hx), by rw [hWm, h.hb]⟩

lemma LB.step1 [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) {ε : ℚ} (hε : 0 < ε) (hε1 : ε < 1)
    {u : Input α} {a0 : α} (h : LB k ε u a0) (S : Finset α) (hS : IsStep1Choice k u S) :
    S = {a0} := by
  obtain ⟨hSbig, hSb, hSmax⟩ := hS
  have hbig : ∀ x ∈ bigElems k u, x = a0 := by
    intro x hx
    rw [bigElems, mem_filter] at hx
    by_contra hne
    rw [h.hs1 x hx.1 hne, h.hb, div_self (by positivity)] at hx
    exact lt_irrefl _ hx.2
  have ha0big : a0 ∈ bigElems k u := by
    rw [bigElems, mem_filter, h.hsa0, h.hb, div_self (by positivity)]
    exact ⟨h.ha0, by linarith⟩
  have hsingle := hSmax {a0} (singleton_subset_iff.2 ha0big) (by
    rw [measure, sum_singleton, h.hsa0, h.hb]
    have : (1 : ℚ) ≤ k := by exact_mod_cast hk
    linarith)
  rw [measure, sum_singleton, h.hsa0] at hsingle
  have hSsub : S ⊆ {a0} := fun x hx => mem_singleton.2 (hbig x (hSbig hx))
  rcases subset_singleton_iff.1 hSsub with h0 | h0
  · rw [h0, measure, sum_empty] at hsingle; linarith
  · exact h0

/-- Every choosable set of the lower-bound instance has measure `k + ε`. -/
lemma LB.choosable_measure [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) {ε : ℚ} (hε : 0 < ε)
    (hε1 : ε < 1) {u : Input α} {a0 : α} (h : LB k ε u a0) (T₁ : Finset α)
    (hT₁ : Choosable k u T₁) : measure u T₁ = (k : ℚ) + ε := by
  obtain ⟨S, hS, σ, hr, hhalt, hsub⟩ := hT₁
  have hS0 := LB.step1 hk hε hε1 h S hS
  obtain ⟨h1, h2, h3, h4, _, h6⟩ := run_inv k u S hS σ hr
  rw [hS0] at h4
  have ha0 : a0 ∈ σ.SUB := h4 (mem_singleton_self _)
  set W := σ.SUB.erase a0 with hW
  have hmeas : measure u σ.SUB = 1 + ε + (W.card : ℚ) := by
    rw [measure, ← insert_erase ha0, sum_insert (notMem_erase _ _), h.hsa0, ← hW]
    rw [sum_congr rfl (fun x hx => h.hs1 x (h1 (mem_of_mem_erase hx)) (ne_of_mem_erase hx)),
      sum_const, nsmul_eq_mul, mul_one]
  -- upper bound on |W|
  have hup : (W.card : ℚ) ≤ (k : ℚ) - 1 := by
    have := h6; rw [hmeas, h.hb] at this
    have hint : W.card ≤ k - 1 := by
      by_contra hc
      push Not at hc
      have : (k : ℚ) ≤ W.card := by exact_mod_cast (by omega : k ≤ W.card)
      linarith
    have : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by push_cast [Nat.cast_sub hk]; ring
    rw [← this]; exact_mod_cast hint
  -- a unit element remains in LEFT
  have hunits : (u.T.erase a0).card = k + 1 := by rw [card_erase_of_mem h.ha0, h.hcard]; omega
  have hWsub : W ⊆ u.T.erase a0 := fun x hx =>
    mem_erase.2 ⟨ne_of_mem_erase hx, h1 (mem_of_mem_erase hx)⟩
  have hWlt : W.card < (u.T.erase a0).card := by
    rw [hunits]
    have : (W.card : ℚ) < (k : ℚ) + 1 := by linarith
    exact_mod_cast this
  obtain ⟨x, hx, hxW⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hWsub
    (fun he => by rw [he] at hWlt; exact lt_irrefl _ hWlt))
  have hxL : x ∈ σ.LEFT := by
    rw [h2]
    refine mem_sdiff.2 ⟨mem_of_mem_erase hx, fun hxS => hxW ?_⟩
    exact mem_erase.2 ⟨ne_of_mem_erase hx, hxS⟩
  have hlow := hhalt x hxL
  rw [h3, hmeas, h.hs1 x (mem_of_mem_erase hx) (ne_of_mem_erase hx), h.hb] at hlow
  have hWk : (W.card : ℚ) = (k : ℚ) - 1 := by
    have hint : k - 1 ≤ W.card := by
      by_contra hc
      push Not at hc
      have : (W.card : ℚ) + 1 ≤ ((k - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : W.card + 1 ≤ k - 1)
      push_cast [Nat.cast_sub hk] at this
      linarith
    have : ((k - 1 : ℕ) : ℚ) ≤ W.card := by exact_mod_cast hint
    push_cast [Nat.cast_sub hk] at this
    linarith
  rw [← hsub, hmeas, hWk]; ring

/-- A choosable set exists for the lower-bound instance. -/
lemma LB.exists_choosable [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) {ε : ℚ} (hε : 0 < ε)
    (hε1 : ε < 1) {u : Input α} {a0 : α} (h : LB k ε u a0) : ∃ T₁, Choosable k u T₁ := by
  have hS : IsStep1Choice k u {a0} := by
    have hbig : ∀ x ∈ bigElems k u, x = a0 := by
      intro x hx
      rw [bigElems, mem_filter] at hx
      by_contra hne
      rw [h.hs1 x hx.1 hne, h.hb, div_self (by positivity)] at hx
      exact lt_irrefl _ hx.2
    refine ⟨?_, ?_, ?_⟩
    · rw [singleton_subset_iff, bigElems, mem_filter, h.hsa0, h.hb, div_self (by positivity)]
      exact ⟨h.ha0, by linarith⟩
    · rw [measure, sum_singleton, h.hsa0, h.hb]
      have : (1 : ℚ) ≤ k := by exact_mod_cast hk
      linarith
    · intro S' hS' _
      have : S' ⊆ {a0} := fun x hx => mem_singleton.2 (hbig x (hS' hx))
      apply measure_mono u this (singleton_subset_iff.2 h.ha0)
  -- reachable states with `j` units added
  have hreach : ∀ j, j ≤ k - 1 → ∃ σ : State α, Relation.ReflTransGen (Step u) (initState u {a0}) σ ∧
      a0 ∈ σ.SUB ∧ (σ.SUB.erase a0).card = j := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨initState u {a0}, Relation.ReflTransGen.refl, mem_singleton_self _, by
        simp [initState]⟩
    | succ j ih =>
      intro hj
      obtain ⟨σ, hr, ha0, hcard⟩ := ih (by omega)
      obtain ⟨h1, h2, h3, _, _, _⟩ := run_inv k u {a0} hS σ hr
      set W := σ.SUB.erase a0 with hW
      have hmeas : measure u σ.SUB = 1 + ε + (j : ℚ) := by
        rw [measure, ← insert_erase ha0, sum_insert (notMem_erase _ _), h.hsa0, ← hW]
        rw [sum_congr rfl (fun x hx => h.hs1 x (h1 (mem_of_mem_erase hx)) (ne_of_mem_erase hx)),
          sum_const, nsmul_eq_mul, mul_one, hcard]
      have hWsub : W ⊆ u.T.erase a0 := fun x hx =>
        mem_erase.2 ⟨ne_of_mem_erase hx, h1 (mem_of_mem_erase hx)⟩
      have hunits : (u.T.erase a0).card = k + 1 := by rw [card_erase_of_mem h.ha0, h.hcard]; omega
      have hWlt : W.card < (u.T.erase a0).card := by rw [hunits, hcard]; omega
      obtain ⟨y, hy, hyW⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hWsub
        (fun he => by rw [he] at hWlt; exact lt_irrefl _ hWlt))
      have hyL : y ∈ σ.LEFT := by
        rw [h2]
        refine mem_sdiff.2 ⟨mem_of_mem_erase hy, fun hyS => hyW ?_⟩
        exact mem_erase.2 ⟨ne_of_mem_erase hy, hyS⟩
      have hsy : u.s y = 1 := h.hs1 y (mem_of_mem_erase hy) (ne_of_mem_erase hy)
      have hjk : (j : ℚ) + 1 ≤ (k : ℚ) - 1 := by
        have : j + 1 ≤ k - 1 := hj
        have : ((j + 1 : ℕ) : ℚ) ≤ ((k - 1 : ℕ) : ℚ) := by exact_mod_cast this
        push_cast [Nat.cast_sub hk] at this
        linarith
      have hfit : u.s y + σ.SUM ≤ u.b := by
        rw [hsy, h3, hmeas, h.hb]; linarith
      have hstep : Step u σ ⟨σ.SUB ∪ {y}, σ.LEFT.erase y, σ.SUM + u.s y⟩ := by
        refine ⟨fun hh => ?_, y, hyL, hfit, fun z hz _ => ?_, rfl⟩
        · have := hh y hyL; linarith
        · have hz0 : z ≠ a0 := by
            intro hz0; rw [h2] at hz; rw [hz0] at hz; exact (mem_sdiff.1 hz).2 ha0
          rw [h2] at hz
          rw [h.hs1 z (mem_sdiff.1 hz).1 hz0, hsy]
      refine ⟨_, hr.tail hstep, mem_union_left _ ha0, ?_⟩
      show ((σ.SUB ∪ {y}).erase a0).card = j + 1
      have hya0 : y ≠ a0 := ne_of_mem_erase hy
      have hyS : y ∉ σ.SUB := by
        intro hyS; exact hyW (mem_erase.2 ⟨hya0, hyS⟩)
      rw [union_comm, ← insert_eq, erase_insert_of_ne hya0, card_insert_of_notMem
        (fun hm => hyS (mem_of_mem_erase hm)), ← hW, hcard]
  obtain ⟨σ, hr, ha0, hcard⟩ := hreach (k - 1) le_rfl
  obtain ⟨h1, h2, h3, _, _, _⟩ := run_inv k u {a0} hS σ hr
  refine ⟨σ.SUB, {a0}, hS, σ, hr, fun x hx => ?_, rfl⟩
  rw [h2] at hx
  have hxa0 : x ≠ a0 := fun hx0 => (mem_sdiff.1 hx).2 (hx0 ▸ ha0)
  have hmeas : measure u σ.SUB = 1 + ε + ((k - 1 : ℕ) : ℚ) := by
    rw [measure, ← insert_erase ha0, sum_insert (notMem_erase _ _), h.hsa0]
    rw [sum_congr rfl (fun x hx => h.hs1 x (h1 (mem_of_mem_erase hx)) (ne_of_mem_erase hx)),
      sum_const, nsmul_eq_mul, mul_one, hcard]
  rw [h.hs1 x (mem_sdiff.1 hx).1 hxa0, h3, hmeas, h.hb]
  push_cast [Nat.cast_sub hk]
  linarith

lemma lb_fin (k : ℕ) (ε : ℚ) (hε : 0 < ε) :
    LB k ε (lowerBoundInput k ε hε) 0 := by
  refine ⟨mem_univ _, by simp [lowerBoundInput], fun x _ hx => by simp [lowerBoundInput, hx],
    by simp [lowerBoundInput], rfl⟩

theorem lowerBoundInput_spec (k : ℕ) (hk : 1 ≤ k) (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) :
    opt (lowerBoundInput k ε hε) = (k : ℚ) + 1 ∧
      (∀ T₁, Choosable k (lowerBoundInput k ε hε) T₁ →
        measure (lowerBoundInput k ε hε) T₁ = (k : ℚ) + ε) ∧
      ∃ T₁, Choosable k (lowerBoundInput k ε hε) T₁ :=
  ⟨(lb_fin k ε hε).opt_eq, fun T₁ hT₁ => (lb_fin k ε hε).choosable_measure hk hε hε1 T₁ hT₁,
    (lb_fin k ε hε).exists_choosable hk hε hε1⟩

/-- The lower-bound instance transported to `ℕ`. -/
def lbNat (k : ℕ) (ε : ℚ) (hε : 0 < ε) : Input ℕ where
  T := range (k + 2)
  s := fun i => if i = 0 then 1 + ε else 1
  b := (k : ℚ) + 1
  s_pos := by intro x _; split_ifs <;> linarith
  b_pos := by positivity

lemma lb_nat (k : ℕ) (ε : ℚ) (hε : 0 < ε) : LB k ε (lbNat k ε hε) 0 := by
  refine ⟨by simp [lbNat], by simp [lbNat], fun x _ hx => by simp [lbNat, hx],
    by simp [lbNat], rfl⟩

theorem subsetSum_Ak_ratio (k : ℕ) (hk : 1 ≤ k) :
    (∀ (α : Type) [DecidableEq α] (u : Input α) (T₁ : Finset α), Choosable k u T₁ →
        (k : ℚ) * opt u ≤ ((k : ℚ) + 1) * measure u T₁) ∧
      (∀ δ : ℚ, 0 < δ → ∃ (u : Input ℕ) (T₁ : Finset ℕ), Choosable k u T₁ ∧
        0 < measure u T₁ ∧ (((k : ℚ) + 1) / k - δ) * measure u T₁ < opt u) := by
  refine ⟨fun α _ u T₁ hT₁ => ?_, fun δ hδ => ?_⟩
  · rcases choosable_opt_or_large k hk u T₁ hT₁ with h | h
    · rw [h]
      have : 0 ≤ opt u := by
        rw [← h]
        obtain ⟨S, hS, σ, hr, _, hsub⟩ := hT₁
        obtain ⟨h1, _⟩ := run_inv k u S hS σ hr
        exact measure_nonneg u T₁ (hsub ▸ h1)
      nlinarith
    · have := opt_le_b u
      have hk0 : (0 : ℚ) ≤ k := by positivity
      nlinarith
  · have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
    set ε := min (1 / 2) (δ * k / (2 * ((k : ℚ) + 1))) with hεdef
    have hε : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hεδ : ε ≤ δ * k / (2 * ((k : ℚ) + 1)) := min_le_right _ _
    have h := lb_nat k ε hε
    obtain ⟨T₁, hT₁⟩ := h.exists_choosable hk hε hε1
    have hm := h.choosable_measure hk hε hε1 T₁ hT₁
    refine ⟨lbNat k ε hε, T₁, hT₁, by rw [hm]; positivity, ?_⟩
    rw [hm, h.opt_eq]
    have hk0 : (0 : ℚ) < k := by linarith
    rw [sub_mul, div_mul_eq_mul_div, sub_lt_iff_lt_add, div_lt_iff₀ hk0]
    have h2 : ((k : ℚ) + 1) * ε ≤ δ * k / 2 := by
      have := mul_le_mul_of_nonneg_left hεδ (by positivity : (0:ℚ) ≤ (k : ℚ) + 1)
      have e : ((k : ℚ) + 1) * (δ * k / (2 * ((k : ℚ) + 1))) = δ * k / 2 := by field_simp
      linarith
    have h3 : δ * k * 1 ≤ δ * k * ((k : ℚ) + ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith

end JohnsonApprox.SubsetSum

open JohnsonApprox.SubsetSum

theorem solution (k : ℕ) (hk : 1 ≤ k) (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) :
    opt (lowerBoundInput k ε hε) = (k : ℚ) + 1 ∧
      (∀ T₁, Choosable k (lowerBoundInput k ε hε) T₁ →
        measure (lowerBoundInput k ε hε) T₁ = (k : ℚ) + ε) ∧
      ∃ T₁, Choosable k (lowerBoundInput k ε hε) T₁ := by
  exact lowerBoundInput_spec k hk ε hε hε1
