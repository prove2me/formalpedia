-- Prove2me | solution 1 for LawlerCompress.TardyJobs.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T02:12:31.767889+00:00
-- url     : https://prove2.me/submissions/3cfc0c04-f321-46cc-b9a1-683b951c3e3a

import Definitions.Def_LawlerCompress_TardyJobs_DynamicProgram

set_option autoImplicit false

open LawlerCompress.TardyJobs

namespace LCAux

variable {m : ℕ}

def load (I : Instance m) (c : Fin I.n → Option (Fin m)) (r : Fin m) (x : Fin I.n) : ℕ :=
  ∑ i, if c i = some r ∧ i ≤ x then I.p i else 0

def Feas (I : Instance m) (c : Fin I.n → Option (Fin m)) : Prop :=
  ∀ j r, c j = some r → load I c r j ≤ I.d j

theorem sum_le_d (I : Instance m) (c : Fin I.n → Option (Fin m)) (hf : Feas I c) (r : Fin m)
    (Q : Fin I.n → Prop) [DecidablePred Q] (hA : ∃ i, c i = some r ∧ Q i) :
    ∃ k, (c k = some r ∧ Q k) ∧ (∑ i, if c i = some r ∧ Q i then I.p i else 0) ≤ I.d k := by
  classical
  have hne : (Finset.univ.filter (fun i => c i = some r ∧ Q i)).Nonempty := by
    obtain ⟨i, hi⟩ := hA
    exact ⟨i, by simp [hi]⟩
  have hk : c ((Finset.univ.filter (fun i => c i = some r ∧ Q i)).max' hne) = some r ∧
      Q ((Finset.univ.filter (fun i => c i = some r ∧ Q i)).max' hne) := by
    have h0 := Finset.max'_mem _ hne
    simpa using h0
  refine ⟨_, hk, ?_⟩
  have h1 : (∑ i, if c i = some r ∧ Q i then I.p i else 0) ≤
      load I c r ((Finset.univ.filter (fun i => c i = some r ∧ Q i)).max' hne) := by
    unfold load
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : c i = some r ∧ Q i
    · have hle : i ≤ (Finset.univ.filter (fun i => c i = some r ∧ Q i)).max' hne :=
        Finset.le_max' _ i (by simp [hi])
      rw [if_pos hi, if_pos ⟨hi.1, hle⟩]
    · rw [if_neg hi]; exact Nat.zero_le _
  exact h1.trans (hf _ r hk.1)

theorem sum_le_dmax (I : Instance m) (c : Fin I.n → Option (Fin m)) (hf : Feas I c) (r : Fin m)
    (Q : Fin I.n → Prop) [DecidablePred Q] :
    (∑ i, if c i = some r ∧ Q i then I.p i else 0) ≤ dmax I := by
  by_cases hA : ∃ i, c i = some r ∧ Q i
  · obtain ⟨k, -, hk⟩ := sum_le_d I c hf r Q hA
    have h3 : I.d k ≤ dmax I := Finset.le_sup (f := I.d) (Finset.mem_univ k)
    omega
  · have h0 : (∑ i, if c i = some r ∧ Q i then I.p i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg (fun h => hA ⟨i, h⟩)]
    omega

theorem load_le_d (I : Instance m) (c : Fin I.n → Option (Fin m)) (hedd : EDD I)
    (hf : Feas I c) (r : Fin m) (x : Fin I.n) (hA : ∃ i, c i = some r ∧ i ≤ x) :
    load I c r x ≤ I.d x := by
  obtain ⟨k, hk, hle⟩ := sum_le_d I c hf r (fun i => i ≤ x) hA
  have h1 : I.d k ≤ I.d x := hedd hk.2
  unfold load
  omega

theorem load_add_le (I : Instance m) (c : Fin I.n → Option (Fin m)) (r : Fin m)
    (a j : Fin I.n) (ha : a < j) (hc : c j = some r) :
    load I c r a + I.p j ≤ load I c r j := by
  have h0 : I.p j = ∑ i, if i = j then I.p i else 0 := by simp
  unfold load
  rw [h0, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hij : i = j
  · rw [hij]; simp [hc, not_le.mpr ha]
  · rw [if_neg hij, add_zero]
    by_cases h : c i = some r ∧ i ≤ a
    · rw [if_pos h, if_pos ⟨h.1, le_of_lt (lt_of_le_of_lt h.2 ha)⟩]
    · rw [if_neg h]; exact Nat.zero_le _

theorem swap_load (I : Instance m) (c c' : Fin I.n → Option (Fin m)) (j h : Fin I.n)
    (hjh : j ≠ h) (hcj' : c' j = none) (hch : c h = none)
    (hrest : ∀ i, i ≠ j → i ≠ h → c' i = c i) (r' : Fin m) (x : Fin I.n) :
    load I c' r' x + (if c j = some r' ∧ j ≤ x then I.p j else 0)
      = load I c r' x + (if c' h = some r' ∧ h ≤ x then I.p h else 0) := by
  have e1 : (if c j = some r' ∧ j ≤ x then I.p j else 0)
      = ∑ i, if i = j then (if c i = some r' ∧ i ≤ x then I.p i else 0) else 0 := by simp
  have e2 : (if c' h = some r' ∧ h ≤ x then I.p h else 0)
      = ∑ i, if i = h then (if c' i = some r' ∧ i ≤ x then I.p i else 0) else 0 := by simp
  unfold load
  rw [e1, e2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i = j
  · rw [hij]; simp [hcj', hjh]
  · by_cases hih : i = h
    · rw [hih]; simp [hch, Ne.symm hjh]
    · simp [hij, hih, hrest i hij hih]

theorem swap_sum (I : Instance m) (c c' : Fin I.n → Option (Fin m)) (j h : Fin I.n) (r : Fin m)
    (hcj : c j = some r) (hch' : c' h = some r) (hcj' : c' j = none) (hch : c h = none)
    (hrest : ∀ i, i ≠ j → i ≠ h → c' i = c i) (g : Fin I.n → ℕ) :
    (∑ i, if (c' i).isSome then g i else 0) + g j
      = (∑ i, if (c i).isSome then g i else 0) + g h := by
  have hjh : j ≠ h := by
    rintro rfl
    rw [hcj] at hch
    cases hch
  have e1 : g j = ∑ i, if i = j then g i else 0 := by simp
  have e2 : g h = ∑ i, if i = h then g i else 0 := by simp
  rw [e1, e2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i = j
  · rw [hij]; simp [hcj', hcj, hjh]
  · by_cases hih : i = h
    · rw [hih]; simp [hch, hch', Ne.symm hjh]
    · simp [hij, hih, hrest i hij hih]

theorem feas_swap (I : Instance m) (c c' : Fin I.n → Option (Fin m)) (hedd : EDD I)
    (hf : Feas I c) (j h : Fin I.n) (r : Fin m)
    (hcj : c j = some r) (hch : c h = none) (hp : I.p h = I.p j)
    (ht : load I c r j ≤ I.d h) (hcj' : c' j = none) (hch' : c' h = some r)
    (hrest : ∀ i, i ≠ j → i ≠ h → c' i = c i) : Feas I c' := by
  have hjh : j ≠ h := by
    rintro rfl
    rw [hcj] at hch
    cases hch
  intro j' r' hj'
  have key := swap_load I c c' j h hjh hcj' hch hrest r' j'
  by_cases hj'h : j' = h
  · have hr : r' = r := by
      rw [hj'h, hch'] at hj'
      exact (Option.some.inj hj').symm
    rw [hr, hj'h] at key ⊢
    rw [if_pos (⟨hch', le_refl h⟩ : c' h = some r ∧ h ≤ h)] at key
    by_cases hle : j ≤ h
    · rw [if_pos (⟨hcj, hle⟩ : c j = some r ∧ j ≤ h)] at key
      have h1 := load_le_d I c hedd hf r h ⟨j, hcj, hle⟩
      omega
    · rw [if_neg (fun hh : c j = some r ∧ j ≤ h => hle hh.2)] at key
      have h1 := load_add_le I c r h j (not_le.mp hle) hcj
      omega
  · have hj'j : j' ≠ j := by
      rintro rfl
      rw [hcj'] at hj'
      cases hj'
    have hcj'' : c j' = some r' := by rw [← hrest j' hj'j hj'h]; exact hj'
    have hfj := hf j' r' hcj''
    by_cases hc : c' h = some r' ∧ h ≤ j'
    · have hr : r' = r := by
        have h0 := hc.1
        rw [hch'] at h0
        exact (Option.some.inj h0).symm
      rw [hr] at key hc hfj ⊢
      rw [if_pos hc] at key
      by_cases hle : j ≤ j'
      · rw [if_pos (⟨hcj, hle⟩ : c j = some r ∧ j ≤ j')] at key
        omega
      · rw [if_neg (fun hh : c j = some r ∧ j ≤ j' => hle hh.2)] at key
        have h1 := load_add_le I c r j' j (not_le.mp hle) hcj
        have h2 : I.d h ≤ I.d j' := hedd hc.2
        omega
    · rw [if_neg hc] at key
      omega

theorem count_le (I : Instance m) (c : Fin I.n → Option (Fin m)) (hf : Feas I c) (p : ℕ)
    (hp : 1 ≤ p) :
    (Finset.univ.filter (fun i => (c i).isSome ∧ I.p i = p)).card ≤ kappa I p := by
  classical
  have hsub : Finset.univ.filter (fun i => (c i).isSome ∧ I.p i = p) ⊆
      Finset.univ.biUnion (fun r : Fin m => Finset.univ.filter (fun i => c i = some r ∧ I.p i = p)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hi.1
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨r, hr, hi.2⟩
  have hr : ∀ r : Fin m,
      (Finset.univ.filter (fun i => c i = some r ∧ I.p i = p)).card ≤ dmax I / p := by
    intro r
    rw [Nat.le_div_iff_mul_le hp]
    have h1 := sum_le_dmax I c hf r (fun i => I.p i = p)
    have h2a : ∑ i ∈ Finset.univ.filter (fun i => c i = some r ∧ I.p i = p), I.p i
        = ∑ i ∈ Finset.univ.filter (fun i => c i = some r ∧ I.p i = p), p :=
      Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2.2)
    have h2 : (∑ i, if c i = some r ∧ I.p i = p then I.p i else 0)
        = (Finset.univ.filter (fun i => c i = some r ∧ I.p i = p)).card * p := by
      rw [← Finset.sum_filter, h2a, Finset.sum_const, smul_eq_mul]
    omega
  calc (Finset.univ.filter (fun i => (c i).isSome ∧ I.p i = p)).card
      ≤ (Finset.univ.biUnion (fun r : Fin m =>
          Finset.univ.filter (fun i => c i = some r ∧ I.p i = p))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ r : Fin m, (Finset.univ.filter (fun i => c i = some r ∧ I.p i = p)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _r : Fin m, dmax I / p := Finset.sum_le_sum (fun r _ => hr r)
    _ = kappa I p := by simp [kappa]

theorem exists_better (I : Instance m) (c : Fin I.n → Option (Fin m))
    (hf : Feas I c) (j : Fin I.n) (r : Fin m) (hcj : c j = some r)
    (hnot : load I c r j ∉ cbar I j) :
    ∃ h, c h = none ∧ I.p h = I.p j ∧ load I c r j ≤ I.d h ∧ higher I h j := by
  classical
  have hpj : I.p j ≤ load I c r j := by
    unfold load
    have h0 := Finset.single_le_sum (f := fun i => if c i = some r ∧ i ≤ j then I.p i else 0)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    simpa [hcj] using h0
  have hd := hf j r hcj
  have hdm : I.d j ≤ dmax I := Finset.le_sup (f := I.d) (Finset.mem_univ j)
  have hel : j ∈ eligible I (I.p j) (load I c r j) := by simp [eligible, hd]
  have htb : j ∉ tbar I (I.p j) (load I c r j) := by
    intro h
    apply hnot
    simp only [cbar, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpj, by omega⟩, h⟩
  have hcard : kappa I (I.p j) ≤
      ((eligible I (I.p j) (load I c r j)).filter (fun h => higher I h j)).card := by
    by_contra hlt
    apply htb
    simp only [tbar, Finset.mem_filter]
    exact ⟨hel, by omega⟩
  by_contra hno
  push Not at hno
  have hsub : insert j ((eligible I (I.p j) (load I c r j)).filter (fun h => higher I h j)) ⊆
      Finset.univ.filter (fun i => (c i).isSome ∧ I.p i = I.p j) := by
    intro i hi
    rw [Finset.mem_insert] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi with hi | hi
    · rw [hi]; exact ⟨by simp [hcj], rfl⟩
    · simp only [Finset.mem_filter, eligible, Finset.mem_univ, true_and] at hi
      refine ⟨?_, hi.1.1⟩
      by_contra hns
      have h3 : c i = none := by simpa using hns
      exact hno i h3 hi.1.1 hi.1.2 hi.2
  have hnotin : j ∉ (eligible I (I.p j) (load I c r j)).filter (fun h => higher I h j) := by
    intro h
    have h3 := (Finset.mem_filter.mp h).2
    rcases h3 with h1 | ⟨_, h2⟩
    · exact lt_irrefl _ h1
    · exact lt_irrefl _ h2
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnotin] at h1
  have h2 := count_le I c hf (I.p j) (I.p_pos j)
  omega

def Phi (I : Instance m) (N : ℕ) (c : Fin I.n → Option (Fin m)) : ℕ :=
  ∑ i, if (c i).isSome then I.w i * N + i.val else 0

def Wt (I : Instance m) (c : Fin I.n → Option (Fin m)) : ℕ :=
  ∑ i, if (c i).isSome then I.w i else 0

theorem exists_canonical (I : Instance m) (hedd : EDD I) (c0 : Fin I.n → Option (Fin m))
    (hf0 : Feas I c0) :
    ∃ c, Feas I c ∧ Wt I c0 ≤ Wt I c ∧ ∀ j r, c j = some r → load I c r j ∈ cbar I j := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (∑ i : Fin I.n, i.val) + I.n + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (fun c => Feas I c))
    (Phi I N) ⟨c0, by simp [hf0]⟩
  have hfc : Feas I c := (Finset.mem_filter.mp hc).2
  refine ⟨c, hfc, ?_, ?_⟩
  · have h1 := hmax c0 (by simp [hf0])
    have lo : N * Wt I c0 ≤ Phi I N c0 := by
      unfold Wt Phi
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · rw [Nat.mul_comm]; exact Nat.le_add_right _ _
      · simp
    have hi : Phi I N c ≤ N * Wt I c + ∑ i : Fin I.n, i.val := by
      unfold Wt Phi
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact le_of_eq (by ring)
      · simp
    by_contra hlt
    push Not at hlt
    have h5 := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hlt)
    rw [Nat.mul_succ] at h5
    omega
  · intro j r hcj
    by_contra hnot
    obtain ⟨h, hch, hp, ht, hhi⟩ := exists_better I c hfc j r hcj hnot
    have hjh : j ≠ h := by
      rintro rfl
      rw [hcj] at hch
      cases hch
    obtain ⟨c', hc'⟩ : ∃ c' : Fin I.n → Option (Fin m),
        c' = Function.update (Function.update c j none) h (some r) := ⟨_, rfl⟩
    have hcj' : c' j = none := by simp [hc', hjh]
    have hch' : c' h = some r := by simp [hc']
    have hrest : ∀ i, i ≠ j → i ≠ h → c' i = c i := by
      intro i h1 h2
      simp [hc', h1, h2]
    have hf' := feas_swap I c c' hedd hfc j h r hcj hch hp ht hcj' hch' hrest
    have hs := swap_sum I c c' j h r hcj hch' hcj' hch hrest (fun i => I.w i * N + i.val)
    have hle := hmax c' (by simp [hf'])
    have hphi : I.w j * N + j.val < I.w h * N + h.val := by
      rcases hhi with h1 | ⟨h1, h2⟩
      · have h3 : (I.w j + 1) * N ≤ I.w h * N := Nat.mul_le_mul_right N h1
        have hjN : j.val < N := by
          have h4 := j.isLt
          omega
        rw [Nat.add_mul, Nat.one_mul] at h3
        omega
      · rw [h1]
        have h3 : j.val < h.val := h2
        omega
    unfold Phi at hle
    omega

theorem prefix_bound {α : Type} [DecidableEq α] (f : α → ℕ) :
    ∀ (l : List α) (T : Finset α), (∀ i ∈ T, i ∈ l) → T.Nonempty →
      ∃ k ∈ T, ∑ i ∈ T, f i ≤ ((l.takeWhile (· ≠ k)).map f).sum + f k
  | [], T, hT, hne => by
    obtain ⟨i, hi⟩ := hne
    exact absurd (hT i hi) (by simp)
  | a :: l, T, hT, hne => by
    by_cases hE : (T.erase a).Nonempty
    · obtain ⟨k, hk, hle⟩ := prefix_bound f l (T.erase a) (fun i hi => by
          have h1 := Finset.mem_erase.mp hi
          have h2 := hT i h1.2
          rcases List.mem_cons.mp h2 with h3 | h3
          · exact absurd h3 h1.1
          · exact h3) hE
      have hka : k ≠ a := (Finset.mem_erase.mp hk).1
      refine ⟨k, (Finset.mem_erase.mp hk).2, ?_⟩
      have htw : (a :: l).takeWhile (· ≠ k) = a :: l.takeWhile (· ≠ k) := by
        rw [List.takeWhile_cons]; simp [Ne.symm hka]
      rw [htw, List.map_cons, List.sum_cons]
      have hs : ∑ i ∈ T, f i ≤ f a + ∑ i ∈ T.erase a, f i := by
        by_cases ha : a ∈ T
        · rw [Finset.add_sum_erase _ _ ha]
        · rw [Finset.erase_eq_of_notMem ha]; omega
      omega
    · have hT1 : T ⊆ {a} := by
        intro i hi
        rw [Finset.mem_singleton]
        by_contra hia
        exact hE ⟨i, Finset.mem_erase.mpr ⟨hia, hi⟩⟩
      obtain ⟨i, hi⟩ := hne
      have hia : i = a := Finset.mem_singleton.mp (hT1 hi)
      refine ⟨a, hia ▸ hi, ?_⟩
      have htw : (a :: l).takeWhile (· ≠ a) = [] := by
        rw [List.takeWhile_cons]; simp
      rw [htw]
      simp only [List.map_nil, List.sum_nil, zero_add]
      calc ∑ i ∈ T, f i ≤ ∑ i ∈ ({a} : Finset α), f i := Finset.sum_le_sum_of_subset hT1
        _ = f a := Finset.sum_singleton _ _

theorem from_schedule (I : Instance m) (hedd : EDD I) (τ : JobLists I) (hτ : Schedule I τ) :
    ∃ c, Feas I c ∧ totalWeight I ≤ Wt I c + lateWeight I τ := by
  classical
  have hex : ∀ j, ∃ r, j ∈ τ r := by
    intro j
    by_contra h
    push Not at h
    have h0 := hτ j
    rw [Finset.sum_eq_zero (fun r _ => List.count_eq_zero.mpr (h r))] at h0
    omega
  obtain ⟨c, hcdef⟩ : ∃ c : Fin I.n → Option (Fin m), c = fun j =>
      if completion I τ j ≤ I.d j then some (Classical.choose (hex j)) else none := ⟨_, rfl⟩
  have hc1 : ∀ j r, c j = some r → completion I τ j ≤ I.d j ∧ j ∈ τ r := by
    intro j r h
    rw [hcdef] at h
    simp only [] at h
    split_ifs at h with h1
    exact ⟨h1, (Option.some.inj h) ▸ Classical.choose_spec (hex j)⟩
  have hc2 : ∀ j, completion I τ j ≤ I.d j → (c j).isSome := by
    intro j h
    rw [hcdef]
    simp [h]
  have hcomp : ∀ k r, k ∈ τ r →
      (((τ r).takeWhile (· ≠ k)).map I.p).sum + I.p k ≤ completion I τ k := by
    intro k r hk
    have h0 : (if k ∈ τ r then (((τ r).takeWhile (· ≠ k)).map I.p).sum + I.p k else 0)
        ≤ ∑ r, if k ∈ τ r then (((τ r).takeWhile (· ≠ k)).map I.p).sum + I.p k else 0 :=
      Finset.single_le_sum
        (f := fun r => if k ∈ τ r then (((τ r).takeWhile (· ≠ k)).map I.p).sum + I.p k else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    rw [if_pos hk] at h0
    exact h0
  refine ⟨c, ?_, ?_⟩
  · intro j r hj
    obtain ⟨T, hTdef⟩ : ∃ T : Finset (Fin I.n),
        T = Finset.univ.filter (fun i => c i = some r ∧ i ≤ j) := ⟨_, rfl⟩
    have hTne : T.Nonempty := ⟨j, by rw [hTdef]; simp [hj]⟩
    obtain ⟨k, hkT, hle⟩ := prefix_bound I.p (τ r) T (fun i hi => by
        rw [hTdef] at hi
        have h3 := (Finset.mem_filter.mp hi).2
        exact (hc1 i r h3.1).2) hTne
    rw [hTdef] at hkT
    have hk := (Finset.mem_filter.mp hkT).2
    have h1 := hcomp k r (hc1 k r hk.1).2
    have h2 := (hc1 k r hk.1).1
    have h3 : I.d k ≤ I.d j := hedd hk.2
    have h4 : load I c r j = ∑ i ∈ T, I.p i := by
      unfold load
      rw [hTdef, Finset.sum_filter]
    omega
  · unfold totalWeight Wt lateWeight
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases h : completion I τ j ≤ I.d j
    · rw [if_pos (hc2 j h)]; exact Nat.le_add_right _ _
    · rw [if_pos (not_le.mp h)]; exact Nat.le_add_left _ _

def xk (I : Instance m) (c : Fin I.n → Option (Fin m)) (k : ℕ) : Fin m → ℕ :=
  fun r => ∑ i, if c i = some r ∧ i.val < k then I.p i else 0

def Wk (I : Instance m) (c : Fin I.n → Option (Fin m)) (k : ℕ) : ℕ :=
  ∑ i, if (c i).isSome ∧ i.val < k then I.w i else 0

theorem xk_mem (I : Instance m) (c : Fin I.n → Option (Fin m)) (hf : Feas I c) (k : ℕ) :
    xk I c k ∈ loads I := by
  simp only [loads, Fintype.mem_piFinset, Finset.mem_range]
  intro r
  exact Nat.lt_succ_of_le (sum_le_dmax I c hf r (fun i => i.val < k))

theorem dp_step (I : Instance m) (c : Fin I.n → Option (Fin m)) (hf : Feas I c)
    (hcan : ∀ j r, c j = some r → load I c r j ∈ cbar I j) :
    ∀ k, k ≤ I.n → (Wk I c k : WithBot ℕ) ≤ algTable I k (xk I c k) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h1 : xk I c 0 = 0 := by
      funext r
      simp [xk]
    have h2 : Wk I c 0 = 0 := by simp [Wk]
    rw [h1, h2]
    simp [algTable]
  | succ k ih =>
    intro hk
    have hk' : k < I.n := hk
    obtain ⟨j, hjv⟩ : ∃ j : Fin I.n, j.val = k := ⟨⟨k, hk'⟩, rfl⟩
    have hget : (List.finRange I.n)[k]? = some j := by
      have hj : j = ⟨k, hk'⟩ := Fin.ext hjv
      rw [hj]
      simp [hk']
    have hlt : ∀ i : Fin I.n, i ≠ j → (i.val < k + 1 ↔ i.val < k) := by
      intro i hij
      have h0 : i.val ≠ k := fun h => hij (Fin.ext (h.trans hjv.symm))
      omega
    have hmem := xk_mem I c hf (k + 1)
    have ih' := ih (by omega)
    have hval : algTable I (k + 1) (xk I c (k + 1)) =
        max (algTable I k (xk I c (k + 1)))
          (Finset.univ.sup fun r : Fin m =>
            if I.p j ≤ xk I c (k + 1) r ∧ xk I c (k + 1) r ∈ cbar I j then
              algTable I k (Function.update (xk I c (k + 1)) r (xk I c (k + 1) r - I.p j))
                + (I.w j : WithBot ℕ)
            else ⊥) := by
      rw [algTable, if_pos hmem, hget]
    rw [hval]
    cases hcj : c j with
    | none =>
      have h1 : xk I c (k + 1) = xk I c k := by
        funext r
        unfold xk
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j
        · rw [hij]; simp [hcj]
        · simp only [hlt i hij]
      have h2 : Wk I c (k + 1) = Wk I c k := by
        unfold Wk
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j
        · rw [hij]; simp [hcj]
        · simp only [hlt i hij]
      refine le_trans ?_ (le_max_left _ _)
      rw [h1, h2]
      exact ih'
    | some r =>
      have h1r : xk I c (k + 1) r = xk I c k r + I.p j := by
        have e : I.p j = ∑ i, if i = j then I.p i else 0 := by simp
        unfold xk
        rw [e, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j
        · rw [hij]; simp [hcj, hjv]
        · simp [hij, hlt i hij]
      have h1o : ∀ r', r' ≠ r → xk I c (k + 1) r' = xk I c k r' := by
        intro r' hr'
        unfold xk
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j
        · rw [hij]; simp [hcj, Ne.symm hr']
        · simp only [hlt i hij]
      have h2 : Wk I c (k + 1) = Wk I c k + I.w j := by
        have e : I.w j = ∑ i, if i = j then I.w i else 0 := by simp
        unfold Wk
        rw [e, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j
        · rw [hij]; simp [hcj, hjv]
        · simp [hij, hlt i hij]
      have hload : xk I c (k + 1) r = load I c r j := by
        unfold xk load
        apply Finset.sum_congr rfl
        intro i _
        have h0 : i.val < k + 1 ↔ i ≤ j := by
          rw [Fin.le_def, hjv]
          omega
        simp only [h0]
      have hcb := hcan j r hcj
      rw [← hload] at hcb
      have hupd : Function.update (xk I c (k + 1)) r (xk I c (k + 1) r - I.p j) = xk I c k := by
        funext r'
        by_cases hr' : r' = r
        · rw [hr']; simp [h1r]
        · simp [hr', h1o r' hr']
      rw [h2]
      push_cast
      refine le_trans ?_ (le_max_right _ _)
      refine le_trans ?_ (Finset.le_sup (Finset.mem_univ r))
      rw [if_pos ⟨by omega, hcb⟩, hupd]
      exact add_le_add ih' le_rfl

end LCAux

open LCAux in
theorem solution {m : ℕ} (hm : 1 ≤ m) (I : Instance m)
    (hn : 1 ≤ I.n) (hedd : EDD I) :
    ∀ τ : JobLists I, Schedule I τ →
      totalWeight I ≤ algValue I + lateWeight I τ := by
  intro τ hτ
  have _ := hm
  have _ := hn
  obtain ⟨c0, hf0, hw0⟩ := from_schedule I hedd τ hτ
  obtain ⟨c, hf, hwc, hcan⟩ := exists_canonical I hedd c0 hf0
  have h1 := dp_step I c hf hcan I.n le_rfl
  have h2 : Wk I c I.n = Wt I c := by
    unfold Wk Wt
    apply Finset.sum_congr rfl
    intro i _
    simp [i.isLt]
  have h3 : algTable I I.n (xk I c I.n) ≤ algMaximum I :=
    Finset.le_sup (f := algTable I I.n) (xk_mem I c hf I.n)
  have h4 : (Wt I c : WithBot ℕ) ≤ (algValue I : WithBot ℕ) := by
    rw [← algMaximum_eq_value, ← h2]
    exact h1.trans h3
  have h5 : Wt I c ≤ algValue I := by exact_mod_cast h4
  omega
