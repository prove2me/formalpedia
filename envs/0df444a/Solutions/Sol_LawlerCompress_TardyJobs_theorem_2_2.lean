-- Prove2me | solution 1 for LawlerCompress.TardyJobs.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T14:05:15.851802+00:00
-- url     : https://prove2.me/submissions/e816645e-9a2d-40ac-936d-8eb0dd93d59f

import Definitions.Def_LawlerCompress_TardyJobs_Canonical

set_option autoImplicit false

namespace LawlerCompress.TardyJobs

def pre {m : ℕ} (I : Instance m) (l : List (Fin I.n)) (j : Fin I.n) : ℕ :=
  ((l.takeWhile (fun x => decide (x ≠ j))).map I.p).sum + I.p j

section basic
variable {m : ℕ} {I : Instance m} {τ : JobLists I}

lemma sched_exists (hτ : Schedule I τ) (j : Fin I.n) : ∃ r, j ∈ τ r := by
  by_contra h
  push_neg at h
  have := hτ j
  have h0 : ∀ r, (τ r).count j = 0 := fun r => List.count_eq_zero.2 (h r)
  simp [h0] at this

lemma sched_unique (hτ : Schedule I τ) {j : Fin I.n} {r b : Fin m} (h : j ∈ τ r) (hb : j ∈ τ b) :
    r = b := by
  by_contra hrb
  have h1 := hτ j
  have h2 : ∑ x ∈ ({r, b} : Finset (Fin m)), (τ x).count j ≤ ∑ x, (τ x).count j :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hrb] at h2
  have := List.count_pos_iff.2 h
  have := List.count_pos_iff.2 hb
  omega

lemma sched_nodup (hτ : Schedule I τ) (r : Fin m) : (τ r).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro j
  have h1 := hτ j
  have : (τ r).count j ≤ ∑ x, (τ x).count j :=
    Finset.single_le_sum (f := fun x => (τ x).count j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  omega

lemma completion_eq (hτ : Schedule I τ) {r : Fin m} {j : Fin I.n} (h : j ∈ τ r) :
    completion I τ j = pre I (τ r) j := by
  unfold completion
  rw [Finset.sum_eq_single r]
  · simp [h, pre]
  · intro b _ hb
    have : j ∉ τ b := fun hb' => hb (sched_unique hτ hb' h)
    simp [this]
  · simp

lemma le_completion (hτ : Schedule I τ) (j : Fin I.n) : I.p j ≤ completion I τ j := by
  obtain ⟨r, hr⟩ := sched_exists hτ j
  rw [completion_eq hτ hr]
  simp [pre]

lemma exists_last (I : Instance m) : ∀ (l : List (Fin I.n)), l.Nodup → ∀ F : Finset (Fin I.n),
    F.Nonempty → (∀ x ∈ F, x ∈ l) → ∃ k ∈ F, ∑ x ∈ F, I.p x ≤ pre I l k := by
  intro l
  induction l with
  | nil => intro _ F hF hm; obtain ⟨x, hx⟩ := hF; simpa using hm x hx
  | cons a l ih =>
    intro hnd F hF hm
    rw [List.nodup_cons] at hnd
    by_cases ha : a ∈ F
    · by_cases hF' : (F.erase a).Nonempty
      · obtain ⟨k, hk, hle⟩ := ih hnd.2 (F.erase a) hF' (by
          intro x hx
          have := hm x (Finset.mem_of_mem_erase hx)
          rcases List.mem_cons.1 this with h | h
          · exact absurd h (Finset.ne_of_mem_erase hx)
          · exact h)
        have hka : k ≠ a := Finset.ne_of_mem_erase hk
        refine ⟨k, Finset.mem_of_mem_erase hk, ?_⟩
        rw [← Finset.add_sum_erase F _ ha]
        have : pre I (a :: l) k = I.p a + pre I l k := by
          simp [pre, List.takeWhile_cons, hka.symm, add_assoc]
        omega
      · have : F = {a} := by
          rw [Finset.not_nonempty_iff_eq_empty, Finset.erase_eq_empty_iff] at hF'
          rcases hF' with h | h
          · exact absurd h (Finset.nonempty_iff_ne_empty.1 hF)
          · exact h
        subst this
        exact ⟨a, by simp, by simp [pre, List.takeWhile_cons]⟩
    · obtain ⟨k, hk, hle⟩ := ih hnd.2 F hF (by
        intro x hx
        have := hm x hx
        rcases List.mem_cons.1 this with h | h
        · exact absurd (h ▸ hx) ha
        · exact h)
      have hka : k ≠ a := fun h => ha (h ▸ hk)
      refine ⟨k, hk, ?_⟩
      have : pre I (a :: l) k = I.p a + pre I l k := by
        simp [pre, List.takeWhile_cons, hka.symm, add_assoc]
      omega

lemma pre_sorted (I : Instance m) : ∀ (l : List (Fin I.n)), l.Pairwise (· < ·) → ∀ j ∈ l,
    pre I l j = ∑ x ∈ l.toFinset.filter (· ≤ j), I.p x := by
  intro l
  induction l with
  | nil => intro _ j hj; simp at hj
  | cons a l ih =>
    intro hl j hj
    rw [List.pairwise_cons] at hl
    by_cases hja : j = a
    · subst hja
      have : (j :: l).toFinset.filter (· ≤ j) = {j} := by
        ext x
        simp only [Finset.mem_filter, List.mem_toFinset, List.mem_cons, Finset.mem_singleton]
        constructor
        · rintro ⟨h | h, hx⟩
          · exact h
          · exact absurd (hl.1 x h) (not_lt.2 hx)
        · intro h; subst h; simp
      rw [this]; simp [pre, List.takeWhile_cons]
    · have hjl : j ∈ l := by
        rcases List.mem_cons.1 hj with h | h
        · exact absurd h hja
        · exact h
      have haj : a < j := hl.1 j hjl
      have h1 : pre I (a :: l) j = I.p a + pre I l j := by
        simp [pre, List.takeWhile_cons, Ne.symm hja, add_assoc]
      have hal : a ∉ l.toFinset.filter (· ≤ j) := by
        simp only [Finset.mem_filter, List.mem_toFinset, not_and]
        intro h; exact absurd (hl.1 a h) (lt_irrefl a)
      have h2 : (a :: l).toFinset.filter (· ≤ j) = insert a (l.toFinset.filter (· ≤ j)) := by
        rw [List.toFinset_cons, Finset.filter_insert, if_pos haj.le]
      rw [h1, ih hl.2 j hjl, h2, Finset.sum_insert hal]

/-- swap -/
def swapL (I : Instance m) (τ : JobLists I) (a b : Fin I.n) : JobLists I :=
  fun r => (τ r).map (Equiv.swap a b)

lemma swap_schedule (hτ : Schedule I τ) (a b : Fin I.n) : Schedule I (swapL I τ a b) := by
  intro j
  have := hτ ((Equiv.swap a b) j)
  simp only [swapL]
  have e : ∀ r, ((τ r).map (Equiv.swap a b)).count j = (τ r).count ((Equiv.swap a b) j) := by
    intro r
    have := List.count_map_of_injective (τ r) (Equiv.swap a b) (Equiv.injective _) ((Equiv.swap a b) j)
    rw [← this]; simp
  simp only [e]; exact this

lemma swap_completion (hτ : Schedule I τ) {a b : Fin I.n} (hp : I.p a = I.p b) (x : Fin I.n) :
    completion I (swapL I τ a b) x = completion I τ (Equiv.swap a b x) := by
  obtain ⟨r, hr⟩ := sched_exists hτ (Equiv.swap a b x)
  have hr' : x ∈ swapL I τ a b r := by
    simp only [swapL, List.mem_map]
    exact ⟨_, hr, by simp⟩
  rw [completion_eq (swap_schedule hτ a b) hr', completion_eq hτ hr]
  simp only [pre, swapL]
  have hpσ : ∀ z, I.p (Equiv.swap a b z) = I.p z := by
    intro z
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; exact hp.symm
    · subst h2; exact hp
    · rfl
  rw [List.takeWhile_map, List.map_map]
  have e1 : (fun x_1 => decide (x_1 ≠ x)) ∘ (Equiv.swap a b) = fun z => decide (z ≠ Equiv.swap a b x) := by
    funext z
    simp only [Function.comp, decide_eq_decide, ne_eq]
    rw [Equiv.swap_apply_eq_iff]
  have e2 : I.p ∘ (Equiv.swap a b) = I.p := funext hpσ
  rw [e1, e2, hpσ]


lemma count_ite (hτ : Schedule I τ) (r : Fin m) (j : Fin I.n) :
    (τ r).count j = if j ∈ τ r then 1 else 0 := by
  split_ifs with h
  · exact List.count_eq_one_of_mem (sched_nodup hτ r) h
  · exact List.count_eq_zero.2 h

lemma pre_append_of_mem (I : Instance m) : ∀ (l1 l2 : List (Fin I.n)) (j : Fin I.n), j ∈ l1 →
    pre I (l1 ++ l2) j = pre I l1 j := by
  intro l1 l2 j
  induction l1 with
  | nil => intro h; simp at h
  | cons a l ih =>
    intro hj
    by_cases haj : a = j
    · subst haj; simp [pre]
    · have hjl : j ∈ l := by
        rcases List.mem_cons.1 hj with h | h
        · exact absurd h.symm haj
        · exact h
      have := ih hjl
      simp only [pre, List.cons_append, List.takeWhile_cons]
      simp only [pre] at this
      have h' := Nat.add_right_cancel this
      simp only [Bool.not_eq_true, decide_not] at h' ⊢
      simp [haj, h']

def onSet (I : Instance m) (τ : JobLists I) : Finset (Fin I.n) :=
  Finset.univ.filter (fun j => completion I τ j ≤ I.d j)

def key (I : Instance m) (x : Fin I.n) : ℕ := I.w x * I.n + x.val

def Phi (I : Instance m) (τ : JobLists I) : ℕ := ∑ x ∈ onSet I τ, key I x

lemma key_lt {h j : Fin I.n} (hh : higher I h j) : key I j < key I h := by
  unfold higher at hh; unfold key
  rcases hh with hh | ⟨he, hj⟩
  · have : (I.w j + 1) * I.n ≤ I.w h * I.n := Nat.mul_le_mul_right _ hh
    have := j.isLt
    nlinarith
  · rw [he]; simp only [Fin.lt_def] at hj; omega

lemma onTime_eq : onTimeWeight I τ = ∑ j ∈ onSet I τ, I.w j := by
  unfold onTimeWeight onSet; rw [Finset.sum_filter]

lemma late_add : lateWeight I τ + onTimeWeight I τ = totalWeight I := by
  unfold lateWeight onTimeWeight totalWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  by_cases h : completion I τ j ≤ I.d j
  · simp [h, not_lt.2 h]
  · simp [h, not_le.1 h]

lemma opt_iff (hτ : Schedule I τ) :
    IsOptSchedule I τ ↔ ∀ τ', Schedule I τ' → onTimeWeight I τ' ≤ onTimeWeight I τ := by
  constructor
  · rintro ⟨_, h⟩ τ' h'
    have h1 := h τ' h'
    have h2 := late_add (τ := τ)
    have h3 := late_add (τ := τ')
    omega
  · intro h
    refine ⟨hτ, fun τ' h' => ?_⟩
    have h1 := h τ' h'
    have h2 := late_add (τ := τ)
    have h3 := late_add (τ := τ')
    omega

lemma count_ontime (hτ : Schedule I τ) (q : ℕ) (hq : 1 ≤ q) :
    (Finset.univ.filter (fun j => I.p j = q ∧ completion I τ j ≤ I.d j)).card
      ≤ m * (dmax I / q) := by
  generalize hG : (Finset.univ.filter (fun j => I.p j = q ∧ completion I τ j ≤ I.d j)) = G
  have h1 : G.card = ∑ r, (G.filter (fun j => j ∈ τ r)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro j _
    obtain ⟨r, hr⟩ := sched_exists hτ j
    rw [Finset.sum_eq_single r]
    · simp [hr]
    · intro b _ hb
      have : j ∉ τ b := fun h => hb (sched_unique hτ h hr)
      simp [this]
    · simp
  have h2 : ∀ r, (G.filter (fun j => j ∈ τ r)).card ≤ dmax I / q := by
    intro r
    generalize hF : G.filter (fun j => j ∈ τ r) = F
    rcases F.eq_empty_or_nonempty with h | h
    · simp [h]
    · have hmem : ∀ x ∈ F, x ∈ G ∧ x ∈ τ r := by
        intro x hx; rw [← hF] at hx; exact Finset.mem_filter.1 hx
      have hGm : ∀ x ∈ G, I.p x = q ∧ completion I τ x ≤ I.d x := by
        intro x hx; rw [← hG] at hx; simpa using hx
      obtain ⟨k, hk, hle⟩ := exists_last I (τ r) (sched_nodup hτ r) F h (fun x hx => (hmem x hx).2)
      have hsum : ∑ x ∈ F, I.p x = F.card * q := by
        rw [Finset.sum_congr rfl (g := fun _ => q) (fun x hx => (hGm x (hmem x hx).1).1)]
        simp
      rw [← completion_eq hτ (hmem k hk).2] at hle
      have h3 := (hGm k (hmem k hk).1).2
      have h4 : I.d k ≤ dmax I := Finset.le_sup (f := I.d) (Finset.mem_univ k)
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
  rw [h1]
  calc ∑ r, (G.filter (fun j => j ∈ τ r)).card ≤ ∑ _r : Fin m, dmax I / q :=
        Finset.sum_le_sum (fun r _ => h2 r)
    _ = m * (dmax I / q) := by simp

lemma canonical (hτ : Schedule I τ) (hopt : IsOptSchedule I τ)
    (hmax : ∀ τ', IsOptSchedule I τ' → Phi I τ' ≤ Phi I τ) (j : Fin I.n)
    (hj : completion I τ j ≤ I.d j) : completion I τ j ∈ cbar I j := by
  have hS := (opt_iff hτ).1 hopt
  have hpj := le_completion hτ j
  have hdj : I.d j ≤ dmax I := Finset.le_sup (f := I.d) (Finset.mem_univ j)
  unfold cbar
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hpj, hj.trans hdj⟩, ?_⟩
  unfold tbar
  rw [Finset.mem_filter]
  have hje : j ∈ eligible I (I.p j) (completion I τ j) := by simp [eligible, hj]
  refine ⟨hje, ?_⟩
  by_contra hnot
  rw [not_lt] at hnot
  generalize hH : (eligible I (I.p j) (completion I τ j)).filter (fun h => higher I h j) = H at hnot
  have hHm : ∀ h ∈ H, I.p h = I.p j ∧ completion I τ j ≤ I.d h ∧ higher I h j := by
    intro h hh
    rw [← hH, Finset.mem_filter] at hh
    have := hh.1
    simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact ⟨this.1, this.2, hh.2⟩
  have hjH : j ∉ H := by
    intro hh
    have := (hHm j hh).2.2
    unfold higher at this
    omega
  by_cases hex : ∃ h ∈ H, I.d h < completion I τ h
  · obtain ⟨h, hhH, hlate⟩ := hex
    obtain ⟨hph, hth, hhi⟩ := hHm h hhH
    have hjh : j ≠ h := by
      intro e; subst e; unfold higher at hhi; omega
    have hp : I.p j = I.p h := hph.symm
    have hs2 := swap_schedule hτ j h
    have hjS : j ∈ onSet I τ := by simp [onSet, hj]
    have hhS : h ∉ onSet I τ := by simp [onSet]; omega
    have hwjh : I.w j ≤ I.w h := by unfold higher at hhi; omega
    have hhE : h ∉ (onSet I τ).erase j := fun e => hhS (Finset.mem_of_mem_erase e)
    have hT : insert h ((onSet I τ).erase j) ⊆ onSet I (swapL I τ j h) := by
      intro x hx
      simp only [onSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.1 hx with hx | hx
      · rw [hx, swap_completion hτ hp, Equiv.swap_apply_right]; exact hth
      · have hxj := Finset.ne_of_mem_erase hx
        have hxS := Finset.mem_of_mem_erase hx
        have hxh : x ≠ h := fun e => hhS (e ▸ hxS)
        rw [swap_completion hτ hp, Equiv.swap_apply_of_ne_of_ne hxj hxh]
        simpa [onSet] using hxS
    have hw1 := Finset.add_sum_erase (onSet I τ) I.w hjS
    have hw2 := Finset.sum_insert (f := I.w) hhE
    have hw3 := Finset.sum_le_sum_of_subset (f := I.w) hT
    have hk1 := Finset.add_sum_erase (onSet I τ) (key I) hjS
    have hk2 := Finset.sum_insert (f := key I) hhE
    have hk3 := Finset.sum_le_sum_of_subset (f := key I) hT
    have hopt2 : IsOptSchedule I (swapL I τ j h) := by
      rw [opt_iff hs2]
      intro τ' h'
      have := hS τ' h'
      rw [onTime_eq (τ := τ)] at this
      rw [onTime_eq (τ := swapL I τ j h)]
      omega
    have := hmax _ hopt2
    have := key_lt hhi
    unfold Phi at *
    omega
  · push Not at hex
    have hsub : insert j H ⊆ Finset.univ.filter (fun x => I.p x = I.p j ∧ completion I τ x ≤ I.d x) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.1 hx with hx | hx
      · subst hx; exact ⟨rfl, hj⟩
      · exact ⟨(hHm x hx).1, not_lt.1 (not_lt.2 (hex x hx)) |> fun h => by omega⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hjH] at h1
    have h2 := count_ontime hτ (I.p j) (I.p_pos j)
    unfold kappa at hnot
    omega


lemma edd_sort (hedd : EDD I) (hτ : Schedule I τ) (hopt : IsOptSchedule I τ) :
    ∃ τ' : JobLists I, Schedule I τ' ∧ onSet I τ' = onSet I τ ∧ OnTimeEDDPrefix I τ' := by
  classical
  let E : Fin m → Finset (Fin I.n) := fun r => Finset.univ.filter (fun j => j ∈ τ r ∧ j ∈ onSet I τ)
  let τ' : JobLists I := fun r => (E r).sort ++ (τ r).filter (fun j => decide (j ∉ onSet I τ))
  have hcount : ∀ r j, (τ' r).count j =
      if j ∈ onSet I τ then (if j ∈ τ r then 1 else 0) else (τ r).count j := by
    intro r j
    simp only [τ', List.count_append]
    by_cases hj : j ∈ onSet I τ
    · have h0 : ((τ r).filter (fun j => decide (j ∉ onSet I τ))).count j = 0 := by
        apply List.count_eq_zero.2
        simp [hj]
      have h1 : ((E r).sort).count j = if j ∈ τ r then 1 else 0 := by
        split_ifs with h
        · exact List.count_eq_one_of_mem (Finset.sort_nodup _ _) (by simp [E, h, hj])
        · exact List.count_eq_zero.2 (by simp [E, h])
      rw [h0, h1]; simp [hj]
    · have h0 : ((E r).sort).count j = 0 := List.count_eq_zero.2 (by simp [E, hj])
      rw [h0, List.count_filter (by simp [hj])]; simp [hj]
  have hsch : Schedule I τ' := by
    intro j
    simp only [hcount]
    by_cases hj : j ∈ onSet I τ
    · simp only [hj, if_true]
      obtain ⟨r, hr⟩ := sched_exists hτ j
      rw [Finset.sum_eq_single r]
      · simp [hr]
      · intro b _ hb
        have : j ∉ τ b := fun h => hb (sched_unique hτ h hr)
        simp [this]
      · simp
    · simp only [hj, if_false]; exact hτ j
  have hsub : onSet I τ ⊆ onSet I τ' := by
    intro j hj
    obtain ⟨r, hr⟩ := sched_exists hτ j
    have hjE : j ∈ E r := by simp [E, hr, hj]
    have hjm : j ∈ τ' r := by
      simp only [τ', List.mem_append]; left; exact (Finset.mem_sort _).2 hjE
    simp only [onSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [completion_eq hsch hjm]
    simp only [τ']
    rw [pre_append_of_mem I _ _ j ((Finset.mem_sort _).2 hjE),
      pre_sorted I _ (Finset.sortedLT_sort (E r)).pairwise j ((Finset.mem_sort _).2 hjE),
      Finset.sort_toFinset]
    have hne : ((E r).filter (· ≤ j)).Nonempty := ⟨j, by simp [hjE]⟩
    obtain ⟨k, hk, hle⟩ := exists_last I (τ r) (sched_nodup hτ r) _ hne (by
      intro x hx
      have := (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).2
      exact this.1)
    have hkE := (Finset.mem_filter.1 hk).1
    have hkle := (Finset.mem_filter.1 hk).2
    have hk1 : k ∈ τ r := (Finset.mem_filter.1 hkE).2.1
    have hk2 : k ∈ onSet I τ := (Finset.mem_filter.1 hkE).2.2
    rw [← completion_eq hτ hk1] at hle
    have hk3 : completion I τ k ≤ I.d k := by simpa [onSet] using hk2
    have := hedd hkle
    omega
  have heq : onSet I τ' = onSet I τ := by
    by_contra hne
    have hss : onSet I τ ⊂ onSet I τ' := lt_of_le_of_ne hsub (Ne.symm hne)
    obtain ⟨i, hit, his⟩ := Finset.exists_of_ssubset hss
    have h1 := Finset.sum_lt_sum_of_subset (f := I.w) hss.1 hit his (I.w_pos i)
      (fun i _ _ => Nat.zero_le _)
    have h2 := ((opt_iff hτ).1 hopt) τ' hsch
    rw [onTime_eq, onTime_eq] at h2
    omega
  refine ⟨τ', hsch, heq, ?_⟩
  intro r
  refine ⟨(E r).sort, (τ r).filter (fun j => decide (j ∉ onSet I τ)), rfl,
    (Finset.sortedLT_sort (E r)).pairwise, ?_, ?_⟩
  · intro j hj
    have := (Finset.mem_filter.1 ((Finset.mem_sort _).1 hj)).2.2
    have h2 : j ∈ onSet I τ' := heq ▸ this
    simpa [onSet] using h2
  · intro j hj
    have h1 := (List.mem_filter.1 hj).2
    have h2 : j ∉ onSet I τ' := by rw [heq]; simpa using h1
    simpa [onSet] using h2

theorem main (hm : 1 ≤ m) (I : Instance m) (hn : 1 ≤ I.n) (hedd : EDD I) :
    ∃ τ : JobLists I, IsOptSchedule I τ ∧
      (∀ j, completion I τ j ≤ I.d j → completion I τ j ∈ cbar I j) ∧
      OnTimeEDDPrefix I τ := by
  classical
  have hex : ∃ τ : JobLists I, Schedule I τ := by
    refine ⟨fun r => if r = ⟨0, hm⟩ then List.finRange I.n else [], ?_⟩
    intro j
    rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
    · simp [List.count_eq_one_of_mem (List.nodup_finRange I.n) (List.mem_finRange j)]
    · intro b _ hb; simp [hb]
    · simp
  have hP : ∃ v, ∃ τ : JobLists I, Schedule I τ ∧ lateWeight I τ = v :=
    let ⟨τ, h⟩ := hex; ⟨_, τ, h, rfl⟩
  obtain ⟨τ0, h0s, h0v⟩ := Nat.find_spec hP
  have h0opt : IsOptSchedule I τ0 := by
    refine ⟨h0s, fun τ' h' => ?_⟩
    rw [h0v]; exact Nat.find_min' hP ⟨τ', h', rfl⟩
  let C := ∑ x, key I x
  have hbound : ∀ τ : JobLists I, Phi I τ ≤ C := fun τ =>
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  let P2 : ℕ → Prop := fun n => ∃ τ : JobLists I, IsOptSchedule I τ ∧ Phi I τ = n
  obtain ⟨τ1, h1opt, h1v⟩ : P2 (Nat.findGreatest P2 C) :=
    Nat.findGreatest_spec (P := P2) (hbound τ0) ⟨τ0, h0opt, rfl⟩
  have hmax1 : ∀ τ', IsOptSchedule I τ' → Phi I τ' ≤ Phi I τ1 := by
    intro τ' h'
    rw [h1v]
    exact Nat.le_findGreatest (hbound τ') ⟨τ', h', rfl⟩
  obtain ⟨τ2, h2s, h2e, h2p⟩ := edd_sort hedd h1opt.1 h1opt
  have h2opt : IsOptSchedule I τ2 := by
    rw [opt_iff h2s]
    intro τ' h'
    have := (opt_iff h1opt.1).1 h1opt τ' h'
    rw [onTime_eq (τ := τ2), h2e, ← onTime_eq]; exact this
  have hPhi : Phi I τ2 = Phi I τ1 := by unfold Phi; rw [h2e]
  exact ⟨τ2, h2opt, canonical h2s h2opt (fun τ' h' => by rw [hPhi]; exact hmax1 τ' h'), h2p⟩

end basic
end LawlerCompress.TardyJobs

theorem solution {m : ℕ} (hm : 1 ≤ m) (I : LawlerCompress.TardyJobs.Instance m)
    (hn : 1 ≤ I.n) (hedd : LawlerCompress.TardyJobs.EDD I) :
    ∃ τ : LawlerCompress.TardyJobs.JobLists I, LawlerCompress.TardyJobs.IsOptSchedule I τ ∧
      (∀ j, LawlerCompress.TardyJobs.completion I τ j ≤ I.d j →
        LawlerCompress.TardyJobs.completion I τ j ∈ LawlerCompress.TardyJobs.cbar I j) ∧
      LawlerCompress.TardyJobs.OnTimeEDDPrefix I τ :=
  LawlerCompress.TardyJobs.main hm I hn hedd
