-- Prove2me | solution 1 for MDPComplexity.StationaryHorizon.one_frequent_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T03:28:53.243422+00:00
-- url     : https://prove2.me/submissions/0b6de0b2-b6ed-4359-8f29-6b52c129d888

import Mathlib
import Definitions.Def_MDPComplexity_StationaryHorizon_Model


namespace OFCList
variable {α : Type*} [DecidableEq α]

def eraseN (a : α) : ℕ → List α → List α
  | 0, l => l
  | j + 1, l => eraseN a j (l.erase a)

theorem sum_map_erase {β : Type*} [AddCommMonoid β] (f : α → β) (a : α) :
    ∀ l : List α, a ∈ l → (l.map f).sum = f a + ((l.erase a).map f).sum
  | [], h => by simp at h
  | b :: l, h => by
    by_cases hb : b = a
    · subst hb; simp
    · rw [List.erase_cons_tail (by simpa using hb)]
      have : a ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hb
        · exact h
      simp only [List.map_cons, List.sum_cons]
      rw [sum_map_erase f a l this]; abel

theorem count_eraseN (a : α) : ∀ (j : ℕ) (l : List α), (eraseN a j l).count a = l.count a - j
  | 0, l => rfl
  | j + 1, l => by
    rw [eraseN, count_eraseN a j, List.count_erase_self]; omega

theorem count_eraseN_ne (a b : α) (hb : b ≠ a) :
    ∀ (j : ℕ) (l : List α), (eraseN a j l).count b = l.count b
  | 0, l => rfl
  | j + 1, l => by rw [eraseN, count_eraseN_ne a b hb j, List.count_erase_of_ne hb]

theorem sum_map_eraseN {β : Type*} [AddCommMonoid β] (f : α → β) (a : α) :
    ∀ (j : ℕ) (l : List α), j ≤ l.count a →
      (l.map f).sum = j • f a + ((eraseN a j l).map f).sum
  | 0, l, _ => by simp [eraseN]
  | j + 1, l, h => by
    have ha : a ∈ l := List.count_pos_iff.mp (by omega)
    rw [eraseN, sum_map_erase f a l ha, sum_map_eraseN f a j (l.erase a)
      (by rw [List.count_erase_self]; omega), succ_nsmul']
    abel

theorem mem_eraseN (a b : α) (hb : b ≠ a) (j : ℕ) (l : List α) (h : b ∈ l) : b ∈ eraseN a j l := by
  have := count_eraseN_ne a b hb j l
  exact List.count_pos_iff.mp (this ▸ List.count_pos_iff.mpr h)

theorem mem_of_mem_eraseN (a b : α) : ∀ (j : ℕ) (l : List α), b ∈ eraseN a j l → b ∈ l
  | 0, l, h => h
  | j + 1, l, h => List.mem_of_mem_erase (mem_of_mem_eraseN a b j _ h)

end OFCList

namespace OFCList
theorem ncard_idx {α : Type*} [DecidableEq α] (l : List α) (a : α) :
    Set.ncard {i : Fin l.length | l[i] = a} = l.count a := by
  rw [Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_setOf]
  rw [Finset.card_filter]
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.count_cons, ← ih]
    refine (Fin.sum_univ_succ (n := l.length) (f := fun i => if (b :: l)[i] = a then 1 else 0)).trans ?_
    have hs : ∀ i : Fin l.length, (b :: l)[i.succ] = l[i] := fun i => rfl
    have h0 : (b :: l)[(0 : Fin (l.length + 1))] = b := rfl
    simp only [hs, h0, beq_iff_eq]
    omega
end OFCList

open MDPComplexity.StationaryHorizon

section CD
variable {S : Type} [Fintype S]

def cdTr (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) : M.D s' := e ▸ x

theorem cdTr_next (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.next s' (cdTr M e x) = M.next s x := by subst e; rfl

theorem cdTr_c (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    M.c s' (cdTr M e x) = M.c s x := by subst e; rfl

theorem cdTr_sig (M : DetMDP S) {s s' : S} (e : s = s') (x : M.D s) :
    (⟨s', cdTr M e x⟩ : Σ s, M.D s) = ⟨s, x⟩ := by subst e; rfl

def wX (M : DetMDP S) {l : ℕ} (W : M.Walk l) (n : ℕ) : S :=
  if h : n ≤ l then W.x ⟨n, by omega⟩ else W.x (Fin.last l)

theorem wX_le (M : DetMDP S) {l : ℕ} (W : M.Walk l) (n : ℕ) (h : n ≤ l) :
    wX M W n = W.x ⟨n, by omega⟩ := dif_pos h

theorem wX_fin (M : DetMDP S) {l : ℕ} (W : M.Walk l) (i : Fin (l+1)) : wX M W i = W.x i := by
  have := i.isLt
  rw [wX_le M W i (by omega)]

theorem wX_zero (M : DetMDP S) {l : ℕ} (W : M.Walk l) : wX M W 0 = W.x 0 := by
  rw [wX_le M W 0 (Nat.zero_le _)]
  exact congrArg W.x (Fin.ext (by simp))

noncomputable def wE (M : DetMDP S) {l : ℕ} (W : M.Walk l) (n : ℕ) : M.D (wX M W n) :=
  if h : n < l then cdTr M (wX_le M W n h.le).symm (W.e ⟨n, h⟩) else Classical.arbitrary _

theorem wE_sig (M : DetMDP S) {l : ℕ} (W : M.Walk l) (n : ℕ) (h : n < l) :
    (⟨wX M W n, wE M W n⟩ : Σ s, M.D s) = ⟨W.x (Fin.castSucc ⟨n, h⟩), W.e ⟨n, h⟩⟩ := by
  simp only [wE, dif_pos h]
  exact cdTr_sig M _ _

theorem wE_next (M : DetMDP S) {l : ℕ} (W : M.Walk l) (n : ℕ) (h : n < l) :
    M.next (wX M W n) (wE M W n) = wX M W (n+1) := by
  simp only [wE, dif_pos h, cdTr_next]
  exact (W.valid ⟨n, h⟩).trans (wX_fin M W _).symm

theorem arcs_eq (M : DetMDP S) {l : ℕ} (W : M.Walk l) :
    W.arcs = (Multiset.range l).map (fun n => (⟨wX M W n, wE M W n⟩ : Σ s, M.D s)) := by
  unfold DetMDP.Walk.arcs
  rw [Multiset.range, Multiset.map_coe]
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [List.getElem_range]
    exact (wE_sig M W n (by simpa using h1)).symm

def ofRaw (M : DetMDP S) (m : ℕ) (f : ℕ → S) (g : (t : ℕ) → M.D (f t))
    (hv : ∀ t < m, M.next (f t) (g t) = f (t+1)) : M.Walk m :=
  ⟨fun i => f i, fun t => g t, fun t => hv t t.isLt⟩

theorem ofRaw_arcs (M : DetMDP S) (m : ℕ) (f : ℕ → S) (g : (t : ℕ) → M.D (f t))
    (hv : ∀ t < m, M.next (f t) (g t) = f (t+1)) :
    (ofRaw M m f g hv).arcs = (Multiset.range m).map (fun t => (⟨f t, g t⟩ : Σ s, M.D s)) := by
  unfold DetMDP.Walk.arcs
  rw [Multiset.range, Multiset.map_coe]
  congr 1
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [List.getElem_range]
    rfl

theorem cost_arcs (M : DetMDP S) {l : ℕ} (W : M.Walk l) :
    W.cost = (W.arcs.map (fun p => M.c p.1 p.2)).sum := by
  unfold DetMDP.Walk.cost DetMDP.Walk.arcs
  rw [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn]
  rfl

theorem card_arcs (M : DetMDP S) {l : ℕ} (W : M.Walk l) : Multiset.card W.arcs = l := by
  simp [DetMDP.Walk.arcs]

theorem cs_cost (M : DetMDP S) (Cs : List (Σ k : ℕ, M.Walk k)) :
    (Cs.map (fun C : (Σ k : ℕ, M.Walk k) => C.2.cost)).sum =
      (((Cs.map (fun C : (Σ k : ℕ, M.Walk k) => C.2.arcs)).sum).map (fun p => M.c p.1 p.2)).sum := by
  induction Cs with
  | nil => simp
  | cons C Cs ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, cost_arcs M C.2,
      Multiset.map_add, Multiset.sum_add]

theorem cs_len (M : DetMDP S) (Cs : List (Σ k : ℕ, M.Walk k)) :
    (Cs.map (fun C : (Σ k : ℕ, M.Walk k) => C.1)).sum =
      Multiset.card ((Cs.map (fun C : (Σ k : ℕ, M.Walk k) => C.2.arcs)).sum) := by
  induction Cs with
  | nil => simp
  | cons C Cs ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, Multiset.card_add,
      card_arcs]

theorem dec_of (M : DetMDP S) {l p : ℕ} (W : M.Walk l) (P : M.Walk p)
    (Cs : List (Σ k : ℕ, M.Walk k)) (hs : P.IsSimplePath) (h0 : P.x 0 = W.x 0)
    (h1 : P.x ⟨p, Nat.lt_succ_self p⟩ = W.x ⟨l, Nat.lt_succ_self l⟩)
    (ha : P.arcs + (Cs.map (fun C => C.2.arcs)).sum = W.arcs)
    (hc : ∀ C ∈ Cs, C.2.IsSimpleCycle ∧ ∃ t : Fin (l + 1), W.x t = C.2.x 0) :
    M.IsCycleDecomposition W P Cs := by
  refine ⟨hs, h0, h1, ?_, ?_, ha, hc⟩
  · have := congrArg Multiset.card ha
    rw [Multiset.card_add, card_arcs, card_arcs, ← cs_len] at this
    exact this
  · rw [cost_arcs M P, cs_cost, cost_arcs M W, ← ha, Multiset.map_add, Multiset.sum_add]

theorem rsplit {α : Type*} (F : ℕ → α) (a b : ℕ) :
    (Multiset.range (a + b)).map F =
      (Multiset.range a).map F + (Multiset.range b).map (fun t => F (a + t)) := by
  rw [Multiset.range_add, Multiset.map_add, Multiset.map_map]
  rfl

def spX (M : DetMDP S) {l : ℕ} (W : M.Walk l) (i d t : ℕ) : S :=
  if t < i then wX M W t else wX M W (t + d)

noncomputable def spE (M : DetMDP S) {l : ℕ} (W : M.Walk l) (i d t : ℕ) : M.D (spX M W i d t) :=
  if h : t < i then cdTr M (by unfold spX; rw [if_pos h]) (wE M W t)
  else cdTr M (by unfold spX; rw [if_neg h]) (wE M W (t + d))

theorem spE_sig1 (M : DetMDP S) {l : ℕ} (W : M.Walk l) (i d t : ℕ) (h : t < i) :
    (⟨spX M W i d t, spE M W i d t⟩ : Σ s, M.D s) = ⟨wX M W t, wE M W t⟩ := by
  simp only [spE, dif_pos h]
  exact cdTr_sig M _ _

theorem spE_sig2 (M : DetMDP S) {l : ℕ} (W : M.Walk l) (i d t : ℕ) (h : ¬ t < i) :
    (⟨spX M W i d t, spE M W i d t⟩ : Σ s, M.D s) = ⟨wX M W (t + d), wE M W (t + d)⟩ := by
  simp only [spE, dif_neg h]
  exact cdTr_sig M _ _

theorem spE_next (M : DetMDP S) {l : ℕ} (W : M.Walk l) (i d : ℕ) (hil : i + d ≤ l)
    (hrep : wX M W i = wX M W (i + d)) (t : ℕ) (ht : t < l - d) :
    M.next (spX M W i d t) (spE M W i d t) = spX M W i d (t + 1) := by
  by_cases h : t < i
  · rw [show M.next (spX M W i d t) (spE M W i d t) = M.next (wX M W t) (wE M W t) by
      simp only [spE, dif_pos h, cdTr_next]]
    rw [wE_next M W t (by omega)]
    by_cases h' : t + 1 < i
    · simp only [spX, if_pos h']
    · have e : t + 1 = i := by omega
      simp only [spX, if_neg h']
      rw [e]; exact hrep
  · rw [show M.next (spX M W i d t) (spE M W i d t) = M.next (wX M W (t + d)) (wE M W (t + d)) by
      simp only [spE, dif_neg h, cdTr_next]]
    rw [wE_next M W (t + d) (by omega)]
    simp only [spX, if_neg (show ¬ t + 1 < i by omega)]
    congr 1; omega
end CD

theorem cd_main {S : Type} [Fintype S] (M : DetMDP S) : ∀ (l : ℕ) (W : M.Walk l),
    ∃ (p : ℕ) (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)), M.IsCycleDecomposition W P Cs := by
  classical
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro W
  by_cases hinj : Function.Injective W.x
  · exact ⟨l, W, [], dec_of M W W [] hinj rfl rfl (by simp) (by simp)⟩
  have hQ : ∃ j, ∃ i < j, j ≤ l ∧ wX M W i = wX M W j := by
    simp only [Function.Injective] at hinj
    push_neg at hinj
    obtain ⟨a, b, hab, hne⟩ := hinj
    have ha := a.isLt
    have hb := b.isLt
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with h | h
    · exact ⟨b, a, h, by omega, by rw [wX_fin, wX_fin, hab]⟩
    · exact ⟨a, b, h, by omega, by rw [wX_fin, wX_fin, hab]⟩
  obtain ⟨i, hij, hjl, hXij⟩ := Nat.find_spec hQ
  have hmin : ∀ a b, a < b → b < Nat.find hQ → wX M W a ≠ wX M W b := by
    intro a b hab hb h
    exact Nat.find_min hQ hb ⟨a, hab, by omega, h⟩
  obtain ⟨d, hd⟩ : ∃ d, Nat.find hQ = i + d := ⟨Nat.find hQ - i, by omega⟩
  rw [hd] at hjl hXij hij hmin
  have hd0 : 0 < d := by omega
  let C : M.Walk d := ofRaw M d (fun t => wX M W (i + t)) (fun t => wE M W (i + t))
    (fun t ht => wE_next M W (i + t) (by omega))
  let R : M.Walk (l - d) := ofRaw M (l - d) (spX M W i d) (spE M W i d)
    (spE_next M W i d hjl hXij)
  obtain ⟨p, P, Cs', hdec⟩ := ih (l - d) (by omega) R
  obtain ⟨hs, h0, h1, -, -, ha, hc⟩ := hdec
  have key : W.arcs = R.arcs + C.arcs := by
    rw [arcs_eq M W, ofRaw_arcs, ofRaw_arcs]
    obtain ⟨r, hr⟩ : ∃ r, l = i + d + r := ⟨l - (i + d), by omega⟩
    have e1 : Multiset.range l = Multiset.range (i + d + r) := by rw [← hr]
    have e2 : l - d = i + r := by omega
    rw [e1, e2, rsplit, rsplit, rsplit]
    have h1 : (Multiset.range i).map (fun n => (⟨wX M W n, wE M W n⟩ : Σ s, M.D s)) =
        (Multiset.range i).map (fun t => (⟨spX M W i d t, spE M W i d t⟩ : Σ s, M.D s)) := by
      apply Multiset.map_congr rfl
      intro t ht
      exact (spE_sig1 M W i d t (Multiset.mem_range.1 ht)).symm
    have h3 : (Multiset.range r).map (fun t => (⟨wX M W (i + d + t), wE M W (i + d + t)⟩ : Σ s, M.D s)) =
        (Multiset.range r).map (fun t => (⟨spX M W i d (i + t), spE M W i d (i + t)⟩ : Σ s, M.D s)) := by
      apply Multiset.map_congr rfl
      intro t _
      rw [spE_sig2 M W i d (i + t) (by omega), show i + t + d = i + d + t by omega]
    rw [h1, h3]
    abel
  refine ⟨p, P, ⟨d, C⟩ :: Cs', dec_of M W P _ hs ?_ ?_ ?_ ?_⟩
  · rw [h0]
    show spX M W i d 0 = W.x 0
    rw [← wX_zero]
    unfold spX
    split_ifs with h
    · rfl
    · have : i = 0 := by omega
      subst this
      simpa using hXij.symm
  · rw [h1]
    show spX M W i d (l - d) = W.x ⟨l, _⟩
    unfold spX
    rw [if_neg (by omega), show l - d + d = l by omega]
    exact wX_le M W l le_rfl
  · rw [List.map_cons, List.sum_cons, key, ← ha]
    abel
  · intro C' hC'
    rcases List.mem_cons.1 hC' with rfl | hC'
    · refine ⟨⟨hd0, ?_, ?_⟩, ⟨⟨i, by omega⟩, ?_⟩⟩
      · show wX M W (i + ((0 : Fin (d+1)) : ℕ)) = wX M W (i + d)
        simpa using hXij
      · intro a b hab
        change wX M W (i + a) = wX M W (i + b) at hab
        have ha : (a : ℕ) < d := a.isLt
        have hb : (b : ℕ) < d := b.isLt
        apply Fin.ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact hmin (i + a) (i + b) (by omega) (by omega) hab
        · exact hmin (i + b) (i + a) (by omega) (by omega) hab.symm
      · show W.x ⟨i, _⟩ = wX M W (i + ((0 : Fin (d+1)) : ℕ))
        rw [← wX_le M W i (by omega)]
        simp
    · obtain ⟨hs', t, ht⟩ := hc C' hC'
      refine ⟨hs', ?_⟩
      rw [← ht]
      have htl := t.isLt
      change ∃ t' : Fin (l + 1), W.x t' = spX M W i d t
      unfold spX
      by_cases h : (t : ℕ) < i
      · rw [if_pos h]
        exact ⟨⟨t, by omega⟩, (wX_le M W t (by omega)).symm⟩
      · rw [if_neg h]
        exact ⟨⟨t + d, by omega⟩, (wX_le M W (t + d) (by omega)).symm⟩


section SPL
variable {S : Type} [Fintype S]

theorem sig_congr (M : DetMDP S) {k : ℕ} (C : M.Walk k) (a b : ℕ) (h : a = b) :
    (⟨wX M C a, wE M C a⟩ : Σ s, M.D s) = ⟨wX M C b, wE M C b⟩ := by subst h; rfl

def insX (M : DetMDP S) {l k : ℕ} (W : M.Walk l) (C : M.Walk k) (i t : ℕ) : S :=
  if t < i then wX M W t else if t < i + k then wX M C (t - i) else wX M W (t - k)

noncomputable def insE (M : DetMDP S) {l k : ℕ} (W : M.Walk l) (C : M.Walk k) (i t : ℕ) :
    M.D (insX M W C i t) :=
  if h : t < i then cdTr M (by unfold insX; rw [if_pos h]) (wE M W t)
  else if h2 : t < i + k then cdTr M (by unfold insX; rw [if_neg h, if_pos h2]) (wE M C (t - i))
  else cdTr M (by unfold insX; rw [if_neg h, if_neg h2]) (wE M W (t - k))

theorem insE_next (M : DetMDP S) {l k : ℕ} (W : M.Walk l) (C : M.Walk k) (i : ℕ) (hi : i ≤ l)
    (hb : wX M C 0 = wX M W i) (hc : wX M C k = wX M C 0) (t : ℕ) (ht : t < l + k) :
    M.next (insX M W C i t) (insE M W C i t) = insX M W C i (t + 1) := by
  by_cases h : t < i
  · rw [show M.next (insX M W C i t) (insE M W C i t) = M.next (wX M W t) (wE M W t) by
      simp only [insE, dif_pos h, cdTr_next]]
    rw [wE_next M W t (by omega)]
    by_cases h' : t + 1 < i
    · simp only [insX, if_pos h']
    · have e : t + 1 = i := by omega
      unfold insX; rw [if_neg h']
      by_cases hk : t + 1 < i + k
      · rw [if_pos hk, e, Nat.sub_self, hb]
      · rw [if_neg hk, e, show i - k = i by omega]
  · by_cases h2 : t < i + k
    · rw [show M.next (insX M W C i t) (insE M W C i t) = M.next (wX M C (t - i)) (wE M C (t - i)) by
        simp only [insE, dif_neg h, dif_pos h2, cdTr_next]]
      rw [wE_next M C (t - i) (by omega)]
      unfold insX; rw [if_neg (show ¬ t + 1 < i by omega)]
      by_cases h3 : t + 1 < i + k
      · rw [if_pos h3, show t - i + 1 = t + 1 - i by omega]
      · rw [if_neg h3, show t - i + 1 = k by omega, hc, hb, show t + 1 - k = i by omega]
    · rw [show M.next (insX M W C i t) (insE M W C i t) = M.next (wX M W (t - k)) (wE M W (t - k)) by
        simp only [insE, dif_neg h, dif_neg h2, cdTr_next]]
      rw [wE_next M W (t - k) (by omega)]
      unfold insX
      rw [if_neg (show ¬ t + 1 < i by omega), if_neg (show ¬ t + 1 < i + k by omega)]
      congr 1; omega

theorem splice (M : DetMDP S) {l k : ℕ} (W : M.Walk l) (C : M.Walk k) (i : ℕ) (hi : i ≤ l)
    (hb : C.x 0 = wX M W i) (hc : C.x (Fin.last k) = C.x 0) :
    ∃ W' : M.Walk (l + k), W'.x 0 = W.x 0 ∧ W'.x (Fin.last _) = W.x (Fin.last _) ∧
      W'.arcs = W.arcs + C.arcs ∧
      (∀ t : Fin (l + 1), ∃ t' : Fin (l + k + 1), W'.x t' = W.x t) ∧
      (∀ s : Fin (k + 1), ∃ t' : Fin (l + k + 1), W'.x t' = C.x s) := by
  have hb' : wX M C 0 = wX M W i := by rw [wX_zero]; exact hb
  have hc' : wX M C k = wX M C 0 := by
    rw [wX_zero, wX_le M C k le_rfl]; exact hc
  refine ⟨ofRaw M (l + k) (insX M W C i) (insE M W C i) (insE_next M W C i hi hb' hc'),
    ?_, ?_, ?_, ?_, ?_⟩
  · show insX M W C i 0 = _
    unfold insX
    by_cases h0 : 0 < i
    · rw [if_pos h0, wX_zero]
    · have : i = 0 := by omega
      subst this
      by_cases hk : 0 < 0 + k
      · rw [if_neg h0, if_pos hk, Nat.sub_zero, hb', wX_zero]
      · rw [if_neg h0, if_neg hk, Nat.zero_sub, wX_zero]
  · show insX M W C i (l + k) = _
    unfold insX
    rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel, wX_le M W l le_rfl]
    rfl
  · rw [ofRaw_arcs, arcs_eq M W, arcs_eq M C,
      show l + k = i + (k + (l - i)) by omega, rsplit, rsplit]
    have e1 : (Multiset.range i).map (fun t => (⟨insX M W C i t, insE M W C i t⟩ : Σ s, M.D s)) =
        (Multiset.range i).map (fun t => (⟨wX M W t, wE M W t⟩ : Σ s, M.D s)) := by
      apply Multiset.map_congr rfl
      intro t ht
      rw [Multiset.mem_range] at ht
      simp only [insE, dif_pos ht]; exact cdTr_sig M _ _
    have e2 : (Multiset.range k).map (fun t => (⟨insX M W C i (i + t), insE M W C i (i + t)⟩ : Σ s, M.D s)) =
        (Multiset.range k).map (fun t => (⟨wX M C t, wE M C t⟩ : Σ s, M.D s)) := by
      apply Multiset.map_congr rfl
      intro t ht
      rw [Multiset.mem_range] at ht
      simp only [insE, dif_neg (show ¬ i + t < i by omega), dif_pos (show i + t < i + k by omega)]
      rw [cdTr_sig]
      exact sig_congr M C _ _ (by omega)
    have e3 : (Multiset.range (l - i)).map
        (fun t => (⟨insX M W C i (i + (k + t)), insE M W C i (i + (k + t))⟩ : Σ s, M.D s)) =
        (Multiset.range (l - i)).map (fun t => (⟨wX M W (i + t), wE M W (i + t)⟩ : Σ s, M.D s)) := by
      apply Multiset.map_congr rfl
      intro t ht
      simp only [insE, dif_neg (show ¬ i + (k + t) < i by omega),
        dif_neg (show ¬ i + (k + t) < i + k by omega)]
      rw [cdTr_sig]
      exact sig_congr M W _ _ (by omega)
    have hl := rsplit (fun n => (⟨wX M W n, wE M W n⟩ : Σ s, M.D s)) i (l - i)
    rw [show i + (l - i) = l by omega] at hl
    rw [e1, e2, e3, hl]
    abel
  · intro t
    by_cases h : (t : ℕ) < i
    · refine ⟨⟨t, by omega⟩, ?_⟩
      show insX M W C i t = _
      unfold insX; rw [if_pos h, wX_fin]
    · refine ⟨⟨t + k, by omega⟩, ?_⟩
      show insX M W C i (t + k) = _
      unfold insX
      rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel, wX_fin]
  · intro s
    by_cases h : (s : ℕ) < k
    · refine ⟨⟨i + s, by omega⟩, ?_⟩
      show insX M W C i (i + s) = _
      unfold insX
      rw [if_neg (by omega), if_pos (by omega), show i + s - i = s by omega, wX_fin]
    · have hs : (s : ℕ) = k := by omega
      refine ⟨⟨i, by omega⟩, ?_⟩
      show insX M W C i i = _
      have : s = Fin.last k := Fin.ext hs
      rw [this, hc]
      unfold insX
      rw [if_neg (lt_irrefl _)]
      by_cases hk : i < i + k
      · rw [if_pos hk, Nat.sub_self, wX_zero]
      · rw [if_neg hk, show i - k = i by omega, ← hb]

def inV (M : DetMDP S) {p : ℕ} (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)) (v : S) : Prop :=
  (∃ t, P.x t = v) ∨ ∃ D ∈ Cs, ∃ t, D.2.x t = v

def good (M : DetMDP S) {p : ℕ} (P : M.Walk p) : List (Σ k : ℕ, M.Walk k) → Prop
  | [] => True
  | C :: Cs => good M P Cs ∧ inV M P Cs (C.2.x 0)

theorem assemble (M : DetMDP S) {p : ℕ} (P : M.Walk p) : ∀ (Cs : List (Σ k : ℕ, M.Walk k)),
    good M P Cs → (∀ C ∈ Cs, C.2.IsSimpleCycle) →
    ∃ L, ∃ W : M.Walk L, L = p + (Cs.map (fun C => C.1)).sum ∧ W.x 0 = P.x 0 ∧
      W.x (Fin.last L) = P.x (Fin.last p) ∧
      W.arcs = P.arcs + (Cs.map (fun C => C.2.arcs)).sum ∧ ∀ v, inV M P Cs v → ∃ t, W.x t = v
  | [], _, _ => ⟨p, P, by simp, rfl, rfl, by simp, fun v hv => by
      rcases hv with h | ⟨D, hD, _⟩
      · exact h
      · simp at hD⟩
  | C :: Cs, hg, hc => by
    obtain ⟨L, W, hL, h0, h1, ha, hv⟩ := assemble M P Cs hg.1 (fun D hD => hc D (List.mem_cons_of_mem _ hD))
    obtain ⟨t, ht⟩ := hv _ hg.2
    have hsc := hc C List.mem_cons_self
    obtain ⟨W', h0', h1', ha', hv1, hv2⟩ := splice M W C.2 t (by omega)
      (by rw [← ht, wX_fin]) hsc.2.1.symm
    refine ⟨L + C.1, W', by simp [hL]; omega, h0'.trans h0, h1'.trans h1, ?_, ?_⟩
    · rw [ha', ha]; simp; abel
    · intro v hv'
      rcases hv' with h | ⟨D, hD, s, hs⟩
      · obtain ⟨t1, ht1⟩ := hv v (Or.inl h)
        obtain ⟨t2, ht2⟩ := hv1 t1
        exact ⟨t2, ht2.trans ht1⟩
      · rcases List.mem_cons.mp hD with rfl | hD'
        · obtain ⟨t2, ht2⟩ := hv2 s
          exact ⟨t2, ht2.trans hs⟩
        · obtain ⟨t1, ht1⟩ := hv v (Or.inr ⟨D, hD', s, hs⟩)
          obtain ⟨t2, ht2⟩ := hv1 t1
          exact ⟨t2, ht2.trans ht1⟩

theorem good_cons_mem (M : DetMDP S) {p : ℕ} (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k))
    (C : Σ k : ℕ, M.Walk k) (hC : C ∈ Cs) (hg : good M P Cs) : good M P (C :: Cs) :=
  ⟨hg, Or.inr ⟨C, hC, 0, rfl⟩⟩

theorem inV_drop (M : DetMDP S) {p : ℕ} (P : M.Walk p) (L₁ L₂ : List (Σ k : ℕ, M.Walk k))
    (C : Σ k : ℕ, M.Walk k) (hC : C ∈ L₂) (v : S) (h : inV M P (L₁ ++ C :: L₂) v) :
    inV M P (L₁ ++ L₂) v := by
  rcases h with h | ⟨D, hD, t, ht⟩
  · exact Or.inl h
  · right
    rcases List.mem_append.mp hD with h1 | h2
    · exact ⟨D, List.mem_append_left _ h1, t, ht⟩
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact ⟨D, List.mem_append_right _ hC, t, ht⟩
      · exact ⟨D, List.mem_append_right _ h3, t, ht⟩

theorem good_drop (M : DetMDP S) {p : ℕ} (P : M.Walk p) (L₂ : List (Σ k : ℕ, M.Walk k))
    (C : Σ k : ℕ, M.Walk k) (hC : C ∈ L₂) :
    ∀ L₁ : List (Σ k : ℕ, M.Walk k), good M P (L₁ ++ C :: L₂) → good M P (L₁ ++ L₂)
  | [], h => h.1
  | D :: L₁, h => ⟨good_drop M P L₂ C hC L₁ h.1, inV_drop M P L₁ L₂ C hC _ h.2⟩

theorem good_erase (M : DetMDP S) [DecidableEq (Σ k : ℕ, M.Walk k)] {p : ℕ} (P : M.Walk p)
    (Cs : List (Σ k : ℕ, M.Walk k)) (C : Σ k : ℕ, M.Walk k) (h2 : 2 ≤ Cs.count C)
    (hg : good M P Cs) : good M P (Cs.erase C) := by
  have hC : C ∈ Cs := List.count_pos_iff.mp (by omega)
  obtain ⟨L₁, L₂, hn, rfl, he⟩ := List.exists_erase_eq hC
  rw [he]
  have : C ∈ L₂ := by
    rw [List.count_append, List.count_cons_self, List.count_eq_zero_of_not_mem hn] at h2
    exact List.count_pos_iff.mp (by omega)
  exact good_drop M P L₂ C this L₁ hg
end SPL

theorem cd_good {S : Type} [Fintype S] (M : DetMDP S) : ∀ (l : ℕ) (W : M.Walk l),
    ∃ (p : ℕ) (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)), M.IsCycleDecomposition W P Cs ∧
      good M P Cs ∧ ∀ t : Fin (l + 1), inV M P Cs (W.x t) := by
  classical
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro W
  by_cases hinj : Function.Injective W.x
  · exact ⟨l, W, [], dec_of M W W [] hinj rfl rfl (by simp) (by simp), trivial, fun t => Or.inl ⟨t, rfl⟩⟩
  have hQ : ∃ j, ∃ i < j, j ≤ l ∧ wX M W i = wX M W j := by
    simp only [Function.Injective] at hinj
    push_neg at hinj
    obtain ⟨a, b, hab, hne⟩ := hinj
    have ha := a.isLt
    have hb := b.isLt
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with h | h
    · exact ⟨b, a, h, by omega, by rw [wX_fin, wX_fin, hab]⟩
    · exact ⟨a, b, h, by omega, by rw [wX_fin, wX_fin, hab]⟩
  obtain ⟨i, hij, hjl, hXij⟩ := Nat.find_spec hQ
  have hmin : ∀ a b, a < b → b < Nat.find hQ → wX M W a ≠ wX M W b := by
    intro a b hab hb h
    exact Nat.find_min hQ hb ⟨a, hab, by omega, h⟩
  obtain ⟨d, hd⟩ : ∃ d, Nat.find hQ = i + d := ⟨Nat.find hQ - i, by omega⟩
  rw [hd] at hjl hXij hij hmin
  have hd0 : 0 < d := by omega
  let C : M.Walk d := ofRaw M d (fun t => wX M W (i + t)) (fun t => wE M W (i + t))
    (fun t ht => wE_next M W (i + t) (by omega))
  let R : M.Walk (l - d) := ofRaw M (l - d) (spX M W i d) (spE M W i d)
    (spE_next M W i d hjl hXij)
  obtain ⟨p, P, Cs', hdec, hgd, hcov⟩ := ih (l - d) (by omega) R
  obtain ⟨hs, h0, h1, -, -, ha, hc⟩ := hdec
  have key : W.arcs = R.arcs + C.arcs := by
    rw [arcs_eq M W, ofRaw_arcs, ofRaw_arcs]
    obtain ⟨r, hr⟩ : ∃ r, l = i + d + r := ⟨l - (i + d), by omega⟩
    have e1 : Multiset.range l = Multiset.range (i + d + r) := by rw [← hr]
    have e2 : l - d = i + r := by omega
    rw [e1, e2, rsplit, rsplit, rsplit]
    have h1 : (Multiset.range i).map (fun n => (⟨wX M W n, wE M W n⟩ : Σ s, M.D s)) =
        (Multiset.range i).map (fun t => (⟨spX M W i d t, spE M W i d t⟩ : Σ s, M.D s)) := by
      apply Multiset.map_congr rfl
      intro t ht
      exact (spE_sig1 M W i d t (Multiset.mem_range.1 ht)).symm
    have h3 : (Multiset.range r).map (fun t => (⟨wX M W (i + d + t), wE M W (i + d + t)⟩ : Σ s, M.D s)) =
        (Multiset.range r).map (fun t => (⟨spX M W i d (i + t), spE M W i d (i + t)⟩ : Σ s, M.D s)) := by
      apply Multiset.map_congr rfl
      intro t _
      rw [spE_sig2 M W i d (i + t) (by omega), show i + t + d = i + d + t by omega]
    rw [h1, h3]
    abel
  have hRi : R.x ⟨i, by omega⟩ = wX M W i := by
    show spX M W i d i = _
    unfold spX; rw [if_neg (lt_irrefl _)]; exact hXij.symm
  have hgood : good M P (⟨d, C⟩ :: Cs') := by
    refine ⟨hgd, ?_⟩
    have := hcov ⟨i, by omega⟩
    rw [hRi] at this
    show inV M P Cs' (wX M W (i + 0))
    simpa using this
  have hcov' : ∀ t : Fin (l + 1), inV M P (⟨d, C⟩ :: Cs') (W.x t) := by
    intro t
    have htl := t.isLt
    have lift : ∀ v, inV M P Cs' v → inV M P (⟨d, C⟩ :: Cs') v := by
      rintro v (h | ⟨D, hD, s, hs⟩)
      · exact Or.inl h
      · exact Or.inr ⟨D, List.mem_cons_of_mem _ hD, s, hs⟩
    by_cases h1 : (t : ℕ) < i
    · apply lift
      have := hcov ⟨t, by omega⟩
      have e : R.x ⟨t, by omega⟩ = W.x t := by
        show spX M W i d t = _
        unfold spX; rw [if_pos h1, wX_fin]
      rwa [e] at this
    · by_cases h2 : (t : ℕ) ≤ i + d
      · right
        refine ⟨⟨d, C⟩, List.mem_cons_self, ⟨t - i, (by omega : (t : ℕ) - i < d + 1)⟩, ?_⟩
        show wX M W (i + (t - i)) = _
        rw [show i + (t - i) = t by omega, wX_fin]
      · apply lift
        have := hcov ⟨t - d, by omega⟩
        have e : R.x ⟨t - d, by omega⟩ = W.x t := by
          show spX M W i d (t - d) = _
          unfold spX; rw [if_neg (by omega), show t - d + d = t by omega, wX_fin]
        rwa [e] at this
  refine ⟨p, P, ⟨d, C⟩ :: Cs', dec_of M W P _ hs ?_ ?_ ?_ ?_, hgood, hcov'⟩
  · rw [h0]
    show spX M W i d 0 = W.x 0
    rw [← wX_zero]
    unfold spX
    split_ifs with h
    · rfl
    · have : i = 0 := by omega
      subst this
      simpa using hXij.symm
  · rw [h1]
    show spX M W i d (l - d) = W.x ⟨l, _⟩
    unfold spX
    rw [if_neg (by omega), show l - d + d = l by omega]
    exact wX_le M W l le_rfl
  · rw [List.map_cons, List.sum_cons, key, ← ha]
    abel
  · intro C' hC'
    rcases List.mem_cons.1 hC' with rfl | hC'
    · refine ⟨⟨hd0, ?_, ?_⟩, ⟨⟨i, by omega⟩, ?_⟩⟩
      · show wX M W (i + ((0 : Fin (d+1)) : ℕ)) = wX M W (i + d)
        simpa using hXij
      · intro a b hab
        change wX M W (i + a) = wX M W (i + b) at hab
        have ha : (a : ℕ) < d := a.isLt
        have hb : (b : ℕ) < d := b.isLt
        apply Fin.ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact hmin (i + a) (i + b) (by omega) (by omega) hab
        · exact hmin (i + b) (i + a) (by omega) (by omega) hab.symm
      · show W.x ⟨i, _⟩ = wX M W (i + ((0 : Fin (d+1)) : ℕ))
        rw [← wX_le M W i (by omega)]
        simp
    · obtain ⟨hs', t, ht⟩ := hc C' hC'
      refine ⟨hs', ?_⟩
      rw [← ht]
      have htl := t.isLt
      change ∃ t' : Fin (l + 1), W.x t' = spX M W i d t
      unfold spX
      by_cases h : (t : ℕ) < i
      · rw [if_pos h]
        exact ⟨⟨t, by omega⟩, (wX_le M W t (by omega)).symm⟩
      · rw [if_neg h]
        exact ⟨⟨t + d, by omega⟩, (wX_le M W (t + d) (by omega)).symm⟩



section OFC
open OFCList
variable {S : Type} [Fintype S]

def GP (M : DetMDP S) (s₀ : S) (T : ℕ) {p : ℕ} (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)) : Prop :=
  P.IsSimplePath ∧ P.x 0 = s₀ ∧ good M P Cs ∧ (∀ C ∈ Cs, C.2.IsSimpleCycle) ∧
    p + (Cs.map (fun C => C.1)).sum = T

def gcost (M : DetMDP S) {p : ℕ} (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)) : ℝ :=
  P.cost + (Cs.map (fun C => C.2.cost)).sum

theorem realize (M : DetMDP S) (s₀ : S) (T : ℕ) {p : ℕ} (P : M.Walk p)
    (Cs : List (Σ k : ℕ, M.Walk k)) (h : GP M s₀ T P Cs) :
    ∃ W : M.Walk T, W.x 0 = s₀ ∧ M.IsCycleDecomposition W P Cs := by
  obtain ⟨hs, hx0, hg, hc, hT⟩ := h
  obtain ⟨L, W, hL, h0, h1, ha, hv⟩ := assemble M P Cs hg hc
  have : L = T := hL.trans hT
  subst this
  refine ⟨W, h0.trans hx0, dec_of M W P Cs hs h0.symm h1.symm ha.symm ?_⟩
  intro C hC
  obtain ⟨t, ht⟩ := hv _ (Or.inr ⟨C, hC, 0, rfl⟩)
  exact ⟨hc C hC, t, ht⟩

theorem of_walk (M : DetMDP S) (s₀ : S) (T : ℕ) (W : M.Walk T) (h0 : W.x 0 = s₀) :
    ∃ (p : ℕ) (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)),
      GP M s₀ T P Cs ∧ gcost M P Cs = W.cost := by
  obtain ⟨p, P, Cs, hd, hg, -⟩ := cd_good M T W
  obtain ⟨hs, hp0, -, hlen, hcost, -, hc⟩ := hd
  exact ⟨p, P, Cs, ⟨hs, hp0.trans h0, hg, fun C hC => (hc C hC).1, hlen⟩, hcost⟩

theorem good_eraseN (M : DetMDP S) [DecidableEq (Σ k : ℕ, M.Walk k)] {p : ℕ} (P : M.Walk p)
    (a : Σ k : ℕ, M.Walk k) : ∀ (j : ℕ) (l : List (Σ k : ℕ, M.Walk k)),
      j < l.count a → good M P l → good M P (eraseN a j l)
  | 0, l, _, hg => hg
  | j + 1, l, hj, hg => by
    rw [eraseN]
    apply good_eraseN M P a j
    · rw [List.count_erase_self]; omega
    · exact good_erase M P l a (by omega) hg

theorem good_rep (M : DetMDP S) {p : ℕ} (P : M.Walk p) (b : Σ k : ℕ, M.Walk k)
    (l : List (Σ k : ℕ, M.Walk k)) (hb : b ∈ l) (hg : good M P l) :
    ∀ j : ℕ, good M P (List.replicate j b ++ l)
  | 0 => hg
  | j + 1 => by
    rw [List.replicate_succ, List.cons_append]
    exact good_cons_mem M P _ b (List.mem_append_right _ hb) (good_rep M P b l hb hg j)

theorem exch (M : DetMDP S) [DecidableEq (Σ k : ℕ, M.Walk k)] (s₀ : S) (T : ℕ) {p : ℕ}
    (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)) (h : GP M s₀ T P Cs)
    (C₁ C₂ : Σ k : ℕ, M.Walk k) (h₂ : C₂ ∈ Cs) (hne : C₂ ≠ C₁) (hk : C₂.1 < Cs.count C₁) :
    let Cs' := List.replicate C₁.1 C₂ ++ eraseN C₁ C₂.1 Cs
    GP M s₀ T P Cs' ∧
      gcost M P Cs' + (C₂.1 : ℝ) * C₁.2.cost = gcost M P Cs + (C₁.1 : ℝ) * C₂.2.cost ∧
      Cs'.count C₁ = Cs.count C₁ - C₂.1 ∧ Cs'.count C₂ = Cs.count C₂ + C₁.1 ∧
      ∀ D, D ≠ C₁ → D ≠ C₂ → Cs'.count D = Cs.count D := by
  intro Cs'
  obtain ⟨hs, hx0, hg, hc, hT⟩ := h
  have hm : C₂ ∈ eraseN C₁ C₂.1 Cs := mem_eraseN C₁ C₂ hne _ _ h₂
  have hlen := sum_map_eraseN (fun C : Σ k : ℕ, M.Walk k => C.1) C₁ C₂.1 Cs hk.le
  have hcst := sum_map_eraseN (fun C : Σ k : ℕ, M.Walk k => C.2.cost) C₁ C₂.1 Cs hk.le
  refine ⟨⟨hs, hx0, good_rep M P C₂ _ hm (good_eraseN M P C₁ _ _ hk hg) _, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro C hC
    rcases List.mem_append.mp hC with h1 | h1
    · rw [List.eq_of_mem_replicate h1]; exact hc C₂ h₂
    · exact hc C (mem_of_mem_eraseN _ _ _ _ h1)
  · simp only [Cs', List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
      smul_eq_mul]
    rw [← hT, hlen, smul_eq_mul]; ring
  · simp only [gcost, Cs', List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, nsmul_eq_mul]
    rw [hcst, nsmul_eq_mul]; ring
  · simp only [Cs', List.count_append, List.count_replicate, count_eraseN]
    rw [if_neg (by simpa using hne)]; simp
  · simp only [Cs', List.count_append, List.count_replicate_self, count_eraseN_ne C₁ C₂ hne]
    omega
  · intro D h1 h2
    simp only [Cs', List.count_append, List.count_replicate, count_eraseN_ne C₁ D h1]
    rw [if_neg (by simpa using h2.symm)]; simp
end OFC

section HW
variable {S : Type} [Fintype S]
def hwPathWalk (M : DetMDP S) (s₀ : S) (δ : M.Policy) (T : ℕ) : M.Walk T where
  x := fun t => M.path s₀ δ t
  e := fun t => δ (M.path s₀ δ t) t
  valid := fun t => rfl

theorem hwPathWalk_cost (M : DetMDP S) (s₀ : S) (δ : M.Policy) (T : ℕ) :
    (hwPathWalk M s₀ δ T).cost = M.horizonCost s₀ δ T := by
  unfold DetMDP.Walk.cost DetMDP.horizonCost
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

theorem hw_finite (M : DetMDP S) (s₀ : S) (T : ℕ) :
    {y : ℝ | ∃ W : M.Walk T, W.x 0 = s₀ ∧ y = W.cost}.Finite := by
  apply (Set.finite_range (fun f : Fin T → (Σ s : S, M.D s) =>
    ∑ t : Fin T, M.c (f t).1 (f t).2)).subset
  rintro y ⟨W, _, rfl⟩
  exact ⟨fun t => ⟨W.x t.castSucc, W.e t⟩, rfl⟩
end HW

theorem cyc_len {S : Type} [Fintype S] (M : DetMDP S) {k : ℕ} (C : M.Walk k) (h : C.IsSimpleCycle) :
    1 ≤ k ∧ k ≤ Fintype.card S := by
  refine ⟨h.1, ?_⟩
  have := Fintype.card_le_of_injective _ h.2.2
  simpa using this

open OFCList in
theorem solution {S : Type} [Fintype S] (M : DetMDP S) (s₀ : S) (T : ℕ) :
    ∃ (W : M.Walk T), W.x 0 = s₀ ∧
      IsLeast {y : ℝ | ∃ V : M.Walk T, V.x 0 = s₀ ∧ y = V.cost} W.cost ∧
      ∃ (p : ℕ) (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)),
        M.IsCycleDecomposition W P Cs ∧
        ∀ C₁ ∈ Cs, ∀ C₂ ∈ Cs,
          Fintype.card S < Set.ncard {i : Fin Cs.length | Cs[i] = C₁} →
          (C₁.2.cost / (C₁.1 : ℝ) ≤ C₂.2.cost / (C₂.1 : ℝ)) ∧
          (Fintype.card S < Set.ncard {i : Fin Cs.length | Cs[i] = C₂} → C₁ = C₂) := by
  classical
  set n := Fintype.card S
  set A := {y : ℝ | ∃ V : M.Walk T, V.x 0 = s₀ ∧ y = V.cost}
  have hne : A.Nonempty :=
    ⟨_, hwPathWalk M s₀ (fun s _ => Classical.arbitrary _) T, rfl, rfl⟩
  obtain ⟨m, hmA, hmin⟩ := (hw_finite M s₀ T).exists_minimal hne
  have hlow : ∀ y ∈ A, m ≤ y := by
    intro y hy
    by_contra hlt
    push_neg at hlt
    exact absurd (hmin hy hlt.le) (by intro h; linarith)
  let Ψ : List (Σ k : ℕ, M.Walk k) → ℕ := fun Cs => (Cs.toFinset.filter (fun C => n < Cs.count C)).card
  have hQ : ∃ j, ∃ (p : ℕ) (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)),
      GP M s₀ T P Cs ∧ gcost M P Cs = m ∧ Ψ Cs = j := by
    obtain ⟨W, hW0, hWc⟩ := hmA
    obtain ⟨p, P, Cs, hG, hc⟩ := of_walk M s₀ T W hW0
    exact ⟨_, p, P, Cs, hG, hc.trans hWc.symm, rfl⟩
  obtain ⟨p, P, Cs, hG, hcost, hΨ⟩ := Nat.find_spec hQ
  have hlowg : ∀ Cs' : List (Σ k : ℕ, M.Walk k), GP M s₀ T P Cs' → m ≤ gcost M P Cs' := by
    intro Cs' hG'
    obtain ⟨W', hW0', hd'⟩ := realize M s₀ T P Cs' hG'
    have := hlow _ ⟨W', hW0', rfl⟩
    have hc' : gcost M P Cs' = W'.cost := hd'.2.2.2.2.1
    linarith
  obtain ⟨W, hW0, hd⟩ := realize M s₀ T P Cs hG
  have hWc : W.cost = m := hd.2.2.2.2.1.symm.trans hcost
  refine ⟨W, hW0, ⟨⟨W, hW0, rfl⟩, fun y hy => hWc ▸ hlow y hy⟩, p, P, Cs, hd, ?_⟩
  have hsc := hG.2.2.2.1
  -- (a) the mean inequality
  have hmean : ∀ Cs' : List (Σ k : ℕ, M.Walk k), GP M s₀ T P Cs' → gcost M P Cs' = m →
      ∀ C₁ ∈ Cs', ∀ C₂ ∈ Cs', n < Cs'.count C₁ →
      C₁.2.cost / (C₁.1 : ℝ) ≤ C₂.2.cost / (C₂.1 : ℝ) := by
    intro Cs' hG' hc' C₁ h₁ C₂ h₂ hf
    by_contra hlt
    push_neg at hlt
    have hne : C₂ ≠ C₁ := by rintro rfl; exact lt_irrefl _ hlt
    obtain ⟨k1, k1n⟩ := cyc_len M C₁.2 (hG'.2.2.2.1 C₁ h₁)
    obtain ⟨k2, k2n⟩ := cyc_len M C₂.2 (hG'.2.2.2.1 C₂ h₂)
    obtain ⟨hG'', hc'', -⟩ := exch M s₀ T P Cs' hG' C₁ C₂ h₂ hne (by omega)
    have hpos1 : (0 : ℝ) < C₁.1 := by exact_mod_cast k1
    have hpos2 : (0 : ℝ) < C₂.1 := by exact_mod_cast k2
    rw [div_lt_div_iff₀ hpos2 hpos1] at hlt
    have := hlowg _ hG''
    nlinarith
  intro C₁ h₁ C₂ h₂ hf₁
  rw [ncard_idx] at hf₁
  refine ⟨hmean Cs hG hcost C₁ h₁ C₂ h₂ hf₁, ?_⟩
  intro hf₂
  rw [ncard_idx] at hf₂
  by_contra hne'
  have hne : C₂ ≠ C₁ := fun h => hne' h.symm
  have e1 := hmean Cs hG hcost C₁ h₁ C₂ h₂ hf₁
  have e2 := hmean Cs hG hcost C₂ h₂ C₁ h₁ hf₂
  obtain ⟨k1, k1n⟩ := cyc_len M C₁.2 (hsc C₁ h₁)
  obtain ⟨k2, k2n⟩ := cyc_len M C₂.2 (hsc C₂ h₂)
  have hpos1 : (0 : ℝ) < C₁.1 := by exact_mod_cast k1
  have hpos2 : (0 : ℝ) < C₂.1 := by exact_mod_cast k2
  have heq : (C₁.1 : ℝ) * C₂.2.cost = (C₂.1 : ℝ) * C₁.2.cost := by
    have := le_antisymm e1 e2
    rw [div_eq_div_iff hpos1.ne' hpos2.ne'] at this
    linarith
  -- repeated exchange
  have rep : ∀ r : ℕ, ∀ Cs' : List (Σ k : ℕ, M.Walk k), GP M s₀ T P Cs' → gcost M P Cs' = m →
      n < Cs'.count C₂ → Cs'.count C₁ ≤ n + r →
      ∃ Cs'' : List (Σ k : ℕ, M.Walk k), GP M s₀ T P Cs'' ∧ gcost M P Cs'' = m ∧
        Cs''.count C₁ ≤ n ∧ n < Cs''.count C₂ ∧
        ∀ D, D ≠ C₁ → D ≠ C₂ → Cs''.count D = Cs'.count D := by
    intro r
    induction r with
    | zero => intro Cs' hG' hc' hf hr; exact ⟨Cs', hG', hc', by omega, hf, fun _ _ _ => rfl⟩
    | succ r ih =>
      intro Cs' hG' hc' hf hr
      by_cases hsmall : Cs'.count C₁ ≤ n
      · exact ⟨Cs', hG', hc', hsmall, hf, fun _ _ _ => rfl⟩
      have h₂' : C₂ ∈ Cs' := List.count_pos_iff.mp (by omega)
      obtain ⟨hG'', hc'', hn1, hn2, hn3⟩ := exch M s₀ T P Cs' hG' C₁ C₂ h₂' hne (by omega)
      obtain ⟨Cs₃, hG₃, hc₃, h31, h32, h33⟩ := ih _ hG''
        (by linarith) (by omega) (by omega)
      exact ⟨Cs₃, hG₃, hc₃, h31, h32, fun D d1 d2 => (h33 D d1 d2).trans (hn3 D d1 d2)⟩
  obtain ⟨Cs'', hG'', hc'', h1, h2, h3⟩ := rep (Cs.count C₁) Cs hG hcost hf₂ (by omega)
  have hsub : (Cs''.toFinset.filter (fun C => n < Cs''.count C)) ⊆
      (Cs.toFinset.filter (fun C => n < Cs.count C)).erase C₁ := by
    intro D hD
    simp only [Finset.mem_filter, List.mem_toFinset] at hD
    have hD1 : D ≠ C₁ := by rintro rfl; omega
    rw [Finset.mem_erase, Finset.mem_filter, List.mem_toFinset]
    by_cases hD2 : D = C₂
    · subst hD2; exact ⟨hD1, h₂, hf₂⟩
    · have := h3 D hD1 hD2
      refine ⟨hD1, List.count_pos_iff.mp (by omega), by omega⟩
  have hmem : C₁ ∈ Cs.toFinset.filter (fun C => n < Cs.count C) := by
    simp only [Finset.mem_filter, List.mem_toFinset]; exact ⟨h₁, hf₁⟩
  have hlt : Ψ Cs'' < Ψ Cs := by
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hmem] at hc1
    have hc2 : 0 < (Cs.toFinset.filter (fun C => n < Cs.count C)).card := Finset.card_pos.mpr ⟨_, hmem⟩
    exact lt_of_le_of_lt hc1 (Nat.sub_lt hc2 Nat.one_pos)
  rw [hΨ] at hlt
  exact Nat.find_min hQ hlt ⟨p, P, Cs'', hG'', hc'', rfl⟩
