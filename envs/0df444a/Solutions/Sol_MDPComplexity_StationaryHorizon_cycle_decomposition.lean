-- Prove2me | solution 1 for MDPComplexity.StationaryHorizon.cycle_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T18:02:54.373228+00:00
-- url     : https://prove2.me/submissions/447f282d-1f22-4315-b219-a12ed4e86590

import Mathlib
import Definitions.Def_MDPComplexity_StationaryHorizon_Model

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

theorem solution {S : Type} [Fintype S] (M : DetMDP S) {l : ℕ} (W : M.Walk l) :
    ∃ (p : ℕ) (P : M.Walk p) (Cs : List (Σ k : ℕ, M.Walk k)),
      M.IsCycleDecomposition W P Cs := cd_main M l W
