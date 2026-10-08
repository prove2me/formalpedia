-- Prove2me | solution 1 for Menger27.Graphs.glue_paths
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:03:07.707264+00:00
-- url     : https://prove2.me/submissions/3834d305-4451-485b-af5a-58623ab3a544

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts



namespace Menger27.Graphs

theorem sideVerts_not_mem {V : Type*} (G : SimpleGraph V) (P S : Finset V) {u : V}
    (hu : u ∈ sideVerts G P S) : u ∉ S := by
  obtain ⟨x, hx, w, hw⟩ := hu
  exact hw u w.end_mem_support

theorem sideVerts_of_P {V : Type*} (G : SimpleGraph V) (P S : Finset V) {x : V}
    (hx : x ∈ P) (hxS : x ∉ S) : x ∈ sideVerts G P S :=
  ⟨x, hx, SimpleGraph.Walk.nil, by simpa using hxS⟩

theorem sidePart_le {V : Type*} (G : SimpleGraph V) (P S : Finset V) : sidePart G P S ≤ G :=
  fun _ _ h => h.1

theorem sideVerts_extend {V : Type*} (G : SimpleGraph V) (P S : Finset V) {a c : V}
    (ha : a ∈ sideVerts G P S) (h : G.Adj a c) (hc : c ∉ S) : c ∈ sideVerts G P S := by
  obtain ⟨x, hx, wx, hwx⟩ := ha
  refine ⟨x, hx, wx.concat h, ?_⟩
  intro q hq
  rw [SimpleGraph.Walk.support_concat] at hq
  simp at hq
  rcases hq with hq | rfl
  · exact hwx q hq
  · exact hc

theorem sidePart_walk_S {V : Type*} (G : SimpleGraph V) (P S : Finset V) {a b : V}
    (w : (sidePart G P S).Walk a b) (ha : a ∈ S → a ∉ P) :
    ∀ z ∈ w.support, z ∈ S → z ∉ P := by
  induction w with
  | nil => intro z hz; simp at hz; subst hz; exact ha
  | @cons a c b h p ih =>
    intro z hz
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ha
    · apply ih _ z hz
      intro hcS
      have h' : G.Adj a c ∧ (a ∈ sideVerts G P S ∨ c ∈ sideVerts G P S) ∧
        (a ∈ sideVerts G P S ∨ (a ∈ S ∧ a ∉ P)) ∧ (c ∈ sideVerts G P S ∨ (c ∈ S ∧ c ∉ P)) := h
      rcases h'.2.2.2 with h4 | ⟨_, h4⟩
      · exact absurd hcS (sideVerts_not_mem G P S h4)
      · exact h4

theorem sidePart_walk_sv {V : Type*} (G : SimpleGraph V) (P S : Finset V) {a b : V}
    (w : (sidePart G P S).Walk a b) (hw : w.IsPath)
    (ha : a ∈ sideVerts G P S) (hS : ∀ y ∈ w.support, y ∈ S → y = b) :
    ∀ z ∈ w.support, z = b ∨ z ∈ sideVerts G P S := by
  induction w with
  | nil => intro z hz; simp at hz; exact Or.inl hz
  | @cons a c b h p ih =>
    intro z hz
    rw [SimpleGraph.Walk.cons_isPath_iff] at hw
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Or.inr ha
    · by_cases hcS : c ∈ S
      · have hcb : c = b := hS c (by simp) hcS
        subst hcb
        have := SimpleGraph.Walk.isPath_iff_eq_nil.mp hw.1
        subst this
        simp at hz
        exact Or.inl hz
      · have hcsv : c ∈ sideVerts G P S := sideVerts_extend G P S ha h.1 hcS
        exact ih hw.1 hcsv (fun y hy hyS => hS y (by simp [hy]) hyS) z hz

theorem side_family {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (P S : Finset V)
    (hP : HasDisjointPaths (sidePart G P S) (P \ S) (S \ P) (S \ P).card) :
    ∃ (α : S → V) (p : ∀ s : S, G.Walk (α s) s.1),
      (∀ s, α s ∈ P) ∧ (∀ s, (p s).IsPath) ∧
      (∀ s s' : S, s ≠ s' → List.Disjoint (p s).support (p s').support) ∧
      (∀ s, ∀ z ∈ (p s).support, z = s.1 ∨ z ∈ sideVerts G P S) := by
  classical
  obtain ⟨a, b, w, hw, hdisj⟩ := hP
  have hb : ∀ i, b i ∈ S \ P := fun i => (hw i).2.1
  have hbinj : Function.Injective b := by
    intro i j hij
    by_contra hne
    have h2 : b i ∈ (w j).support := by rw [hij]; exact (w j).end_mem_support
    exact hdisj i j hne (w i).end_mem_support h2
  have hbsurj : ∀ y ∈ S \ P, ∃ i, b i = y := by
    have hsub : (Finset.univ : Finset (Fin (S \ P).card)).image b ⊆ S \ P := by
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact hb i
    have hc : (S \ P).card ≤ ((Finset.univ : Finset (Fin (S \ P).card)).image b).card := by
      rw [Finset.card_image_of_injective _ hbinj]; simp
    have heq := Finset.eq_of_subset_of_card_le hsub hc
    intro y hy
    rw [← heq] at hy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hy
    exact ⟨i, hi⟩
  have hwS : ∀ i, ∀ y ∈ (w i).support, y ∈ S → y = b i := by
    intro i y hy hyS
    have hy' : y ∉ P := sidePart_walk_S G P S (w i)
      (fun h => absurd h (Finset.mem_sdiff.mp (hw i).1).2) y hy hyS
    obtain ⟨j, hj⟩ := hbsurj y (Finset.mem_sdiff.mpr ⟨hyS, hy'⟩)
    by_cases hij : i = j
    · rw [← hj, hij]
    · have hyj : y ∈ (w j).support := by rw [← hj]; exact (w j).end_mem_support
      exact absurd hyj (fun h => hdisj i j hij hy h)
  have hwsv : ∀ i, ∀ z ∈ (w i).support, z = b i ∨ z ∈ sideVerts G P S := fun i =>
    sidePart_walk_sv G P S (w i) (hw i).2.2
      (sideVerts_of_P G P S (Finset.mem_sdiff.mp (hw i).1).1 (Finset.mem_sdiff.mp (hw i).1).2)
      (hwS i)
  have claim : ∀ s : S, ∃ (α : V) (p : G.Walk α s.1), α ∈ P ∧ p.IsPath ∧
      (∀ z ∈ p.support, z = s.1 ∨ z ∈ sideVerts G P S) ∧ (s.1 ∈ P → p.support = [s.1]) ∧
      (s.1 ∉ P → ∃ i, b i = s.1 ∧ p.support = (w i).support) := by
    intro s
    by_cases hsP : s.1 ∈ P
    · exact ⟨s.1, SimpleGraph.Walk.nil, hsP, by simp,
        by intro z hz; simp at hz; exact Or.inl hz, fun _ => by simp, fun h => absurd hsP h⟩
    · obtain ⟨i, hi⟩ := hbsurj s.1 (Finset.mem_sdiff.mpr ⟨s.2, hsP⟩)
      refine ⟨a i, ((w i).mapLe (sidePart_le G P S)).copy rfl hi,
        (Finset.mem_sdiff.mp (hw i).1).1, ?_, ?_, fun h => absurd h hsP, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact (SimpleGraph.Walk.isPath_mapLe _).mpr (hw i).2.2
      · intro z hz
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_mapLe_eq_support] at hz
        rcases hwsv i z hz with h | h
        · exact Or.inl (h.trans hi)
        · exact Or.inr h
      · intro _
        exact ⟨i, hi, by rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_mapLe_eq_support]⟩
  choose α p hα hpath hsv hP1 hP2 using claim
  refine ⟨α, p, hα, hpath, ?_, hsv⟩
  intro s s' hss' z hz hz'
  by_cases hs : s.1 ∈ P <;> by_cases hs' : s'.1 ∈ P
  · rw [hP1 s hs] at hz; rw [hP1 s' hs'] at hz'
    simp at hz hz'
    exact hss' (Subtype.ext (hz.symm.trans hz'))
  · rw [hP1 s hs] at hz
    simp at hz
    rcases hsv s' z hz' with h | h
    · exact hss' (Subtype.ext (hz.symm.trans h))
    · exact sideVerts_not_mem G P S h (by rw [hz]; exact s.2)
  · rw [hP1 s' hs'] at hz'
    simp at hz'
    rcases hsv s z hz with h | h
    · exact hss' (Subtype.ext (h.symm.trans hz'))
    · exact sideVerts_not_mem G P S h (by rw [hz']; exact s'.2)
  · obtain ⟨i, hi, hsup⟩ := hP2 s hs
    obtain ⟨j, hj, hsup'⟩ := hP2 s' hs'
    have hne : i ≠ j := by
      intro h; subst h
      exact hss' (Subtype.ext (hi.symm.trans hj))
    rw [hsup] at hz; rw [hsup'] at hz'
    exact hdisj i j hne hz hz'

theorem sideVerts_disjoint {V : Type*} (G : SimpleGraph V) (P Q S : Finset V)
    (hS : Separates G P Q S) {z : V} (h1 : z ∈ sideVerts G P S) (h2 : z ∈ sideVerts G Q S) :
    False := by
  obtain ⟨x, hx, wx, hwx⟩ := h1
  obtain ⟨y, hy, wy, hwy⟩ := h2
  obtain ⟨v, hv, hvS⟩ := hS x hx y hy (wx.append wy.reverse)
  rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse] at hv
  rcases List.mem_append.mp hv with h | h
  · exact hwx v h hvS
  · exact hwy v (by
      have := List.mem_of_mem_tail h
      simpa using this) hvS

theorem glue_paths_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (S : Finset V) (hS : Separates G P Q S) (hcard : S.card = n)
    (hP : HasDisjointPaths (sidePart G P S) (P \ S) (S \ P) (n - (S ∩ P).card))
    (hQ : HasDisjointPaths (sidePart G Q S) (Q \ S) (S \ Q) (n - (S ∩ Q).card)) :
    HasDisjointPaths G P Q n := by
  classical
  have hP' : HasDisjointPaths (sidePart G P S) (P \ S) (S \ P) (S \ P).card := by
    have h1 := Finset.card_sdiff_add_card_inter S P
    have : n - (S ∩ P).card = (S \ P).card := by omega
    rwa [this] at hP
  have hQ' : HasDisjointPaths (sidePart G Q S) (Q \ S) (S \ Q) (S \ Q).card := by
    have h1 := Finset.card_sdiff_add_card_inter S Q
    have : n - (S ∩ Q).card = (S \ Q).card := by omega
    rwa [this] at hQ
  obtain ⟨α, p, hα, hp, hpd, hpsv⟩ := side_family G P S hP'
  obtain ⟨β, q, hβ, hq, hqd, hqsv⟩ := side_family G Q S hQ'
  let e : S ≃ Fin n := Finset.equivFinOfCardEq hcard
  refine ⟨fun i => α (e.symm i), fun i => β (e.symm i),
    fun i => (p (e.symm i)).append (q (e.symm i)).reverse, ?_, ?_⟩
  · intro i
    refine ⟨hα _, hβ _, ?_⟩
    set s := e.symm i
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, List.nodup_append]
    have hr : (q s).reverse.support.Nodup := ((hq s).reverse).support_nodup
    refine ⟨(hp s).support_nodup, hr.sublist (List.tail_sublist _), ?_⟩
    intro z hz z' hz' hzz
    subst hzz
    have hzr : z ∈ (q s).support := by
      have := List.mem_of_mem_tail hz'
      simpa [SimpleGraph.Walk.support_reverse] using this
    have htail : s.1 ∉ (q s).reverse.support.tail := by
      have := (SimpleGraph.Walk.cons_tail_support (q s).reverse) ▸ hr
      exact (List.nodup_cons.mp this).1
    rcases hpsv s z hz with h1 | h1 <;> rcases hqsv s z hzr with h2 | h2
    · exact htail (h1 ▸ hz')
    · exact sideVerts_not_mem G Q S h2 (h1 ▸ s.2)
    · exact sideVerts_not_mem G P S h1 (h2 ▸ s.2)
    · exact sideVerts_disjoint G P Q S hS h1 h2
  · intro i j hij z hz hz'
    have hne : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    set s := e.symm i
    set s' := e.symm j
    simp only [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse] at hz hz'
    have hz1 : z ∈ (p s).support ∨ z ∈ (q s).support := by
      rcases List.mem_append.mp hz with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using List.mem_of_mem_tail h)
    have hz2 : z ∈ (p s').support ∨ z ∈ (q s').support := by
      rcases List.mem_append.mp hz' with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using List.mem_of_mem_tail h)
    rcases hz1 with h1 | h1 <;> rcases hz2 with h2 | h2
    · exact hpd s s' hne h1 h2
    · rcases hpsv s z h1 with a1 | a1 <;> rcases hqsv s' z h2 with a2 | a2
      · exact hne (Subtype.ext (a1.symm.trans a2))
      · exact sideVerts_not_mem G Q S a2 (a1 ▸ s.2)
      · exact sideVerts_not_mem G P S a1 (a2 ▸ s'.2)
      · exact sideVerts_disjoint G P Q S hS a1 a2
    · rcases hqsv s z h1 with a1 | a1 <;> rcases hpsv s' z h2 with a2 | a2
      · exact hne (Subtype.ext (a1.symm.trans a2))
      · exact sideVerts_not_mem G P S a2 (a1 ▸ s.2)
      · exact sideVerts_not_mem G Q S a1 (a2 ▸ s'.2)
      · exact sideVerts_disjoint G P Q S hS a2 a1
    · exact hqd s s' hne h1 h2

end Menger27.Graphs

open Menger27.Graphs


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (S : Finset V) (hS : Separates G P Q S) (hcard : S.card = n)
    (hP : HasDisjointPaths (sidePart G P S) (P \ S) (S \ P) (n - (S ∩ P).card))
    (hQ : HasDisjointPaths (sidePart G Q S) (Q \ S) (S \ Q) (n - (S ∩ Q).card)) :
    HasDisjointPaths G P Q n := by
  exact glue_paths_core G P Q hPQ n S hS hcard hP hQ
