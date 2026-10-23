-- Prove2me | solution 1 for LeeSviridenkoVondrak.LocalSearch.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:25:43.249431+00:00
-- url     : https://prove2.me/submissions/4de80d25-918d-4b5d-82cd-7ba28b7aaa3f

import Mathlib
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Exchange

open scoped symmDiff

namespace X6LSV
open LeeSviridenkoVondrak.LocalSearch Classical

variable {n : ℕ}

/-- In a bipartite "arc graph" with a unique perfect matching, some left vertex is only
adjacent to its partner. -/
lemma exists_deg_one (M : Matroid (Fin n)) (I L R : Finset (Fin n)) (E : Finset (Fin n × Fin n))
    (hE : PerfectMatching M I L R E) (huniq : ∀ F, PerfectMatching M I L R F → F = E)
    (hL : L.Nonempty) :
    ∃ x ∈ L, ∀ y ∈ R, ExchangeArc M I x y → (x, y) ∈ E := by
  by_contra hcon
  push Not at hcon
  choose! g hgR hgA hgE using hcon
  obtain ⟨hE1, hE2, hE3⟩ := hE
  choose! p hp using hE3
  -- p y is the partner of y
  have hpE : ∀ y ∈ R, (p y, y) ∈ E := fun y hy => (hp y hy).1
  have hpL : ∀ y ∈ R, p y ∈ L := fun y hy => (hE1 _ (hpE y hy)).1
  have hpu : ∀ y ∈ R, ∀ x, (x, y) ∈ E → x = p y := fun y hy x hx => (hp y hy).2 x hx
  set f : Fin n → Fin n := fun x => p (g x) with hf
  have hfL : ∀ x ∈ L, f x ∈ L := fun x hx => hpL _ (hgR x hx)
  have hfne : ∀ x ∈ L, f x ≠ x := by
    intro x hx h
    apply hgE x hx
    have := hpE _ (hgR x hx)
    simp only [hf] at h
    rwa [h] at this
  obtain ⟨xa, hxa⟩ := hL
  have hit : ∀ i, f^[i] xa ∈ L := by
    intro i; induction i with
    | zero => simpa using hxa
    | succ i ih => rw [Function.iterate_succ_apply']; exact hfL _ ih
  -- pigeonhole
  obtain ⟨a, b, hab, heq⟩ : ∃ a b : ℕ, a < b ∧ f^[a] xa = f^[b] xa := by
    have : ¬ Function.Injective (fun i : ℕ => (⟨f^[i] xa, hit i⟩ : L)) := by
      intro hinj
      exact (Infinite.of_injective _ hinj).not_finite inferInstance
    simp only [Function.Injective, not_forall] at this
    obtain ⟨i, j, hij, hne⟩ := this
    have hij' : f^[i] xa = f^[j] xa := congrArg Subtype.val hij
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, hij'⟩
    · exact ⟨j, i, h, hij'.symm⟩
  set x0 := f^[a] xa with hx0
  set q := b - a with hq
  have hqpos : 0 < q := by omega
  have hper : f^[q] x0 = x0 := by
    show f^[q] (f^[a] xa) = f^[a] xa
    rw [← Function.iterate_add_apply, show q + a = b by omega]; exact heq.symm
  set C : Set (Fin n) := Set.range (fun i : ℕ => f^[i] x0) with hC
  have hx0L : x0 ∈ L := hit a
  have hCL : ∀ x ∈ C, x ∈ L := by
    rintro x ⟨i, rfl⟩
    simp only [hx0, ← Function.iterate_add_apply]; exact hit _
  have hmaps : Set.MapsTo f C C := by
    rintro x ⟨i, rfl⟩; exact ⟨i + 1, Function.iterate_succ_apply' f i x0⟩
  have hsurj : Set.SurjOn f C C := by
    rintro x ⟨i, rfl⟩
    rcases i with _ | i
    · refine ⟨f^[q - 1] x0, ⟨q - 1, rfl⟩, ?_⟩
      show f (f^[q-1] x0) = f^[0] x0
      rw [← Function.iterate_succ_apply' f, show (q - 1).succ = q by omega, hper]; rfl
    · exact ⟨f^[i] x0, ⟨i, rfl⟩, (Function.iterate_succ_apply' f i x0).symm⟩
  have hCfin : C.Finite := (L.finite_toSet).subset (fun x hx => hCL x hx)
  have hinj : Set.InjOn f C := ((hCfin.surjOn_iff_bijOn_of_mapsTo hmaps).1 hsurj).injOn
  have hx0C : x0 ∈ C := ⟨0, rfl⟩
  -- the new matching
  set E2 : Finset (Fin n × Fin n) :=
    (L ×ˢ R).filter (fun e => (e ∈ E ∧ e.1 ∉ C) ∨ (e.1 ∈ C ∧ e.2 = g e.1)) with hE2def
  have mem2 : ∀ x y, (x, y) ∈ E2 ↔ ((x, y) ∈ E ∧ x ∉ C) ∨ (x ∈ C ∧ y = g x) := by
    intro x y
    simp only [hE2def, Finset.mem_filter, Finset.mem_product]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rcases h with ⟨h1, _⟩ | ⟨h1, rfl⟩
      · exact ⟨(hE1 _ h1).1, (hE1 _ h1).2.1⟩
      · exact ⟨hCL x h1, hgR x (hCL x h1)⟩
  have hPM2 : PerfectMatching M I L R E2 := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ he
      rw [mem2] at he
      rcases he with ⟨h1, _⟩ | ⟨h1, rfl⟩
      · exact hE1 _ h1
      · exact ⟨hCL x h1, hgR x (hCL x h1), hgA x (hCL x h1)⟩
    · intro x hx
      by_cases hxC : x ∈ C
      · refine ⟨g x, (mem2 _ _).2 (Or.inr ⟨hxC, rfl⟩), ?_⟩
        intro y hy
        rw [mem2] at hy
        rcases hy with ⟨_, h⟩ | ⟨_, h⟩
        · exact absurd hxC h
        · exact h
      · obtain ⟨y, hy, hyu⟩ := hE2 x hx
        refine ⟨y, (mem2 _ _).2 (Or.inl ⟨hy, hxC⟩), ?_⟩
        intro y' hy'
        rw [mem2] at hy'
        rcases hy' with ⟨h, _⟩ | ⟨h, _⟩
        · exact hyu y' h
        · exact absurd h hxC
    · intro y hy
      by_cases hpC : p y ∈ C
      · obtain ⟨x', hx'C, hx'⟩ := hsurj hpC
        -- g x' = y
        have hgx' : g x' = y := by
          have h1 : (p y, g x') ∈ E := by
            rw [← hx']; exact hpE _ (hgR x' (hCL x' hx'C))
          have h2 := hE2 (p y) (hpL y hy)
          obtain ⟨z, _, hz⟩ := h2
          rw [hz _ h1, hz _ (hpE y hy)]
        refine ⟨x', (mem2 _ _).2 (Or.inr ⟨hx'C, hgx'.symm⟩), ?_⟩
        intro x hx
        rw [mem2] at hx
        rcases hx with ⟨h, hxC⟩ | ⟨hxC, hxy⟩
        · rw [hpu y hy x h] at hxC; exact absurd hpC hxC
        · apply hinj hxC hx'C
          show p (g x) = p (g x')
          rw [← hxy, hgx']
      · refine ⟨p y, (mem2 _ _).2 (Or.inl ⟨hpE y hy, hpC⟩), ?_⟩
        intro x hx
        rw [mem2] at hx
        rcases hx with ⟨h, _⟩ | ⟨hxC, hxy⟩
        · exact hpu y hy x h
        · exfalso; apply hpC
          have : p y = f x := by simp only [hf]; rw [← hxy]
          rw [this]; exact hmaps hxC
  have := huniq E2 hPM2
  have hin : (x0, g x0) ∈ E2 := (mem2 _ _).2 (Or.inr ⟨hx0C, rfl⟩)
  rw [this] at hin
  exact hgE x0 hx0L hin

lemma mem_closure_of_not_indep (M : Matroid (Fin n)) (hE : M.E = Set.univ) {I : Finset (Fin n)}
    (hI : M.Indep (I : Set (Fin n))) {x y : Fin n} (hy : y ∉ I)
    (h : ¬ M.Indep (↑(insert y (I.erase x)) : Set (Fin n))) :
    y ∈ M.closure (↑(I.erase x) : Set (Fin n)) := by
  have hI' : M.Indep (↑(I.erase x) : Set (Fin n)) :=
    hI.subset (by intro z hz; simp only [Finset.coe_erase, Set.mem_sdiff] at hz; exact hz.1)
  have hy' : y ∉ (↑(I.erase x) : Set (Fin n)) := by simp [hy]
  rw [Finset.coe_insert, hI'.insert_indep_iff_of_notMem hy'] at h
  simp only [hE, Set.mem_sdiff, Set.mem_univ, true_and, not_not] at h
  exact h

lemma not_mem_closure_of_indep (M : Matroid (Fin n)) {I : Finset (Fin n)}
    (hI : M.Indep (I : Set (Fin n))) {x y : Fin n} (hy : y ∉ I)
    (h : M.Indep (↑(insert y (I.erase x)) : Set (Fin n))) :
    y ∉ M.closure (↑(I.erase x) : Set (Fin n)) := by
  have hI' : M.Indep (↑(I.erase x) : Set (Fin n)) :=
    hI.subset (by intro z hz; simp only [Finset.coe_erase, Set.mem_sdiff] at hz; exact hz.1)
  have hy' : y ∉ (↑(I.erase x) : Set (Fin n)) := by simp [hy]
  rw [Finset.coe_insert, hI'.insert_indep_iff_of_notMem hy'] at h
  exact h.2

theorem main (M : Matroid (Fin n)) (hE : M.E = Set.univ) (I : Finset (Fin n))
    (hI : M.Indep (I : Set (Fin n))) :
    ∀ k, ∀ L R : Finset (Fin n), L.card = k → L ⊆ I → Disjoint R I →
      (∃! E, PerfectMatching M I L R E) → M.Indep (↑((I \ L) ∪ R) : Set (Fin n)) := by
  intro k
  induction k with
  | zero =>
    intro L R hk _ _ hu
    have hL : L = ∅ := Finset.card_eq_zero.1 hk
    obtain ⟨E, hEm, _⟩ := hu
    have hR : R = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      obtain ⟨x, hx, _⟩ := hEm.2.2 y hy
      have := (hEm.1 _ hx).1
      rw [hL] at this; simp at this
    subst hL; subst hR; simpa using hI
  | succ k ih =>
    intro L R hk hLI hRI hu
    obtain ⟨E, hEm, hEu⟩ := hu
    have hLne : L.Nonempty := by rw [← Finset.card_pos, hk]; omega
    obtain ⟨x1, hx1L, hx1⟩ := exists_deg_one M I L R E hEm hEu hLne
    obtain ⟨y1, hy1E, hy1u⟩ := hEm.2.1 x1 hx1L
    obtain ⟨-, hy1R, hy1A⟩ := hEm.1 _ hy1E
    have hx1I : x1 ∈ I := hLI hx1L
    have hy1I : y1 ∉ I := Finset.disjoint_left.1 hRI hy1R
    set L' := L.erase x1
    set R' := R.erase y1
    set E' := E.erase (x1, y1)
    have hPM' : PerfectMatching M I L' R' E' := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨x, y⟩ he
        rw [Finset.mem_erase] at he
        obtain ⟨hne, he⟩ := he
        obtain ⟨hxL, hyR, hA⟩ := hEm.1 _ he
        refine ⟨Finset.mem_erase.2 ⟨?_, hxL⟩, Finset.mem_erase.2 ⟨?_, hyR⟩, hA⟩
        · intro (h : x = x1); apply hne; rw [h] at he ⊢; rw [hy1u y he]
        · intro (h : y = y1); apply hne; rw [h] at he ⊢
          obtain ⟨z, _, hz⟩ := hEm.2.2 y1 hy1R
          rw [hz x he, hz x1 hy1E]
      · intro x hx
        obtain ⟨hxne, hxL⟩ := Finset.mem_erase.1 hx
        obtain ⟨y, hy, hyu⟩ := hEm.2.1 x hxL
        refine ⟨y, Finset.mem_erase.2 ⟨fun h => hxne (Prod.mk.inj h).1, hy⟩, ?_⟩
        intro y' hy'
        exact hyu y' (Finset.mem_of_mem_erase hy')
      · intro y hy
        obtain ⟨hyne, hyR⟩ := Finset.mem_erase.1 hy
        obtain ⟨x, hx, hxu⟩ := hEm.2.2 y hyR
        refine ⟨x, Finset.mem_erase.2 ⟨fun h => hyne (Prod.mk.inj h).2, hx⟩, ?_⟩
        intro x' hx'
        exact hxu x' (Finset.mem_of_mem_erase hx')
    have hu' : ∃! F, PerfectMatching M I L' R' F := by
      refine ⟨E', hPM', ?_⟩
      intro F hF
      have hnot : (x1, y1) ∉ F := fun h => by
        have := (hF.1 _ h).1; simp [L'] at this
      have hPM : PerfectMatching M I L R (insert (x1, y1) F) := by
        refine ⟨?_, ?_, ?_⟩
        · intro e he
          rw [Finset.mem_insert] at he
          rcases he with rfl | he
          · exact ⟨hx1L, hy1R, hy1A⟩
          · obtain ⟨h1, h2, h3⟩ := hF.1 e he
            exact ⟨Finset.mem_of_mem_erase h1, Finset.mem_of_mem_erase h2, h3⟩
        · intro x hx
          by_cases hxx : x = x1
          · subst hxx
            refine ⟨y1, Finset.mem_insert_self _ _, ?_⟩
            intro y hy
            rw [Finset.mem_insert] at hy
            rcases hy with h | h
            · exact (Prod.mk.inj h).2
            · have := (hF.1 _ h).1; simp [L'] at this
          · obtain ⟨y, hy, hyu⟩ := hF.2.1 x (Finset.mem_erase.2 ⟨hxx, hx⟩)
            refine ⟨y, Finset.mem_insert_of_mem hy, ?_⟩
            intro y' hy'
            rw [Finset.mem_insert] at hy'
            rcases hy' with h | h
            · exact absurd (Prod.mk.inj h).1 hxx
            · exact hyu y' h
        · intro y hy
          by_cases hyy : y = y1
          · subst hyy
            refine ⟨x1, Finset.mem_insert_self _ _, ?_⟩
            intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with h | h
            · exact (Prod.mk.inj h).1
            · have := (hF.1 _ h).2.1; simp [R'] at this
          · obtain ⟨x, hx, hxu⟩ := hF.2.2 y (Finset.mem_erase.2 ⟨hyy, hy⟩)
            refine ⟨x, Finset.mem_insert_of_mem hx, ?_⟩
            intro x' hx'
            rw [Finset.mem_insert] at hx'
            rcases hx' with h | h
            · exact absurd (Prod.mk.inj h).2 hyy
            · exact hxu x' h
      have := hEu _ hPM
      show F = E.erase (x1, y1)
      rw [← this, Finset.erase_insert hnot]
    have hS := ih L' R' (by rw [Finset.card_erase_of_mem hx1L, hk]; rfl)
      ((Finset.erase_subset _ _).trans hLI)
      (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hRI) hu'
    -- T := (I \ L) ∪ R'
    set T : Finset (Fin n) := (I \ L) ∪ R' with hT
    have hTS : T ⊆ (I \ L') ∪ R' := by
      apply Finset.union_subset_union _ le_rfl
      exact Finset.sdiff_subset_sdiff le_rfl (Finset.erase_subset _ _)
    have hTi : M.Indep (T : Set (Fin n)) := hS.subset (by exact_mod_cast hTS)
    have hTcl : (T : Set (Fin n)) ⊆ M.closure (↑(I.erase x1) : Set (Fin n)) := by
      intro z hz
      rw [Finset.mem_coe, hT, Finset.mem_union] at hz
      rcases hz with hz | hz
      · apply M.subset_closure _ (by rw [hE]; exact Set.subset_univ _)
        rw [Finset.mem_sdiff] at hz
        simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
        exact ⟨hz.1, fun h => hz.2 (h ▸ hx1L)⟩
      · obtain ⟨hzne, hzR⟩ := Finset.mem_erase.1 hz
        have hzI : z ∉ I := Finset.disjoint_left.1 hRI hzR
        apply mem_closure_of_not_indep M hE hI hzI
        intro hind
        have := hx1 z hzR ⟨hx1I, hzI, hind⟩
        exact hzne (hy1u z this)
    have hy1cl : y1 ∉ M.closure (T : Set (Fin n)) := by
      intro h
      exact not_mem_closure_of_indep M hI hy1I hy1A.2.2
        (M.closure_subset_closure_of_subset_closure hTcl h)
    have hy1T : y1 ∉ (T : Set (Fin n)) := fun h => hy1cl (M.subset_closure _ (by rw [hE]; exact Set.subset_univ _) h)
    have hfin : M.Indep (insert y1 (T : Set (Fin n))) := by
      rw [hTi.insert_indep_iff_of_notMem hy1T, hE]
      exact ⟨Set.mem_univ _, hy1cl⟩
    convert hfin using 1
    rw [← Finset.coe_insert]
    congr 1
    ext z
    simp only [hT, R', Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · by_cases hz : z = y1
        · exact Or.inl hz
        · exact Or.inr (Or.inr ⟨hz, h⟩)
    · rintro (rfl | h | h)
      · exact Or.inr hy1R
      · exact Or.inl h
      · exact Or.inr h.2

end X6LSV


namespace X6LSV
open LeeSviridenkoVondrak.LocalSearch Classical

variable {n : ℕ}

lemma mem_zip_tail {α : Type*} {l : List α} {x y : α} :
    (x, y) ∈ l.zip l.tail ↔ ∃ i, ∃ h : i + 1 < l.length, l[i] = x ∧ l[i+1] = y := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, h⟩
    simp only [List.length_zip, List.length_tail] at hi
    rw [List.getElem_zip, List.getElem_tail] at h
    exact ⟨i, by omega, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  · rintro ⟨i, hi, h1, h2⟩
    refine ⟨i, by simp; omega, ?_⟩
    rw [List.getElem_zip, List.getElem_tail, h1, h2]

lemma edge_iff (A : WalkData n) (x y : Fin n) :
    A.edge x y ↔ (∃ i, ∃ h : i + 1 < A.vertices.length,
        A.vertices[i] = x ∧ A.vertices[i+1] = y) ∨
      (A.closed = true ∧ ∃ h : 0 < A.vertices.length,
        A.vertices[A.vertices.length - 1] = x ∧ A.vertices[0] = y) := by
  unfold WalkData.edge
  rw [mem_zip_tail, List.getLast?_eq_getElem?, List.head?_eq_getElem?]
  apply or_congr Iff.rfl
  apply and_congr Iff.rfl
  simp only [List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨h3, h2, h4⟩
  · rintro ⟨h, h2, h4⟩; exact ⟨⟨by omega, h2⟩, ⟨h, h4⟩⟩

lemma edge_mem (A : WalkData n) {x y : Fin n} (h : A.edge x y) :
    x ∈ A.vertices ∧ y ∈ A.vertices := by
  rw [edge_iff] at h
  rcases h with ⟨i, hi, rfl, rfl⟩ | ⟨_, h0, rfl, rfl⟩
  · exact ⟨List.getElem_mem _, List.getElem_mem _⟩
  · exact ⟨List.getElem_mem _, List.getElem_mem _⟩

lemma succ_ex (A : WalkData n) (hc : A.closed = true) {x : Fin n} (hx : x ∈ A.vertices) :
    ∃ y, A.edge x y := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  by_cases h : j + 1 < A.vertices.length
  · exact ⟨_, (edge_iff A _ _).2 (Or.inl ⟨j, h, rfl, rfl⟩)⟩
  · refine ⟨A.vertices[0], (edge_iff A _ _).2 (Or.inr ⟨hc, by omega, ?_, rfl⟩)⟩
    congr 1; omega

lemma pred_ex (A : WalkData n) (hc : A.closed = true) {y : Fin n} (hy : y ∈ A.vertices) :
    ∃ x, A.edge x y := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
  rcases j with _ | j
  · exact ⟨_, (edge_iff A _ _).2 (Or.inr ⟨hc, hj, rfl, rfl⟩)⟩
  · exact ⟨_, (edge_iff A _ _).2 (Or.inl ⟨j, hj, rfl, rfl⟩)⟩

lemma succ_uniq (A : WalkData n) (hnd : A.vertices.Nodup) {x y y' : Fin n}
    (h1 : A.edge x y) (h2 : A.edge x y') : y = y' := by
  rw [edge_iff] at h1 h2
  rcases h1 with ⟨i, hi, hx, rfl⟩ | ⟨_, h0, hx, rfl⟩ <;>
    rcases h2 with ⟨j, hj, hx', rfl⟩ | ⟨_, h0', hx', rfl⟩
  · have := (hnd.getElem_inj_iff).1 (hx.trans hx'.symm); subst this; rfl
  · have := (hnd.getElem_inj_iff).1 (hx.trans hx'.symm); omega
  · have := (hnd.getElem_inj_iff).1 (hx.trans hx'.symm); omega
  · rfl

lemma pred_uniq (A : WalkData n) (hnd : A.vertices.Nodup) {x x' y : Fin n}
    (h1 : A.edge x y) (h2 : A.edge x' y) : x = x' := by
  rw [edge_iff] at h1 h2
  rcases h1 with ⟨i, hi, rfl, hy⟩ | ⟨_, h0, rfl, hy⟩ <;>
    rcases h2 with ⟨j, hj, rfl, hy'⟩ | ⟨_, h0', rfl, hy'⟩
  · have := (hnd.getElem_inj_iff).1 (hy.trans hy'.symm)
    have : i = j := by omega
    subst this; rfl
  · have := (hnd.getElem_inj_iff).1 (hy.trans hy'.symm); omega
  · have := (hnd.getElem_inj_iff).1 (hy.trans hy'.symm); omega
  · rfl

lemma open_pred (B : WalkData n) {y : Fin n} (hy : y ∈ B.vertices)
    (hh : B.vertices.head? ≠ some y) : ∃ x, B.edge x y := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
  rcases j with _ | j
  · exact absurd (by rw [List.head?_eq_getElem?]; simp) hh
  · exact ⟨_, (edge_iff B _ _).2 (Or.inl ⟨j, hj, rfl, rfl⟩)⟩

lemma open_succ (B : WalkData n) {x : Fin n} (hx : x ∈ B.vertices)
    (hl : B.vertices.getLast? ≠ some x) : ∃ y, B.edge x y := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  by_cases h : j + 1 < B.vertices.length
  · exact ⟨_, (edge_iff B _ _).2 (Or.inl ⟨j, h, rfl, rfl⟩)⟩
  · exfalso; apply hl
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_some_iff]
    exact ⟨by omega, by congr 1; omega⟩

/-- A sub-collection of the unique perfect matching is the unique perfect matching between
its own endpoints. -/
lemma sub_unique (M : Matroid (Fin n)) (I L R : Finset (Fin n)) (E : Finset (Fin n × Fin n))
    (hE : PerfectMatching M I L R E) (hu : ∀ F, PerfectMatching M I L R F → F = E)
    (E' : Finset (Fin n × Fin n)) (hsub : E' ⊆ E) :
    ∃! F, PerfectMatching M I (E'.image Prod.fst) (E'.image Prod.snd) F := by
  obtain ⟨hE1, hE2, hE3⟩ := hE
  -- matching property of E
  have fst_inj : ∀ x y y', (x, y) ∈ E → (x, y') ∈ E → y = y' := by
    intro x y y' h h'
    obtain ⟨z, _, hz⟩ := hE2 x (hE1 _ h).1
    rw [hz y h, hz y' h']
  have snd_inj : ∀ x x' y, (x, y) ∈ E → (x', y) ∈ E → x = x' := by
    intro x x' y h h'
    obtain ⟨z, _, hz⟩ := hE3 y (hE1 _ h).2.1
    rw [hz x h, hz x' h']
  have hPM' : PerfectMatching M I (E'.image Prod.fst) (E'.image Prod.snd) E' := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      exact ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he, (hE1 e (hsub he)).2.2⟩
    · intro x hx
      obtain ⟨⟨x0, y⟩, he, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨y, he, fun y' hy' => fst_inj _ _ _ (hsub hy') (hsub he)⟩
    · intro y hy
      obtain ⟨⟨x, y0⟩, he, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨x, he, fun x' hx' => snd_inj _ _ _ (hsub hx') (hsub he)⟩
  refine ⟨E', hPM', ?_⟩
  intro F hF
  obtain ⟨hF1, hF2, hF3⟩ := hF
  -- F' ∪ (E \ E') is a perfect matching for (L, R)
  have key : ∀ e ∈ E, e ∉ E' → e.1 ∉ E'.image Prod.fst ∧ e.2 ∉ E'.image Prod.snd := by
    rintro ⟨x, y⟩ he hne
    constructor
    · intro hx
      obtain ⟨⟨x', y'⟩, he', hxx⟩ := Finset.mem_image.1 hx
      simp only at hxx; subst hxx
      exact hne (by rw [fst_inj _ _ _ he (hsub he')]; exact he')
    · intro hy
      obtain ⟨⟨x', y'⟩, he', hyy⟩ := Finset.mem_image.1 hy
      simp only at hyy; subst hyy
      exact hne (by rw [snd_inj _ _ _ he (hsub he')]; exact he')
  have hFsub : F ⊆ E := by
    have hG : PerfectMatching M I L R (F ∪ E.filter (fun e => e ∉ E')) := by
      refine ⟨?_, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_union.1 he with he | he
        · obtain ⟨h1, h2, h3⟩ := hF1 e he
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 h1
          obtain ⟨⟨c, d⟩, hcd, hd⟩ := Finset.mem_image.1 h2
          exact ⟨(hE1 _ (hsub hab)).1, by rw [← hd]; exact (hE1 _ (hsub hcd)).2.1, h3⟩
        · exact hE1 e (Finset.mem_filter.1 he).1
      · intro x hx
        by_cases hx' : x ∈ E'.image Prod.fst
        · obtain ⟨y, hy, hyu⟩ := hF2 x hx'
          refine ⟨y, Finset.mem_union_left _ hy, fun y' hy' => ?_⟩
          rcases Finset.mem_union.1 hy' with h | h
          · exact hyu y' h
          · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
            exact absurd hx' (key _ h1 h2).1
        · obtain ⟨y, hy, hyu⟩ := hE2 x hx
          have hyE' : (x, y) ∉ E' := fun h => hx' (Finset.mem_image_of_mem Prod.fst h)
          refine ⟨y, Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hy, hyE'⟩), fun y' hy' => ?_⟩
          rcases Finset.mem_union.1 hy' with h | h
          · exact absurd (hF1 _ h).1 hx'
          · exact hyu y' (Finset.mem_filter.1 h).1
      · intro y hy
        by_cases hy' : y ∈ E'.image Prod.snd
        · obtain ⟨x, hx, hxu⟩ := hF3 y hy'
          refine ⟨x, Finset.mem_union_left _ hx, fun x' hx' => ?_⟩
          rcases Finset.mem_union.1 hx' with h | h
          · exact hxu x' h
          · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
            exact absurd hy' (key _ h1 h2).2
        · obtain ⟨x, hx, hxu⟩ := hE3 y hy
          have hxE' : (x, y) ∉ E' := fun h => hy' (Finset.mem_image_of_mem Prod.snd h)
          refine ⟨x, Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hx, hxE'⟩), fun x' hx' => ?_⟩
          rcases Finset.mem_union.1 hx' with h | h
          · exact absurd (hF1 _ h).2.1 hy'
          · exact hxu x' (Finset.mem_filter.1 h).1
    have := hu _ hG
    intro e he
    rw [← this]; exact Finset.mem_union_left _ he
  ext ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨h1, -, -⟩ := hF1 _ h
    obtain ⟨⟨x', y'⟩, he', hxx⟩ := Finset.mem_image.1 h1
    simp only at hxx; subst hxx
    rw [fst_inj _ _ _ (hFsub h) (hsub he')]; exact he'
  · intro h
    obtain ⟨y', hy', -⟩ := hF2 x (Finset.mem_image_of_mem Prod.fst h)
    rw [fst_inj _ _ _ (hsub h) (hFsub hy')]; exact hy'

/-- Core: a sub-collection of a unique perfect matching can be exchanged. -/
lemma core (M : Matroid (Fin n)) (hE : M.E = Set.univ) (I L R : Finset (Fin n))
    (hI : M.Indep (I : Set (Fin n))) (E : Finset (Fin n × Fin n))
    (hPM : PerfectMatching M I L R E) (hu : ∀ F, PerfectMatching M I L R F → F = E)
    (hLI : L ⊆ I) (hRI : Disjoint R I) (E' : Finset (Fin n × Fin n)) (hsub : E' ⊆ E) :
    M.Indep (↑((I \ E'.image Prod.fst) ∪ E'.image Prod.snd) : Set (Fin n)) := by
  apply main M hE I hI _ _ _ rfl
  · intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
    exact hLI (hPM.1 e (hsub he)).1
  · rw [Finset.disjoint_left]
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.disjoint_left.1 hRI (hPM.1 e (hsub he)).2.1
  · exact sub_unique M I L R E hPM hu E' hsub

end X6LSV

open LeeSviridenkoVondrak.LocalSearch X6LSV Classical in
theorem solution {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (I : Finset (Fin n)) (hI₁ : M₁.Indep (↑I : Set (Fin n)))
    (hI₂ : M₂.Indep (↑I : Set (Fin n))) (A : WalkData n)
    (hA : Irreducible M₁ M₂ I A) : FeasibleWalk M₁ M₂ I A := by
  obtain ⟨hdir, hc, ⟨E₁, hPM₁, hu₁⟩, ⟨E₂, hPM₂, hu₂⟩⟩ := hA
  have ⟨_, hnd, _, harc⟩ := hdir
  set S := A.support with hS
  have memS : ∀ x, x ∈ S ↔ x ∈ A.vertices := fun x => List.mem_toFinset
  -- the cycle matchings
  set C₁ : Finset (Fin n × Fin n) := (S ×ˢ S).filter (fun e => A.edge e.1 e.2 ∧ e.1 ∈ I)
  set C₂ : Finset (Fin n × Fin n) := (S ×ˢ S).filter (fun e => A.edge e.2 e.1 ∧ e.1 ∈ I)
  have memC₁ : ∀ x y, (x, y) ∈ C₁ ↔ A.edge x y ∧ x ∈ I := by
    intro x y
    simp only [C₁, Finset.mem_filter, Finset.mem_product, memS]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨edge_mem A h.1, h⟩
  have memC₂ : ∀ x y, (x, y) ∈ C₂ ↔ A.edge y x ∧ x ∈ I := by
    intro x y
    simp only [C₂, Finset.mem_filter, Finset.mem_product, memS]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨(edge_mem A h.1).symm, h⟩
  -- arcs from cycle edges
  have arc₁ : ∀ x y, A.edge x y → x ∈ I → ExchangeArc M₁ I x y := by
    intro x y h hx
    rcases harc x y h with h | h
    · exact h
    · exact absurd hx h.2.1
  have arc₂ : ∀ x y, A.edge y x → x ∈ I → ExchangeArc M₂ I x y := by
    intro x y h hx
    rcases harc y x h with h | h
    · exact absurd hx h.2.1
    · exact h
  have hC₁ : PerfectMatching M₁ I (I ∩ S) (S \ I) C₁ := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ he
      rw [memC₁] at he
      have ha := arc₁ x y he.1 he.2
      obtain ⟨hx, hy⟩ := edge_mem A he.1
      exact ⟨Finset.mem_inter.2 ⟨he.2, (memS x).2 hx⟩,
        Finset.mem_sdiff.2 ⟨(memS y).2 hy, ha.2.1⟩, ha⟩
    · intro x hx
      obtain ⟨hxI, hxS⟩ := Finset.mem_inter.1 hx
      obtain ⟨y, hy⟩ := succ_ex A hc ((memS x).1 hxS)
      exact ⟨y, (memC₁ _ _).2 ⟨hy, hxI⟩, fun y' h => succ_uniq A hnd ((memC₁ _ _).1 h).1 hy⟩
    · intro y hy
      obtain ⟨hyS, hyI⟩ := Finset.mem_sdiff.1 hy
      obtain ⟨x, hx⟩ := pred_ex A hc ((memS y).1 hyS)
      have hxI : x ∈ I := by
        rcases harc x y hx with h | h
        · exact h.1
        · exact absurd h.1 hyI
      exact ⟨x, (memC₁ _ _).2 ⟨hx, hxI⟩, fun x' h => pred_uniq A hnd ((memC₁ _ _).1 h).1 hx⟩
  have hC₂ : PerfectMatching M₂ I (I ∩ S) (S \ I) C₂ := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ he
      rw [memC₂] at he
      have ha := arc₂ x y he.1 he.2
      obtain ⟨hy, hx⟩ := edge_mem A he.1
      exact ⟨Finset.mem_inter.2 ⟨he.2, (memS x).2 hx⟩,
        Finset.mem_sdiff.2 ⟨(memS y).2 hy, ha.2.1⟩, ha⟩
    · intro x hx
      obtain ⟨hxI, hxS⟩ := Finset.mem_inter.1 hx
      obtain ⟨y, hy⟩ := pred_ex A hc ((memS x).1 hxS)
      exact ⟨y, (memC₂ _ _).2 ⟨hy, hxI⟩, fun y' h => pred_uniq A hnd ((memC₂ _ _).1 h).1 hy⟩
    · intro y hy
      obtain ⟨hyS, hyI⟩ := Finset.mem_sdiff.1 hy
      obtain ⟨x, hx⟩ := succ_ex A hc ((memS y).1 hyS)
      have hxI : x ∈ I := by
        rcases harc y x hx with h | h
        · exact absurd h.1 hyI
        · exact h.1
      exact ⟨x, (memC₂ _ _).2 ⟨hx, hxI⟩, fun x' h => succ_uniq A hnd ((memC₂ _ _).1 h).1 hx⟩
  have e₁ : C₁ = E₁ := hu₁ _ hC₁
  have e₂ : C₂ = E₂ := hu₂ _ hC₂
  have hu₁' : ∀ F, PerfectMatching M₁ I (I ∩ S) (S \ I) F → F = C₁ := by
    intro F hF; rw [e₁]; exact hu₁ F hF
  have hu₂' : ∀ F, PerfectMatching M₂ I (I ∩ S) (S \ I) F → F = C₂ := by
    intro F hF; rw [e₂]; exact hu₂ F hF
  have hLI : I ∩ S ⊆ I := Finset.inter_subset_left
  have hRI : Disjoint (S \ I) I := Finset.sdiff_disjoint
  -- generic consequence of `core`
  have fin₁ : ∀ E' ⊆ C₁, ∀ T : Finset (Fin n),
      (∀ z ∈ T, z ∈ I → z ∉ E'.image Prod.fst) → (∀ z ∈ T, z ∉ I → z ∈ E'.image Prod.snd) →
      M₁.Indep (↑T : Set (Fin n)) := by
    intro E' hE' T h1 h2
    refine (core M₁ hE₁ I _ _ hI₁ C₁ hC₁ hu₁' hLI hRI E' hE').subset ?_
    intro z hz
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff] at hz ⊢
    by_cases hzI : z ∈ I
    · exact Or.inl ⟨hzI, h1 z hz hzI⟩
    · exact Or.inr (h2 z hz hzI)
  have fin₂ : ∀ E' ⊆ C₂, ∀ T : Finset (Fin n),
      (∀ z ∈ T, z ∈ I → z ∉ E'.image Prod.fst) → (∀ z ∈ T, z ∉ I → z ∈ E'.image Prod.snd) →
      M₂.Indep (↑T : Set (Fin n)) := by
    intro E' hE' T h1 h2
    refine (core M₂ hE₂ I _ _ hI₂ C₂ hC₂ hu₂' hLI hRI E' hE').subset ?_
    intro z hz
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff] at hz ⊢
    by_cases hzI : z ∈ I
    · exact Or.inl ⟨hzI, h1 z hz hzI⟩
    · exact Or.inr (h2 z hz hzI)
  have harcI : ∀ x y, A.edge x y → y ∉ I → x ∈ I := by
    intro x y h hy
    rcases harc x y h with h | h
    · exact h.1
    · exact absurd h.1 hy
  have harcI' : ∀ x y, A.edge y x → y ∉ I → x ∈ I := by
    intro x y h hy
    rcases harc y x h with h | h
    · exact absurd h.1 hy
    · exact h.1
  have notA : ∀ x, ¬ A.endpoint x := by
    intro x h; rw [WalkData.endpoint, hc] at h; simp at h
  refine ⟨hdir, ⟨?_, ?_⟩, ?_⟩
  · apply fin₁ C₁ subset_rfl
    · intro z hz hzI hz'
      obtain ⟨⟨a, b⟩, he, rfl⟩ := Finset.mem_image.1 hz'
      have := (Finset.mem_symmDiff.1 hz)
      have hb := (edge_mem A ((memC₁ _ _).1 he).1).1
      rcases this with ⟨_, h⟩ | ⟨_, h⟩
      · exact h ((memS _).2 hb)
      · exact h hzI
    · intro z hz hzI
      have hzS : z ∈ S := by
        rcases Finset.mem_symmDiff.1 hz with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h hzI
        · exact h
      obtain ⟨x, hx⟩ := pred_ex A hc ((memS z).1 hzS)
      exact Finset.mem_image.2 ⟨(x, z), (memC₁ _ _).2 ⟨hx, harcI x z hx hzI⟩, rfl⟩
  · apply fin₂ C₂ subset_rfl
    · intro z hz hzI hz'
      obtain ⟨⟨a, b⟩, he, rfl⟩ := Finset.mem_image.1 hz'
      have := (Finset.mem_symmDiff.1 hz)
      have hb := (edge_mem A ((memC₂ _ _).1 he).1).2
      rcases this with ⟨_, h⟩ | ⟨_, h⟩
      · exact h ((memS _).2 hb)
      · exact h hzI
    · intro z hz hzI
      have hzS : z ∈ S := by
        rcases Finset.mem_symmDiff.1 hz with ⟨h, _⟩ | ⟨h, _⟩
        · exact absurd h hzI
        · exact h
      obtain ⟨x, hx⟩ := succ_ex A hc ((memS z).1 hzS)
      exact Finset.mem_image.2 ⟨(x, z), (memC₂ _ _).2 ⟨hx, harcI' x z hx hzI⟩, rfl⟩
  · intro B hB hend
    obtain ⟨hBc, -, -, hBsub, hBedge⟩ := hB
    have memB : ∀ x, x ∈ B.support ↔ x ∈ B.vertices := fun x => List.mem_toFinset
    have hhead : ∀ x, B.vertices.head? = some x → x ∈ I := fun x h =>
      (hend x ⟨hBc, Or.inl h⟩).resolve_left (notA x)
    have hlast : ∀ x, B.vertices.getLast? = some x → x ∈ I := fun x h =>
      (hend x ⟨hBc, Or.inr h⟩).resolve_left (notA x)
    constructor
    · apply fin₁ (C₁.filter (fun e => B.edge e.1 e.2)) (Finset.filter_subset _ _)
      · intro z hz hzI hz'
        obtain ⟨⟨a, b⟩, he, rfl⟩ := Finset.mem_image.1 hz'
        have hb := (edge_mem B (Finset.mem_filter.1 he).2).1
        rcases Finset.mem_symmDiff.1 hz with ⟨_, h⟩ | ⟨_, h⟩
        · exact h ((memB _).2 hb)
        · exact h hzI
      · intro z hz hzI
        have hzB : z ∈ B.vertices := by
          rcases Finset.mem_symmDiff.1 hz with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h hzI
          · exact (memB _).1 h
        obtain ⟨x, hx⟩ := open_pred B hzB (fun h => hzI (hhead z h))
        have hxA := hBedge x z hx
        exact Finset.mem_image.2 ⟨(x, z), Finset.mem_filter.2
          ⟨(memC₁ _ _).2 ⟨hxA, harcI x z hxA hzI⟩, hx⟩, rfl⟩
    · apply fin₂ (C₂.filter (fun e => B.edge e.2 e.1)) (Finset.filter_subset _ _)
      · intro z hz hzI hz'
        obtain ⟨⟨a, b⟩, he, rfl⟩ := Finset.mem_image.1 hz'
        have hb := (edge_mem B (Finset.mem_filter.1 he).2).2
        rcases Finset.mem_symmDiff.1 hz with ⟨_, h⟩ | ⟨_, h⟩
        · exact h ((memB _).2 hb)
        · exact h hzI
      · intro z hz hzI
        have hzB : z ∈ B.vertices := by
          rcases Finset.mem_symmDiff.1 hz with ⟨h, _⟩ | ⟨h, _⟩
          · exact absurd h hzI
          · exact (memB _).1 h
        obtain ⟨x, hx⟩ := open_succ B hzB (fun h => hzI (hlast z h))
        have hxA := hBedge z x hx
        exact Finset.mem_image.2 ⟨(x, z), Finset.mem_filter.2
          ⟨(memC₂ _ _).2 ⟨hxA, harcI' x z hxA hzI⟩, hx⟩, rfl⟩
