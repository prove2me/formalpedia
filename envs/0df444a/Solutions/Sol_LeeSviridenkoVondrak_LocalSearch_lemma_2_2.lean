-- Prove2me | solution 1 for LeeSviridenkoVondrak.LocalSearch.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:19:51.978617+00:00
-- url     : https://prove2.me/submissions/2f456219-278f-418f-ae98-da605329efd3

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

open LeeSviridenkoVondrak.LocalSearch in
theorem solution {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (I J : Finset (Fin n)) (hI : M.Indep (↑I : Set (Fin n)))
    (hcard : I.card = J.card)
    (hunique : ∃! E, PerfectMatching M I (I \ J) (J \ I) E) :
    M.Indep (↑J : Set (Fin n)) := by
  have h := X6LSV.main M hE I hI _ (I \ J) (J \ I) rfl Finset.sdiff_subset
    Finset.sdiff_disjoint hunique
  have : (I \ (I \ J)) ∪ (J \ I) = J := by
    ext z; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rwa [this] at h
