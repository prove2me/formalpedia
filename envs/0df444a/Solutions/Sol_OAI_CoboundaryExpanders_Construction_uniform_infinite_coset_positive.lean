-- Prove2me | solution 1 for OAI.CoboundaryExpanders.Construction.uniform_infinite_coset_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:30:47.31493+00:00
-- url     : https://prove2.me/submissions/80917d58-886f-450f-852b-4a6e28734150

import Mathlib
import Definitions.Def_OAIQ3Cb002

section
-- module Solutions.OAIQ3_Cob.Coboundary_Chains
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Augmented F2 simplicial chains, boundaries, exactness, and relative attachments.
-/

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains

namespace Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma project_apply (F : Finset W) (c : Raw (W ⊕ V)) (t : Finset V) :
    project F c t = c (F.disjSum t) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single s a =>
    simp only [project_single]
    by_cases h : s.toLeft = F
    · rw [ite_eq_left h]
      have he : s = F.disjSum t ↔ s.toRight = t := by
        rw [Finset.eq_disjSum_iff]
        simp [h]
      simp only [Finsupp.single_apply, he]
    · rw [ite_eq_right h]
      have he : s ≠ F.disjSum t := by
        intro he
        exact h (by simp [he])
      simp [he]

omit [DecidableEq V] [DecidableEq W] in
lemma joinFaces_downward (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V)
    {s t : Finset (W ⊕ V)} (hs : s ∈ joinFaces F O) (ht : t ⊆ s) :
    t ∈ joinFaces F O :=
  ⟨(Finset.toLeft_subset_toLeft ht).trans hs.1,
    O.downward hs.2 (Finset.toRight_subset_toRight ht)⟩

lemma project_eq_zero_iff (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (c : Raw (W ⊕ V))
    (hc : c ∈ supported (joinFaces F O)) :
    project F c = 0 ↔ c ∈ supported (oldFaces F O) := by
  rw [mem_supported] at hc ⊢
  constructor
  · intro hz s hs
    refine ⟨hc s hs, ?_⟩
    intro he
    have he' : F.disjSum s.toRight = s := by
      rw [← he, Finset.toLeft_disjSum_toRight]
    have := congrArg (fun b : Raw V => b s.toRight) hz
    rw [project_apply, he'] at this
    exact hs this
  · intro h
    apply Finsupp.ext
    intro t
    rw [project_apply]
    by_contra he
    obtain ⟨_, ht⟩ := h (F.disjSum t) he
    exact ht (by simp)

lemma boundary_supported (P : Set (Finset V))
    (hdown : ∀ {s t}, s ∈ P → t ⊆ s → t ∈ P)
    (c : Raw V) (hc : c ∈ supported P) : rawBoundary c ∈ supported P := by
  apply map_supported rawBoundary P P _ c hc
  intro s hs a
  rw [rawBoundary_single]
  apply Submodule.sum_mem
  intro v hv
  exact single_mem_supported (hdown hs (Finset.erase_subset v s)) a

lemma project_boundary_single (F : Finset W) (s : Finset (W ⊕ V)) (a : k)
    (hs : s.toLeft ⊆ F) :
    project F (rawBoundary (Finsupp.single s a)) =
      rawBoundary (project F (Finsupp.single s a)) := by
  conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := s)]
  rw [boundary_disjSum_single, map_add, map_sum, map_sum]
  have hleft : (∑ w ∈ s.toLeft,
      project F (Finsupp.single ((s.toLeft.erase w).disjSum s.toRight) a)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    have he : s.toLeft.erase w ≠ F := by
      intro he
      have hf : w ∈ s.toLeft.erase w := he ▸ hs hw
      exact Finset.notMem_erase w s.toLeft hf
    simp [he]
  rw [hleft, zero_add, project_single]
  by_cases he : s.toLeft = F
  · simp only [he, Finset.toLeft_disjSum, Finset.toRight_disjSum, project_single,
      ite_true, rawBoundary_single]
  · simp only [project_single, Finset.toLeft_disjSum, he, ite_false, map_zero,
      Finset.sum_const_zero]

lemma project_boundary (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (c : Raw (W ⊕ V))
    (hc : c ∈ supported (joinFaces F O)) :
    project F (rawBoundary c) = rawBoundary (project F c) := by
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact project_boundary_single F s (c s)
    (((mem_supported _ c).mp hc s (Finsupp.mem_support_iff.mp hs)).1)

omit [DecidableEq V] in
lemma graded_forget (P : Set (Finset V)) (n : ℕ) :
    supported (graded P n) ≤ supported P :=
  supported_mono (fun _ hs => hs.1)

lemma append_graded (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ)
    (c : Raw V) (hc : c ∈ supported (graded O.faces n)) :
    append F c ∈ supported (graded (joinFaces F O) (F.card+n)) := by
  apply map_supported (append F) (graded O.faces n)
    (graded (joinFaces F O) (F.card+n)) _ c hc
  intro s hs a
  rw [append_single]
  apply single_mem_supported
  refine ⟨⟨by simp, by simpa using hs.1⟩, ?_⟩
  simp [hs.2]

lemma project_graded (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ)
    (c : Raw (W ⊕ V)) (hc : c ∈ supported (graded (joinFaces F O) (F.card+n))) :
    project F c ∈ supported (graded O.faces n) := by
  rw [mem_supported] at hc ⊢
  intro t ht
  rw [project_apply] at ht
  obtain ⟨hs, hn⟩ := hc (F.disjSum t) ht
  refine ⟨by simpa using hs.2, ?_⟩
  simp only [Finset.card_disjSum] at hn
  omega

theorem relative_filling (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ)
    (hO : ExactIn O.faces n)
    (c : Raw (W ⊕ V))
    (hc : c ∈ supported (graded (joinFaces F O) (F.card+n)))
    (hδ : rawBoundary c ∈ supported (oldFaces F O)) :
    ∃ b ∈ supported (graded (joinFaces F O) (F.card+n+1)),
      c - rawBoundary b ∈ supported (graded (oldFaces F O) (F.card+n)) := by
  have hc' := graded_forget (joinFaces F O) (F.card+n) hc
  have hδ' := boundary_supported (joinFaces F O) (joinFaces_downward F O) c hc'
  have hz : rawBoundary (project F c) = 0 := by
    rw [← project_boundary F O c hc']
    exact (project_eq_zero_iff F O (rawBoundary c) hδ').mpr hδ
  obtain ⟨b, hb, hbc⟩ := hO (project F c) (project_graded F O n c hc) hz
  have hab : append F b ∈ supported (graded (joinFaces F O) (F.card+n+1)) := by
    simpa [Nat.add_assoc] using append_graded F O (n+1) b hb
  refine ⟨append F b, hab, ?_⟩
  have hDB := boundary_graded (joinFaces F O) (joinFaces_downward F O)
    (F.card+n) (append F b) hab
  have hsub := (supported (graded (joinFaces F O) (F.card+n))).sub_mem hc hDB
  have hsub' := graded_forget (joinFaces F O) (F.card+n) hsub
  have hzero : project F (c - rawBoundary (append F b)) = 0 := by
    rw [map_sub, project_boundary F O (append F b)
      (graded_forget (joinFaces F O) (F.card+n+1) hab)]
    have hep : project F (append F b) = b :=
      congrArg (fun f : Raw V →ₗ[k] Raw V => f b) (project_append F)
    rw [hep, hbc, sub_self]
  have hold := (project_eq_zero_iff F O _ hsub').mp hzero
  rw [mem_supported] at hsub hold ⊢
  exact fun s hs => ⟨hold s hs, (hsub s hs).2⟩

omit [DecidableEq V] [DecidableEq W] in
lemma low_degree_old (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ) (hn : n < F.card)
    (c : Raw (W ⊕ V)) (hc : c ∈ supported (graded (joinFaces F O) n)) :
    c ∈ supported (graded (oldFaces F O) n) := by
  rw [mem_supported] at hc ⊢
  intro s hs
  obtain ⟨hface, hcard⟩ := hc s hs
  refine ⟨⟨hface, ?_⟩, hcard⟩
  intro he
  have h := Finset.card_toLeft_add_card_toRight (u := s)
  rw [he, hcard] at h
  omega

lemma relativeExactIn_join (F : Finset W) (O : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ)
    (hO : F.card ≤ n → ExactIn O.faces (n-F.card)) :
    RelativeExactIn (oldFaces F O) (joinFaces F O) n := by
  intro c hc hδ
  by_cases hn : F.card ≤ n
  · have he : F.card + (n-F.card) = n := Nat.add_sub_of_le hn
    simpa only [he] using relative_filling F O (n-F.card) (hO hn) c
      (by simpa only [he] using hc) hδ
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    simpa using (low_degree_old F O n (by omega) c hc)

omit [DecidableEq V] in
lemma finite_stage (P : ℕ → Set (Finset V)) (hP : Monotone P) (n : ℕ)
    (c : Raw V) (hc : c ∈ supported (graded (⋃ m, P m) n)) :
    ∃ m, c ∈ supported (graded (P m) n) := by
  have hdir : Directed (· ⊆ ·) P := fun i j =>
    ⟨max i j, hP (le_max_left i j), hP (le_max_right i j)⟩
  have hs : (c.support : Set (Finset V)) ⊆ ⋃ m, P m := by
    intro s hs
    exact ((mem_supported _ c).mp hc s (Finsupp.mem_support_iff.mp hs)).1
  obtain ⟨m, hm⟩ := hdir.exists_mem_subset_of_finset_subset_biUnion hs
  refine ⟨m, ?_⟩
  rw [mem_supported] at hc ⊢
  exact fun s hs => ⟨hm (Finsupp.mem_support_iff.mpr hs), (hc s hs).2⟩

lemma push_filling (P Q : Set (Finset V)) (n : ℕ)
    (hPQ : RelativeExactIn P Q (n+1))
    (b : Raw V) (hb : b ∈ supported (graded Q (n+1)))
    (hδ : rawBoundary b ∈ supported P) :
    ∃ a ∈ supported (graded P (n+1)), rawBoundary a = rawBoundary b := by
  obtain ⟨e, _, he⟩ := hPQ b hb hδ
  refine ⟨b - rawBoundary e, he, ?_⟩
  rw [map_sub]
  have hh := LinearMap.congr_fun (rawBoundary_squared (V := V)) e
  change rawBoundary (rawBoundary e) = 0 at hh
  rw [hh, sub_zero]

theorem exactIn_initial_of_filtration (P : ℕ → Set (Finset V))
    (hP : Monotone P) (n : ℕ)
    (hstep : ∀ m, RelativeExactIn (P m) (P (m+1)) (n+1))
    (hunion : ExactIn (⋃ m, P m) n) : ExactIn (P 0) n := by
  intro c hc hcz
  have hcu : c ∈ supported (graded (⋃ m, P m) n) :=
    supported_mono (P := graded (P 0) n) (Q := graded (⋃ m, P m) n)
      (fun s hs => ⟨Set.mem_iUnion.mpr ⟨0, hs.1⟩, hs.2⟩) hc
  obtain ⟨b, hb, hbc⟩ := hunion c hcu hcz
  obtain ⟨m, hbm⟩ := finite_stage P hP (n+1) b hb
  have hdesc : ∀ m, ∀ b ∈ supported (graded (P m) (n+1)), rawBoundary b = c →
      ∃ a ∈ supported (graded (P 0) (n+1)), rawBoundary a = c := by
    intro m
    induction m with
    | zero => exact fun b hb hbc => ⟨b, hb, hbc⟩
    | succ m ih =>
      intro b hb hbc
      have hδ : rawBoundary b ∈ supported (P m) := by
        rw [hbc]
        exact supported_mono (hP (Nat.zero_le m)) (graded_forget (P 0) n hc)
      obtain ⟨a, ha, hab⟩ := push_filling (P m) (P (m+1)) n (hstep m) b hb hδ
      exact ih a ha (hab.trans hbc)
  exact hdesc m b hbm hbc

omit [DecidableEq V] in
lemma embed_supported_equiv (X : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ) (c : X.Chains n) :
    X.embed n c = ((Finsupp.supportedEquivFinsupp (R := k)
      (graded X.faces n)).symm c : Raw V) := by
  let e := Finsupp.supportedEquivFinsupp (M := k) (R := k) (graded X.faces n)
  have he : X.embed n = (Finsupp.supported k k (graded X.faces n)).subtype.comp
      e.symm.toLinearMap := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
      CoboundaryExpanders.InfiniteChains.Complex.embed_single]
    exact (Finsupp.supportedEquivFinsupp_symm_single (R := k) (graded X.faces n) s a).symm
  exact LinearMap.congr_fun he c

omit [DecidableEq V] in
lemma embed_mem_graded (X : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ) (c : X.Chains n) :
    X.embed n c ∈ supported (graded X.faces n) := by
  rw [embed_supported_equiv]
  exact ((Finsupp.supportedEquivFinsupp (R := k) (graded X.faces n)).symm c).property

omit [DecidableEq V] in
lemma exists_embed_of_mem_graded (X : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ) (c : Raw V)
    (hc : c ∈ supported (graded X.faces n)) : ∃ b : X.Chains n, X.embed n b = c := by
  let e := Finsupp.supportedEquivFinsupp (M := k) (R := k) (graded X.faces n)
  have hc' : c ∈ Finsupp.supported k k (graded X.faces n) := hc
  refine ⟨e ⟨c, hc'⟩, ?_⟩
  exact (embed_supported_equiv X n _).trans
    (congrArg Subtype.val (e.symm_apply_apply ⟨c, hc'⟩))

lemma exactIn_iff_boundary_exact (X : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ) :
    ExactIn X.faces (n+1) ↔ Function.Exact (X.boundary (n+1)) (X.boundary n) := by
  constructor
  · intro h c
    constructor
    · intro hc
      have hz : rawBoundary (X.embed (n+1) c) = 0 := by
        calc
          rawBoundary (X.embed (n+1) c) = X.embed n (X.boundary n c) :=
            (LinearMap.congr_fun (X.embed_boundary n) c).symm
          _ = 0 := by rw [hc, map_zero]
      obtain ⟨b, hb, hbc⟩ := h _ (embed_mem_graded X (n+1) c) hz
      obtain ⟨a, rfl⟩ := exists_embed_of_mem_graded X (n+2) b hb
      refine ⟨a, X.embed_injective (n+1) ?_⟩
      exact (LinearMap.congr_fun (X.embed_boundary (n+1)) a).trans hbc
    · rintro ⟨b, rfl⟩
      exact LinearMap.congr_fun (X.boundary_squared n) b
  · intro h c hc hz
    obtain ⟨a, rfl⟩ := exists_embed_of_mem_graded X (n+1) c hc
    have ha : X.boundary n a = 0 := by
      apply X.embed_injective n
      rw [map_zero]
      exact (LinearMap.congr_fun (X.embed_boundary n) a).trans hz
    obtain ⟨b, hb⟩ := (h a).mp ha
    refine ⟨X.embed (n+2) b, embed_mem_graded X (n+2) b, ?_⟩
    calc
      rawBoundary (X.embed (n+2) b) = X.embed (n+1) (X.boundary (n+1) b) :=
        (LinearMap.congr_fun (X.embed_boundary (n+1)) b).symm
      _ = X.embed (n+1) a := congrArg (X.embed (n+1)) hb

lemma chainComplex_exactAt_of_exactIn (X : CoboundaryExpanders.InfiniteChains.Complex V) (n : ℕ)
    (h : ExactIn X.faces (n+2)) : X.chainComplex.ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  apply (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (X.chainComplex.d (n+2) (n+1)) (X.chainComplex.d (n+1) n)
  rw [CoboundaryExpanders.InfiniteChains.Complex.chainComplex_d, CoboundaryExpanders.InfiniteChains.Complex.chainComplex_d]
  exact (exactIn_iff_boundary_exact X (n+1)).mp h

omit [DecidableEq V] in
lemma split_union (A B : Set (Finset V)) (n : ℕ) (c : Raw V)
    (hc : c ∈ supported (graded (A ∪ B) n)) :
    ∃ a ∈ supported (graded A n), ∃ b ∈ supported (graded B n), c = a+b := by
  classical
  refine ⟨c.filter (· ∈ A), ?_, c.filter (· ∉ A), ?_, ?_⟩
  · rw [mem_supported]
    intro s hs
    have ha : s ∈ A := by
      by_contra hn
      exact hs (Finsupp.filter_apply_neg _ _ hn)
    have hs' : c s ≠ 0 := by simpa [Finsupp.filter_apply, ha] using hs
    exact ⟨ha, ((mem_supported _ c).mp hc s hs').2⟩
  · rw [mem_supported]
    intro s hs
    have ha : s ∉ A := by
      intro hy
      exact hs (by simp [hy])
    have hs' : c s ≠ 0 := by simpa [Finsupp.filter_apply, ha] using hs
    obtain ⟨hAB, hn⟩ := (mem_supported _ c).mp hc s hs'
    exact ⟨hAB.resolve_left ha, hn⟩
  · exact (Finsupp.filter_add_filter_not c (· ∈ A)).symm

lemma boundary_piece_supported (P A B : Set (Finset V))
    (hAB : A ∩ B ⊆ P) (a b : Raw V)
    (ha : rawBoundary a ∈ supported A) (hb : rawBoundary b ∈ supported B)
    (hab : rawBoundary (a+b) ∈ supported P) : rawBoundary a ∈ supported P := by
  rw [mem_supported] at ha hb hab ⊢
  intro s hs
  by_contra hp
  have hz : rawBoundary (a+b) s = 0 := by
    by_contra he
    exact hp (hab s he)
  have hs' : rawBoundary b s ≠ 0 := by
    intro hbz
    rw [map_add, Finsupp.add_apply, hbz, add_zero] at hz
    exact hs hz
  exact hp (hAB ⟨ha s hs, hb s hs'⟩)

lemma relativeExactIn_union (P A B : Set (Finset V)) (n : ℕ)
    (hA : ∀ {s t}, s ∈ A → t ⊆ s → t ∈ A)
    (hB : ∀ {s t}, s ∈ B → t ⊆ s → t ∈ B)
    (hAB : A ∩ B ⊆ P)
    (hPA : RelativeExactIn P A n) (hPB : RelativeExactIn P B n) :
    RelativeExactIn P (A ∪ B) n := by
  intro c hc hδ
  obtain ⟨a, ha, b, hb, rfl⟩ := split_union A B n c hc
  have hda := boundary_supported A hA a (graded_forget A n ha)
  have hdb := boundary_supported B hB b (graded_forget B n hb)
  have had := boundary_piece_supported P A B hAB a b hda hdb hδ
  have hbd : rawBoundary b ∈ supported P := by
    have he : rawBoundary b = rawBoundary (a+b) - rawBoundary a := by
      rw [map_add]; abel
    rw [he]
    exact (supported P).sub_mem hδ had
  obtain ⟨ea, hea, hae⟩ := hPA a ha had
  obtain ⟨eb, heb, hbe⟩ := hPB b hb hbd
  refine ⟨ea+eb, ?_, ?_⟩
  · apply Submodule.add_mem
    · exact supported_mono (P := graded A (n+1)) (Q := graded (A ∪ B) (n+1))
        (fun s hs => ⟨Or.inl hs.1, hs.2⟩) hea
    · exact supported_mono (P := graded B (n+1)) (Q := graded (A ∪ B) (n+1))
        (fun s hs => ⟨Or.inr hs.1, hs.2⟩) heb
  · have he : a+b-rawBoundary (ea+eb) = (a-rawBoundary ea)+(b-rawBoundary eb) := by
      rw [map_add]; abel
    rw [he]
    exact Submodule.add_mem _ hae hbe

lemma relativeExactIn_empty (P : Set (Finset V)) (n : ℕ) :
    RelativeExactIn P ∅ n := by
  intro c hc _
  have hz : c = 0 := by
    ext s
    by_contra hs
    exact ((mem_supported _ c).mp hc s hs).1
  subst c
  exact ⟨0, Submodule.zero_mem _, by simp⟩

lemma relativeExactIn_finite_union {ι : Type*} (P : Set (Finset V))
    (A : ι → Set (Finset V)) (n : ℕ)
    (hA : ∀ i, ∀ {s t}, s ∈ A i → t ⊆ s → t ∈ A i)
    (hAB : ∀ i j, i ≠ j → A i ∩ A j ⊆ P)
    (hPA : ∀ i, RelativeExactIn P (A i) n) (I : Finset ι) :
    RelativeExactIn P (⋃ i ∈ I, A i) n := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using relativeExactIn_empty P n
  | @insert i I hi ih =>
    rw [Finset.set_biUnion_insert]
    apply relativeExactIn_union P (A i) (⋃ j ∈ I, A j) n (hA i) _ _ (hPA i) ih
    · intro s t hs ht
      obtain ⟨j, hj, hs⟩ := Set.mem_iUnion₂.mp hs
      exact Set.mem_iUnion₂.mpr ⟨j, hj, hA j hs ht⟩
    · intro s hs
      obtain ⟨j, hj, hjs⟩ := Set.mem_iUnion₂.mp hs.2
      exact hAB i j (by intro he; exact hi (he ▸ hj)) ⟨hs.1, hjs⟩

theorem relativeExactIn_iUnion {ι : Type*} (P : Set (Finset V))
    (A : ι → Set (Finset V)) (n : ℕ)
    (hA : ∀ i, ∀ {s t}, s ∈ A i → t ⊆ s → t ∈ A i)
    (hAB : ∀ i j, i ≠ j → A i ∩ A j ⊆ P)
    (hPA : ∀ i, RelativeExactIn P (A i) n) :
    RelativeExactIn P (⋃ i, A i) n := by
  classical
  intro c hc hδ
  have hs : (c.support : Set (Finset V)) ⊆ ⋃ i, A i := by
    intro s hs
    exact ((mem_supported _ c).mp hc s (Finsupp.mem_support_iff.mp hs)).1
  obtain ⟨I, hI, hcs⟩ := Set.finite_subset_iUnion c.support.finite_toSet hs
  have hci : c ∈ supported (graded (⋃ i ∈ hI.toFinset, A i) n) := by
    rw [mem_supported] at hc ⊢
    intro s hs
    refine ⟨?_, (hc s hs).2⟩
    simpa only [hI.mem_toFinset] using hcs (Finsupp.mem_support_iff.mpr hs)
  obtain ⟨b, hb, hbc⟩ := relativeExactIn_finite_union P A n hA hAB hPA hI.toFinset c hci hδ
  refine ⟨b, ?_, hbc⟩
  apply supported_mono (P := graded (⋃ i ∈ hI.toFinset, A i) (n+1)) _ hb
  intro s hs
  obtain ⟨i, _, his⟩ := Set.mem_iUnion₂.mp hs.1
  exact ⟨Set.mem_iUnion.mpr ⟨i, his⟩, hs.2⟩

end Attachment
end CoboundaryExpanders.InfiniteChains

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Cones
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Quantitative chain cones, face-model transport, relabeling, and exactness under retractions.
-/

section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma rawCone_supported (a : V) (P Q : Set (Finset V))
    (h : ∀ s ∈ P, a ∉ s → insert a s ∈ Q)
    (c : Raw V) (hc : c ∈ supported P) : rawCone a c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs r
  rw [rawCone_single]
  split_ifs with ha
  · exact Submodule.zero_mem _
  · exact single_mem_supported (h s hs ha) r

lemma rawCone_graded (a : V) (P Q : Set (Finset V)) (n : ℕ)
    (h : ∀ s ∈ P, a ∉ s → insert a s ∈ Q)
    (c : Raw V) (hc : c ∈ supported (graded P n)) :
    rawCone a c ∈ supported (graded Q (n+1)) := by
  apply rawCone_supported a (graded P n) (graded Q (n+1)) _ c hc
  intro s hs ha
  exact ⟨h s hs.1 ha, by rw [Finset.card_insert_of_notMem ha, hs.2]⟩

lemma carrierFill_eq (apex : Finset V → V) (s : Finset V) :
    carrierFill apex s = rawCone (apex s)
      (Finsupp.single s 1 + ∑ v ∈ s, carrierFill apex (s.erase v)) := by
  rw [carrierFill]
  congr 2
  exact Finset.sum_coe_sort s (fun v => carrierFill apex (s.erase v))

lemma boundary_carrierFill (apex : Finset V → V) (s : Finset V) :
    rawBoundary (carrierFill apex s) =
      Finsupp.single s 1 + ∑ v ∈ s, carrierFill apex (s.erase v) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hdd := LinearMap.congr_fun (rawBoundary_squared (V := V)) (Finsupp.single s 1)
    have hz := congrArg (carrierMap apex) hdd
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, rawBoundary_single,
      map_sum, carrierMap_single, one_smul, map_zero] at hz
    have he : rawBoundary (∑ v ∈ s, carrierFill apex (s.erase v)) = rawBoundary (Finsupp.single s 1) := by
      rw [map_sum]
      trans ∑ v ∈ s, (Finsupp.single (s.erase v) 1 + ∑ w ∈ s.erase v,
          carrierFill apex ((s.erase v).erase w))
      · apply Finset.sum_congr rfl
        intro v hv
        exact ih (s.erase v) (Finset.erase_ssubset hv)
      · rw [Finset.sum_add_distrib, hz, add_zero, rawBoundary_single]
    have hcycle : rawBoundary (Finsupp.single s 1 + ∑ v ∈ s,
        carrierFill apex (s.erase v)) = 0 := by
      rw [map_add, he, twice]
    rw [carrierFill_eq]
    have h := LinearMap.congr_fun (raw_contraction (apex s))
      (Finsupp.single s 1 + ∑ v ∈ s, carrierFill apex (s.erase v))
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hcycle, map_zero, add_zero] using h

lemma carrierMap_contraction (apex : Finset V → V) :
    rawBoundary.comp (carrierMap apex) + (carrierMap apex).comp rawBoundary = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, carrierMap_single,
    map_smul, boundary_carrierFill, rawBoundary_single, map_sum, LinearMap.id_apply]
  rw [smul_add, Finset.smul_sum]
  have h : (∑ v ∈ s, a • carrierFill apex (s.erase v)) +
      (∑ v ∈ s, a • carrierFill apex (s.erase v)) = 0 := twice _
  rw [add_assoc, h, add_zero]
  simp

lemma carrierFill_size (apex : Finset V → V) (s : Finset V) :
    size (carrierFill apex s) ≤ carrierBound s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rw [carrierFill_eq]
    calc
      size (rawCone (apex s) _) ≤ size (Finsupp.single s 1 +
          ∑ v ∈ s, carrierFill apex (s.erase v)) := size_rawCone_le _ _
      _ ≤ 1 + ∑ v ∈ s, size (carrierFill apex (s.erase v)) :=
        (size_add_le _ _).trans (Nat.add_le_add (size_single_le _ _) (size_sum_le _ _))
      _ ≤ 1 + s.card * carrierBound (s.card-1) := by
        apply Nat.add_le_add_left
        calc
          (∑ v ∈ s, size (carrierFill apex (s.erase v))) ≤
              ∑ _v ∈ s, carrierBound (s.card-1) := by
            apply Finset.sum_le_sum
            intro v hv
            simpa only [Finset.card_erase_of_mem hv] using ih (s.erase v) (Finset.erase_ssubset hv)
          _ = _ := by simp
      _ = carrierBound s.card := by
        cases he : s.card with
        | zero => simp [carrierBound]
        | succ n => simp [carrierBound]

lemma carrierFill_supported (X : CoboundaryExpanders.InfiniteChains.Complex V) (C : Finset V → Set (Finset V))
    (apex : Finset V → V)
    (hself : ∀ s ∈ X.faces, s ∈ C s)
    (hmono : ∀ s ∈ X.faces, ∀ t ⊆ s, C t ⊆ C s)
    (hcone : ∀ s ∈ X.faces, ∀ t ∈ C s, insert (apex s) t ∈ C s)
    (s : Finset V) (hs : s ∈ X.faces) :
    carrierFill apex s ∈ supported (graded (C s) (s.card+1)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rw [carrierFill_eq]
    apply rawCone_graded (apex s) (C s) (C s) s.card
      (fun t ht _ => hcone s hs t ht)
    apply Submodule.add_mem
    · exact single_mem_supported (P := graded (C s) s.card) ⟨hself s hs, rfl⟩ _
    · apply Submodule.sum_mem
      intro v hv
      have hi := ih (s.erase v) (Finset.erase_ssubset hv)
        (X.downward hs (Finset.erase_subset _ _))
      apply supported_mono (P := graded (C (s.erase v)) ((s.erase v).card+1))
        (Q := graded (C s) s.card) ?_ hi
      intro t ht
      refine ⟨hmono s hs _ (Finset.erase_subset _ _) ht.1, ?_⟩
      have htcard := ht.2
      rw [Finset.card_erase_of_mem hv] at htcard
      have hpos := Finset.card_pos.mpr ⟨v, hv⟩
      omega

lemma cone_link_without (v : V) (c : Raw V) :
    rawCone v (link v c) + without v c = c := by
  have h : (rawCone v).comp (link v) + without v = LinearMap.id := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
      link_single, without_single, LinearMap.id_apply]
    by_cases hv : v ∈ s
    · simp [hv, Finset.insert_erase hv]
    · simp [hv]
  exact LinearMap.congr_fun h c

lemma link_boundary (v : V) :
    (link v).comp rawBoundary = rawBoundary.comp (link v) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, rawBoundary_single, map_sum,
    link_single]
  by_cases hv : v ∈ s
  · rw [ite_eq_left hv, rawBoundary_single]
    rw [← Finset.sum_erase_add _ _ hv]
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro w hw
    have hwv := (Finset.mem_erase.mp hw).1
    rw [ite_eq_left ⟨Ne.symm hwv, hv⟩, Finset.erase_right_comm]
  · rw [ite_eq_right hv, map_zero]
    apply Finset.sum_eq_zero
    intro w hw
    exact ite_eq_right (fun h => hv (Finset.mem_of_mem_erase h))

lemma link_cycle (v : V) (c : Raw V) (hc : rawBoundary c = 0) :
    rawBoundary (link v c) = 0 := by
  have h := LinearMap.congr_fun (link_boundary v) c
  simpa [hc] using h.symm

lemma link_supported (v : V) (P Q : Set (Finset V))
    (h : ∀ s ∈ P, v ∈ s → s.erase v ∈ Q)
    (c : Raw V) (hc : c ∈ supported P) : link v c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs a
  rw [link_single]
  split_ifs with hv
  · exact single_mem_supported (h s hs hv) a
  · exact Submodule.zero_mem _

lemma link_graded (v : V) (P Q : Set (Finset V)) (n : ℕ)
    (h : ∀ s ∈ P, v ∈ s → s.erase v ∈ Q)
    (c : Raw V) (hc : c ∈ supported (graded P (n+1))) :
    link v c ∈ supported (graded Q n) := by
  apply link_supported v (graded P (n+1)) (graded Q n) _ c hc
  intro s hs hv
  exact ⟨h s hs.1 hv, by rw [Finset.card_erase_of_mem hv, hs.2]; omega⟩

lemma without_supported (v : V) (P : Set (Finset V))
    (c : Raw V) (hc : c ∈ supported P) :
    without v c ∈ supported {s | s ∈ P ∧ v ∉ s} := by
  apply map_supported _ P _ _ c hc
  intro s hs a
  rw [without_single]
  split_ifs with hv
  · exact Submodule.zero_mem _
  · exact single_mem_supported (P := {s | s ∈ P ∧ v ∉ s}) ⟨hs, hv⟩ a

lemma link_size (v : V) (c : Raw V) : size (link v c) ≤ size c := by
  have h := size_map_le (link v) Set.univ 1 (fun s _ => by
    rw [link_single]
    split_ifs
    · exact size_single_le _ _
    · simp) c (by rw [mem_supported]; simp)
  simpa using h

lemma without_size (v : V) (c : Raw V) : size (without v c) ≤ size c := by
  have h := size_map_le (without v) Set.univ 1 (fun s _ => by
    rw [without_single]
    split_ifs
    · simp
    · exact size_single_le _ _) c (by rw [mem_supported]; simp)
  simpa using h

lemma elimination_identity (v : V) (c b : Raw V) (hb : rawBoundary b = link v c) :
    rawBoundary (rawCone v b) + (without v c + b) = c := by
  have h := LinearMap.congr_fun (raw_contraction v) b
  have he : rawBoundary (rawCone v b) + rawCone v (link v c) = b := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hb] using h
  have he' : rawBoundary (rawCone v b) = b + rawCone v (link v c) := by
    calc
      rawBoundary (rawCone v b) = rawBoundary (rawCone v b) +
          (rawCone v (link v c) + rawCone v (link v c)) := by rw [twice, add_zero]
      _ = b + rawCone v (link v c) := by rw [← add_assoc, he]
  rw [he']
  calc
    b + rawCone v (link v c) + (without v c + b) =
        (rawCone v (link v c) + without v c) + (b+b) := by ac_rfl
    _ = c := by rw [twice, add_zero, cone_link_without]

lemma elimination_cycle (v : V) (c b : Raw V) (hc : rawBoundary c = 0)
    (hb : rawBoundary b = link v c) : rawBoundary (without v c + b) = 0 := by
  have he := congrArg rawBoundary (elimination_identity v c b hb)
  have hdd := LinearMap.congr_fun (rawBoundary_squared (V := V)) (rawCone v b)
  have hdd' : rawBoundary (rawBoundary (rawCone v b)) = 0 := hdd
  simpa only [map_add, hdd', zero_add, hc] using he

namespace BoundedCone
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)

lemma fills (r : ℕ) (hr : r ≤ n) (c : Raw V)
    (hc : c ∈ supported (graded X.faces r)) (hz : rawBoundary c = 0) :
    rawBoundary (H.hom c) = c := by
  simpa only [hz, map_zero, add_zero] using H.contraction_apply r hr c hc

include H in
lemma exactIn (r : ℕ) (hr : r ≤ n) : ExactIn X.faces r := by
  intro c hc hz
  exact ⟨H.hom c, H.map_graded r hr c hc, H.fills r hr c hc hz⟩

end BoundedCone

lemma mem_vertices (c : Raw V) (s : Finset V) (hs : c s ≠ 0) (v : V) (hv : v ∈ s) :
    v ∈ vertices c := Finset.mem_biUnion.mpr ⟨s, Finsupp.mem_support_iff.mpr hs, hv⟩

lemma vertices_card_le (P : Set (Finset V)) (r : ℕ) (c : Raw V)
    (hc : c ∈ supported (graded P r)) : (vertices c).card ≤ r * size c := by
  calc
    (vertices c).card ≤ ∑ s ∈ c.support, s.card := Finset.card_biUnion_le
    _ = r * size c := by
      rw [Finset.sum_congr rfl (fun s hs =>
        ((mem_supported _ _).mp hc s (Finsupp.mem_support_iff.mp hs)).2)]
      simp [size, Nat.mul_comm]

omit [DecidableEq V] in
lemma allowed_forget (X : CoboundaryExpanders.InfiniteChains.Complex V) (bad : V → Prop) (A : Finset V) (r : ℕ) :
    supported (graded (allowed X bad A).faces r) ≤ supported (graded X.faces r) :=
  supported_mono (fun _ hs => ⟨hs.1.1, hs.2⟩)

lemma removeBad (X : CoboundaryExpanders.InfiniteChains.Complex V) (bad : V → Prop) (r R : ℕ)
    (linkFill : ∀ v, bad v → ∀ c : Raw V,
      c ∈ supported (graded X.faces r) → rawBoundary c = 0 →
      ∃ b : Raw V,
        b ∈ supported (graded {s | s ∈ X.faces ∧
          (∀ w ∈ s, ¬bad w) ∧ insert v s ∈ X.faces} r) ∧
        rawBoundary b = link v c ∧ size b ≤ R * size c)
    (A : Finset V) (hA : ∀ v ∈ A, bad v) (c : Raw V)
    (hc : c ∈ supported (graded (allowed X bad A).faces r)) (hz : rawBoundary c = 0) :
    ∃ e c' : Raw V,
      e ∈ supported (graded X.faces (r+1)) ∧
      c' ∈ supported (graded (allowed X bad ∅).faces r) ∧
      rawBoundary c' = 0 ∧ rawBoundary e + c' = c ∧
      size e + size c' ≤ (2*R+2)^A.card * size c := by
  induction A using Finset.induction_on generalizing c with
  | empty =>
    refine ⟨0, c, Submodule.zero_mem _, hc, hz, by simp, ?_⟩
    simp
  | @insert v A hv ih =>
    have hcX := allowed_forget X bad (insert v A) r hc
    obtain ⟨b, hb, hdb, hsize⟩ := linkFill v (hA v (Finset.mem_insert_self _ _)) c hcX hz
    let P : Set (Finset V) := {s | s ∈ X.faces ∧ (∀ w ∈ s, ¬ bad w) ∧ insert v s ∈ X.faces}
    have hbP : b ∈ supported (graded P r) := hb
    have hbA : b ∈ supported (graded (allowed X bad A).faces r) := by
      apply supported_mono (P := graded P r) (Q := graded (allowed X bad A).faces r) ?_ hbP
      intro s hs
      exact ⟨⟨hs.1.1, fun w hw hbad => False.elim (hs.1.2.1 w hw hbad)⟩, hs.2⟩
    have hwA : without v c ∈ supported (graded (allowed X bad A).faces r) := by
      have hw := without_supported v (graded (allowed X bad (insert v A)).faces r) c hc
      apply supported_mono (P := {s | s ∈ graded (allowed X bad (insert v A)).faces r ∧ v ∉ s})
        (Q := graded (allowed X bad A).faces r) ?_ hw
      intro s hs
      refine ⟨⟨hs.1.1.1, ?_⟩, hs.1.2⟩
      intro w hw hbad
      rcases Finset.mem_insert.mp (hs.1.1.2 w hw hbad) with he | he
      · exact False.elim (hs.2 (he ▸ hw))
      · exact he
    have hz' := elimination_cycle v c b hz hdb
    obtain ⟨e, c', he, hc', hz'', hec', hbound⟩ :=
      ih (fun w hw => hA w (Finset.mem_insert_of_mem hw))
        (without v c + b) (Submodule.add_mem _ hwA hbA) hz'
    have hcone : rawCone v b ∈ supported (graded X.faces (r+1)) :=
      rawCone_graded v P X.faces r (fun s hs _ => hs.2.2) b hbP
    refine ⟨rawCone v b + e, c', Submodule.add_mem _ hcone he, hc', hz'', ?_, ?_⟩
    · rw [map_add, add_assoc, hec']
      exact elimination_identity v c b hdb
    · have hnew : size (without v c + b) ≤ (R+1)*size c := by
        have hw := without_size v c
        have hadd := size_add_le (without v c) b
        nlinarith
      have hconesize : size (rawCone v b) ≤ R*size c := (size_rawCone_le _ _).trans hsize
      have hp : 1 ≤ (2*R+2)^A.card := Nat.one_le_pow _ _ (by omega)
      have hh := Nat.mul_le_mul_left ((2*R+2)^A.card) hnew
      have hbnd := size_add_le (rawCone v b) e
      rw [Finset.card_insert_of_notMem hv, pow_succ]
      nlinarith

omit [DecidableEq V] in
lemma relabel_injective (f : V → W) (hf : Function.Injective f) :
    Function.Injective (relabel f) :=
  Finsupp.mapDomain_injective (Finset.image_injective hf)

end CoboundaryExpanders.InfiniteChains.Cone

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

end

open scoped Polynomial BigOperators

namespace CoboundaryExpanders.InfiniteChains.Cone

section
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma exactIn_equivalence (e : V ≃ W) (P : Set (Finset V)) (Q : Set (Finset W))
    (he : ∀ s, s ∈ P ↔ s.image e ∈ Q) (r : ℕ) (hQ : ExactIn Q r) : ExactIn P r := by
  intro c hc hz
  have hm (s : Finset W) (hs : s ∈ Q) : s.image e.symm ∈ P := by
    apply (he _).mpr
    simpa only [Finset.image_image,Equiv.apply_symm_apply,Function.comp_def,Finset.image_id'] using hs
  have ha : relabel e c ∈ supported (graded Q r) :=
    relabel_graded e P Q r (fun s hs => (he s).mp hs) (fun _ _ => e.injective.injOn) c hc
  have haz : rawBoundary (relabel e c) = 0 := by
    have h := LinearMap.congr_fun (relabel_boundary e e.injective) c
    change rawBoundary (relabel e c) = relabel e (rawBoundary c) at h
    rw [h,hz,map_zero]
  obtain ⟨b,hb,heq⟩ := hQ _ ha haz
  refine ⟨relabel e.symm b,relabel_graded e.symm Q P (r+1) hm
    (fun _ _ => e.symm.injective.injOn) b hb,?_⟩
  have h := LinearMap.congr_fun (relabel_boundary e.symm e.symm.injective) b
  change rawBoundary (relabel e.symm b) = relabel e.symm (rawBoundary b) at h
  rw [h,heq]
  exact relabel_retraction e.symm e (graded P r)
    (fun _ _ _ _ => e.symm_apply_apply _) c hc

theorem exactIn_retract (f : V → W) (g : W → V) (P : Set (Finset V)) (Q : Set (Finset W))
    (hf : ∀ s ∈ P, s.image f ∈ Q) (hg : ∀ s ∈ Q, s.image g ∈ P)
    (hfi : ∀ s ∈ P, Set.InjOn f (s : Set V))
    (hgi : ∀ s ∈ Q, Set.InjOn g (s : Set W))
    (hret : ∀ s ∈ P, ∀ v ∈ s, g (f v) = v)
    (r : ℕ) (hQ : ExactIn Q r) : ExactIn P r := by
  intro c hc hz
  have hfc := relabel_graded f P Q r hf hfi c hc
  have hfz : rawBoundary (relabel f c) = 0 := by
    rw [relabel_boundary_on f (graded P r) (fun s hs => hfi s hs.1) c hc,hz,map_zero]
  obtain ⟨b,hb,hbc⟩ := hQ _ hfc hfz
  refine ⟨relabel g b,relabel_graded g Q P (r+1) hg hgi b hb,?_⟩
  rw [relabel_boundary_on g (graded Q (r+1)) (fun s hs => hgi s hs.1) b hb,hbc]
  exact relabel_retraction g f (graded P r) (fun s hs => hret s hs.1) c hc

theorem relativeExactIn_retract (f : V → W) (g : W → V)
    (P Q : Set (Finset V)) (U T : Set (Finset W))
    (hQ : ∀ {s t}, s ∈ Q → t ⊆ s → t ∈ Q)
    (hf : ∀ s ∈ Q, s.image f ∈ T) (hg : ∀ s ∈ T, s.image g ∈ Q)
    (hfOld : ∀ s ∈ P ∩ Q, s.image f ∈ U) (hgOld : ∀ s ∈ U, s.image g ∈ P)
    (hfi : ∀ s ∈ Q, Set.InjOn f (s : Set V))
    (hgi : ∀ s ∈ T, Set.InjOn g (s : Set W)) (hUT : U ⊆ T)
    (hret : ∀ s ∈ Q, ∀ v ∈ s, g (f v) = v)
    (r : ℕ) (H : RelativeExactIn U T r) : RelativeExactIn P Q r := by
  intro c hc hz
  have hbc := boundary_supported Q hQ c (graded_forget Q r hc)
  have hz' : rawBoundary c ∈ supported (P ∩ Q) := by
    rw [mem_supported] at hz hbc ⊢
    exact fun s hs => ⟨hz s hs,hbc s hs⟩
  have hfc := relabel_graded f Q T r hf hfi c hc
  have hfz : rawBoundary (relabel f c) ∈ supported U := by
    rw [relabel_boundary_on f (graded Q r) (fun s hs => hfi s hs.1) c hc]
    exact relabel_supported f (P ∩ Q) U hfOld _ hz'
  obtain ⟨b,hb,hres⟩ := H _ hfc hfz
  refine ⟨relabel g b,relabel_graded g T Q (r+1) hg hgi b hb,?_⟩
  have hh := relabel_graded g U P r hgOld (fun s hs => hgi s (hUT hs)) _ hres
  rw [map_sub,← relabel_boundary_on g (graded T (r+1)) (fun s hs => hgi s hs.1) b hb,
    relabel_retraction g f (graded Q r) (fun s hs => hret s hs.1) c hc] at hh
  exact hh
end

section
variable {V : Type} [DecidableEq V]
lemma untag_tagBy (F : Finset V) (v : V) : Sum.elim id id (tagBy F v) = v := by
  simp only [tagBy]; split <;> rfl
lemma tagBy_injective (F : Finset V) : Function.Injective (tagBy F) := by
  intro v w he
  have hh := congrArg (Sum.elim id id) he
  simpa only [untag_tagBy] using hh
lemma tagBy_left (F s : Finset V) : (s.image (tagBy F)).toLeft = s ∩ F := by
  ext v
  simp only [Finset.mem_toLeft,Finset.mem_image,Finset.mem_inter]
  constructor
  · rintro ⟨w,hw,he⟩
    by_cases hh : w ∈ F
    · simp only [tagBy,ite_eq_left hh,Sum.inl.injEq] at he
      exact he ▸ ⟨hw,hh⟩
    · simp [tagBy,hh] at he
  · rintro ⟨hv,hF⟩
    exact ⟨v,hv,by simp [tagBy,hF]⟩
lemma tagBy_right (F s : Finset V) : (s.image (tagBy F)).toRight = s \ F := by
  ext v
  simp only [Finset.mem_toRight,Finset.mem_image,Finset.mem_sdiff]
  constructor
  · rintro ⟨w,hw,he⟩
    by_cases hh : w ∈ F
    · simp [tagBy,hh] at he
    · simp only [tagBy,ite_eq_right hh,Sum.inr.injEq] at he
      exact he ▸ ⟨hw,hh⟩
  · rintro ⟨hv,hF⟩
    exact ⟨v,hv,by simp [tagBy,hF]⟩
lemma untag_image (s : Finset (V ⊕ V)) : s.image (Sum.elim id id) = s.toLeft ∪ s.toRight := by
  ext v
  simp only [Finset.mem_image,Finset.mem_union,Finset.mem_toLeft,Finset.mem_toRight]
  constructor
  · rintro ⟨(w|w),hw,he⟩
    · exact Or.inl (he ▸ hw)
    · exact Or.inr (he ▸ hw)
  · rintro (h|h)
    · exact ⟨Sum.inl v,h,rfl⟩
    · exact ⟨Sum.inr v,h,rfl⟩
end

open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W] [Nonempty V]
lemma exactIn_of_image (f : V → W) (hinj : Function.Injective f)
    (P : Set (Finset V)) (Q : Set (Finset W))
    (hf : ∀ s ∈ P, s.image f ∈ Q)
    (hg : ∀ s ∈ Q, ∃ t ∈ P, t.image f = s)
    (r : ℕ) (H : ExactIn Q r) : ExactIn P r := by
  classical
  let g := Function.invFun f
  have hgf (v : V) : g (f v) = v := Function.leftInverse_invFun hinj v
  have hfg (s) (hs : s ∈ Q) (w) (hw : w ∈ s) : f (g w) = w := by
    obtain ⟨t,_,rfl⟩ := hg s hs
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    rw [hgf]
  apply exactIn_retract f g P Q hf ?_ (fun _ _ => hinj.injOn) ?_ (fun _ _ v _ => hgf v) r H
  · intro s hs
    obtain ⟨t,ht,rfl⟩ := hg s hs
    simpa [Finset.image_image,Function.comp_def,hgf] using ht
  · intro s hs v hv w hw he
    rw [← hfg s hs v hv,← hfg s hs w hw,he]
end CoboundaryExpanders.InfiniteChains.Cone

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Flags
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Complete flags, spherical opposition, unitriangular groups, and the flag-coset model.
-/

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.SphericalOpposition
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

variable {N : ℕ}

namespace CompleteFlag
variable [FiniteDimensional K V]

lemma forbidden_rank (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (hlt : finrank K W < N) :
    finrank K (F.forbidden W) = N-1 := by
  have hd := F.opposed_disjoint_below W hW ⟨N-finrank K W-1, by omega⟩ (by simp)
  have he := Submodule.finrank_sup_add_finrank_inf_eq W
    (F.space ⟨N-finrank K W-1, by omega⟩)
  rw [hd.eq_bot, finrank_bot, F.rank, add_zero] at he
  dsimp only [Fin.val_mk] at he
  change finrank K (W ⊔ F.space ⟨N-finrank K W-1, by omega⟩ : Submodule K V) = N-1
  omega

lemma forbidden_ne_top (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (hlt : finrank K W < N) : F.forbidden W ≠ ⊤ := by
  intro e
  have he := F.forbidden_rank W hW hlt
  rw [e, finrank_top, F.dimension] at he
  omega

lemma extension_rank (F : CompleteFlag K V N) (W : Submodule K V)
    {v : V} (hv : v ∉ F.forbidden W) :
    finrank K (W ⊔ Submodule.span K {v} : Submodule K V) = finrank K W + 1 := by
  apply Submodule.finrank_sup_span_singleton
  exact fun h => hv ((show W ≤ F.forbidden W from le_sup_left) h)

lemma opposed_extension (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (hlt : finrank K W < N)
    {v : V} (hv : v ∉ F.forbidden W) :
    F.Opposed (W ⊔ Submodule.span K {v}) := by
  let A := F.space ⟨N-finrank K W-1, by omega⟩
  have hr : finrank K (W ⊔ Submodule.span K {v} : Submodule K V) = finrank K W + 1 :=
    F.extension_rank W hv
  have ht : W ⊔ Submodule.span K {v} ⊔ A = ⊤ := by
    have hb := Submodule.finrank_sup_span_singleton hv
    rw [F.forbidden_rank W hW hlt] at hb
    have he : F.forbidden W ⊔ Submodule.span K {v} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [F.dimension]
      omega
    simpa [forbidden, A, sup_assoc, sup_comm, sup_left_comm] using he
  have hai : (⟨N-finrank K (W ⊔ Submodule.span K {v} : Submodule K V), by omega⟩ : Fin (N+1)) =
      ⟨N-finrank K W-1, by omega⟩ := by
    apply Fin.ext
    dsimp
    omega
  rw [F.opposed_iff_disjoint, hai]
  apply disjoint_iff.mpr
  apply Submodule.finrank_eq_zero.mp
  have he := Submodule.finrank_sup_add_finrank_inf_eq (W ⊔ Submodule.span K {v}) A
  rw [ht, finrank_top, F.dimension, hr, F.rank] at he
  dsimp [A] at he ⊢
  omega

lemma good_extension (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Good W) (hlt : finrank K W + 1 < N)
    {v : V} (hv : v ∉ F.forbidden W) :
    F.Good (W ⊔ Submodule.span K {v}) := by
  refine ⟨?_, ?_, F.opposed_extension W hW.2.2 hW.2.1 hv⟩ <;>
    rw [F.extension_rank W hv] <;> omega

lemma opposed_line (F : CompleteFlag K V N) (hN : 0 < N) {v : V}
    (hv : v ∉ F.space ⟨N-1, by omega⟩) : F.Opposed (Submodule.span K {v}) := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; exact Submodule.zero_mem _)
  rw [F.opposed_iff_disjoint]
  simpa only [finrank_span_singleton hv0] using (Submodule.disjoint_span_singleton_of_notMem hv).symm

lemma good_line (F : CompleteFlag K V N) (hN : 1 < N) {v : V}
    (hv : v ∉ F.space ⟨N-1, by omega⟩) : F.Good (Submodule.span K {v}) := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; exact Submodule.zero_mem _)
  refine ⟨?_, ?_, F.opposed_line (by omega) hv⟩ <;>
    rw [finrank_span_singleton hv0] <;> omega

lemma good_lower_map (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (A : Submodule K W) (hA : (F.lower W hW).Good A) :
    F.Good (A.map W.subtype) := by
  refine ⟨?_, ?_, (F.opposed_lower_iff W hW A).mp hA.2.2⟩
  · simpa only [Submodule.finrank_map_subtype_eq] using hA.1
  · rw [Submodule.finrank_map_subtype_eq]
    exact lt_of_lt_of_le hA.2.1 (F.rank_le W)

lemma sup_mem_face (F : CompleteFlag K V N) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hne : s.Nonempty) : s.sup id ∈ s := by
  obtain ⟨W, hW, hmax⟩ := F.face_has_greatest s hs hne
  have he : s.sup id = W := le_antisymm (Finset.sup_le hmax) (Finset.le_sup (f := id) hW)
  exact he ▸ hW

omit [FiniteDimensional K V] in
lemma carrierApex_mono (F : CompleteFlag K V N) (v : V)
    {s t : Finset (Submodule K V)} (hst : s ⊆ t) :
    F.carrierApex v s ≤ F.carrierApex v t := by
  apply sup_le_sup_right
  exact Finset.sup_mono hst

lemma carrierApex_good (F : CompleteFlag K V N) (hN : 1 < N) (v : V)
    (hv : v ∉ F.space ⟨N-1, by omega⟩) (s : Finset (Submodule K V))
    (hs : s ∈ (F.safeComplex v).faces) : F.Good (F.carrierApex v s) := by
  rcases s.eq_empty_or_nonempty with he | he
  · subst s
    simpa [carrierApex] using F.good_line hN hv
  · have hm := F.sup_mem_face s hs.1 he
    exact F.good_extension (s.sup id) (hs.1.1 _ hm) (hs.2 _ hm).1 (hs.2 _ hm).2

omit [FiniteDimensional K V] in
lemma self_mem_carrier (F : CompleteFlag K V N) (v : V) (s : Finset (Submodule K V))
    (hs : s ∈ (F.safeComplex v).faces) : s ∈ F.carrier v s :=
  ⟨hs.1, fun _ hW => (Finset.le_sup (f := id) hW).trans le_sup_left⟩

omit [FiniteDimensional K V] in
lemma carrier_mono (F : CompleteFlag K V N) (v : V) {s t : Finset (Submodule K V)}
    (hst : s ⊆ t) : F.carrier v s ⊆ F.carrier v t :=
  fun _ ha => ⟨ha.1, fun W hW => (ha.2 W hW).trans (F.carrierApex_mono v hst)⟩

lemma carrier_cone (F : CompleteFlag K V N) (hN : 1 < N) (v : V)
    (hv : v ∉ F.space ⟨N-1, by omega⟩) (s : Finset (Submodule K V))
    (hs : s ∈ (F.safeComplex v).faces) (t : Finset (Submodule K V))
    (ht : t ∈ F.carrier v s) : insert (F.carrierApex v s) t ∈ F.carrier v s := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro W hW
    rcases Finset.mem_insert.mp hW with rfl | hW
    · exact F.carrierApex_good hN v hv s hs
    · exact ht.1.1 W hW
  · intro W hW U hU hne
    rcases Finset.mem_insert.mp hW with rfl | hW
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact False.elim (hne rfl)
      · exact Or.inr (ht.2 U hU)
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact Or.inl (ht.2 W hW)
      · exact ht.1.2 hW hU hne
  · intro W hW
    rcases Finset.mem_insert.mp hW with rfl | hW
    · exact le_rfl
    · exact ht.2 W hW

lemma good_lower_comap (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (A : Submodule K V) (hA : F.Good A) (hAW : A < W) :
    (F.lower W hW).Good (A.comap W.subtype) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rank_comap_lower W A hAW.le]
    exact hA.1
  · rw [rank_comap_lower W A hAW.le]
    exact Submodule.finrank_strictMono hAW
  · rw [F.opposed_lower_iff W hW, map_comap_lower W A hAW.le]
    exact hA.2.2

lemma lower_face_map (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (s : Finset (Submodule K W))
    (hs : s ∈ (F.lower W hW).complex.faces) :
    s.image (Submodule.map W.subtype) ∈ F.complex.faces ∧
      ∀ A ∈ s.image (Submodule.map W.subtype), A < W := by
  have hinj := Submodule.map_injective_of_injective W.injective_subtype
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact F.good_lower_map W hW B (hs.1 B hB)
  · intro A hA B hB hab
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
    exact (hs.2 hA' hB' (fun e => hab (congrArg _ e))).imp Submodule.map_mono Submodule.map_mono
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    refine lt_of_le_of_ne ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      exact y.property
    · intro he
      have hr := congrArg (fun U : Submodule K V => finrank K U) he
      rw [Submodule.finrank_map_subtype_eq] at hr
      exact (ne_of_lt (hs.1 B hB).2.1) hr

lemma lower_face_comap (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Opposed W) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hsW : ∀ A ∈ s, A < W) :
    s.image (Submodule.comap W.subtype) ∈ (F.lower W hW).complex.faces := by
  refine ⟨?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    exact F.good_lower_comap W hW B (hs.1 B hB) (hsW B hB)
  · intro A hA B hB hab
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
    exact (hs.2 hA' hB' (fun e => hab (congrArg _ e))).imp Submodule.comap_mono Submodule.comap_mono

omit [FiniteDimensional K V] in
lemma comap_injOn_lower (W : Submodule K V) (s : Finset (Submodule K V))
    (hs : ∀ A ∈ s, A ≤ W) : Set.InjOn (Submodule.comap W.subtype) (s : Set (Submodule K V)) := by
  intro A hA B hB he
  have hm := congrArg (Submodule.map W.subtype) he
  rwa [map_comap_lower W A (hs A hA), map_comap_lower W B (hs B hB)] at hm

lemma hyperplane_link_lower (F : CompleteFlag K V N) (W : Submodule K V)
    (hr : finrank K W = N-1) (s : Finset (Submodule K V))
    (hs : s ∈ F.complex.faces) (hW : W ∈ s) :
    ∀ A ∈ s.erase W, A < W := by
  intro A hA
  obtain ⟨hne, hAs⟩ := Finset.mem_erase.mp hA
  rcases hs.2 hAs hW hne with h | h
  · exact lt_of_le_of_ne h hne
  · have he : W = A := Submodule.eq_of_le_of_finrank_le h (by
      have ha := (hs.1 A hAs).2.1
      omega)
    exact False.elim (hne he.symm)

omit [FiniteDimensional K V] in
lemma insert_greatest_face (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.Good W) (s : Finset (Submodule K V)) (hs : s ∈ F.complex.faces)
    (hsW : ∀ A ∈ s, A ≤ W) : insert W s ∈ F.complex.faces := by
  refine ⟨?_, ?_⟩
  · intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hAs
    · exact hW
    · exact hs.1 A hAs
  · intro A hA B hB hab
    rcases Finset.mem_insert.mp hA with heA | hAs
    · subst A
      rcases Finset.mem_insert.mp hB with heB | hBs
      · exact False.elim (hab heB.symm)
      · exact Or.inr (hsW B hBs)
    · rcases Finset.mem_insert.mp hB with heB | hBs
      · subst B
        exact Or.inl (hsW A hAs)
      · exact hs.2 hAs hBs hab

end CompleteFlag

theorem exists_vector_avoiding [Fintype K] [Fintype V] [FiniteDimensional K V]
    {ι : Type} [Fintype ι] (P : ι → Submodule K V)
    (hP : ∀ i, P i ≠ ⊤) (hι : Fintype.card ι < Fintype.card K)
    (hdim : 0 < finrank K V) : ∃ v : V, ∀ i, v ∉ P i := by
  classical
  let bad : Finset V := Finset.univ.biUnion (fun i => (P i : Set V).toFinset)
  have hbound (i : ι) : (P i : Set V).toFinset.card ≤
      Fintype.card K ^ (finrank K V - 1) := by
    rw [Set.toFinset_card]
    change Fintype.card (P i) ≤ _
    rw [Module.card_eq_pow_finrank (K := K)]
    exact Nat.pow_le_pow_right Fintype.card_pos (by have := Submodule.finrank_lt (hP i); omega)
  have hcard : bad.card < Finset.univ.card (α := V) := by
    calc
      bad.card ≤ ∑ i : ι, (P i : Set V).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _i : ι, Fintype.card K ^ (finrank K V - 1) :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ = Fintype.card ι * Fintype.card K ^ (finrank K V - 1) := by simp
      _ < Fintype.card K * Fintype.card K ^ (finrank K V - 1) :=
        Nat.mul_lt_mul_of_pos_right hι (Nat.pow_pos Fintype.card_pos)
      _ = Fintype.card K ^ finrank K V := by
        rw [← pow_succ']
        congr 1
        omega
      _ = Finset.univ.card (α := V) := by rw [Finset.card_univ, Module.card_eq_pow_finrank (K := K) (V := V)]
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨v, fun i hi => hv ?_⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa using hi⟩

theorem exists_vector_avoiding_finset [Fintype K] [Fintype V] [FiniteDimensional K V]
    (S : Finset (Submodule K V)) (hS : ∀ P ∈ S, P ≠ ⊤)
    (hcard : S.card < Fintype.card K) (hdim : 0 < finrank K V) :
    ∃ v : V, ∀ P ∈ S, v ∉ P := by
  classical
  obtain ⟨v, hv⟩ := exists_vector_avoiding (fun P : S => P.val)
    (fun P => hS P.val P.property) (by simpa using hcard) hdim
  exact ⟨v, fun P hP => hv ⟨P, hP⟩⟩

theorem exists_common_good_line [Fintype K] [Fintype V] [FiniteDimensional K V]
    {ι : Type} [Fintype ι] [Nonempty ι] (F : ι → CompleteFlag K V N)
    (hN : 1 < N) (hι : Fintype.card ι < Fintype.card K) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, (F i).Good (Submodule.span K {v}) := by
  classical
  let base : ι := Classical.choice inferInstance
  obtain ⟨v, hv⟩ := exists_vector_avoiding
    (fun i => (F i).space ⟨N-1, by omega⟩) (fun i => by
      intro he
      have hr := (F i).rank ⟨N-1, by omega⟩
      rw [he, finrank_top, (F i).dimension] at hr
      dsimp at hr
      omega) hι (by rw [(F base).dimension]; omega)
  refine ⟨v, ?_, fun i => (F i).good_line hN (hv i)⟩
  intro he
  exact hv base (by rw [he]; exact Submodule.zero_mem _)

end CoboundaryExpanders.SphericalOpposition

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

lemma safe_filling (F : CompleteFlag K V N) (hN : 1 < N) (v : V)
    (hv : v ∉ F.space ⟨N-1, by omega⟩) (r : ℕ) (c : Raw (Submodule K V))
    (hc : c ∈ supported (graded (F.safeComplex v).faces r)) (hz : rawBoundary c = 0) :
    ∃ b : Raw (Submodule K V), b ∈ supported (graded F.complex.faces (r+1)) ∧
      rawBoundary b = c ∧ size b ≤ carrierBound r * size c := by
  classical
  let T := carrierMap (F.carrierApex v)
  have hsingle (s : Finset (Submodule K V)) (hs : s ∈ (F.safeComplex v).faces) :
      T (Finsupp.single s 1) ∈ supported (graded F.complex.faces (s.card+1)) := by
    have hb := carrierFill_supported (F.safeComplex v) (F.carrier v) (F.carrierApex v)
      (F.self_mem_carrier v) (fun _ _ _ h => F.carrier_mono v h)
      (F.carrier_cone hN v hv) s hs
    have hcarr : graded (F.carrier v s) (s.card+1) ⊆ graded F.complex.faces (s.card+1) :=
      fun _ ht => ⟨ht.1.1, ht.2⟩
    simpa [T] using supported_mono hcarr hb
  refine ⟨T c, ?_, ?_, ?_⟩
  · apply map_supported T (graded (F.safeComplex v).faces r) _ _ c hc
    intro s hs a
    have he : Finsupp.single s a = a • Finsupp.single s (1 : k) := by simp
    rw [he, map_smul]
    apply Submodule.smul_mem
    simpa [hs.2] using hsingle s hs.1
  · have hh := LinearMap.congr_fun (carrierMap_contraction (F.carrierApex v)) c
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hz, map_zero, add_zero] using hh
  · apply size_map_le T (graded (F.safeComplex v).faces r) (carrierBound r) _ c hc
    intro s hs
    simpa [T, hs.2] using carrierFill_size (F.carrierApex v) s

lemma no_top_filling [Fintype K] [Fintype V] (F : CompleteFlag K V N)
    (hN : 1 < N) (r : ℕ) (c : Raw (Submodule K V))
    (hc : c ∈ supported (graded (allowed F.complex F.TopBad ∅).faces r))
    (hz : rawBoundary c = 0) (hq : 1+r*size c < Fintype.card K) :
    ∃ b : Raw (Submodule K V), b ∈ supported (graded F.complex.faces (r+1)) ∧
      rawBoundary b = c ∧ size b ≤ carrierBound r * size c := by
  classical
  have hvert (W : Submodule K V) (hW : W ∈ vertices c) :
      F.Good W ∧ finrank K W + 1 < N := by
    obtain ⟨s, hs, hWs⟩ := Finset.mem_biUnion.mp hW
    have hsf := (mem_supported _ _).mp hc s (Finsupp.mem_support_iff.mp hs)
    have hg := hsf.1.1.1 W hWs
    have hne : finrank K W ≠ N-1 := fun hr =>
      Finset.notMem_empty W (hsf.1.2 W hWs ⟨hg, hr⟩)
    exact ⟨hg, by have := hg.2.1; omega⟩
  let Z : Submodule K V := F.space ⟨N-1, by omega⟩
  let S := insert Z ((vertices c).image F.forbidden)
  have hS : ∀ P ∈ S, P ≠ ⊤ := by
    intro P hP
    rcases Finset.mem_insert.mp hP with he | hP
    · subst P
      intro he
      have hr := F.rank ⟨N-1, by omega⟩
      change finrank K Z = N-1 at hr
      rw [he, finrank_top, F.dimension] at hr
      omega
    · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hP
      exact F.forbidden_ne_top W (hvert W hW).1.2.2 (hvert W hW).1.2.1
  have hcard : S.card < Fintype.card K := by
    have hi := Finset.card_insert_le Z ((vertices c).image F.forbidden)
    have him := Finset.card_image_le (s := vertices c) (f := F.forbidden)
    have hv := vertices_card_le (allowed F.complex F.TopBad ∅).faces r c hc
    dsimp [S]
    omega
  obtain ⟨v, hv⟩ := exists_vector_avoiding_finset S hS hcard (by rw [F.dimension]; omega)
  apply F.safe_filling hN v (hv Z (Finset.mem_insert_self _ _)) r c _ hz
  rw [mem_supported] at hc ⊢
  intro s hs
  refine ⟨⟨(hc s hs).1.1, ?_⟩, (hc s hs).2⟩
  intro W hW
  have hWv := mem_vertices c s hs W hW
  refine ⟨(hvert W hWv).2, ?_⟩
  exact hv (F.forbidden W) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨W, hWv, rfl⟩))

lemma hyperplane_link_filling (F : CompleteFlag K V N) (W : Submodule K V)
    (hW : F.TopBad W) (n R r : ℕ)
    (H : BoundedCone (F.lower W hW.1.2.2).complex n R) (hr : r ≤ n)
    (c : Raw (Submodule K V)) (hc : c ∈ supported (graded F.complex.faces (r+1)))
    (hz : rawBoundary c = 0) :
    ∃ b : Raw (Submodule K V),
      b ∈ supported (graded {s | s ∈ F.complex.faces ∧
        (∀ A ∈ s, ¬F.TopBad A) ∧ insert W s ∈ F.complex.faces} (r+1)) ∧
      rawBoundary b = link W c ∧ size b ≤ R * size c := by
  classical
  let L := F.lower W hW.1.2.2
  let P : Set (Finset (Submodule K V)) :=
    {s | s ∈ F.complex.faces ∧ ∀ A ∈ s, A < W}
  let f : Submodule K W → Submodule K V := Submodule.map W.subtype
  let g : Submodule K V → Submodule K W := Submodule.comap W.subtype
  have hinj : Function.Injective f := Submodule.map_injective_of_injective W.injective_subtype
  have hl : link W c ∈ supported (graded P r) := by
    apply link_graded W F.complex.faces P r _ c hc
    intro s hs hWs
    exact ⟨F.complex.downward hs (Finset.erase_subset _ _), F.hyperplane_link_lower W hW.2 s hs hWs⟩
  let a := relabel g (link W c)
  have ha : a ∈ supported (graded L.complex.faces r) := by
    apply relabel_graded g P L.complex.faces r _ _ _ hl
    · intro s hs
      exact F.lower_face_comap W hW.1.2.2 s hs.1 hs.2
    · intro s hs
      exact comap_injOn_lower W s (fun A hA => (hs.2 A hA).le)
  have hret : relabel f a = link W c := by
    apply relabel_retraction f g (graded P r) _ _ hl
    intro s hs A hA
    exact map_comap_lower W A (hs.1.2 A hA).le
  have haz : rawBoundary a = 0 := by
    apply relabel_injective f hinj
    rw [map_zero]
    have nat := LinearMap.congr_fun (relabel_boundary f hinj) a
    change rawBoundary (relabel f a) = relabel f (rawBoundary a) at nat
    rw [← nat, hret, link_cycle W c hz]
  let b := relabel f (H.hom a)
  refine ⟨b, ?_, ?_, ?_⟩
  · apply relabel_graded f L.complex.faces _ (r+1) _ (fun _ _ => hinj.injOn)
      (H.hom a) (H.map_graded r hr a ha)
    intro s hs
    have hm := F.lower_face_map W hW.1.2.2 s hs
    refine ⟨hm.1, ?_, F.insert_greatest_face W hW.1 _ hm.1 (fun A hA => (hm.2 A hA).le)⟩
    intro A hA hbad
    have hrank := Submodule.finrank_strictMono (hm.2 A hA)
    have hArank := hbad.2
    change finrank K A < finrank K W at hrank
    rw [hW.2, hArank] at hrank
    exact Nat.lt_irrefl _ hrank
  · have nat := LinearMap.congr_fun (relabel_boundary f hinj) (H.hom a)
    change rawBoundary b = relabel f (rawBoundary (H.hom a)) at nat
    rw [nat, H.fills r hr a ha haz, hret]
  · calc
      size b ≤ size (H.hom a) := relabel_size f _
      _ ≤ R * size a := H.size_apply r hr a ha
      _ ≤ R * size (link W c) := Nat.mul_le_mul_left R (relabel_size g _)
      _ ≤ R * size c := Nat.mul_le_mul_left R (link_size W c)

lemma small_filling [Fintype K] [Fintype V] (F : CompleteFlag K V N)
    (hN : 1 < N) (n R r S : ℕ)
    (H : ∀ W, ∀ hW : F.TopBad W, BoundedCone (F.lower W hW.1.2.2).complex n R)
    (hr : r ≤ n) (c : Raw (Submodule K V))
    (hc : c ∈ supported (graded F.complex.faces (r+1))) (hz : rawBoundary c = 0)
    (hsize : size c ≤ S) (hq : fieldBound R (r+1) S < Fintype.card K) :
    ∃ b : Raw (Submodule K V), b ∈ supported (graded F.complex.faces (r+2)) ∧
      rawBoundary b = c ∧ size b ≤ fillingBound R (r+1) S := by
  classical
  let A := (vertices c).filter F.TopBad
  have hA : ∀ W ∈ A, F.TopBad W := fun _ h => (Finset.mem_filter.mp h).2
  have hcA : c ∈ supported (graded (allowed F.complex F.TopBad A).faces (r+1)) := by
    rw [mem_supported] at hc ⊢
    intro s hs
    refine ⟨⟨(hc s hs).1, ?_⟩, (hc s hs).2⟩
    intro W hW hbad
    exact Finset.mem_filter.mpr ⟨mem_vertices c s hs W hW, hbad⟩
  obtain ⟨e, c', he, hc', hz', hec, htotal⟩ :=
    removeBad F.complex F.TopBad (r+1) R
      (fun W hW c hc hz => F.hyperplane_link_filling W hW n R r (H W hW) hr c hc hz)
      A hA c hcA hz
  have hAc : A.card ≤ (r+1)*S :=
    (Finset.card_filter_le _ _).trans ((vertices_card_le F.complex.faces (r+1) c hc).trans
      (Nat.mul_le_mul_left (r+1) hsize))
  have hE : size e + size c' ≤ eliminationBound R (r+1) S := by
    apply htotal.trans
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 0 < 2*R+2) hAc) hsize
  have hcE : size c' ≤ eliminationBound R (r+1) S := (Nat.le_add_left _ _).trans hE
  have hq' : 1+(r+1)*size c' < Fintype.card K :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left (r+1) hcE) 1).trans_lt hq
  obtain ⟨b, hb, hdb, hsz⟩ := F.no_top_filling hN (r+1) c' hc' hz' hq'
  refine ⟨e+b, Submodule.add_mem _ he hb, ?_, ?_⟩
  · rw [map_add, hdb, hec]
  · have hadd := size_add_le e b
    have hbE := hsz.trans (Nat.mul_le_mul_left (carrierBound (r+1)) hcE)
    dsimp [fillingBound]
    nlinarith

theorem exists_uniform_cones (n : ℕ) :
    ∃ Q R : ℕ, ∀ (K : Type) [Field K] [Fintype K]
      (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V],
      ∀ (N : ℕ) (F : CompleteFlag K V N), n+2 ≤ N → Q < Fintype.card K →
        Nonempty (BoundedCone F.complex n R) := by
  classical
  induction n with
  | zero =>
    refine ⟨1, 1, ?_⟩
    intro K _ _ V _ _ _ _ N F hN hq
    obtain ⟨v, hv, hg⟩ := exists_common_good_line (ι := Unit) (fun _ => F) (by omega)
      (by simpa using hq)
    refine ⟨BoundedCone.initial F.complex (Submodule.span K {v}) ?_⟩
    refine ⟨?_, ?_⟩
    · intro W hW
      have he : W = Submodule.span K {v} := Finset.mem_singleton.mp hW
      exact he ▸ hg ()
    · simp
  | succ n ih =>
    obtain ⟨Q, R, hcones⟩ := ih
    let S := 1+R*(n+1)
    refine ⟨max Q (fieldBound R (n+1) S), max R (fillingBound R (n+1) S), ?_⟩
    intro K _ _ V _ _ _ _ N F hN hq
    have hqQ : Q < Fintype.card K := (Nat.le_max_left _ _).trans_lt hq
    have hqF : fieldBound R (n+1) S < Fintype.card K := (Nat.le_max_right _ _).trans_lt hq
    let H : BoundedCone F.complex n R := (hcones K V N F (by omega) hqQ).some
    have hlower (W : Submodule K V) (hW : F.TopBad W) :
        Nonempty (BoundedCone (F.lower W hW.1.2.2).complex n R) := by
      apply hcones K W (finrank K W) (F.lower W hW.1.2.2)
      · rw [hW.2]
        omega
      · exact hqQ
    exact ⟨H.extend (fillingBound R (n+1) S)
      (fun c hc hz hs => F.small_filling (by omega) n R n S
        (fun W hW => (hlower W hW).some) le_rfl c hc hz hs hqF)⟩

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Lattices
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Affine and rational lattices, polynomial congruence actions, and lattice-chain geometry.
-/

noncomputable section


namespace CoboundaryExpanders.AffineLattices
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
open scoped BigOperators

variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

lemma singleton_face (A : Vertex T C) : IsFace T C {A} := by
  constructor
  · intro B hB D hD
    simp only [Finset.mem_singleton] at hB hD
    subst B; subst D
    exact Or.inl le_rfl
  · intro B hB D hD
    simp only [Finset.mem_singleton] at hB hD
    subst B; subst D
    exact vertex_shift_le T C A

lemma ball_mono (hC : T C ≤ C) {a b : ℕ} (hab : a ≤ b) :
    (ball T C a).faces ⊆ (ball T C b).faces := by
  intro s hs
  exact ⟨hs.1,fun A hA => (level_antitone T C hC hab).trans (hs.2 A hA)⟩

lemma le_raise (hC : T C ≤ C) (m : ℕ) (A : Vertex T C) :
    A ≤ raise T C hC m A := le_sup_left

lemma raise_good (hC : T C ≤ C) (m : ℕ) (A : Vertex T C) :
    level T C m ≤ (raise T C hC m A : P) := le_sup_right

lemma insert_raise_face (hC : T C ≤ C) (m : ℕ) (A : Vertex T C)
    (s : Finset (Vertex T C)) (hs : insert A s ∈ (ball T C (m+1)).faces)
    (hmax : ∀ B ∈ s, A < B → level T C m ≤ (B : P)) :
    insert (raise T C hC m A) (insert A s) ∈ (ball T C (m+1)).faces := by
  let v := raise T C hC m A
  have hAv : A ≤ v := le_raise T C hC m A
  have hcmp : ∀ B ∈ insert A s, B ≤ v ∨ v ≤ B := by
    intro B hB
    rcases (hs.1.1 A (Finset.mem_insert_self _ _) B hB) with hAB | hBA
    · by_cases he : A = B
      · subst B; exact Or.inl hAv
      · have hBs : B ∈ s := (Finset.mem_insert.mp hB).resolve_left (Ne.symm he)
        exact Or.inr (sup_le hAB (hmax B hBs (lt_of_le_of_ne hAB he)))
    · exact Or.inl (hBA.trans hAv)
  have hTv : ∀ B ∈ insert A s, T (v : P) ≤ (B : P) := by
    intro B hB
    change T ((A : P) ⊔ level T C m) ≤ _
    rw [T.map_sup]
    exact sup_le (hs.1.2 A (Finset.mem_insert_self _ _) B hB) (hs.2 B hB)
  have hTo : ∀ B ∈ insert A s, T (B : P) ≤ (v : P) := by
    intro B hB
    exact (hs.1.2 B hB A (Finset.mem_insert_self _ _)).trans hAv
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB D hD
    rcases Finset.mem_insert.mp hB with rfl | hB
    · rcases Finset.mem_insert.mp hD with rfl | hD
      · exact Or.inl le_rfl
      · exact (hcmp D hD).symm
    · rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hcmp B hB
      · exact hs.1.1 B hB D hD
  · intro B hB D hD
    rcases Finset.mem_insert.mp hB with rfl | hB
    · rcases Finset.mem_insert.mp hD with rfl | hD
      · exact vertex_shift_le T C v
      · exact hTv D hD
    · rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hTo B hB
      · exact hs.1.2 B hB D hD
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact (level_antitone T C hC (Nat.le_succ m)).trans (raise_good T C hC m A)
    · exact hs.2 B hB

lemma eliminate_maximal (hC : T C ≤ C) (m r : ℕ)
    (A : Finset (Vertex T C)) (v : Vertex T C)
    (hv : Maximal (· ∈ A) v)
    (c : Raw (Vertex T C))
    (hc : c ∈ supported (graded (allowed (ball T C (m+1))
      (fun w => ¬ level T C m ≤ (w : P)) A).faces (r+1)))
    (hz : rawBoundary c = 0) :
    ∃ e c' : Raw (Vertex T C),
      e ∈ supported (graded (ball T C (m+1)).faces (r+2)) ∧
      c' ∈ supported (graded (allowed (ball T C (m+1))
        (fun w => ¬ level T C m ≤ (w : P)) (A.erase v)).faces (r+1)) ∧
      rawBoundary c' = 0 ∧ rawBoundary e + c' = c := by
  classical
  let X := ball T C (m+1)
  let bad := fun w : Vertex T C => ¬ level T C m ≤ (w : P)
  let v' := raise T C hC m v
  let L : Set (Finset (Vertex T C)) := {s | insert v s ∈ X.faces ∧
    v ∉ s ∧ ∀ w ∈ s, bad w → w ∈ A.erase v}
  have hlink : link v c ∈ supported (graded L r) := by
    apply link_graded v (allowed X bad A).faces L r ?_ c hc
    intro s hs hvs
    refine ⟨?_,Finset.notMem_erase _ _,?_⟩
    · simpa only [Finset.insert_erase hvs] using hs.1
    · intro w hw hbw
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1,
        hs.2 w (Finset.mem_of_mem_erase hw) hbw⟩
  let Q : Set (Finset (Vertex T C)) := {s | s ∈ (allowed X bad (A.erase v)).faces ∧
    insert v s ∈ X.faces}
  have hcone : ∀ s ∈ L, v' ∉ s → insert v' s ∈ Q := by
    intro s hs _
    have hm : ∀ w ∈ s, v < w → level T C m ≤ (w : P) := by
      intro w hw hvw
      by_contra hbw
      have hwA := Finset.mem_of_mem_erase (hs.2.2 w hw hbw)
      exact (not_le_of_gt hvw) (hv.2 hwA hvw.le)
    have hi := insert_raise_face T C hC m v s hs.1 hm
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact X.downward hi (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
    · intro w hw hbw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact False.elim (hbw (raise_good T C hC m v))
      · exact hs.2.2 w hw hbw
    · simpa only [Finset.insert_comm] using hi
  let b := rawCone v' (link v c)
  have hb : b ∈ supported (graded Q (r+1)) := rawCone_graded v' L Q r hcone _ hlink
  have hdb : rawBoundary b = link v c := by
    have he := LinearMap.congr_fun (raw_contraction v') (link v c)
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply,
      link_cycle v c hz,map_zero,add_zero] using he
  refine ⟨rawCone v b,without v c + b,?_,?_,elimination_cycle v c b hz hdb,
    elimination_identity v c b hdb⟩
  · exact rawCone_graded v Q X.faces (r+1) (fun s hs _ => hs.2) b hb
  · apply Submodule.add_mem
    · have hw := without_supported v (graded (allowed X bad A).faces (r+1)) c hc
      apply supported_mono ?_ hw
      intro s hs
      refine ⟨⟨hs.1.1.1,?_⟩,hs.1.2⟩
      intro w hw hbw
      exact Finset.mem_erase.mpr ⟨fun he => hs.2 (he ▸ hw),hs.1.1.2 w hw hbw⟩
    · apply supported_mono (P := graded Q (r+1)) ?_ hb
      intro s hs
      exact ⟨hs.1.1,hs.2⟩

lemma push_cycle_down (hC : T C ≤ C) (m r : ℕ)
    (A : Finset (Vertex T C)) (hA : ∀ v ∈ A, ¬ level T C m ≤ (v : P))
    (c : Raw (Vertex T C))
    (hc : c ∈ supported (graded (allowed (ball T C (m+1))
      (fun w => ¬ level T C m ≤ (w : P)) A).faces (r+1)))
    (hz : rawBoundary c = 0) :
    ∃ e c' : Raw (Vertex T C),
      e ∈ supported (graded (ball T C (m+1)).faces (r+2)) ∧
      c' ∈ supported (graded (ball T C m).faces (r+1)) ∧
      rawBoundary c' = 0 ∧ rawBoundary e + c' = c := by
  classical
  induction A using Finset.strongInductionOn generalizing c with
  | _ A ih =>
    by_cases hne : A.Nonempty
    · obtain ⟨v,hv⟩ := A.exists_maximal hne
      obtain ⟨e,c',he,hc',hz',hec⟩ := eliminate_maximal T C hC m r A v hv c hc hz
      obtain ⟨f,c'',hf,hc'',hz'',hfc⟩ :=
        ih (A.erase v) (Finset.erase_ssubset hv.1)
          (fun w hw => hA w (Finset.mem_of_mem_erase hw)) c' hc' hz'
      refine ⟨e+f,c'',Submodule.add_mem _ he hf,hc'',hz'',?_⟩
      rw [map_add,add_assoc,hfc,hec]
    · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst A
      refine ⟨0,c,Submodule.zero_mem _,?_,hz,by simp⟩
      apply supported_mono ?_ hc
      intro s hs
      refine ⟨⟨hs.1.1.1,?_⟩,hs.2⟩
      intro v hv
      by_contra hbad
      exact Finset.notMem_empty v (hs.1.2 v hv hbad)

lemma push_ball_cycle (hC : T C ≤ C) (m r : ℕ)
    (c : Raw (Vertex T C))
    (hc : c ∈ supported (graded (ball T C (m+1)).faces (r+1)))
    (hz : rawBoundary c = 0) :
    ∃ e c' : Raw (Vertex T C),
      e ∈ supported (graded (ball T C (m+1)).faces (r+2)) ∧
      c' ∈ supported (graded (ball T C m).faces (r+1)) ∧
      rawBoundary c' = 0 ∧ rawBoundary e + c' = c := by
  classical
  let A : Finset (Vertex T C) := (vertices c).filter (fun (v : Vertex T C) => ¬ level T C m ≤ (v : P))
  apply push_cycle_down T C hC m r A (fun v hv => (Finset.mem_filter.mp hv).2) c ?_ hz
  rw [mem_supported] at hc ⊢
  intro s hs
  refine ⟨⟨(hc s hs).1,?_⟩,(hc s hs).2⟩
  intro v hv hbad
  exact Finset.mem_filter.mpr ⟨mem_vertices c s hs v hv,hbad⟩

lemma ball_zero_face (hC : T C ≤ C) (hstrict : ¬ C ≤ T C)
    (s : Finset (Vertex T C)) (hs : s ∈ (ball T C 0).faces) :
    insert (base T C hC hstrict) s ∈ (ball T C 0).faces := by
  have he : ∀ v ∈ s, v = base T C hC hstrict := by
    intro v hv
    apply Subtype.ext
    exact le_antisymm (vertex_le T C v) (hs.2 v hv)
  have hsub : insert (base T C hC hstrict) s ⊆ {base T C hC hstrict} := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp
    · simp [he v hv]
  refine (ball T C 0).downward ?_ hsub
  exact ⟨singleton_face T C _,by simp [base]⟩

theorem ball_exact (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (m r : ℕ) :
    ExactIn (ball T C m).faces (r+1) := by
  induction m with
  | zero =>
    intro c hc hz
    refine ⟨rawCone (base T C hC hstrict) c,
      rawCone_graded _ _ _ _ (fun s hs _ => ball_zero_face T C hC hstrict s hs) c hc,?_⟩
    have he := LinearMap.congr_fun (raw_contraction (base T C hC hstrict)) c
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply,hz,map_zero,add_zero] using he
  | succ m ih =>
    intro c hc hz
    obtain ⟨e,c',he,hc',hz',hec⟩ := push_ball_cycle T C hC m r c hc hz
    obtain ⟨b,hb,hbc⟩ := ih c' hc' hz'
    refine ⟨e+b,Submodule.add_mem _ he ?_,?_⟩
    · apply supported_mono (P := graded (ball T C m).faces (r+2)) ?_ hb
      intro s hs
      exact ⟨ball_mono T C hC (Nat.le_succ m) hs.1,hs.2⟩
    · rw [map_add,hbc,hec]

lemma finite_ball (hC : T C ≤ C) (r : ℕ) (c : Raw (Vertex T C))
    (hc : c ∈ supported (graded (complex T C).faces r)) :
    ∃ m, c ∈ supported (graded (ball T C m).faces r) := by
  classical
  have hex : ∀ v ∈ vertices c, ∃ m, level T C m ≤ (v : P) := fun v _ => vertex_bounded T C v
  choose f hf using hex
  let m := (vertices c).sup (fun v => if h : v ∈ vertices c then f v h else 0)
  refine ⟨m,?_⟩
  rw [mem_supported] at hc ⊢
  intro s hs
  refine ⟨⟨(hc s hs).1,?_⟩,(hc s hs).2⟩
  intro v hv
  have hvc := mem_vertices c s hs v hv
  have hfm : f v hvc ≤ m := by
    simpa only [dite_eq_left hvc] using Finset.le_sup (f := fun v => if h : v ∈ vertices c then f v h else 0) hvc
  exact (level_antitone T C hC hfm).trans (hf v hvc)

theorem complex_exact (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (r : ℕ) :
    ExactIn (complex T C).faces (r+1) := by
  intro c hc hz
  obtain ⟨m,hm⟩ := finite_ball T C hC (r+1) c hc
  obtain ⟨b,hb,hbc⟩ := ball_exact T C hC hstrict m r c hm hz
  refine ⟨b,?_,hbc⟩
  apply supported_mono (P := graded (ball T C m).faces (r+2)) ?_ hb
  intro s hs
  exact ⟨hs.1.1,hs.2⟩

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.RationalLattices
open InfiniteChains InfiniteChains.Attachment
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)

theorem building_exact (hN : 0 < N) (r : ℕ) :
    ExactIn (building K N).faces (r+1) :=
  AffineLattices.complex_exact (shift K N) (standard K N)
    (shift_standard_le K N) (standard_not_le_shift K N hN) r

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
variable (K : Type) [Field K] (N : ℕ)

lemma cut_antitone : Antitone (cutLattice K N) := by
  intro a b hab v hv i
  by_cases hi : i.val < a.val
  · obtain ⟨f,hf⟩ := hv i
    exact ⟨f,by simpa only [cutExponent,ite_eq_left hi,ite_eq_left (show i.val < b.val by omega)] using hf⟩
  · obtain ⟨f,hf⟩ := (cut_le_standard K N b hv) i
    exact ⟨f,by simpa only [cutExponent,ite_eq_right hi,pow_zero,mul_one] using hf⟩

lemma cut_le_cut_iff (a b : Fin N) : cutLattice K N a ≤ cutLattice K N b ↔ b ≤ a := by
  constructor
  · intro hle
    by_contra hba
    have hab : a.val < b.val := lt_of_not_ge hba
    obtain ⟨f,hf⟩ := hle (single_mem_cut K N a) a
    apply uniformizer_mul_ne_one K f
    simpa only [cutExponent,ite_eq_left hab,pow_one,Pi.single_eq_same,mul_comm] using hf
  · intro hba; exact cut_antitone K N hba

lemma cut_injective : Function.Injective (cutLattice K N) := by
  intro a b he
  exact le_antisymm ((cut_le_cut_iff K N b a).mp he.ge) ((cut_le_cut_iff K N a b).mp he.le)

lemma cutVertex_injective : Function.Injective (cutVertex K N) := by
  intro a b he
  exact cut_injective K N (congrArg Subtype.val he)

lemma baseChamber_face : baseChamber K N ∈ (building K N).faces := by
  constructor
  · intro A hA B hB
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hB
    rcases le_total a b with hab | hba
    · exact Or.inr (cut_antitone K N hab)
    · exact Or.inl (cut_antitone K N hba)
  · intro A hA B hB
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hB
    exact ((shift K N).monotone (cut_le_standard K N a)).trans (shift_standard_le_cut K N b)

lemma baseChamber_card : (baseChamber K N).card = N := by
  rw [baseChamber,Finset.card_image_of_injective _ (cutVertex_injective K N),Finset.card_univ,Fintype.card_fin]

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.AffineLattices
variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

lemma level_reflect_le (m : ℕ) (A B : P) : level T A m ≤ level T B m ↔ A ≤ B :=
  by simpa only [iterIso_apply] using ((iterIso T m).le_iff_le (x := A) (y := B))

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.AffineLattices
variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

lemma level_swap (A : P) (a b : ℕ) : level T (level T A a) b = level T (level T A b) a := by
  rw [← level_add,← level_add,Nat.add_comm]

lemma normalized_level_le (hC : T C ≤ C) (A B : Vertex T C) (a b : ℕ)
    (hle : level T A.val a ≤ level T B.val b) : b ≤ a := by
  by_contra h
  have hab : a < b := by omega
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hab)
  subst b
  have ha : A.val ≤ level T B.val d := by
    apply (level_reflect_le T a _ _).mp
    rw [← level_add,Nat.add_comm d a]
    exact hle
  apply vertex_normalized T C A
  exact ha.trans ((level_vertex_le T C B d).trans
    (level_antitone T C hC (show 1 ≤ d by omega)))

lemma compatible_symm {A B : P} (h : Compatible T A B) : Compatible T B A := by
  obtain ⟨a,b,hab,hba⟩ := h
  exact ⟨b,a+1,T.monotone hba,hab⟩

lemma compatible_homothetic_left {A A' B : P} (hA : Homothetic T A A')
    (h : Compatible T A B) : Compatible T A' B := by
  obtain ⟨r,s,he⟩ := hA
  obtain ⟨a,b,hab,hba⟩ := h
  have he' : level T A' (a+s) = level T A (a+r) := by
    rw [Nat.add_comm a s,level_add,← he,← level_add,Nat.add_comm r a]
  refine ⟨a+s,b+r,?_,?_⟩
  · rw [he',level_add,level_add,← level_map]
    exact level_mono T r hab
  · rw [he',level_add,level_add]
    exact level_mono T r hba

lemma compatible_homothetic {A A' B B' : P} (hA : Homothetic T A A')
    (hB : Homothetic T B B') (h : Compatible T A B) : Compatible T A' B' :=
  compatible_symm T (compatible_homothetic_left T hB
    (compatible_symm T (compatible_homothetic_left T hA h)))

lemma compatible_normalized_iff (hC : T C ≤ C) (A B : Vertex T C) :
    Compatible T A.val B.val ↔ (A ≤ B ∨ B ≤ A) ∧ T A.val ≤ B.val ∧ T B.val ≤ A.val := by
  constructor
  · rintro ⟨a,b,hab,hba⟩
    have h₁ : a ≤ b := normalized_level_le T C hC B A b a hba
    have h₂ : b ≤ a+1 := normalized_level_le T C hC A B (a+1) b hab
    have hc : b = a ∨ b = a+1 := by omega
    rcases hc with he | he
    · rw [he] at hab hba
      have hBA : B.val ≤ A.val := (level_reflect_le T a _ _).mp hba
      have hAB : T A.val ≤ B.val := by
        apply (level_reflect_le T a _ _).mp
        rwa [level_map]
      exact ⟨Or.inr hBA,hAB,(T.monotone hBA).trans (vertex_shift_le T C A)⟩
    · rw [he] at hab hba
      have hAB : A.val ≤ B.val := (level_reflect_le T (a+1) _ _).mp hab
      have hBA : T B.val ≤ A.val := by
        apply (level_reflect_le T a _ _).mp
        rwa [level_map]
      exact ⟨Or.inl hAB,(T.monotone hAB).trans (vertex_shift_le T C B),hBA⟩
  · rintro ⟨hcmp,hab,hba⟩
    rcases hcmp with hAB | hBA
    · exact compatible_symm T ⟨0,0,hba,hAB⟩
    · exact ⟨0,0,hab,hBA⟩

lemma isFace_iff_compatible (hC : T C ≤ C) (s : Finset (Vertex T C)) :
    IsFace T C s ↔ ∀ A ∈ s, ∀ B ∈ s, Compatible T A.val B.val := by
  constructor
  · intro h A hA B hB
    exact (compatible_normalized_iff T C hC A B).mpr
      ⟨h.1 A hA B hB,h.2 A hA B hB,h.2 B hB A hA⟩
  · intro h
    exact ⟨fun A hA B hB => ((compatible_normalized_iff T C hC A B).mp (h A hA B hB)).1,
      fun A hA B hB => ((compatible_normalized_iff T C hC A B).mp (h A hA B hB)).2.1⟩

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.AffineLattices
variable {P : Type} [Lattice P] (T : P ≃o P) (C : P)

lemma homothetic_map_iff (S : P ≃o P) (hS : ∀ A, S (T A) = T (S A))
    (A B : P) : Homothetic T (S A) (S B) ↔ Homothetic T A B := by
  constructor
  · rintro ⟨a,b,he⟩
    refine ⟨a,b,S.injective ?_⟩
    simpa only [map_level T S hS] using he
  · exact homothetic_map T S hS

lemma compatible_map (S : P ≃o P) (hS : ∀ A, S (T A) = T (S A))
    {A B : P} (h : Compatible T A B) : Compatible T (S A) (S B) := by
  obtain ⟨a,b,hab,hba⟩ := h
  refine ⟨a,b,?_,?_⟩
  · simpa only [hS,map_level T S hS] using S.monotone hab
  · simpa only [map_level T S hS] using S.monotone hba

lemma mapVertex_injective (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (S : P ≃o P)
    (hS : ∀ A, S (T A) = T (S A))
    (hu : ∃ r, level T (S C) r ≤ C) (hl : ∃ s, level T C s ≤ S C) :
    Function.Injective (mapVertex T C hC hstrict S hS hu hl) := by
  intro A B he
  have hA := mapVertex_homothetic T C hC hstrict S hS hu hl A
  have hB := mapVertex_homothetic T C hC hstrict S hS hu hl B
  rw [he] at hA
  exact (homothetic_normalized_iff T C hC A B).mp ((homothetic_map_iff T S hS _ _).mp
    (homothetic_trans T hA (homothetic_symm T hB)))

lemma mapVertex_face (hC : T C ≤ C) (hstrict : ¬ C ≤ T C) (S : P ≃o P)
    (hS : ∀ A, S (T A) = T (S A))
    (hu : ∃ r, level T (S C) r ≤ C) (hl : ∃ s, level T C s ≤ S C)
    (s : Finset (Vertex T C)) (hs : IsFace T C s) :
    IsFace T C (s.image (mapVertex T C hC hstrict S hS hu hl)) := by
  apply (isFace_iff_compatible T C hC _).mpr
  intro A hA B hB
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hB
  exact compatible_homothetic T (mapVertex_homothetic T C hC hstrict S hS hu hl a)
    (mapVertex_homothetic T C hC hstrict S hS hu hl b)
    (compatible_map T S hS ((isFace_iff_compatible T C hC s).mp hs a ha b hb))

end CoboundaryExpanders.AffineLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma actVertex_face (hN : 0 < N) (g : Matrix.SpecialLinearGroup (Fin N) K[X])
    (s : Finset (Vertex K N)) (hs : s ∈ (building K N).faces) :
    s.image (actVertex K N hN g) ∈ (building K N).faces :=
  mapVertex_face _ _ _ _ _ _ _ _ s hs

end CoboundaryExpanders.RationalLattices

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Polynomial-vector leading terms, degree reduction, and normalized rational lattice representatives.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.PolynomialVectors
attribute [local instance] Classical.propDecidable
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma pivot_monic (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) :
    ((pivot A hA i) i).coeff (pivotDegree A hA i) = 1 := by
  simp [pivot, (pivotRaw_leading A hA i).1]

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma reflect_sum {I : Type} (s : Finset I) (f : I → K[X]) (a : ℕ) :
    Polynomial.reflect a (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.reflect a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,Polynomial.reflect_add,ih]

lemma polynomial_eq_one_of_dvd_X_pow (f : K[X]) (m : ℕ)
    (hf : f ∣ Polynomial.X^m) (hc : f.coeff 0 = 1) : f = 1 := by
  obtain ⟨a,_,ha⟩ := (dvd_prime_pow Polynomial.prime_X m).mp hf
  have ha0 : a = 0 := by
    by_contra hn
    have hX : Polynomial.X ∣ f := ha.dvd_iff_dvd_right.mpr
      (dvd_pow_self _ hn)
    have hz := Polynomial.X_dvd_iff.mp hX
    rw [hc] at hz
    exact one_ne_zero hz
  rw [ha0,pow_zero] at ha
  have hu : IsUnit f := ha.isUnit_iff.mpr isUnit_one
  obtain ⟨c,_,he⟩ := Polynomial.isUnit_iff.mp hu
  have hc1 : c = 1 := by simpa [← he] using hc
  rw [← he,hc1,Polynomial.C_1]

lemma columnReflect_det_eq_one (B C : Matrix (Fin N) (Fin N) K[X])
    (a : Fin N → ℕ) (m : ℕ) (hBC : B*C = (Polynomial.X^m : K[X]) • 1)
    (hB : ∀ i j, (B i j).natDegree ≤ a j)
    (hc : ((columnReflect B a).det).coeff 0 = 1) :
    (columnReflect B a).det = 1 := by
  classical
  let L := m + Finset.univ.sup (fun p : Fin N × Fin N => a p.1+(C p.1 p.2).natDegree)
  have hL : ∀ i j, a i+(C i j).natDegree ≤ L := by
    intro i j
    exact le_trans (Finset.le_sup (f := fun p : Fin N × Fin N => a p.1+(C p.1 p.2).natDegree)
      (Finset.mem_univ (i,j))) (Nat.le_add_left _ _)
  have hmL : m ≤ L := Nat.le_add_right _ _
  let D : Matrix (Fin N) (Fin N) K[X] := fun i j => Polynomial.reflect (L-a i) (C i j)
  have hGD : columnReflect B a * D = (Polynomial.X^(L-m) : K[X]) • 1 := by
    apply Matrix.ext
    intro i j
    change (∑ t, Polynomial.reflect (a t) (B i t) * Polynomial.reflect (L-a t) (C t j)) = _
    have he : (∑ t, Polynomial.reflect (a t) (B i t) * Polynomial.reflect (L-a t) (C t j)) =
        Polynomial.reflect L ((B*C) i j) := by
      rw [Matrix.mul_apply,reflect_sum]
      apply Finset.sum_congr rfl
      intro t _
      have hCt := hL t j
      have hh := Polynomial.reflect_mul (B i t) (C t j) (hB i t)
        (show (C t j).natDegree ≤ L-a t by omega)
      rw [Nat.add_sub_of_le (show a t ≤ L by omega)] at hh
      exact hh.symm
    rw [he,hBC]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one]
      rw [Polynomial.reflect_monomial,Polynomial.revAt_le hmL]
    · simp [hij]
  have hdet := congrArg Matrix.det hGD
  rw [Matrix.det_mul,Matrix.det_smul,Matrix.det_one,mul_one,Fintype.card_fin,← pow_mul] at hdet
  exact polynomial_eq_one_of_dvd_X_pow _ ((L-m)*N) ⟨D.det,hdet.symm⟩ hc

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma positive_reflect_uniformizer (f : K[X]) (a : ℕ) (hf : f.natDegree ≤ a) :
    positive K (Polynomial.reflect a f) * uniformizer K^a = algebraMap K[X] (RatFunc K) f := by
  let : Invertible (uniformizer K) := invertibleOfNonzero (uniformizer_ne_zero K)
  change Polynomial.eval₂ (algebraMap K (RatFunc K)) (uniformizer K)⁻¹ (Polynomial.reflect a f) * uniformizer K^a = _
  simpa only [invOf_eq_inv,eval_uniformizer] using
    Polynomial.eval₂_reflect_mul_pow (algebraMap K (RatFunc K)) (uniformizer K) a f hf

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

theorem simultaneous_minimal_basis
    (A : Submodule K[X] (V K N)) (hA : HasPivots A)
    (B : Fin (M+1) → Submodule K[X] (V K N))
    (hB : ∀ r, HasPivots (B r)) (hanti : Antitone B)
    (hzero : B 0 = A) (hbelow : ∀ r, powerShift A 1 ≤ B r) :
    ∃ b : Fin N → V K N,
      (∀ i, b i ∈ A) ∧ (∀ i, Leading (b i) i (pivotDegree A hA i)) ∧
      (∀ i, (b i i).coeff (pivotDegree A hA i) = 1) ∧
      ∀ r, Submodule.span K[X] (Set.range fun i =>
        if pivotDegree (B r) (hB r) i = pivotDegree A hA i
        then b i else (Polynomial.X : K[X]) • b i) = B r := by
  classical
  let S (i : Fin N) : Finset (Fin (M+1)) :=
    Finset.univ.filter (fun r => pivotDegree (B r) (hB r) i = pivotDegree A hA i)
  have hS (i : Fin N) : (S i).Nonempty := by
    refine ⟨0,?_⟩
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    subst A
    rfl
  let last (i : Fin N) := (S i).max' (hS i)
  have hlast (i : Fin N) : pivotDegree (B (last i)) (hB (last i)) i = pivotDegree A hA i := by
    have hh := Finset.max'_mem (S i) (hS i)
    exact (Finset.mem_filter.mp hh).2
  let b (i : Fin N) := pivot (B (last i)) (hB (last i)) i
  have hmem (i : Fin N) : b i ∈ A := by
    rw [← hzero]
    exact hanti (Fin.zero_le _) (pivot_mem _ _ _)
  have hlead (i : Fin N) : Leading (b i) i (pivotDegree A hA i) := by
    rw [← hlast i]
    exact pivot_leading _ _ _
  refine ⟨b,hmem,hlead,?_,?_⟩
  · intro i
    rw [← hlast i]
    exact pivot_monic _ _ _
  · intro r
    let c (i : Fin N) := if pivotDegree (B r) (hB r) i = pivotDegree A hA i
      then b i else (Polynomial.X : K[X]) • b i
    have hBA : B r ≤ A := by rw [← hzero]; exact hanti (Fin.zero_le _)
    have hinc (i : Fin N) := interval_pivot_increment hA (hB r) hBA (hbelow r) i
    have hc (i : Fin N) : c i ∈ B r := by
      dsimp [c]
      split_ifs with he
      · have hr : r ∈ S i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
        have hrlast : r ≤ last i := Finset.le_max' (S i) r hr
        exact hanti hrlast (pivot_mem _ _ _)
      · apply hbelow r
        refine ⟨b i,hmem i,?_⟩
        simp [powerLinear]
    have hcl (i : Fin N) : Leading (c i) i (pivotDegree (B r) (hB r) i) := by
      dsimp [c]
      split_ifs with he
      · rw [he]; exact hlead i
      · have hh : pivotDegree (B r) (hB r) i = pivotDegree A hA i+1 := (hinc i).resolve_left he
        rw [hh]
        simpa using leading_X_pow (hlead i) 1
    exact span_of_minimal (B r) c (pivotDegree (B r) (hB r)) hc hcl
      (fun hv hl => pivotDegree_min _ _ _ hv hl)

lemma matrix_right_multiple_of_span (b : Fin N → V K N)
    (A : Submodule K[X] (V K N)) (hspan : Submodule.span K[X] (Set.range b) = A)
    (m : ℕ) (hm : ∀ i : Fin N, Pi.single i (Polynomial.X^m : K[X]) ∈ A) :
    ∃ C : Matrix (Fin N) (Fin N) K[X], (show Matrix (Fin N) (Fin N) K[X] from fun i j => b j i)*C = (Polynomial.X^m : K[X]) • 1 := by
  classical
  have hex : ∀ j : Fin N, ∃ c : Fin N → K[X],
      ∑ i, c i • b i = Pi.single j (Polynomial.X^m : K[X]) := by
    intro j
    apply (Submodule.mem_span_range_iff_exists_fun K[X]).mp
    rw [hspan]
    exact hm j
  choose c hc using hex
  refine ⟨fun i j => c j i,?_⟩
  apply Matrix.ext
  intro i j
  have he := congr_fun (hc j) i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he
  change (∑ t, b t i * c j t) = (Polynomial.X^m : K[X]) * (if i = j then 1 else 0)
  have he' : (∑ t, c j t * b t i) = (Polynomial.X^m : K[X]) * (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · subst j; simpa using he
    · simpa [hij] using he
  exact (Finset.sum_congr rfl (fun _ _ => mul_comm _ _)).trans he'

lemma monic_reflect_det (b : Fin N → V K N) (a : Fin N → ℕ)
    (hl : ∀ i, Leading (b i) i (a i)) (hmonic : ∀ i, (b i i).coeff (a i) = 1)
    (A : Submodule K[X] (V K N)) (hspan : Submodule.span K[X] (Set.range b) = A)
    (m : ℕ) (hm : ∀ i : Fin N, Pi.single i (Polynomial.X^m : K[X]) ∈ A) :
    (columnReflect (fun i j => b j i) a).det = 1 := by
  classical
  obtain ⟨C,hC⟩ := matrix_right_multiple_of_span b A hspan m hm
  apply columnReflect_det_eq_one _ C a m hC (fun i j => leading_natDegree_le (hl j) i)
  have hupper : ((Polynomial.constantCoeff).mapMatrix (columnReflect (fun i j => b j i) a)).IsUpperTriangular := by
    intro i j hij
    change Polynomial.constantCoeff (Polynomial.reflect (a j) (b j i)) = 0
    rw [Polynomial.constantCoeff_apply,Polynomial.coeff_reflect,Polynomial.revAt_zero]
    exact (hl j).2 _ _ (Nat.add_lt_add_left hij _)
  rw [← Polynomial.constantCoeff_apply,RingHom.map_det,Matrix.det_of_isUpperTriangular hupper]
  apply Finset.prod_eq_one
  intro i _
  change Polynomial.constantCoeff (Polynomial.reflect (a i) (b i i)) = 1
  rw [Polynomial.constantCoeff_apply,Polynomial.coeff_reflect,Polynomial.revAt_zero]
  exact hmonic i

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma reflected_columns_leading (g : Matrix (Fin N) (Fin N) K[X]) (M : ℕ)
    (hdeg : ∀ i j, (g i j).natDegree ≤ M)
    (hc : ∀ i j, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j) :
    ∀ j, Leading (fun i => Polynomial.reflect M (g i j)) j M := by
  classical
  intro j
  constructor
  · rw [Polynomial.coeff_reflect,Polynomial.revAt_le le_rfl,Nat.sub_self,hc j j le_rfl,Matrix.one_apply_eq]
    exact one_ne_zero
  · intro i b hb
    by_cases hMb : M < b
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((Polynomial.natDegree_reflect_le.trans (max_le le_rfl (hdeg i j))).trans_lt hMb)
    · have hbM : b = M := by
        by_contra hn
        have hm := Nat.mul_le_mul_left N (show b+1 ≤ M by omega)
        simp only [Nat.mul_add,Nat.mul_one] at hm
        have hi := i.isLt
        omega
      subst b
      have hji : j < i := by omega
      rw [Polynomial.coeff_reflect,Polynomial.revAt_le le_rfl,Nat.sub_self,hc i j hji.le,
        Matrix.one_apply_ne (ne_of_gt hji)]

theorem pivotDegree_image (C : Matrix (Fin N) (Fin N) K[X]) (M : ℕ)
    (hC : ∀ j, Leading (fun i => C i j) j M)
    (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) :
    pivotDegree (A.map (matrixLinear C)) (image_hasPivots C M hC A hA) i =
      pivotDegree A hA i+M := by
  let hI := image_hasPivots C M hC A hA
  apply le_antisymm
  · exact pivotDegree_min _ hI i ⟨pivot A hA i,pivot_mem A hA i,rfl⟩
      (leading_mulVec C M hC (pivot_leading _ _ _))
  · obtain ⟨v,hv,he⟩ := pivot_mem (A.map (matrixLinear C)) hI i
    have hv0 : v ≠ 0 := by
      intro hz
      apply leading_ne_zero (pivot_leading (A.map (matrixLinear C)) hI i)
      rw [← he,hz,map_zero]
    obtain ⟨j,a,hl⟩ := exists_leading hv0
    have ht := leading_mulVec C M hC hl
    change Leading (matrixLinear C v) j (a+M) at ht
    rw [he] at ht
    obtain ⟨hji,hd⟩ := leading_unique ht (pivot_leading _ hI i)
    subst j
    have hmin := pivotDegree_min A hA i hv hl
    change pivotDegree A hA i+M ≤ pivotDegree (A.map (matrixLinear C)) hI i
    omega

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices
variable (K : Type) [Field K] (N M : ℕ)

theorem lattice_flag_birkhoff (B : Fin (M+1) → Vertex K N)
    (hanti : Antitone (fun r => (B r).val))
    (hbelow : ∀ r, level (shift K N) (B 0).val 1 ≤ (B r).val) :
    ∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
      (∀ i j : Fin N, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      ∀ r, positiveAction K N g (exponentLattice K N (diagonalExponents K N (B r))) = (B r).val := by
  classical
  let A := polynomialLattice K N (B 0)
  let P (r : Fin (M+1)) := polynomialLattice K N (B r)
  let hA := polynomialHasPivots K N (B 0)
  let hP (r : Fin (M+1)) := polynomialHasPivots K N (B r)
  let a := PolynomialVectors.pivotDegree A hA
  obtain ⟨b,hb,hl,hmonic,hspan⟩ := PolynomialVectors.simultaneous_minimal_basis A hA P hP
    (fun r s hrs => polynomialLattice_mono K N (hanti hrs)) rfl
    (fun r => polynomialLattice_power_le K N (hbelow r))
  have hspan0 : Submodule.span K[X] (Set.range b) = A := by
    simpa only [P,A,↓reduceIte] using hspan 0
  obtain ⟨m,hm⟩ := polynomialLattice_bound K N (B 0)
  let g : Matrix.SpecialLinearGroup (Fin N) K[X] :=
    ⟨PolynomialVectors.columnReflect (fun i j => b j i) a,
      PolynomialVectors.monic_reflect_det b a hl hmonic A hspan0 m hm⟩
  refine ⟨g,?_,?_⟩
  · intro i j hji
    change (Polynomial.reflect (a j) (b j i)).coeff 0 = _
    rw [Polynomial.coeff_reflect,Polynomial.revAt_zero]
    by_cases hij : i = j
    · subst j; rw [Matrix.one_apply_eq]; exact hmonic i
    · rw [Matrix.one_apply_ne hij]
      have hj : j < i := lt_of_le_of_ne hji (Ne.symm hij)
      exact (hl j).2 i (a j) (Nat.add_lt_add_left hj _)
  · intro r
    let c (i : Fin N) := if PolynomialVectors.pivotDegree (P r) (hP r) i = a i
      then b i else (Polynomial.X : K[X]) • b i
    have hinc (i : Fin N) := PolynomialVectors.interval_pivot_increment hA (hP r)
      (polynomialLattice_mono K N (hanti (Fin.zero_le r)))
      (polynomialLattice_power_le K N (hbelow r)) i
    have hcol (j : Fin N) : positiveLinear K N g
        (Pi.single j (uniformizer K ^ diagonalExponents K N (B r) j)) = polynomialEmbedding K N (c j) := by
      rw [positiveLinear_apply,Matrix.mulVec_single]
      funext i
      change positive K (Polynomial.reflect (a j) (b j i)) *
        uniformizer K ^ PolynomialVectors.pivotDegree (P r) (hP r) j =
        algebraMap K[X] (RatFunc K) (c j i)
      have hh := positive_reflect_uniformizer K (b j i) (a j)
        (PolynomialVectors.leading_natDegree_le (hl j) i)
      dsimp only [c]
      split_ifs with he
      · rw [he]; exact hh
      · have he' : PolynomialVectors.pivotDegree (P r) (hP r) j = a j+1 := (hinc j).resolve_left he
        rw [he',pow_succ,← mul_assoc,hh]
        change algebraMap K[X] (RatFunc K) (b j i) * uniformizer K =
          algebraMap K[X] (RatFunc K) (Polynomial.X * b j i)
        rw [map_mul]
        exact mul_comm _ _
    change (Submodule.span K[X] (Set.range fun i : Fin N =>
      Pi.single i (uniformizer K ^ diagonalExponents K N (B r) i))).map
      (positiveLinear K N g).toLinearMap = (B r).val
    rw [Submodule.map_span,← Set.range_comp]
    change Submodule.span K[X] (Set.range (fun i : Fin N => positiveLinear K N g
      (Pi.single i (uniformizer K ^ diagonalExponents K N (B r) i)))) = (B r).val
    rw [show (fun i : Fin N => positiveLinear K N g (Pi.single i (uniformizer K ^ diagonalExponents K N (B r) i))) =
      fun i => polynomialEmbedding K N (c i) from funext hcol]
    change Submodule.span K[X] (Set.range ((polynomialEmbedding K N) ∘ c)) = (B r).val
    rw [Set.range_comp,← Submodule.map_span]
    have hs : Submodule.span K[X] (Set.range c) = P r := hspan r
    rw [hs]
    exact polynomialLattice_map K N (B r)

end CoboundaryExpanders.RationalLattices

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Windows
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Affine windows, residue chambers, lattice flags, and chamber parametrizations.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.AffineWindow

variable {N : ℕ}

lemma sub_not_dvd {a b : ℤ} (h : a % (N : ℤ) ≠ b % (N : ℤ)) :
    ¬ (N : ℤ) ∣ b-a := by
  intro hd
  have he := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hd)
  exact h he.symm

lemma div_neg_nondiv (hN : 0 < N) {z : ℤ} (hz : ¬ (N : ℤ) ∣ z) :
    (-z)/(N : ℤ) = -(z/(N : ℤ))-1 := by
  have hpos : (0 : ℤ) < N := by exact_mod_cast hN
  have hm := Int.emod_nonneg z (ne_of_gt hpos)
  have hm' := Int.emod_lt_of_pos z hpos
  have hne : z % (N : ℤ) ≠ 0 := by
    intro he
    exact hz (Int.dvd_of_emod_eq_zero he)
  have hmp : 0 < z % (N : ℤ) := by omega
  have he := Int.mul_ediv_add_emod z (N : ℤ)
  apply (Int.ediv_eq_iff_of_pos hpos).2
  constructor <;> nlinarith

lemma pairCost_reverse (hN : 0 < N) {a b : ℤ}
    (hr : a % (N : ℤ) ≠ b % (N : ℤ)) (hab : a < b) :
    pairCost N b a = pairCost N a b + 1 := by
  have hq : 0 ≤ (b-a)/(N : ℤ) := Int.ediv_nonneg (by omega) (by omega)
  have hn := div_neg_nondiv hN (sub_not_dvd hr)
  rw [neg_sub] at hn
  unfold pairCost
  rw [hn]
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [abs_of_nonneg hq]
  have hneg : -((b-a)/(N : ℤ))-1 ≤ 0 := by omega
  rw [abs_of_nonpos hneg]
  omega

lemma pairCost_rotate (hN : 0 < N) {a b : ℤ}
    (hr : a % (N : ℤ) ≠ b % (N : ℤ)) :
    pairCost N b (a+N) = pairCost N a b := by
  have hp : (N : ℤ) ≠ 0 := by omega
  have hn := div_neg_nondiv hN (sub_not_dvd hr)
  have he : (a+(N : ℤ)-b)/(N : ℤ) = -((b-a)/(N : ℤ)) := by
    have hs : a+(N : ℤ)-b = -(b-a) + N := by ring
    rw [hs, Int.add_ediv_of_dvd_right (dvd_refl (N : ℤ)), Int.ediv_self hp, hn]
    omega
  unfold pairCost
  rw [he, Int.natAbs_neg]

lemma pairCost_eq_zero_iff (hN : 0 < N) (a b : ℤ) :
    pairCost N a b = 0 ↔ a ≤ b ∧ b < a+N := by
  unfold pairCost
  rw [Int.natAbs_eq_zero, Int.ediv_eq_iff_of_pos (show (0 : ℤ) < N by omega)]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

lemma pairCost_shift (a b c : ℤ) : pairCost N (a+c) (b+c) = pairCost N a b := by
  unfold pairCost
  congr 2
  ring

lemma inversion_append (l r : List ℤ) :
    inversion (N := N) (l++r) = inversion (N := N) l + inversion (N := N) r +
      ((l.map (fun a => (r.map (pairCost N a)).sum))).sum := by
  induction l with
  | nil => simp [inversion]
  | cons a l ih => simp only [List.cons_append,inversion,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons,ih]; omega

lemma inversion_adjacent (l r : List ℤ) (a b : ℤ) :
    inversion (N := N) (l++a::b::r) + pairCost N b a =
      inversion (N := N) (l++b::a::r) + pairCost N a b := by
  induction l with
  | nil => simp [inversion]; omega
  | cons c l ih =>
    simp only [List.cons_append,inversion,List.map_append,List.sum_append,List.map_cons,
      List.sum_cons] at *
    omega

lemma inversion_adjacent_increase (hN : 0 < N) (l r : List ℤ) {a b : ℤ}
    (hr : a % (N : ℤ) ≠ b % (N : ℤ)) (hab : a < b) :
    inversion (N := N) (l++b::a::r) = inversion (N := N) (l++a::b::r)+1 := by
  have h := inversion_adjacent (N := N) l r a b
  rw [pairCost_reverse hN hr hab] at h
  omega

lemma inversion_rotate (hN : 0 < N) (a : ℤ) (l : List ℤ)
    (hr : ∀ b ∈ l, a % (N : ℤ) ≠ b % (N : ℤ)) :
    inversion (N := N) (l++[a+N]) = inversion (N := N) (a::l) := by
  rw [inversion_append,inversion]
  have he : (l.map (fun b => ([a+(N:ℤ)].map (pairCost N b)).sum)).sum =
      (l.map (pairCost N a)).sum := by
    congr 1
    apply List.map_congr_left
    intro b hb
    simpa using pairCost_rotate hN (hr b hb)
  rw [he]
  simp [inversion,Nat.add_comm]

lemma inversion_shift (l : List ℤ) (c : ℤ) :
    inversion (N := N) (l.map (·+c)) = inversion (N := N) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,inversion,ih,List.map_map]
    congr 2
    exact List.map_congr_left fun b _ => pairCost_shift a b c

lemma inversion_zero_iff (hN : 0 < N) (l : List ℤ) :
    inversion (N := N) l = 0 ↔ l.Pairwise (fun a b => a ≤ b ∧ b < a+(N : ℤ)) := by
  induction l with
  | nil => simp [inversion]
  | cons a l ih =>
    simp only [inversion,Nat.add_eq_zero_iff,List.sum_eq_zero_iff,List.mem_map,
      List.pairwise_cons,ih]
    constructor
    · rintro ⟨hs,hl⟩
      refine ⟨?_,hl⟩
      intro b hb
      exact (pairCost_eq_zero_iff hN a b).mp (hs _ ⟨b,hb,rfl⟩)
    · rintro ⟨hs,hl⟩
      refine ⟨?_,hl⟩
      rintro _ ⟨b,hb,rfl⟩
      exact (pairCost_eq_zero_iff hN a b).mpr (hs b hb)

lemma consecutive_of_bounds (hN : 0 < N) (p : Fin N → ℤ)
    (hp : StrictMono p) (hspan : ∀ i, p i < p ⟨0,hN⟩+N) :
    ∀ i, p i = p ⟨0,hN⟩ + i.val := by
  let f (i : Fin N) : Fin N := ⟨(p i-p ⟨0,hN⟩).toNat, by
    have hn : 0 ≤ p i-p ⟨0,hN⟩ := sub_nonneg.mpr (hp.monotone (show (⟨0,hN⟩ : Fin N) ≤ i from Nat.zero_le _))
    have := hspan i
    omega⟩
  have hf : StrictMono f := by
    intro i j hij
    change (p i-p ⟨0,hN⟩).toNat < (p j-p ⟨0,hN⟩).toNat
    have hn := hp.monotone (show (⟨0,hN⟩ : Fin N) ≤ i from Nat.zero_le _)
    have hh := hp hij
    omega
  intro i
  have he := congrArg Fin.val (congr_fun hf.eq_id i)
  have hn := hp.monotone (show (⟨0,hN⟩ : Fin N) ≤ i from Nat.zero_le _)
  change (p i-p ⟨0,hN⟩).toNat = i.val at he
  omega

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}

lemma pairs_perm (f : ℤ → ℤ → ℕ) (hf : ∀ a b, f a b = f b a)
    {l r : List ℤ} (h : l.Perm r) : pairs f l = pairs f r := by
  induction h with
  | nil => rfl
  | cons a h ih =>
      simp only [pairs,ih]
      exact congrArg (·+pairs f _) (h.map (f a)).sum_eq
  | swap a b l => simp [pairs,hf a b]; omega
  | trans h h' ih ih' => exact ih.trans ih'

lemma sortedCost_comm (a b : ℤ) : sortedCost N a b = sortedCost N b a := by
  simp only [sortedCost,min_comm,max_comm]

lemma pairCost_decompose (hN : 0 < N) {a b : ℤ}
    (hr : a % (N : ℤ) ≠ b % (N : ℤ)) :
    pairCost N a b = sortedCost N a b + disorder a b := by
  have hne : a ≠ b := fun h => hr (congrArg (· % (N : ℤ)) h)
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [sortedCost,min_eq_left h.le,max_eq_right h.le,disorder,ite_eq_right (not_lt_of_ge h.le),Nat.add_zero]
  · rw [pairCost_reverse hN (Ne.symm hr) h]
    simp only [sortedCost,min_eq_right h.le,max_eq_left h.le,disorder,ite_eq_left h]

lemma inversion_decompose (hN : 0 < N) (l : List ℤ)
    (hr : l.Pairwise (fun a b => a % (N : ℤ) ≠ b % (N : ℤ))) :
    inversion (N := N) l = pairs (sortedCost N) l + pairs disorder l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.pairwise_cons] at hr
    rw [inversion,pairs,pairs,ih hr.2]
    have he : (l.map (pairCost N a)).sum =
        (l.map (sortedCost N a)).sum + (l.map (disorder a)).sum := by
      rw [← List.sum_map_add]
      apply congrArg List.sum
      exact List.map_congr_left fun b hb => pairCost_decompose hN (hr.1 b hb)
    omega

lemma disorder_zero_iff (l : List ℤ) : pairs disorder l = 0 ↔ l.Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [pairs]
  | cons a l ih =>
    simp only [pairs,Nat.add_eq_zero_iff,List.sum_eq_zero_iff,List.mem_map,
      List.pairwise_cons,ih]
    constructor
    · rintro ⟨hs,hl⟩
      refine ⟨?_,hl⟩
      intro b hb
      have hh := hs _ ⟨b,hb,rfl⟩
      simp only [disorder,ite_eq_right_iff,one_ne_zero,imp_false] at hh
      omega
    · rintro ⟨hs,hl⟩
      refine ⟨?_,hl⟩
      rintro _ ⟨b,hb,rfl⟩
      simp only [disorder,ite_eq_right (not_lt_of_ge (hs b hb))]

theorem inversion_minimal_perm (hN : 0 < N) {l r : List ℤ}
    (hperm : l.Perm r) (hs : l.Pairwise (· ≤ ·))
    (hr : r.Pairwise (fun a b => a % (N : ℤ) ≠ b % (N : ℤ))) :
    inversion (N := N) r = inversion (N := N) l + pairs disorder r := by
  have hl : l.Pairwise (fun a b => a % (N : ℤ) ≠ b % (N : ℤ)) :=
    (hperm.pairwise_iff (fun h => Ne.symm h)).mpr hr
  rw [inversion_decompose hN r hr,inversion_decompose hN l hl,
    (disorder_zero_iff l).mpr hs,Nat.add_zero,pairs_perm (sortedCost N) sortedCost_comm hperm]

lemma inversion_permute_middle (l r p q : List ℤ) (hpq : p.Perm q) :
    inversion (N := N) (l++q++r) + inversion (N := N) p =
      inversion (N := N) (l++p++r) + inversion (N := N) q := by
  induction l with
  | nil =>
      simp only [List.nil_append]
      rw [inversion_append,inversion_append]
      have hh := (hpq.map (fun a => (r.map (pairCost N a)).sum)).sum_eq
      omega
  | cons a l ih =>
      simp only [List.cons_append,inversion,List.map_append,List.sum_append]
      have hh := (hpq.map (pairCost N a)).sum_eq
      omega

lemma inversion_sorted_middle (hN : 0 < N) (l r : List ℤ) {p q : List ℤ}
    (hpq : p.Perm q) (hs : p.Pairwise (· ≤ ·))
    (hr : q.Pairwise (fun a b => a % (N : ℤ) ≠ b % (N : ℤ))) :
    inversion (N := N) (l++q++r) = inversion (N := N) (l++p++r) + pairs disorder q := by
  have h₁ := inversion_permute_middle (N := N) l r p q hpq
  have h₂ := inversion_minimal_perm hN hpq hs hr
  omega

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}

lemma periodicEnd_mono_iff (hN : 0 < N) (p : Fin N → ℤ) :
    Monotone (periodicEnd hN p) ↔ descents hN p = ∅ := by
  classical
  rw [Fin.monotone_iff_le_succ,Finset.eq_empty_iff_forall_notMem]
  simp only [descents,Finset.mem_filter,Finset.mem_univ,true_and,not_lt,periodicEnd_castSucc]

lemma last_ne_periodic_start (hN : 0 < N) (p : Fin N → ℤ)
    (hp : Function.Injective (fun r => p r % (N : ℤ))) :
    p ⟨N-1,by omega⟩ ≠ p ⟨0,hN⟩ + N := by
  intro he
  have hm := congrArg (· % (N : ℤ)) he
  simp only [Int.add_emod_right] at hm
  have hi := hp hm
  have hv := congrArg p hi
  have hpos : (0 : ℤ) < N := by exact_mod_cast hN
  omega

lemma inversion_zero_of_no_descents (hN : 0 < N) (p : Fin N → ℤ)
    (hp : Function.Injective (fun r => p r % (N : ℤ)))
    (hd : descents hN p = ∅) : inversion (N := N) (List.ofFn p) = 0 := by
  have hm := (periodicEnd_mono_iff hN p).mpr hd
  have hpmono : Monotone p := by
    intro i j hij
    simpa only [periodicEnd_castSucc] using hm (show i.castSucc ≤ j.castSucc from hij)
  have hl : p ⟨N-1,by omega⟩ < p ⟨0,hN⟩ + N := by
    have hle := hm (show (⟨N-1,by omega⟩ : Fin N).castSucc ≤ Fin.last N from Fin.le_last _)
    simp only [periodicEnd_castSucc,periodicEnd_last] at hle
    exact lt_of_le_of_ne hle (last_ne_periodic_start hN p hp)
  apply (inversion_zero_iff hN _).mpr
  apply List.pairwise_ofFn.mpr
  intro i j hij
  refine ⟨hpmono hij.le,?_⟩
  have hj := hpmono (show j ≤ ⟨N-1,by omega⟩ from by change j.val ≤ N-1; omega)
  have hi := hpmono (show (⟨0,hN⟩ : Fin N) ≤ i from Nat.zero_le _)
  omega

theorem descents_nonempty (hN : 0 < N) (p : Fin N → ℤ)
    (hp : Function.Injective (fun r => p r % (N : ℤ)))
    (hl : 0 < inversion (N := N) (List.ofFn p)) : (descents hN p).Nonempty := by
  by_contra hn
  have hz := inversion_zero_of_no_descents hN p hp (Finset.not_nonempty_iff_eq_empty.mp hn)
  omega

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}

lemma window_entry_consecutive (hN : 0 < N) (p : Fin N → ℤ)
    (hp : Function.Injective (fun r => p r % (N : ℤ)))
    (hz : inversion (N := N) (List.ofFn p) = 0) :
    ∀ i, p i = p ⟨0,hN⟩ + i.val := by
  have hh := List.pairwise_ofFn.mp ((inversion_zero_iff hN _).mp hz)
  have hstrict : StrictMono p := by
    intro i j hij
    apply lt_of_le_of_ne (hh hij).1
    intro he
    exact (ne_of_lt hij) (hp (congrArg (· % (N : ℤ)) he))
  apply consecutive_of_bounds hN p hstrict
  intro i
  by_cases hi : i.val = 0
  · have he : i = ⟨0,hN⟩ := Fin.ext hi
    rw [he]
    have hpos : (0 : ℤ) < N := by exact_mod_cast hN
    omega
  · exact (hh (show (⟨0,hN⟩ : Fin N) < i from by change 0 < i.val; omega)).2

lemma same_residue_short_interval {x y c i : ℕ}
    (hx : c ≤ N*x+i ∧ N*x+i < c+N)
    (hy : c ≤ N*y+i ∧ N*y+i < c+N) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have hh := Nat.mul_le_mul_left N (show x+1 ≤ y from h)
    rw [Nat.mul_add,Nat.mul_one] at hh
    omega
  · exact h
  · have hh := Nat.mul_le_mul_left N (show y+1 ≤ x from h)
    rw [Nat.mul_add,Nat.mul_one] at hh
    omega

lemma cyclic_cut_exponents (hN : 0 < N) (a : Fin N → ℕ)
    (σ : Equiv.Perm (Fin N)) (c : ℕ)
    (hc : ∀ r : Fin N, N*a (σ r)+(σ r).val = c+r.val)
    (r : ℕ) (hr : r ≤ N) (i : Fin N) :
    a i + (if (σ.symm i).val < r then 1 else 0) =
      (c+r)/N + (if i.val < (c+r)%N then 1 else 0) := by
  have hbase := hc (σ.symm i)
  rw [σ.apply_symm_apply] at hbase
  apply same_residue_short_interval (N := N) (c := c+r) (i := i.val)
  · have hj := (σ.symm i).isLt
    split_ifs with h
    · rw [Nat.mul_add,Nat.mul_one]
      omega
    · rw [Nat.add_zero]
      omega
  · have hmod := Nat.mod_lt (c+r) hN
    have hdiv := Nat.mod_add_div (c+r) N
    have hi := i.isLt
    split_ifs with h
    · rw [Nat.mul_add,Nat.mul_one]
      omega
    · rw [Nat.add_zero]
      omega

theorem zero_window_cut_flag (hN : 0 < N) (a : Fin N → ℕ)
    (σ : Equiv.Perm (Fin N))
    (hz : inversion (N := N) (List.ofFn (fun r => (N*a (σ r)+(σ r).val : ℕ))) = 0) :
    ∃ c : ℕ, ∀ r : Fin (N+1), ∀ i : Fin N,
      a i + (if (σ.symm i).val < r.val then 1 else 0) =
        (c+r.val)/N + (if i.val < (c+r.val)%N then 1 else 0) := by
  let p (r : Fin N) : ℤ := (N*a (σ r)+(σ r).val : ℕ)
  have hp : Function.Injective (fun r => p r % (N : ℤ)) := by
    intro r s he
    have hmod (j : Fin N) : p j % (N : ℤ) = ((σ j).val : ℤ) := by
      dsimp only [p]
      push_cast
      have h0 : 0 ≤ ((σ j).val : ℤ) := Int.natCast_nonneg _
      have hlt : ((σ j).val : ℤ) < N := by exact_mod_cast (σ j).isLt
      simp only [Int.add_emod,Int.mul_emod_right,Int.zero_add,Int.emod_eq_of_lt h0 hlt]
    dsimp only at he
    rw [hmod,hmod] at he
    exact σ.injective (Fin.ext (by exact_mod_cast he))
  let c : ℕ := N*a (σ ⟨0,hN⟩)+(σ ⟨0,hN⟩).val
  have hc : ∀ r : Fin N, N*a (σ r)+(σ r).val = c+r.val := by
    intro r
    have hh := window_entry_consecutive hN p hp hz r
    dsimp [p,c] at hh ⊢
    exact_mod_cast hh
  exact ⟨c,fun r i => cyclic_cut_exponents hN a σ c hc r.val (by omega) i⟩

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))

theorem zero_flag (hN : 0 < N) (hz : C.length = 0) :
    ∃ c : ℕ, ∀ r : Fin (N+1), ∀ i : Fin N,
      pivotDegree (C.stage r) (C.hasStage r) i =
        (c+r.val)/N + (if i.val < (c+r.val)%N then 1 else 0) := by
  obtain ⟨c,hc⟩ := AffineWindow.zero_window_cut_flag hN
    (pivotDegree C.top C.hasTop) C.word hz
  exact ⟨c,fun r i => (C.stage_degree r i).trans (hc r i)⟩

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma exponent_cut (cut : Fin N) : exponentLattice K N (cutExponent N cut) = cutLattice K N cut := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩ j
    by_cases hj : j = i
    · subst j
      exact ⟨1,by simp⟩
    · exact ⟨0,by simp [Pi.single_eq_of_ne hj]⟩
  · intro v hv
    choose f hf using hv
    have he : v = ∑ i : Fin N, (f i) • Pi.single i (uniformizer K ^ cutExponent N cut i) := by
      funext j
      simp only [Finset.sum_apply,Algebra.smul_def,Pi.mul_apply,Pi.algebraMap_apply,
        Pi.single_apply,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      exact (hf j).symm
    rw [he]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))

lemma shift_exponent (a : Fin N → ℕ) :
    shift K N (exponentLattice K N a) = exponentLattice K N (fun i => a i+1) := by
  classical
  change (Submodule.span K[X] (Set.range fun i : Fin N => Pi.single i (uniformizer K ^ a i))).map
    (shiftLinear K N).toLinearMap = _
  rw [Submodule.map_span,← Set.range_comp]
  apply congrArg (Submodule.span K[X])
  apply congrArg Set.range
  funext i j
  by_cases hij : j = i
  · subst j
    simp [uniformizer,pow_succ,mul_comm]
  · simp [Function.comp_apply,hij]

lemma level_exponent (a : Fin N → ℕ) (m : ℕ) :
    level (shift K N) (exponentLattice K N a) m = exponentLattice K N (fun i => a i+m) := by
  induction m with
  | zero => simp [level]
  | succ m ih =>
    rw [level_succ,ih,shift_exponent]
    rfl

lemma exponent_cut_level (cut : Fin N) (m : ℕ) :
    exponentLattice K N (fun i => m+cutExponent N cut i) = level (shift K N) (cutLattice K N cut) m := by
  rw [← exponent_cut,level_exponent]
  congr 1
  funext i
  exact Nat.add_comm _ _

theorem zero_pivots_common_orbit {M : ℕ} (hN : 0 < N) (B : Fin (M+1) → Vertex K N)
    (hanti : Antitone (fun r => (B r).val))
    (hbelow : ∀ r, level (shift K N) (B 0).val 1 ≤ (B r).val)
    (cut : Fin (M+1) → Fin N) (m : Fin (M+1) → ℕ)
    (hdeg : ∀ r i, diagonalExponents K N (B r) i = m r+cutExponent N (cut r) i) :
    ∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
      (∀ i j : Fin N, j ≤ i → Polynomial.eval 0 (g i j) = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      ∀ r, B r = actVertex K N hN g (cutVertex K N (cut r)) := by
  obtain ⟨g,hg,hB⟩ := lattice_flag_birkhoff K N M B hanti hbelow
  refine ⟨g,fun i j hij => by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hg i j hij,?_⟩
  intro r
  have hexp : exponentLattice K N (diagonalExponents K N (B r)) =
      level (shift K N) (cutVertex K N (cut r)).val (m r) := by
    rw [show diagonalExponents K N (B r) = fun i => m r+cutExponent N (cut r) i from funext (hdeg r)]
    exact exponent_cut_level K N _ _
  have hh : Homothetic (shift K N) (B r).val
      (positiveAction K N g (cutVertex K N (cut r)).val) := by
    refine ⟨0,m r,?_⟩
    rw [level_zero,← map_level _ _ (positiveAction_shift K N g)]
    rw [← hexp]
    exact (hB r).symm
  apply (homothetic_normalized_iff (shift K N) (standard K N) (shift_standard_le K N) _ _).mp
  exact homothetic_trans _ hh (actVertex_homothetic K N hN g (cutVertex K N (cut r)))

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

namespace FullChamber
variable {K N} {hN : 0 < N} (C : FullChamber K N hN)

lemma stage_castSucc (r : Fin N) : C.stage r.castSucc = polynomialLattice K N (C.vertex r) := by
  simp only [stage,Fin.val_castSucc,dite_eq_left r.isLt]

lemma stage_last : C.stage (Fin.last N) = powerShift (polynomialLattice K N (C.vertex C.topIndex)) 1 := by
  unfold stage
  split_ifs with h
  · exact False.elim (Nat.lt_irrefl N h)
  · rfl

lemma zero_pivots (hz : C.length = 0) :
    ∃ c : ℕ, ∀ r : Fin N, ∀ i : Fin N,
      diagonalExponents K N (C.vertex r) i = (c+r.val)/N + (if i.val < (c+r.val)%N then 1 else 0) := by
  obtain ⟨c,hc⟩ := C.polynomialChamber.zero_flag hN hz
  refine ⟨c,fun r i => ?_⟩
  have hh := hc r.castSucc i
  simpa only [polynomialChamber,stage_castSucc,Fin.val_castSucc,diagonalExponents] using hh

theorem zero_common_orbit (hz : C.length = 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
      (∀ i j : Fin N, j ≤ i → Polynomial.eval 0 (g i j) = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      ∃ c : ℕ, ∀ r : Fin N,
        C.vertex r = actVertex K N hN g (cutVertex K N ⟨(c+r.val)%N,Nat.mod_lt _ hN⟩) := by
  obtain ⟨c,hc⟩ := C.zero_pivots hz
  cases N with
  | zero => omega
  | succ M =>
    have hh := zero_pivots_common_orbit K (M+1) hN C.vertex C.strict.antitone C.lower
      (fun r => ⟨(c+r.val)%(M+1),Nat.mod_lt _ hN⟩) (fun r => (c+r.val)/(M+1)) hc
    obtain ⟨g,hg,hv⟩ := hh
    exact ⟨g,hg,c,hv⟩

end FullChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

lemma polynomialEmbedding_injective : Function.Injective (polynomialEmbedding K N) := by
  intro v w he
  funext i
  exact RatFunc.algebraMap_injective K (congr_fun he i)

lemma reciprocal_reflect (f : K[X]) (M : ℕ) (hf : f.natDegree ≤ M) :
    positive K f * uniformizer K^M = algebraMap K[X] (RatFunc K) (Polynomial.reflect M f) := by
  have hh := positive_reflect_uniformizer K (Polynomial.reflect M f) M
    (Polynomial.natDegree_reflect_le.trans (max_le le_rfl hf))
  simpa only [Polynomial.reflect_reflect] using hh

lemma reflectedMatrix_embedding (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (M : ℕ)
    (hg : ∀ i j, (g i j).natDegree ≤ M) (v : PolynomialVectors.V K N) :
    polynomialEmbedding K N ((reflectedMatrix K N g.val M).mulVec v) =
      (Polynomial.X^M : K[X]) • positiveLinear K N g (polynomialEmbedding K N v) := by
  classical
  funext i
  change algebraMap K[X] (RatFunc K) (∑ j, Polynomial.reflect M (g i j) * v j) = _
  simp only [map_sum,map_mul,Pi.smul_apply,Algebra.smul_def,map_pow,positiveLinear_apply]
  change (∑ j, algebraMap K[X] (RatFunc K) (Polynomial.reflect M (g i j)) *
    algebraMap K[X] (RatFunc K) (v j)) =
    uniformizer K^M * ∑ j, positive K (g i j) * algebraMap K[X] (RatFunc K) (v j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← reciprocal_reflect K _ M (hg i j)]
  ring

lemma reflectedLattice_map_embedding (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (M : ℕ)
    (hg : ∀ i j, (g i j).natDegree ≤ M) (P : Submodule K[X] (PolynomialVectors.V K N)) :
    (P.map (matrixLinear (reflectedMatrix K N g.val M))).map (polynomialEmbedding K N) =
      level (shift K N) (positiveAction K N g (P.map (polynomialEmbedding K N))) M := by
  ext v
  constructor
  · rintro ⟨w,⟨z,hz,rfl⟩,rfl⟩
    apply (mem_level K N _ _ _).mpr
    refine ⟨positiveLinear K N g (polynomialEmbedding K N z),?_,?_⟩
    · exact (mem_positiveAction K N g _ _).mpr ⟨polynomialEmbedding K N z,⟨z,hz,rfl⟩,rfl⟩
    · exact (reflectedMatrix_embedding K N g M hg z).symm
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_level K N _ _ _).mp hv
    obtain ⟨y,⟨z,hz,rfl⟩,rfl⟩ := (mem_positiveAction K N g _ _).mp hw
    exact ⟨matrixLinear (reflectedMatrix K N g.val M) z,⟨z,hz,rfl⟩,
      reflectedMatrix_embedding K N g M hg z⟩

lemma matrix_degree_bound (g : Matrix (Fin N) (Fin N) K[X]) :
    ∃ M : ℕ, ∀ i j, (g i j).natDegree ≤ M := by
  classical
  refine ⟨Finset.univ.sup (fun i => Finset.univ.sup (fun j => (g i j).natDegree)),?_⟩
  intro i j
  exact (Finset.le_sup (f := fun j => (g i j).natDegree) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun i => Finset.univ.sup (fun j => (g i j).natDegree)) (Finset.mem_univ i))

theorem homothetic_action_pivots (g : Matrix.SpecialLinearGroup (Fin N) K[X])
    (hg : ∀ i j : Fin N, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j)
    (A B : Vertex K N) (a b : ℕ)
    (he : level (shift K N) (positiveAction K N g A.val) a = level (shift K N) B.val b) :
    ∀ i, diagonalExponents K N A i+a = diagonalExponents K N B i+b := by
  obtain ⟨M,hM⟩ := matrix_degree_bound K N g.val
  let R := reflectedMatrix K N g.val M
  have hR : ∀ j, Leading (fun i => R i j) j M := reflected_columns_leading g.val M hM hg
  let P := (polynomialLattice K N A).map (matrixLinear R)
  have hP : HasPivots P := image_hasPivots R M hR _ (polynomialHasPivots K N A)
  have hmap : P.map (polynomialEmbedding K N) =
      level (shift K N) (positiveAction K N g A.val) M := by
    rw [show P = (polynomialLattice K N A).map (matrixLinear (reflectedMatrix K N g.val M)) from rfl,
      reflectedLattice_map_embedding K N g M hM,polynomialLattice_map]
  have hpow : powerShift P a = powerShift (polynomialLattice K N B) (b+M) := by
    apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K N)
    rw [powerShift_map_embedding,hmap,powerShift_map_embedding,polynomialLattice_map]
    rw [level_swap,he,← level_add]
  intro i
  have hdeg : pivotDegree (powerShift P a) (powerShift_hasPivots P hP a) i =
      pivotDegree (powerShift (polynomialLattice K N B) (b+M))
        (powerShift_hasPivots _ (polynomialHasPivots K N B) (b+M)) i := by
    simp only [hpow]
  rw [pivotDegree_powerShift P hP a,
    pivotDegree_powerShift _ (polynomialHasPivots K N B) (b+M),
    pivotDegree_image R M hR _ (polynomialHasPivots K N A)] at hdeg
  change diagonalExponents K N A i+M+a = diagonalExponents K N B i+(b+M) at hdeg
  omega

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

lemma diagonalExponents_cut (cut : Fin N) (i : Fin N) :
    diagonalExponents K N (cutVertex K N cut) i = cutExponent N cut i := by
  classical
  let A := polynomialLattice K N (cutVertex K N cut)
  let hA := polynomialHasPivots K N (cutVertex K N cut)
  change pivotDegree A hA i = cutExponent N cut i
  apply le_antisymm
  · apply pivotDegree_min A hA i (v := Pi.single i (Polynomial.X ^ cutExponent N cut i))
    · intro j
      by_cases hji : j = i
      · subst j
        exact ⟨1,by simp [polynomialEmbedding_apply,uniformizer]⟩
      · exact ⟨0,by simp [polynomialEmbedding_apply,hji]⟩
    · exact leading_monomial _ _
  · by_cases hc : i.val < cut.val
    · suffices hn : pivotDegree A hA i ≠ 0 by simpa only [cutExponent,ite_eq_left hc] using Nat.one_le_iff_ne_zero.mpr hn
      intro hz
      obtain ⟨f,hf⟩ := pivot_mem A hA i i
      have hp : f * Polynomial.X = (pivot A hA i) i := by
        apply RatFunc.algebraMap_injective K
        simpa only [polynomialEmbedding_apply,
          cutExponent,ite_eq_left hc,pow_one,map_mul,uniformizer] using hf
      have hn := (pivot_leading A hA i).1
      rw [hz,← hp] at hn
      simp at hn
    · simp only [cutExponent,ite_eq_right hc,Nat.zero_le]

lemma orbit_cut_pivots (hN : 0 < N) (g : Matrix.SpecialLinearGroup (Fin N) K[X])
    (hg : ∀ i j : Fin N, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j)
    (cut : Fin N) : ∃ m : ℕ, ∀ i,
      diagonalExponents K N (actVertex K N hN g (cutVertex K N cut)) i = m+cutExponent N cut i := by
  let B := actVertex K N hN g (cutVertex K N cut)
  obtain ⟨a,b,he⟩ := actVertex_homothetic K N hN g (cutVertex K N cut)
  have hh := homothetic_action_pivots K N g hg (cutVertex K N cut) B a b he
  have hl : N-1 < N := by omega
  let last : Fin N := ⟨N-1,hl⟩
  have hc : ¬last.val < cut.val := by dsimp [last]; have := cut.isLt; omega
  have ht := hh last
  rw [diagonalExponents_cut] at ht
  simp only [cutExponent,ite_eq_right hc,zero_add] at ht
  refine ⟨diagonalExponents K N B last,fun i => ?_⟩
  change diagonalExponents K N B i = _
  have hi := hh i
  rw [diagonalExponents_cut] at hi
  omega

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.AffineWindow
open scoped BigOperators
variable {N : ℕ}

lemma sum_indicator_lt (r : ℕ) (hr : r ≤ N) :
    (∑ i : Fin N, if i.val < r then 1 else 0 : ℕ) = r := by
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,
    smul_eq_mul,mul_one,Fin.card_filter_val_lt,min_eq_right hr]

lemma sum_cut_shift (m : ℕ) (cut : Fin N) :
    (∑ i : Fin N, (m + (if i.val < cut.val then 1 else 0))) = N*m+cut.val := by
  rw [Finset.sum_add_distrib,sum_indicator_lt cut.val cut.isLt.le]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

lemma cutDegree_succ (hN : 0 < N) (t : ℕ) (i : Fin N) :
    cutDegree N (t+1) i = cutDegree N t i + if i.val = t%N then 1 else 0 := by
  have hm := Nat.mod_lt t hN
  have hi := i.isLt
  have hr := Nat.mod_add_div t N
  by_cases hs : t%N+1 < N
  · have hd : (t+1)/N = t/N := by
      rw [show t+1 = N*(t/N)+(t%N+1) by omega,Nat.mul_add_div hN,
        Nat.div_eq_of_lt hs,Nat.add_zero]
    have hl : (t+1)%N = t%N+1 := by rw [Nat.add_mod,Nat.mod_eq_of_lt (show 1<N by omega),Nat.mod_eq_of_lt hs]
    simp only [cutDegree,hd,hl]
    split_ifs <;> omega
  · have he : t%N+1 = N := by omega
    have hl : (t+1)%N = 0 := by
      rw [← Nat.mod_add_mod t N 1,he,Nat.mod_self]
    have hd : (t+1)/N = t/N+1 := by
      have hh := Nat.div_add_mod (t+1) N
      rw [hl] at hh
      nlinarith [Nat.div_add_mod t N]
    simp only [cutDegree,hd,hl,not_lt_zero,ite_false]
    split_ifs <;> omega

lemma cut_shift_identify (hN : 0 < N) (t m : ℕ) (cut : Fin N)
    (he : N*m+cut.val = t) :
    (fun i : Fin N => m+if i.val < cut.val then 1 else 0) = cutDegree N t := by
  have hd : t/N = m := by rw [← he,Nat.mul_add_div hN,Nat.div_eq_of_lt cut.isLt,Nat.add_zero]
  have hm : t%N = cut.val := by rw [← he,Nat.mul_add_mod,Nat.mod_eq_of_lt cut.isLt]
  funext i
  simp only [cutDegree,hd,hm]

lemma flag_height (a : Fin N → ℕ) (p : Equiv.Perm (Fin N)) (r : Fin (N+1)) :
    (∑ i : Fin N, (a i + (if (p.symm i).val < r.val then 1 else 0))) = (∑ i : Fin N, a i)+r.val := by
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i : Fin N, if (p.symm i).val < r.val then 1 else 0) =
        (∑ i : Fin N, if i.val < r.val then 1 else 0) :=
      p.symm.sum_comp (fun i => if i.val < r.val then 1 else 0)
    _ = r.val := sum_indicator_lt r.val (by omega : r.val ≤ N)

theorem inversion_zero_of_cut_flag (hN : 0 < N) (a : Fin N → ℕ)
    (p : Equiv.Perm (Fin N))
    (hc : ∀ r : Fin (N+1), ∃ m : ℕ, ∃ cut : Fin N, ∀ i,
      a i + (if (p.symm i).val < r.val then 1 else 0) = m+if i.val < cut.val then 1 else 0) :
    inversion (N := N) (List.ofFn (fun r => (N*a (p r)+(p r).val : ℕ) : Fin N → ℤ)) = 0 := by
  let c := ∑ i : Fin N, a i
  have hflag (r : Fin (N+1)) : ∀ i,
      a i + (if (p.symm i).val < r.val then 1 else 0) = cutDegree N (c+r.val) i := by
    obtain ⟨m,cut,hh⟩ := hc r
    have hs := congrArg (fun f : Fin N → ℕ => ∑ i, f i) (funext hh)
    rw [flag_height,sum_cut_shift] at hs
    have he := cut_shift_identify hN (c+r.val) m cut hs.symm
    intro i
    exact (hh i).trans (congr_fun he i)
  have hres (r : Fin N) : (p r).val = (c+r.val)%N := by
    have hs := hflag r.succ (p r)
    have ht := hflag r.castSucc (p r)
    simp only [Equiv.symm_apply_apply,Fin.val_succ,Fin.val_castSucc,Nat.lt_succ_self,ite_true,
      lt_self_iff_false,ite_false,Nat.add_zero] at hs ht
    rw [← Nat.add_assoc,cutDegree_succ hN,← ht] at hs
    split_ifs at hs with he
    · exact he
    · omega
  have hw (r : Fin N) : N*a (p r)+(p r).val = c+r.val := by
    have ht := hflag r.castSucc (p r)
    simp only [Equiv.symm_apply_apply,Fin.val_castSucc,lt_self_iff_false,ite_false,Nat.add_zero,
      cutDegree,hres r,lt_self_iff_false,ite_false,Nat.add_zero] at ht
    rw [ht,hres]
    exact Nat.div_add_mod _ _
  apply (inversion_zero_iff hN _).mpr
  apply List.pairwise_ofFn.mpr
  intro i j hij
  simp only [hw]
  have hi := i.isLt
  have hj := j.isLt
  constructor
  · exact_mod_cast (show c+i.val ≤ c+j.val by omega)
  · exact_mod_cast (show c+j.val < c+i.val+N by omega)

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

lemma opposed_pivots (hN : 0 < N) (A : Vertex K N) (hA : OpposedVertex K N hN A) :
    ∃ m : ℕ, ∃ cut : Fin N, ∀ i, diagonalExponents K N A i = m+cutExponent N cut i := by
  obtain ⟨g,hg,cut,rfl⟩ := hA
  obtain ⟨m,hm⟩ := orbit_cut_pivots K N hN g hg cut
  exact ⟨m,cut,hm⟩

theorem opposed_flag_common_orbit {M : ℕ} (hN : 0 < N) (B : Fin (M+1) → Vertex K N)
    (hanti : Antitone (fun r => (B r).val))
    (hbelow : ∀ r, level (shift K N) (B 0).val 1 ≤ (B r).val)
    (hop : ∀ r, OpposedVertex K N hN (B r)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
      (∀ i j : Fin N, j ≤ i → Polynomial.eval 0 (g i j) = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      ∃ cut : Fin (M+1) → Fin N, ∀ r,
        B r = actVertex K N hN g (cutVertex K N (cut r)) := by
  choose m cut hi using fun r => opposed_pivots K N hN (B r) (hop r)
  obtain ⟨g,hg,hv⟩ := zero_pivots_common_orbit K N hN B hanti hbelow cut m hi
  exact ⟨g,hg,cut,hv⟩

namespace FullChamber
variable {K N} {hN : 0 < N} (C : FullChamber K N hN)

theorem zero_of_cut_pivots
    (hc : ∀ r : Fin N, ∃ m : ℕ, ∃ cut : Fin N, ∀ i,
      diagonalExponents K N (C.vertex r) i = m+cutExponent N cut i) :
    C.length = 0 := by
  apply AffineWindow.inversion_zero_of_cut_flag hN
    (pivotDegree C.polynomialChamber.top C.polynomialChamber.hasTop) C.polynomialChamber.word
  intro r
  have he : ∃ m : ℕ, ∃ cut : Fin N, ∀ i,
      pivotDegree (C.stage r) (C.hasStage r) i = m+cutExponent N cut i := by
    by_cases hr : r.val < N
    · obtain ⟨m,cut,hh⟩ := hc ⟨r.val,hr⟩
      refine ⟨m,cut,?_⟩
      intro i
      have hstage : C.stage r = polynomialLattice K N (C.vertex ⟨r.val,hr⟩) := dite_eq_left hr
      simpa only [hstage,diagonalExponents] using hh i
    · have hre : r = Fin.last N := Fin.ext (by change r.val = N; have := r.isLt; omega)
      subst r
      obtain ⟨m,cut,hh⟩ := hc C.topIndex
      refine ⟨m+1,cut,?_⟩
      intro i
      have hp : pivotDegree (C.stage (Fin.last N)) (C.hasStage _) i =
          diagonalExponents K N (C.vertex C.topIndex) i+1 := by
        simpa only [C.stage_last,diagonalExponents] using
          pivotDegree_powerShift _ (polynomialHasPivots K N (C.vertex C.topIndex)) 1 i
      rw [hp]
      have hi := hh i
      omega
  obtain ⟨m,cut,he⟩ := he
  refine ⟨m,cut,?_⟩
  intro i
  exact (C.polynomialChamber.stage_degree r i).symm.trans (he i)

theorem zero_iff_vertexwise_opposed :
    C.length = 0 ↔ ∀ r, OpposedVertex K N hN (C.vertex r) := by
  constructor
  · intro hz
    obtain ⟨g,hg,c,hv⟩ := C.zero_common_orbit hz
    intro r
    refine ⟨g,?_,⟨(c+r.val)%N,Nat.mod_lt _ hN⟩,hv r⟩
    intro i j hij
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hg i j hij
  · intro hc
    exact C.zero_of_cut_pivots (fun r => opposed_pivots K N hN (C.vertex r) (hc r))

end FullChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders

lemma finite_chain_enumeration {P : Type} [PartialOrder P] [DecidableEq P] (s : Finset P) (hs : s.Nonempty)
    (hc : ∀ a ∈ s, ∀ b ∈ s, a ≤ b ∨ b ≤ a) :
    ∃ M : ℕ, ∃ B : Fin (M+1) → P, StrictAnti B ∧ Finset.univ.image B = s := by
  classical
  have hchain : IsChain (· ≤ ·) (s : Set P) := fun a ha b hb _ => hc a ha b hb
  let : LinearOrder (s : Set P) := hchain.linearOrder
  obtain ⟨M,hM⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Finset.card_pos.mpr hs))
  have hcard : Fintype.card (OrderDual (s : Set P)) = M+1 := by
    change Fintype.card {p // p ∈ s} = M+1
    simpa only [Fintype.card_coe] using hM
  let e := Fintype.orderIsoFinOfCardEq (OrderDual (s : Set P)) hcard
  let B (r : Fin (M+1)) : P := (e r).val
  refine ⟨M,B,?_,?_⟩
  · intro r t hrt
    exact e.strictMono hrt
  · ext a
    constructor
    · rintro ha
      obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp ha
      exact (e r).property
    · intro ha
      obtain ⟨r,hr⟩ := e.surjective (⟨a,ha⟩ : (s : Set P))
      exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,(show B r = a from congrArg Subtype.val hr)⟩

end CoboundaryExpanders

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

theorem common_orbit_iff_induced (hN : 0 < N) (s : Finset (Vertex K N)) :
    (∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
      (∀ i j : Fin N, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      ∃ A : Finset (Fin N),
        A.image (fun cut => actVertex K N hN g (cutVertex K N cut)) = s) ↔
    s ∈ (building K N).faces ∧ ∀ A ∈ s, OpposedVertex K N hN A := by
  classical
  constructor
  · rintro ⟨g,hg,A,rfl⟩
    constructor
    · change A.image (actVertex K N hN g ∘ cutVertex K N) ∈ _
      rw [← Finset.image_image]
      exact actVertex_face K N hN g _ ((building K N).downward
        (baseChamber_face K N) (Finset.image_subset_image (Finset.subset_univ A)))
    · intro B hB
      obtain ⟨cut,_,rfl⟩ := Finset.mem_image.mp hB
      exact ⟨g,hg,cut,rfl⟩
  · rintro ⟨hs,hop⟩
    by_cases hempty : s = ∅
    · subst s
      refine ⟨1,?_,∅,Finset.image_empty _⟩
      intro i j hij
      simp only [Matrix.SpecialLinearGroup.coe_one,Matrix.one_apply]
      split_ifs <;> simp
    · obtain ⟨M,B,hanti,hB⟩ := CoboundaryExpanders.finite_chain_enumeration s
        (Finset.nonempty_iff_ne_empty.mpr hempty) hs.1
      have hmem (r : Fin (M+1)) : B r ∈ s := by
        rw [← hB]
        exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
      have hbelow (r : Fin (M+1)) : level (shift K N) (B 0).val 1 ≤ (B r).val := by
        simpa only [level_succ,level_zero] using hs.2 (B 0) (hmem 0) (B r) (hmem r)
      obtain ⟨g,hg,cut,hv⟩ := opposed_flag_common_orbit K N hN B
        (fun r t hrt => hanti.antitone hrt) hbelow (fun r => hop (B r) (hmem r))
      refine ⟨g,?_,Finset.univ.image cut,?_⟩
      · intro i j hij
        simpa only [Polynomial.coeff_zero_eq_eval_zero] using hg i j hij
      · rw [Finset.image_image]
        convert hB using 1
        all_goals try with_reducible_and_instances rfl
        apply Finset.image_congr
        intro r hr
        exact (hv r).symm

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma intervalNormalize_homothetic (hN : 0 < N) (A : Vertex K N) (B : ResidueInterval K N A) :
    Homothetic (shift K N) B.val (intervalNormalize K N hN A B).val :=
  (interval_exists_normalized K N hN A B).choose_spec

lemma intervalNormalize_vertex (hN : 0 < N) (A D : Vertex K N)
    (hd : shift K N A.val ≤ D.val) (hu : D.val ≤ A.val) :
    intervalNormalize K N hN A ⟨D.val,hd,hu⟩ = D := by
  apply ((homothetic_normalized_iff (shift K N) (standard K N) (shift_standard_le K N) _ _).mp)
  exact homothetic_symm _ (intervalNormalize_homothetic K N hN A ⟨D.val,hd,hu⟩)

lemma intervalNormalize_injOn (hN : 0 < N) (A : Vertex K N) :
    Set.InjOn (intervalNormalize K N hN A) {B | B.val ≠ shift K N A.val} := by
  intro B hB D hD he
  have hb : ¬ B.val ≤ shift K N A.val := fun h => hB (le_antisymm h B.property.1)
  have hd : ¬ D.val ≤ shift K N A.val := fun h => hD (le_antisymm h D.property.1)
  let VB : AffineLattices.Vertex (shift K N) A.val :=
    ⟨B.val,B.property.2,hb,⟨1,B.property.1⟩,(shift K N).monotone B.property.2 |>.trans B.property.1⟩
  let VD : AffineLattices.Vertex (shift K N) A.val :=
    ⟨D.val,D.property.2,hd,⟨1,D.property.1⟩,(shift K N).monotone D.property.2 |>.trans D.property.1⟩
  have hh : Homothetic (shift K N) VB.val VD.val :=
    homothetic_trans _ (intervalNormalize_homothetic K N hN A B)
      (he ▸ homothetic_symm _ (intervalNormalize_homothetic K N hN A D))
  have hBD := (homothetic_normalized_iff (shift K N) A.val (shift_le_self K N A.val) VB VD).mp hh
  exact Subtype.ext (congrArg (fun Z : AffineLattices.Vertex (shift K N) A.val => Z.val) hBD)

lemma intervalNormalize_face (hN : 0 < N) (A : Vertex K N)
    (s : Finset (ResidueInterval K N A))
    (hc : ∀ B ∈ s, ∀ D ∈ s, B ≤ D ∨ D ≤ B) :
    s.image (intervalNormalize K N hN A) ∈ (building K N).faces := by
  classical
  apply (isFace_iff_compatible (shift K N) (standard K N) (shift_standard_le K N) _).mpr
  intro B hB D hD
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hD
  apply compatible_homothetic _ (intervalNormalize_homothetic K N hN A b)
    (intervalNormalize_homothetic K N hN A d)
  rcases hc b hb d hd with hBD | hDB
  · apply compatible_symm
    exact ⟨0,0,(shift K N).monotone d.property.2 |>.trans b.property.1,hBD⟩
  · exact ⟨0,0,(shift K N).monotone b.property.2 |>.trans d.property.1,hDB⟩

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma covBy_finrank {U W : Submodule K V} (h : U ⋖ W) :
    finrank K W = finrank K U + 1 := by
  obtain ⟨v,hvW,hvU⟩ := SetLike.exists_of_lt h.lt
  have hle : U ⊔ K ∙ v ≤ W := sup_le h.le ((Submodule.span_singleton_le_iff_mem v W).mpr hvW)
  have hlt : U < U ⊔ K ∙ v := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hvU (he.symm ▸ (show v ∈ U ⊔ K ∙ v from (show K ∙ v ≤ U ⊔ K ∙ v from le_sup_right) (Submodule.mem_span_singleton_self v))))
  have he : U ⊔ K ∙ v = W := (h.eq_or_eq le_sup_left hle).resolve_left (ne_of_gt hlt)
  rw [← he,Submodule.finrank_sup_span_singleton hvU]

theorem ambient_chain_complete_flag (s : Finset (Submodule K V))
    (hc : ∀ A ∈ s, ∀ B ∈ s, A ≤ B ∨ B ≤ A) :
    ∃ F : Fin (finrank K V + 1) → Submodule K V,
      StrictMono F ∧ (∀ i, finrank K (F i) = i.val) ∧
      F 0 = ⊥ ∧ F (Fin.last (finrank K V)) = ⊤ ∧
      ∀ W ∈ s, ∃ i, F i = W := by
  classical
  have hc' : ∀ A ∈ insert (⊥ : Submodule K V) s, ∀ B ∈ insert ⊥ s, A ≤ B ∨ B ≤ A := by
    intro A hA B hB
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact Or.inl bot_le
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact Or.inr bot_le
    exact hc A hA B hB
  obtain ⟨M,B,hB,hBi⟩ := finite_chain_enumeration (insert (⊥ : Submodule K V) s)
    (Finset.insert_nonempty _ _) hc'
  let c : LTSeries (Submodule K V) := LTSeries.mk M (fun i => B i.rev)
    (fun i j hij => hB (Fin.rev_lt_rev.mpr hij))
  obtain ⟨t,e,hte,ht0,htN⟩ := c.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
  have htstrict : StrictMono t := Fin.strictMono_iff_lt_succ.mpr (fun i => (t.step i).lt)
  have htrank (i : Fin (t.length+1)) : finrank K (t i) = i.val := by
    induction i using Fin.induction with
    | zero => change finrank K t.head = 0; rw [ht0,finrank_bot]
    | succ i ih =>
      rw [covBy_finrank (t.step i),ih]
      rfl
  have hlen : t.length = finrank K V := by
    have hh := htrank (Fin.last t.length)
    change finrank K t.last = t.length at hh
    rw [htN,finrank_top] at hh
    exact hh.symm
  let F (i : Fin (finrank K V+1)) : Submodule K V :=
    t (Fin.cast (congrArg (·+1) hlen.symm) i)
  refine ⟨F,?_,?_,?_,?_,?_⟩
  · exact fun i j hij => htstrict (show Fin.cast _ i < Fin.cast _ j from hij)
  · intro i
    exact htrank _
  · simpa only [F,Fin.cast_zero,RelSeries.head] using ht0
  · simpa only [F,Fin.cast_last,RelSeries.last] using htN
  · intro W hW
    have hm : W ∈ Finset.univ.image B := by rw [hBi]; exact Finset.mem_insert_of_mem hW
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hm
    refine ⟨Fin.cast (congrArg (·+1) hlen) (e r.rev),?_⟩
    change t (Fin.cast _ (Fin.cast _ (e r.rev))) = W
    have hcanc : Fin.cast (congrArg (·+1) hlen.symm)
        (Fin.cast (congrArg (·+1) hlen) (e r.rev)) = e r.rev := Fin.ext rfl
    apply (congrArg t hcanc).trans
    have hh := congr_fun hte r.rev
    change t (e r.rev) = B r.rev.rev at hh
    simpa only [Fin.rev_rev,hr] using hh

end CoboundaryExpanders

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices Module
variable (K : Type) [Field K] (N : ℕ)

theorem ambient_face_extend (hN : 0 < N) (s : Finset (Vertex K N))
    (hs : s ∈ (building K N).faces) :
    ∃ t : Finset (Vertex K N), s ⊆ t ∧ t ∈ (building K N).faces ∧ t.card = N := by
  classical
  by_cases hempty : s = ∅
  · subst s
    exact ⟨baseChamber K N,Finset.empty_subset _,baseChamber_face K N,baseChamber_card K N⟩
  obtain ⟨M,B,hB,hBi⟩ := CoboundaryExpanders.finite_chain_enumeration s
    (Finset.nonempty_iff_ne_empty.mpr hempty) hs.1
  have hbmem (r : Fin (M+1)) : B r ∈ s := by
    rw [← hBi]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  let A := B 0
  let D (r : Fin (M+1)) : ResidueInterval K N A :=
    ⟨(B r).val,hs.2 (B 0) (hbmem 0) (B r) (hbmem r),hB.antitone (Fin.zero_le r)⟩
  let e := residueIntervalIso K N A
  have hc : ∀ W ∈ Finset.univ.image (fun r => e (D r)),
      ∀ Z ∈ Finset.univ.image (fun r => e (D r)), W ≤ Z ∨ Z ≤ W := by
    intro W hW Z hZ
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hZ
    rcases le_total r t with hrt | htr
    · exact Or.inr (e.monotone (hB.antitone hrt))
    · exact Or.inl (e.monotone (hB.antitone htr))
  have hfull : ∃ F : Fin (N+1) → Submodule K (Fin N → K),
      StrictMono F ∧ (∀ i, finrank K (F i) = i.val) ∧
      F 0 = ⊥ ∧ F (Fin.last N) = ⊤ ∧
      ∀ W ∈ Finset.univ.image (fun r => e (D r)), ∃ i, F i = W := by
    have hdim : finrank K (Fin N → K) = N := Module.finrank_fin_fun K
    have hh := CoboundaryExpanders.ambient_chain_complete_flag (K := K) (V := Fin N → K)
      (Finset.univ.image (fun r => e (D r))) hc
    rw [hdim] at hh
    exact hh
  obtain ⟨F,hF,hFr,hF0,hFN,hFs⟩ := hfull
  let G (i : Fin N) : ResidueInterval K N A := e.symm (F i.succ)
  have hG : StrictMono G := fun i j hij => e.symm.strictMono (hF (Fin.succ_lt_succ_iff.mpr hij))
  let L : ResidueInterval K N A := ⟨shift K N A.val,le_rfl,shift_le_self K N A.val⟩
  have heL : e L = ⊥ := by
    apply le_antisymm _ bot_le
    have hh : L ≤ e.symm ⊥ := (e.symm ⊥).property.1
    simpa only [e.apply_symm_apply] using e.monotone hh
  have hGbot (i : Fin N) : (G i).val ≠ shift K N A.val := by
    intro he
    have hh : G i = L := Subtype.ext he
    have hf : F i.succ = ⊥ := by
      simpa only [G,e.apply_symm_apply,heL] using congrArg e hh
    have hr := hFr i.succ
    rw [hf,finrank_bot] at hr
    have hi : i.succ.val = i.val+1 := rfl
    omega
  let v (i : Fin N) := intervalNormalize K N hN A (G i)
  have hv : Function.Injective v := by
    intro i j hij
    exact hG.injective (intervalNormalize_injOn K N hN A (hGbot i) (hGbot j) hij)
  have htface : Finset.univ.image v ∈ (building K N).faces := by
    have hh := intervalNormalize_face K N hN A (Finset.univ.image G) (by
      intro Y hY Z hZ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hY
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hZ
      rcases le_total i j with hij | hji
      · exact Or.inl (hG.monotone hij)
      · exact Or.inr (hG.monotone hji))
    simpa only [Finset.image_image,Function.comp_def,v] using hh
  refine ⟨Finset.univ.image v,?_,htface,by rw [Finset.card_image_of_injective _ hv]; simp⟩
  intro W hW
  have hBW : W ∈ Finset.univ.image B := by rw [hBi]; exact hW
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hBW
  obtain ⟨j,hj⟩ := hFs (e (D r)) (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩)
  have hj0 : j ≠ 0 := by
    intro he
    subst j
    have hh : D r = L := e.injective (by simpa only [heL,hF0] using hj.symm)
    have hval := congrArg (fun Y : ResidueInterval K N A => Y.val) hh
    apply vertex_normalized (shift K N) (standard K N) (B r)
    change (B r).val = shift K N A.val at hval
    rw [hval]
    exact (shift K N).monotone (vertex_le _ _ A)
  have hjpos : 0 < j.val := by
    have hh : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
    omega
  let i : Fin N := ⟨j.val-1,by have := j.isLt; omega⟩
  have hi : i.succ = j := Fin.ext (by simp only [Fin.val_succ,i]; omega)
  have hGi : G i = D r := by
    apply e.injective
    change e (e.symm (F i.succ)) = e (D r)
    rw [e.apply_symm_apply,hi,hj]
  refine Finset.mem_image.mpr ⟨i,Finset.mem_univ _,?_⟩
  change intervalNormalize K N hN A (G i) = B r
  rw [hGi]
  exact intervalNormalize_vertex K N hN A (B r) (D r).property.1 (D r).property.2

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders
lemma finite_chain_enumeration_of_card {P : Type} [PartialOrder P] [DecidableEq P]
    {N : ℕ} (s : Finset P) (hs : s.card = N)
    (hc : ∀ a ∈ s, ∀ b ∈ s, a ≤ b ∨ b ≤ a) :
    ∃ B : Fin N → P, StrictAnti B ∧ Finset.univ.image B = s := by
  classical
  have hchain : IsChain (· ≤ ·) (s : Set P) := fun a ha b hb _ => hc a ha b hb
  let : LinearOrder (s : Set P) := hchain.linearOrder
  have hcard : Fintype.card (OrderDual (s : Set P)) = N := by
    change Fintype.card {p // p ∈ s} = N
    simpa only [Fintype.card_coe] using hs
  let e := Fintype.orderIsoFinOfCardEq (OrderDual (s : Set P)) hcard
  let B (r : Fin N) : P := (e r).val
  refine ⟨B,fun _ _ h => e.strictMono h,?_⟩
  ext a
  constructor
  · rintro ha
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp ha
    exact (e r).property
  · intro ha
    obtain ⟨r,hr⟩ := e.surjective (⟨a,ha⟩ : (s : Set P))
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,congrArg Subtype.val hr⟩
end CoboundaryExpanders

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)
namespace FullChamber
variable {K N} {hN : 0 < N} (C : FullChamber K N hN)
lemma mem_face (r : Fin N) : C.vertex r ∈ C.face := by
  classical
  exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
lemma vertex_injective : Function.Injective C.vertex := by
  intro i j h
  exact C.strict.injective (congrArg Subtype.val h)
lemma card_face : C.face.card = N := by
  classical
  rw [face,Finset.card_image_of_injective _ C.vertex_injective]
  simp
lemma face_mem : C.face ∈ (building K N).faces := by
  classical
  constructor
  · intro A hA B hB
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    rcases le_total i j with hij | hji
    · exact Or.inr (C.strict.antitone hij)
    · exact Or.inl (C.strict.antitone hji)
  · intro A hA B hB
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    exact ((shift K N).monotone (C.strict.antitone (show C.topIndex ≤ i from Nat.zero_le _))).trans (C.lower j)
end FullChamber

theorem ambient_face_in_chamber (hN : 0 < N) (s : Finset (Vertex K N))
    (hs : s ∈ (building K N).faces) :
    ∃ C : FullChamber K N hN, s ⊆ C.face := by
  classical
  obtain ⟨t,hst,ht,htN⟩ := ambient_face_extend K N hN s hs
  obtain ⟨B,hB,hBt⟩ := CoboundaryExpanders.finite_chain_enumeration_of_card t htN ht.1
  have hmem (r : Fin N) : B r ∈ t := by
    rw [← hBt]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  let C : FullChamber K N hN := ⟨B,hB,fun r => ht.2 _ (hmem ⟨0,hN⟩) _ (hmem r)⟩
  refine ⟨C,?_⟩
  change s ⊆ Finset.univ.image B
  rw [hBt]
  exact hst

lemma codistanceStage_mono (hN : 0 < N) : Monotone (codistanceStage K N hN) := by
  rintro m n hmn s ⟨C,hC,hs⟩
  exact ⟨C,hC.trans hmn,hs⟩

lemma codistanceStage_downward (hN : 0 < N) (m : ℕ) {s t : Finset (Vertex K N)}
    (hs : s ∈ codistanceStage K N hN m) (ht : t ⊆ s) :
    t ∈ codistanceStage K N hN m := by
  obtain ⟨C,hC,hs⟩ := hs
  exact ⟨C,hC,ht.trans hs⟩

lemma codistanceStage_exhaust (hN : 0 < N) :
    (⋃ m, codistanceStage K N hN m) = (building K N).faces := by
  ext s
  constructor
  · intro hs
    obtain ⟨m,C,_,hs⟩ := Set.mem_iUnion.mp hs
    exact (building K N).downward C.face_mem hs
  · intro hs
    obtain ⟨C,hC⟩ := ambient_face_in_chamber K N hN s hs
    exact Set.mem_iUnion.mpr ⟨C.length,C,le_rfl,hC⟩

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)
lemma actVertex_injective (hN : 0 < N) (g : Matrix.SpecialLinearGroup (Fin N) K[X]) :
    Function.Injective (actVertex K N hN g) :=
  mapVertex_injective (shift K N) (standard K N) (shift_standard_le K N)
    (standard_not_le_shift K N hN) (positiveAction K N g) (positiveAction_shift K N g)
    (positiveAction_upper K N g) (positiveAction_lower K N g)

lemma fullChamber_of_face_card (hN : 0 < N) (s : Finset (Vertex K N))
    (hs : s ∈ (building K N).faces) (hcard : s.card = N) :
    ∃ C : FullChamber K N hN, C.face = s := by
  classical
  obtain ⟨B,hB,hBs⟩ := CoboundaryExpanders.finite_chain_enumeration_of_card s hcard hs.1
  have hmem (r : Fin N) : B r ∈ s := by
    rw [← hBs]
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  exact ⟨⟨B,hB,fun r => hs.2 _ (hmem ⟨0,hN⟩) _ (hmem r)⟩,hBs⟩

theorem codistanceStage_zero (hN : 0 < N) (s : Finset (Vertex K N)) :
    s ∈ codistanceStage K N hN 0 ↔
    s ∈ (building K N).faces ∧ ∀ A ∈ s, OpposedVertex K N hN A := by
  classical
  constructor
  · rintro ⟨C,hC,hs⟩
    refine ⟨(building K N).downward C.face_mem hs,?_⟩
    intro A hA
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp (hs hA)
    exact C.zero_iff_vertexwise_opposed.mp (Nat.eq_zero_of_le_zero hC) r
  · intro hs
    obtain ⟨g,hg,A,hA⟩ := (common_orbit_iff_induced K N hN s).mpr hs
    let f (i : Fin N) := actVertex K N hN g (cutVertex K N i)
    let t := Finset.univ.image f
    have ht : t ∈ (building K N).faces := by
      have hh := actVertex_face K N hN g _ (baseChamber_face K N)
      simpa only [baseChamber,Finset.image_image,Function.comp_def,t,f] using hh
    have htN : t.card = N := by
      change (Finset.univ.image (actVertex K N hN g ∘ cutVertex K N)).card = N
      rw [Finset.card_image_of_injective _ ((actVertex_injective K N hN g).comp (cutVertex_injective K N))]
      simp
    obtain ⟨C,hC⟩ := fullChamber_of_face_card K N hN t ht htN
    refine ⟨C,?_,?_⟩
    · apply Nat.le_zero.mpr
      apply C.zero_iff_vertexwise_opposed.mpr
      intro r
      have hm : C.vertex r ∈ t := hC ▸ C.mem_face r
      obtain ⟨cut,_,he⟩ := Finset.mem_image.mp hm
      exact ⟨g,hg,cut,he.symm⟩
    · rw [hC,← hA]
      exact Finset.image_subset_image (Finset.subset_univ A)

end CoboundaryExpanders.RationalLattices

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Chambers
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bounded and full chambers, codistance, descent cores, and their affine-window descriptions.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))
lemma rotateStage_castSucc (hN : 0 < N) (r : Fin N) :
    C.rotateStage hN r.castSucc = C.stage r.succ := by
  apply (dite_eq_left r.isLt).trans
  rfl
lemma rotateStage_last (hN : 0 < N) :
    C.rotateStage hN (Fin.last N) = powerShift (C.stage (C.nextIndex hN)) 1 := by
  exact dite_eq_right (Nat.lt_irrefl N)

lemma step_degree (r : Fin N) (i : Fin N) :
    pivotDegree (C.stage r.succ) (C.hasStage r.succ) i =
      pivotDegree (C.stage r.castSucc) (C.hasStage r.castSucc) i +
        if i = C.word r then 1 else 0 := by
  classical
  rw [C.stage_degree,C.stage_degree]
  by_cases he : i = C.word r
  · subst i
    simp
  · have hne : (C.word.symm i).val ≠ r.val := by
      intro hh
      apply he
      have hi := congrArg C.word (Fin.ext hh)
      simpa only [Equiv.apply_symm_apply] using hi
    simp only [Fin.val_succ,Fin.val_castSucc,ite_eq_right he]
    split_ifs <;> omega
lemma word_eq_iff (r : Fin N) (i : Fin N) : C.word r = i ↔
    pivotDegree (C.stage r.castSucc) (C.hasStage r.castSucc) i <
      pivotDegree (C.stage r.succ) (C.hasStage r.succ) i := by
  rw [C.step_degree]
  by_cases hi : i = C.word r
  · simp [hi]
  · simp [hi,Ne.symm hi]

variable {M : ℕ}
lemma rotate_word (C : ResidueChamber (K := K) (N := M+1)) (r : Fin (M+1)) :
    (C.rotate (Nat.zero_lt_succ M)).word r = C.word (finRotate (M+1) r) := by
  classical
  apply ((C.rotate (Nat.zero_lt_succ M)).word_eq_iff r _).mpr
  by_cases hr : r.val < M
  · have he : finRotate (M+1) r = ⟨r.val+1,by omega⟩ := finRotate_of_lt hr
    rw [he]
    let r' : Fin (M+1) := ⟨r.val+1,by omega⟩
    change pivotDegree (C.rotateStage (Nat.zero_lt_succ M) r.castSucc) _ (C.word r') <
      pivotDegree (C.rotateStage (Nat.zero_lt_succ M) r.succ) _ (C.word r')
    have hs0 : C.rotateStage (Nat.zero_lt_succ M) r.castSucc = C.stage r'.castSucc := by
      exact C.rotateStage_castSucc _ r
    have hs1 : C.rotateStage (Nat.zero_lt_succ M) r.succ = C.stage r'.succ := by
      exact dite_eq_left (show r.succ.val < M+1 from by simp only [Fin.val_succ]; omega)
    simp only [hs0,hs1]
    exact (C.word_eq_iff r' _).mp rfl
  · have hr' : r = Fin.last M := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
    subst r
    rw [finRotate_last]
    change pivotDegree (C.rotateStage (Nat.zero_lt_succ M) (Fin.last M).castSucc) _ (C.word 0) <
      pivotDegree (C.rotateStage (Nat.zero_lt_succ M) (Fin.last M).succ) _ (C.word 0)
    have he0 : C.rotateStage (Nat.zero_lt_succ M) (Fin.last M).castSucc = powerShift C.top 1 := by
      rw [C.rotateStage_castSucc]
      exact C.terminal
    have he1 : C.rotateStage (Nat.zero_lt_succ M) (Fin.last M).succ =
        powerShift (C.stage (C.nextIndex (Nat.zero_lt_succ M))) 1 := C.rotateStage_last _
    simp only [he0,he1]
    have hp0 := pivotDegree_powerShift C.top C.hasTop 1 (C.word 0)
    have hp1 := pivotDegree_powerShift (C.stage (C.nextIndex (Nat.zero_lt_succ M)))
      (C.hasStage _) 1 (C.word 0)
    simp only [nextIndex] at hp1 ⊢
    have hh := C.stage_degree (C.nextIndex (Nat.zero_lt_succ M)) (C.word 0)
    simp only [Equiv.symm_apply_apply,nextIndex,Fin.val_mk,Fin.val_zero,
      show (0:ℕ) < 1 by omega,ite_true] at hh
    omega

lemma rotate_window_castSucc (C : ResidueChamber (K := K) (N := M+1)) (r : Fin M) :
    (C.rotate (Nat.zero_lt_succ M)).window r.castSucc = C.window r.succ := by
  have he : finRotate (M+1) r.castSucc = r.succ := finRotate_of_lt r.isLt
  simp only [window,C.rotate_word,he]
  change (((M+1)*pivotDegree (C.stage (C.nextIndex (Nat.zero_lt_succ M))) (C.hasStage _) (C.word r.succ)+
    (C.word r.succ).val : ℕ) : ℤ) = _
  rw [C.stage_degree]
  simp only [Equiv.symm_apply_apply,nextIndex,Fin.val_mk,Fin.val_succ,show ¬r.val+1 < 1 by omega,ite_false,Nat.add_zero]
lemma rotate_window_last (C : ResidueChamber (K := K) (N := M+1)) :
    (C.rotate (Nat.zero_lt_succ M)).window (Fin.last M) = C.window 0 + (M+1) := by
  simp only [window,C.rotate_word,finRotate_last]
  change (((M+1)*pivotDegree (C.stage (C.nextIndex (Nat.zero_lt_succ M))) (C.hasStage _) (C.word 0)+
    (C.word 0).val : ℕ) : ℤ) = _
  rw [C.stage_degree]
  simp only [Equiv.symm_apply_apply,nextIndex,Fin.val_mk,Fin.val_zero,show (0:ℕ) < 1 by omega,ite_true]
  push_cast
  ring
lemma window_mod (_ : 0 < N) (r : Fin N) : C.window r % N = (C.word r).val := by
  unfold window
  push_cast
  have h0 : 0 ≤ ((C.word r).val : ℤ) := Int.natCast_nonneg _
  have hlt : ((C.word r).val : ℤ) < N := by exact_mod_cast (C.word r).isLt
  simp only [Int.add_emod,Int.mul_emod_right,Int.zero_add,Int.emod_eq_of_lt h0 hlt]

theorem rotate_length (C : ResidueChamber (K := K) (N := M+1)) :
    (C.rotate (Nat.zero_lt_succ M)).length = C.length := by
  unfold length
  rw [List.ofFn_succ',List.concat_eq_append]
  simp only [C.rotate_window_castSucc,C.rotate_window_last]
  rw [List.ofFn_succ (f := C.window)]
  apply AffineWindow.inversion_rotate (Nat.zero_lt_succ M)
  intro b hb
  obtain ⟨r,hr⟩ := List.mem_ofFn.mp hb
  rw [← hr,C.window_mod (Nat.zero_lt_succ M),C.window_mod (Nat.zero_lt_succ M)]
  intro he
  have hh : (0 : Fin (M+1)) = r.succ := C.word.injective (Fin.ext (by exact_mod_cast he))
  have hv := congrArg Fin.val hh
  simp only [Fin.val_zero,Fin.val_succ] at hv
  omega

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma combination_lowest_pivot (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (f : Fin N → K[X]) (i : Fin N)
    (hl : Leading (∑ j, f j • b j) i (a i)) :
    f i ≠ 0 ∧ (f i).natDegree = 0 ∧
      ∀ j, N*a i+i.val < N*a j+j.val → f j = 0 := by
  classical
  let s := Finset.univ.filter (fun j => f j ≠ 0)
  have hs : s.Nonempty := by
    by_contra hn
    have hz : ∀ j, f j = 0 := by
      intro j
      by_contra hj
      exact hn ⟨j,by simp [s,hj]⟩
    have he : (∑ j, f j • b j) = 0 := by simp [hz]
    exact leading_ne_zero hl he
  let w (j : Fin N) := N*(a j+(f j).natDegree)+j.val
  obtain ⟨j,hjs,hmax⟩ := Finset.exists_max_image s w hs
  have hj : f j ≠ 0 := (Finset.mem_filter.mp hjs).2
  have hl' := leading_combination_max b a hb f j hj
    (fun k hk => hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩))
  obtain ⟨hji,he⟩ := leading_unique hl' hl
  subst j
  have hdegree : (f i).natDegree = 0 := by omega
  refine ⟨hj,hdegree,?_⟩
  intro j hlt
  by_contra hjz
  have hh := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjz⟩)
  dsimp only [w] at hh
  rw [hdegree,Nat.add_zero] at hh
  have hh' := Nat.mul_le_mul_left N (Nat.le_add_right (a j) (f j).natDegree)
  omega

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma diagonalChamber_word (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (π : Equiv.Perm (Fin N)) :
    (diagonalChamber b a hb π).word = π := by
  classical
  apply Equiv.ext
  intro r
  apply ((diagonalChamber b a hb π).word_eq_iff r (π r)).mpr
  change pivotDegree (diagonalModule b (wordPrefix π r.castSucc)) _ (π r) <
    pivotDegree (diagonalModule b (wordPrefix π r.succ)) _ (π r)
  rw [diagonal_pivotDegree b a hb,diagonal_pivotDegree b a hb]
  simp [wordPrefix]

lemma diagonalChamber_window (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (π : Equiv.Perm (Fin N)) (r : Fin N) :
    (diagonalChamber b a hb π).window r = (N*a (π r)+(π r).val : ℕ) := by
  unfold ResidueChamber.window
  rw [diagonalChamber_word]
  change ((N*pivotDegree (Submodule.span K[X] (Set.range b)) _ (π r)+(π r).val : ℕ) : ℤ) = _
  rw [span_pivotDegree b a hb]

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))

theorem diagonal_representation :
    ∃ b : Fin N → V K N,
      (∀ i, Leading (b i) i (pivotDegree C.top C.hasTop i)) ∧
      (∀ i, (b i i).coeff (pivotDegree C.top C.hasTop i) = 1) ∧
      Submodule.span K[X] (Set.range b) = C.top ∧
      ∀ r, C.stage r = diagonalModule b (wordPrefix C.word r) := by
  classical
  obtain ⟨b,hmem,hlead,hmonic,hstage⟩ := simultaneous_minimal_basis C.top C.hasTop C.stage
    C.hasStage C.strict.antitone C.initial C.lower
  refine ⟨b,hlead,hmonic,?_,?_⟩
  · have hh := hstage 0
    simpa only [C.initial,ite_true] using hh
  · intro r
    rw [← hstage r]
    unfold diagonalModule
    congr 2
    funext i
    rw [C.stage_degree]
    simp only [diagonalFamily,wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> simp_all

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {M : ℕ}

lemma prefix_first_swap (π : Equiv.Perm (Fin (M+2))) (r : Fin (M+3)) (hr : r.val ≠ 1) :
    wordPrefix ((Equiv.swap 0 (1 : Fin (M+2))).trans π) r = wordPrefix π r := by
  classical
  ext i
  simp only [wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [Equiv.symm_trans,Equiv.trans_apply,Equiv.symm_swap]
  by_cases he0 : π.symm i = 0
  · rw [he0,Equiv.swap_apply_left]
    have h1 : (1 : Fin (M+2)).val = 1 := by rfl
    simp only [h1,Fin.val_zero]
    omega
  · by_cases he1 : π.symm i = 1
    · rw [he1,Equiv.swap_apply_right]
      have h1 : (1 : Fin (M+2)).val = 1 := by rfl
      simp only [h1,Fin.val_zero]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne he0 he1]

namespace ResidueChamber

theorem first_panel_lower (C : ResidueChamber (K := K) (N := M+2))
    (hdesc : C.window 1 < C.window 0) :
    ∃ D : ResidueChamber (K := K) (N := M+2),
      D.top = C.top ∧ (∀ r : Fin (M+3), r.val ≠ 1 → D.stage r = C.stage r) ∧
      D.stage 1 ≠ C.stage 1 ∧ D.length + 1 = C.length := by
  classical
  obtain ⟨b,hb,_,htop,hstage⟩ := C.diagonal_representation
  let π := (Equiv.swap 0 (1 : Fin (M+2))).trans C.word
  let D := diagonalChamber b (pivotDegree C.top C.hasTop) hb π
  have hwin (r : Fin (M+2)) : D.window r = C.window (Equiv.swap 0 (1 : Fin (M+2)) r) := by
    rw [diagonalChamber_window]
    rfl
  have h0 : D.window 0 = C.window 1 := by rw [hwin,Equiv.swap_apply_left]
  have h1 : D.window (1 : Fin (M+2)) = C.window 0 := by rw [hwin,Equiv.swap_apply_right]
  have hrest (i : Fin M) : D.window i.succ.succ = C.window i.succ.succ := by
    rw [hwin,Equiv.swap_apply_of_ne_of_ne]
    · intro he
      have h := congrArg Fin.val he
      simp only [Fin.val_succ,Fin.val_zero] at h
      omega
    · intro he
      have h := congrArg Fin.val he
      change i.val+1+1 = 1 at h
      omega
  refine ⟨D,htop,?_,?_,?_⟩
  · intro r hr
    change diagonalModule b (wordPrefix π r) = C.stage r
    rw [hstage,prefix_first_swap C.word r hr]
  · intro he
    have hpre : wordPrefix π (1 : Fin (M+3)) = wordPrefix C.word (1 : Fin (M+3)) := by
      apply diagonal_injective b _ hb
      change D.stage 1 = _
      rw [he,hstage]
    have hh : C.word 0 ∈ wordPrefix C.word (1 : Fin (M+3)) := by simp [wordPrefix]
    rw [← hpre] at hh
    have hh' := (Finset.mem_filter.mp hh).2
    simp only [π,Equiv.symm_trans,Equiv.trans_apply,Equiv.symm_swap,
      Equiv.symm_apply_apply,Equiv.swap_apply_left] at hh'
    have hval : (1 : Fin (M+2)).val = 1 := rfl
    have hrval : (1 : Fin (M+3)).val = 1 := rfl
    rw [hval,hrval] at hh'
    exact (lt_irrefl _ hh')
  · have hlistD : List.ofFn D.window = D.window 0 :: D.window 1 ::
        List.ofFn (fun i : Fin M => D.window i.succ.succ) := by
      rw [List.ofFn_succ,List.ofFn_succ]
      rfl
    have hlistC : List.ofFn C.window = C.window 0 :: C.window 1 ::
        List.ofFn (fun i : Fin M => C.window i.succ.succ) := by
      rw [List.ofFn_succ,List.ofFn_succ]
      rfl
    unfold length
    rw [hlistD,hlistC,h0,h1,show (fun i : Fin M => D.window i.succ.succ) =
      (fun i : Fin M => C.window i.succ.succ) from funext hrest]
    symm
    apply AffineWindow.inversion_adjacent_increase (by omega : 0 < M+2) []
    · rw [C.window_mod (by omega),C.window_mod (by omega)]
      intro he
      have h := C.word.injective (Fin.ext (by exact_mod_cast he))
      have hv := congrArg Fin.val h
      change 1 = 0 at hv
      omega
    · exact hdesc

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial
variable {K : Type} [Field K] {N : ℕ}
lemma ext_stage {C D : ResidueChamber (K := K) (N := N)}
    (ht : C.top = D.top) (hs : C.stage = D.stage) : C = D := by
  cases C
  cases D
  simp_all
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))
lemma scale_word (m : ℕ) (r : Fin N) : (C.scale m).word r = C.word r := by
  apply ((C.scale m).word_eq_iff r _).mpr
  change pivotDegree (powerShift (C.stage r.castSucc) m) _ (C.word r) <
    pivotDegree (powerShift (C.stage r.succ) m) _ (C.word r)
  rw [pivotDegree_powerShift _ (C.hasStage r.castSucc),pivotDegree_powerShift _ (C.hasStage r.succ)]
  exact Nat.add_lt_add_right ((C.word_eq_iff r _).mp rfl) m
lemma scale_window (m : ℕ) (r : Fin N) : (C.scale m).window r = C.window r + N*m := by
  simp only [window,C.scale_word]
  change ((N*pivotDegree (powerShift C.top m) _ (C.word r)+(C.word r).val : ℕ) : ℤ) = _
  rw [pivotDegree_powerShift _ C.hasTop]
  push_cast
  ring
lemma scale_length (m : ℕ) : (C.scale m).length = C.length := by
  unfold length
  have he : List.ofFn (C.scale m).window = (List.ofFn C.window).map (·+(N*m : ℤ)) := by
    rw [List.map_ofFn]
    congr 1
    funext r
    exact C.scale_window m r
  rw [he,AffineWindow.inversion_shift]
end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N : ℕ}

lemma normalizedPolynomial_spec (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) :
    ∃ m, A.map (polynomialEmbedding K N) =
      level (shift K N) (normalizedPolynomial hN A hA).val m :=
  (normalizedPolynomial_exists hN A hA).choose_spec
lemma normalizedPolynomial_homothetic (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) :
    Homothetic (shift K N) (A.map (polynomialEmbedding K N)) (normalizedPolynomial hN A hA).val := by
  obtain ⟨m,hm⟩ := normalizedPolynomial_spec hN A hA
  exact ⟨0,m,hm⟩
lemma normalizedPolynomial_eq (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) (B : Vertex K N)
    (he : Homothetic (shift K N) (A.map (polynomialEmbedding K N)) B.val) :
    normalizedPolynomial hN A hA = B := by
  apply (homothetic_normalized_iff _ _ (shift_standard_le K N) _ _).mp
  exact homothetic_trans _ (homothetic_symm _ (normalizedPolynomial_homothetic hN A hA)) he
lemma normalizedPolynomial_vertex (hN : 0 < N) (B : Vertex K N) :
    normalizedPolynomial hN (polynomialLattice K N B) (polyBounded_vertex B) = B := by
  apply normalizedPolynomial_eq
  rw [polynomialLattice_map]
  exact homothetic_refl _ _
lemma normalizedPolynomial_power (hN : 0 < N)
    (A : Submodule K[X] (PolynomialVectors.V K N)) (hA : PolyBounded A) (m : ℕ) :
    normalizedPolynomial hN (powerShift A m) (hA.powerShift m) = normalizedPolynomial hN A hA := by
  apply normalizedPolynomial_eq
  apply homothetic_trans _ _ (normalizedPolynomial_homothetic hN A hA)
  rw [powerShift_map_embedding]
  exact ⟨0,m,rfl⟩

namespace BoundedChamber
variable (C : ResidueChamber (K := K) (N := N)) (hC : PolyBounded C.top)
lemma vertex_homothetic (hN : 0 < N) (r : Fin N) :
    Homothetic (shift K N) ((C.stage r.castSucc).map (polynomialEmbedding K N))
      (vertex C hC hN r).val := normalizedPolynomial_homothetic _ _ _
lemma nonterminal_ne (r : Fin N) : C.stage r.castSucc ≠ powerShift C.top 1 := by
  rw [← C.terminal]
  exact (C.strict (show r.castSucc < Fin.last N by exact r.isLt)).ne'

lemma vertex_injective (hN : 0 < N) : Function.Injective (vertex C hC hN) := by
  let L := C.top.map (polynomialEmbedding K N)
  let v (r : Fin N) : AffineLattices.Vertex (shift K N) L := ⟨
    (C.stage r.castSucc).map (polynomialEmbedding K N),
    (by apply Submodule.map_mono; rw [← C.initial]; exact C.strict.antitone (Fin.zero_le _)),
    (by
      intro he
      have hh : (C.stage r.castSucc).map (polynomialEmbedding K N) = shift K N L :=
        le_antisymm he (by
          change level (shift K N) (C.top.map (polynomialEmbedding K N)) 1 ≤ _
          rw [← powerShift_map_embedding]
          exact Submodule.map_mono (C.lower _))
      have heq : C.stage r.castSucc = powerShift C.top 1 := by
        apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K N)
        rw [powerShift_map_embedding]
        exact hh
      exact nonterminal_ne C r heq),
    ⟨1,(by
      change level (shift K N) (C.top.map (polynomialEmbedding K N)) 1 ≤ _
      rw [← powerShift_map_embedding]
      exact Submodule.map_mono (C.lower _))⟩,
    shift_le_self K N _⟩
  intro r s hrs
  have he : Homothetic (shift K N) (v r).val (v s).val :=
    homothetic_trans _ (vertex_homothetic C hC hN r)
      (hrs ▸ homothetic_symm _ (vertex_homothetic C hC hN s))
  have hh := (homothetic_normalized_iff (shift K N) L (shift_le_self K N L) _ _).mp he
  have hmap := congrArg (fun Z : AffineLattices.Vertex (shift K N) L => Z.val) hh
  have hs := Submodule.map_injective_of_injective (polynomialEmbedding_injective K N) hmap
  exact Fin.castSucc_injective _ (C.strict.injective hs)

lemma card_face (hN : 0 < N) : (face C hC hN).card = N := by
  classical
  rw [face,Finset.card_image_of_injective _ (vertex_injective C hC hN)]
  simp
lemma face_mem (hN : 0 < N) : face C hC hN ∈ (building K N).faces := by
  classical
  apply (isFace_iff_compatible (shift K N) (standard K N) (shift_standard_le K N) _).mpr
  intro A hA B hB
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hB
  apply compatible_homothetic _ (vertex_homothetic C hC hN r) (vertex_homothetic C hC hN s)
  have hlow (r s : Fin N) : shift K N ((C.stage r.castSucc).map (polynomialEmbedding K N)) ≤
      (C.stage s.castSucc).map (polynomialEmbedding K N) := by
    apply le_trans _ (Submodule.map_mono (C.lower s.castSucc))
    rw [powerShift_map_embedding]
    change shift K N _ ≤ shift K N _
    apply (shift K N).monotone
    apply Submodule.map_mono
    rw [← C.initial]
    exact C.strict.antitone (Fin.zero_le _)
  rcases le_total r s with hrs | hsr
  · exact ⟨0,0,hlow r s,Submodule.map_mono (C.strict.antitone (Fin.castSucc_le_castSucc_iff.mpr hrs))⟩
  · apply compatible_symm
    exact ⟨0,0,hlow s r,Submodule.map_mono (C.strict.antitone (Fin.castSucc_le_castSucc_iff.mpr hsr))⟩
end BoundedChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial
variable {K : Type} [Field K] {N : ℕ}
lemma reroot_stage (C : ResidueChamber (K := K) (N := N)) (hN : 0 < N)
    (j : ℕ) (r : Fin (N+1)) (hjr : j+r.val ≤ N) :
    (C.reroot hN j).stage r = C.stage ⟨j+r.val,by omega⟩ := by
  induction j generalizing r with
  | zero => simp only [reroot_zero,Nat.zero_add]
  | succ j ih =>
    rw [reroot_succ]
    change (C.reroot hN j).rotateStage hN r = _
    have hr : r.val < N := by omega
    rw [show (C.reroot hN j).rotateStage hN r =
      (C.reroot hN j).stage ⟨r.val+1,by omega⟩ from dite_eq_left hr]
    rw [ih _ (by dsimp only; omega)]
    congr 1
    apply Fin.ext
    dsimp only
    omega
lemma reroot_top (C : ResidueChamber (K := K) (N := N)) (hN : 0 < N)
    (j : ℕ) (hj : j ≤ N) : (C.reroot hN j).top = C.stage ⟨j,by omega⟩ := by
  rw [← (C.reroot hN j).initial,C.reroot_stage hN j 0 (by simpa using hj)]
  rfl
lemma reroot_length {M : ℕ} (C : ResidueChamber (K := K) (N := M+1)) (j : ℕ) :
    (C.reroot (Nat.zero_lt_succ M) j).length = C.length := by
  induction j with
  | zero => rfl
  | succ j ih => rw [reroot_succ,rotate_length,ih]
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N M : ℕ}
variable (C : ResidueChamber (K := K) (N := N)) (hC : PolyBounded C.top)
lemma scale_vertex (m : ℕ) (hN : 0 < N) (r : Fin N) :
    vertex (C.scale m) (hC.powerShift m) hN r = vertex C hC hN r := by
  exact normalizedPolynomial_power hN _ (stage_bounded C hC r.castSucc) m
lemma scale_face (m : ℕ) (hN : 0 < N) :
    face (C.scale m) (hC.powerShift m) hN = face C hC hN := by
  unfold face
  congr 1
  exact funext (scale_vertex C hC m hN)

lemma rotate_vertex (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top)
    (r : Fin (M+1)) : vertex (C.rotate (Nat.zero_lt_succ M))
      (rotate_bounded C hC _) (Nat.zero_lt_succ M) r =
      vertex C hC (Nat.zero_lt_succ M) (finRotate (M+1) r) := by
  apply normalizedPolynomial_eq
  change Homothetic (shift K (M+1))
    (((C.rotate (Nat.zero_lt_succ M)).stage r.castSucc).map _) _
  change Homothetic (shift K (M+1)) ((C.rotateStage _ r.castSucc).map _) _
  rw [C.rotateStage_castSucc]
  by_cases hr : r.val < M
  · rw [finRotate_of_lt hr]
    exact vertex_homothetic C hC _ ⟨r.val+1,by omega⟩
  · have he : r = Fin.last M := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
    subst r
    rw [finRotate_last]
    have he : (Fin.last M).succ = Fin.last (M+1) := Fin.ext rfl
    rw [he,C.terminal,powerShift_map_embedding]
    apply homothetic_trans _ ⟨0,1,rfl⟩
    have hh := vertex_homothetic C hC (Nat.zero_lt_succ M) 0
    rw [show (0 : Fin (M+1)).castSucc = 0 from rfl,C.initial] at hh
    exact hh
lemma rotate_face (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top) :
    face (C.rotate (Nat.zero_lt_succ M)) (rotate_bounded C hC _) (Nat.zero_lt_succ M) =
      face C hC (Nat.zero_lt_succ M) := by
  classical
  ext v
  simp only [face,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨finRotate (M+1) r, (rotate_vertex C hC r).symm.trans hr⟩
  · rintro ⟨r,hr⟩
    obtain ⟨s,hs⟩ := (finRotate (M+1)).surjective r
    exact ⟨s,by rw [rotate_vertex,hs]; exact hr⟩
lemma reroot_face (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top) (j : ℕ) :
    face (C.reroot (Nat.zero_lt_succ M) j) (reroot_bounded C hC _ j) (Nat.zero_lt_succ M) =
      face C hC (Nat.zero_lt_succ M) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [C.reroot_succ]
    exact (rotate_face _ (reroot_bounded C hC _ j)).trans ih

end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N : ℕ}
lemma homothetic_interval_eq (T A B : LatticeSpace K N)
    (hAT : A ≤ T) (hBT : B ≤ T) (hTA : shift K N T ≤ A) (hTB : shift K N T ≤ B)
    (hneA : A ≠ shift K N T) (hneB : B ≠ shift K N T)
    (hh : Homothetic (shift K N) A B) : A = B := by
  let VA : AffineLattices.Vertex (shift K N) T :=
    ⟨A,hAT,fun h => hneA (le_antisymm h hTA),⟨1,hTA⟩,shift_le_self K N A⟩
  let VB : AffineLattices.Vertex (shift K N) T :=
    ⟨B,hBT,fun h => hneB (le_antisymm h hTB),⟨1,hTB⟩,shift_le_self K N B⟩
  exact congrArg (fun Z : AffineLattices.Vertex (shift K N) T => Z.val)
    ((homothetic_normalized_iff (shift K N) T (shift_le_self K N T) VA VB).mp hh)

namespace BoundedChamber
variable (C D : ResidueChamber (K := K) (N := N))
variable (hC : PolyBounded C.top) (hD : PolyBounded D.top) (hN : 0 < N)
lemma stage_top_le (r : Fin (N+1)) : C.stage r ≤ C.top := by
  rw [← C.initial]
  exact C.strict.antitone (Fin.zero_le _)
lemma mapped_lower (r : Fin (N+1)) : shift K N (C.top.map (polynomialEmbedding K N)) ≤
    (C.stage r).map (polynomialEmbedding K N) := by
  change level (shift K N) (C.top.map (polynomialEmbedding K N)) 1 ≤ _
  rw [← powerShift_map_embedding]
  exact Submodule.map_mono (C.lower r)
lemma mapped_nonterminal (r : Fin N) :
    (C.stage r.castSucc).map (polynomialEmbedding K N) ≠ shift K N (C.top.map (polynomialEmbedding K N)) := by
  intro he
  apply nonterminal_ne C r
  apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K N)
  rw [powerShift_map_embedding]
  exact he

lemma stage_eq_of_vertex_eq (ht : C.top = D.top) (r s : Fin N)
    (he : vertex C hC hN r = vertex D hD hN s) : C.stage r.castSucc = D.stage s.castSucc := by
  apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K N)
  apply homothetic_interval_eq (C.top.map (polynomialEmbedding K N))
  · exact Submodule.map_mono (stage_top_le C _)
  · rw [ht]; exact Submodule.map_mono (stage_top_le D _)
  · exact mapped_lower C _
  · rw [ht]; exact mapped_lower D _
  · exact mapped_nonterminal C _
  · rw [ht]; exact mapped_nonterminal D _
  · exact homothetic_trans _ (vertex_homothetic C hC hN r)
      (he ▸ homothetic_symm _ (vertex_homothetic D hD hN s))

lemma eq_of_face_of_top (ht : C.top = D.top) (hf : face C hC hN = face D hD hN) : C = D := by
  classical
  have hrange : Set.range (fun r : Fin N => C.stage r.castSucc) =
      Set.range (fun r : Fin N => D.stage r.castSucc) := by
    ext A
    constructor
    · rintro ⟨r,rfl⟩
      have hm : vertex C hC hN r ∈ face C hC hN := Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
      rw [hf] at hm
      obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hm
      exact ⟨s,(stage_eq_of_vertex_eq C D hC hD hN ht r s hs.symm).symm⟩
    · rintro ⟨s,rfl⟩
      have hm : vertex D hD hN s ∈ face D hD hN := Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩
      rw [← hf] at hm
      obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hm
      exact ⟨r,stage_eq_of_vertex_eq C D hC hD hN ht r s hr⟩
  let eC : Fin N ↪o OrderDual (Submodule K[X] (PolynomialVectors.V K N)) :=
    OrderEmbedding.ofStrictMono (fun r => C.stage r.castSucc)
      (fun r s hrs => C.strict (Fin.castSucc_lt_castSucc_iff.mpr hrs))
  let eD : Fin N ↪o OrderDual (Submodule K[X] (PolynomialVectors.V K N)) :=
    OrderEmbedding.ofStrictMono (fun r => D.stage r.castSucc)
      (fun r s hrs => D.strict (Fin.castSucc_lt_castSucc_iff.mpr hrs))
  have he : eC = eD := OrderEmbedding.range_eq_iff.mp hrange
  apply ResidueChamber.ext_stage ht
  funext r
  refine Fin.lastCases ?_ (fun s => ?_) r
  · rw [C.terminal,D.terminal,ht]
  · exact congrArg (fun e : Fin N ↪o OrderDual (Submodule K[X] (PolynomialVectors.V K N)) => e s) he

lemma full_vertex {hN : 0 < N} (E : FullChamber K N hN) (r : Fin N) :
    vertex E.polynomialChamber (polyBounded_vertex _) hN r = E.vertex r := by
  apply normalizedPolynomial_eq
  change Homothetic (shift K N) ((E.stage r.castSucc).map _) _
  rw [E.stage_castSucc,polynomialLattice_map]
  exact homothetic_refl _ _
lemma full_face {hN : 0 < N} (E : FullChamber K N hN) :
    face E.polynomialChamber (polyBounded_vertex _) hN = E.face := by
  unfold face FullChamber.face
  congr 1
  exact funext (full_vertex E)

theorem normalization {M : ℕ} (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top) :
    ∃ E : FullChamber K (M+1) (Nat.zero_lt_succ M),
      E.face = face C hC (Nat.zero_lt_succ M) ∧ E.length = C.length := by
  classical
  let hN := Nat.zero_lt_succ M
  obtain ⟨E,hE⟩ := ambient_face_in_chamber K (M+1) hN (face C hC hN) (face_mem C hC hN)
  have hface : E.face = face C hC hN := (Finset.eq_of_subset_of_card_le hE
    (by rw [E.card_face,card_face])).symm
  have hA : normalizedPolynomial hN C.top hC ∈ E.face := by
    rw [hface]
    apply Finset.mem_image.mpr
    refine ⟨0,Finset.mem_univ _,?_⟩
    change normalizedPolynomial hN (C.stage 0) _ = _
    simp only [C.initial]
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hA
  obtain ⟨m,hm⟩ := normalizedPolynomial_spec hN C.top hC
  let R := (E.polynomialChamber.reroot hN j.val).scale m
  have hb : PolyBounded R.top := (reroot_bounded E.polynomialChamber (polyBounded_vertex _) hN j.val).powerShift m
  have ht : R.top = C.top := by
    apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+1))
    change (powerShift (E.polynomialChamber.reroot hN j.val).top m).map _ = _
    rw [powerShift_map_embedding,E.polynomialChamber.reroot_top hN j.val j.isLt.le]
    change level (shift K (M+1)) ((E.stage j.castSucc).map _) m = _
    rw [E.stage_castSucc,polynomialLattice_map,hj]
    exact hm.symm
  have hf : face R hb hN = face C hC hN := by
    rw [show face R hb hN = face (E.polynomialChamber.reroot hN j.val)
      (reroot_bounded E.polynomialChamber (polyBounded_vertex _) hN j.val) hN from scale_face _ _ m hN]
    rw [reroot_face E.polynomialChamber (polyBounded_vertex _) j.val,full_face E,hface]
  have heq : R = C := eq_of_face_of_top R C hb hC hN ht hf
  refine ⟨E,hface,?_⟩
  change E.polynomialChamber.length = C.length
  rw [← heq]
  change _ = ((E.polynomialChamber.reroot hN j.val).scale m).length
  rw [ResidueChamber.scale_length,ResidueChamber.reroot_length]
end BoundedChamber
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}

theorem rooted_panel_previous (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
    (hd : C.window 1 < C.window 0) :
    (face C hC (by omega)).erase (vertex C hC (by omega) 1) ∈
      codistanceStage K (M+2) (by omega) (C.length-1) := by
  classical
  obtain ⟨D,ht,hs,_,hlen⟩ := C.first_panel_lower hd
  have hD : PolyBounded D.top := by rw [ht]; exact hC
  obtain ⟨E,hface,hLength⟩ := normalization D hD
  refine ⟨E,?_,?_⟩
  · rw [hLength]
    omega
  · intro v hv
    rw [hface]
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hv
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hmem
    have hr1 : r.val ≠ 1 := by
      intro he
      have hh : r = 1 := Fin.ext he
      exact hne (hr.symm.trans (congrArg (vertex C hC (by omega)) hh))
    refine Finset.mem_image.mpr ⟨r,Finset.mem_univ _,?_⟩
    apply Eq.trans _ hr
    change normalizedPolynomial _ (D.stage r.castSucc) _ = normalizedPolynomial _ (C.stage r.castSucc) _
    simp only [hs r.castSucc hr1]

theorem full_rooted_panel_previous (E : FullChamber K (M+2) (by omega)) (j : ℕ)
    (hd : (E.polynomialChamber.reroot (by omega) j).window 1 <
      (E.polynomialChamber.reroot (by omega) j).window 0) :
    E.face.erase (vertex (E.polynomialChamber.reroot (by omega) j)
      (reroot_bounded E.polynomialChamber (polyBounded_vertex _) (by omega) j) (by omega) 1) ∈
      codistanceStage K (M+2) (by omega) (E.length-1) := by
  have hh := rooted_panel_previous (E.polynomialChamber.reroot (by omega) j)
    (reroot_bounded E.polynomialChamber (polyBounded_vertex _) (by omega) j) hd
  rw [reroot_face E.polynomialChamber (polyBounded_vertex _) j,full_face E,
    ResidueChamber.reroot_length] at hh
  exact hh
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {M : ℕ}
lemma reroot_window_nonwrap (C : ResidueChamber (K := K) (N := M+1))
    (j : ℕ) (r : Fin (M+1)) (hjr : j+r.val < M+1) :
    (C.reroot (Nat.zero_lt_succ M) j).window r = C.window ⟨j+r.val,by omega⟩ := by
  induction j generalizing r with
  | zero => simp only [reroot_zero,Nat.zero_add,Fin.eta]
  | succ j ih =>
    rw [reroot_succ]
    have hr : r.val < M := by omega
    have he := (C.reroot (Nat.zero_lt_succ M) j).rotate_window_castSucc ⟨r.val,hr⟩
    change ((C.reroot (Nat.zero_lt_succ M) j).rotate _).window r = _ at he
    rw [he,ih _ (by simp only [Fin.val_succ]; omega)]
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
lemma reroot_period (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top) :
    C.reroot (Nat.zero_lt_succ M) (M+1) = C.scale 1 := by
  apply eq_of_face_of_top _ _ (reroot_bounded C hC _ (M+1)) (hC.powerShift 1) (Nat.zero_lt_succ M)
  · rw [C.reroot_top _ _ le_rfl]
    exact C.terminal
  · rw [reroot_face C hC,scale_face C hC]
lemma reroot_vertex_nonwrap (C : ResidueChamber (K := K) (N := M+1)) (hC : PolyBounded C.top)
    (j : ℕ) (r : Fin (M+1)) (hjr : j+r.val < M+1) :
    vertex (C.reroot (Nat.zero_lt_succ M) j) (reroot_bounded C hC _ j) (Nat.zero_lt_succ M) r =
      vertex C hC (Nat.zero_lt_succ M) ⟨j+r.val,by omega⟩ := by
  change normalizedPolynomial _ ((C.reroot _ j).stage r.castSucc) _ = _
  simp only [C.reroot_stage _ j r.castSucc (by simp only [Fin.val_castSucc]; omega)]
  rfl
lemma last_root_window_one (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top) :
    (C.reroot (by omega) (M+1)).window 1 = C.window 0 + (M+2) := by
  have he := (C.reroot (by omega) (M+1)).rotate_window_castSucc (0 : Fin (M+1))
  change ((C.reroot (by omega) (M+1)).rotate _).window 0 =
    (C.reroot (by omega) (M+1)).window 1 at he
  rw [← he,← C.reroot_succ,reroot_period C hC]
  rw [ResidueChamber.scale_window]
  simp
lemma last_root_vertex_one (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top) :
    vertex (C.reroot (by omega) (M+1)) (reroot_bounded C hC _ (M+1)) (by omega) 1 =
      vertex C hC (by omega) 0 := by
  have he := rotate_vertex (C.reroot (by omega) (M+1)) (reroot_bounded C hC _ (M+1)) 0
  rw [finRotate_apply_zero] at he
  rw [← he]
  simp only [← C.reroot_succ,reroot_period C hC]
  exact scale_vertex C hC 1 _ 0
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
lemma reroot_window_zero (C : ResidueChamber (K := K) (N := M+2)) (r : Fin (M+2)) :
    (C.reroot (by omega) r.val).window 0 = C.window r := by
  simpa only [Fin.val_zero,Nat.add_zero,Fin.eta] using
    C.reroot_window_nonwrap r.val 0 (by simpa only [Fin.val_zero,Nat.add_zero] using r.isLt)
lemma reroot_window_one (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
    (r : Fin (M+2)) : (C.reroot (by omega) r.val).window 1 =
      AffineWindow.periodicEnd (by omega) C.window r.succ := by
  classical
  by_cases hr : r.val < M+1
  · have hn : r.val+1 < M+2 := by omega
    rw [AffineWindow.periodicEnd,dite_eq_left (show r.succ.val < M+2 from hn)]
    have hh := C.reroot_window_nonwrap r.val 1
      (show r.val+(1:Fin (M+2)).val < M+2 by simpa using hn)
    simpa using hh
  · have he : r.val = M+1 := by have := r.isLt; omega
    have hs : r.succ = Fin.last (M+2) := Fin.ext (by change r.val+1 = M+2; omega)
    rw [he,hs,AffineWindow.periodicEnd_last,last_root_window_one C hC]
    simp
lemma reroot_vertex_one (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
    (r : Fin (M+2)) :
    vertex (C.reroot (by omega) r.val) (reroot_bounded C hC _ r.val) (by omega) 1 =
      vertex C hC (by omega) (finRotate (M+2) r) := by
  by_cases hr : r.val < M+1
  · rw [finRotate_of_lt hr]
    have hh := reroot_vertex_nonwrap C hC r.val 1
      (show r.val+(1:Fin (M+2)).val < M+2 by simp; omega)
    simpa using hh
  · have he : r = Fin.last (M+1) := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
    subst r
    exact (last_root_vertex_one C hC).trans (congrArg _ finRotate_last.symm)

theorem descent_panel_previous (E : FullChamber K (M+2) (by omega))
    (r : Fin (M+2)) (hr : r ∈ AffineWindow.descents (by omega) E.polynomialChamber.window) :
    E.face.erase (E.vertex (finRotate (M+2) r)) ∈ codistanceStage K (M+2) (by omega) (E.length-1) := by
  have hd := (Finset.mem_filter.mp hr).2
  have hh := full_rooted_panel_previous E r.val
    (by rw [reroot_window_zero,reroot_window_one _ (polyBounded_vertex _)]; exact hd)
  rw [reroot_vertex_one _ (polyBounded_vertex _),full_vertex] at hh
  exact hh
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.FullChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
lemma descentCore_subset (E : FullChamber K (M+2) (by omega)) : E.descentCore ⊆ E.face := by
  intro v hv
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hv
  exact E.mem_face _
lemma descentCore_nonempty (E : FullChamber K (M+2) (by omega)) (hE : 0 < E.length) :
    E.descentCore.Nonempty := by
  apply Finset.Nonempty.image
  apply AffineWindow.descents_nonempty
  · intro r s he
    dsimp only at he
    rw [E.polynomialChamber.window_mod (by omega),E.polynomialChamber.window_mod (by omega)] at he
    exact E.polynomialChamber.word.injective (Fin.ext (by exact_mod_cast he))
  · exact hE

theorem face_missing_descent_previous (E : FullChamber K (M+2) (by omega))
    {s : Finset (Vertex K (M+2))} (hs : s ⊆ E.face) (hcore : ¬ E.descentCore ⊆ s) :
    s ∈ codistanceStage K (M+2) (by omega) (E.length-1) := by
  classical
  obtain ⟨v,hv,hvs⟩ := Finset.not_subset.mp hcore
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
  apply codistanceStage_downward K (M+2) (by omega) (E.length-1)
    (BoundedChamber.descent_panel_previous E r hr)
  intro v hv
  exact Finset.mem_erase.mpr ⟨fun he => hvs (he ▸ hv),hs hv⟩
end CoboundaryExpanders.RationalLattices.FullChamber

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}

theorem inversion_sorted_blocks (hN : 0 < N) (p q : List (List ℤ))
    (h : List.Forall₂ (fun a b => a.Perm b ∧ a.Pairwise (· ≤ ·) ∧
      b.Pairwise (fun x y => x % (N : ℤ) ≠ y % (N : ℤ))) p q)
    (l r : List ℤ) :
    inversion (N := N) (l ++ q.flatten ++ r) =
      inversion (N := N) (l ++ p.flatten ++ r) + (q.map (pairs disorder)).sum := by
  induction h generalizing l r with
  | nil => simp
  | @cons a b p q hh ht ih =>
    have hb := inversion_sorted_middle hN l (q.flatten ++ r) hh.1 hh.2.1 hh.2.2
    have hp := ih (l ++ a) r
    simp only [List.flatten_cons,List.map_cons,List.sum_cons]
    simp only [List.append_assoc] at hb hp ⊢
    omega

lemma sorted_blocks_eq_of_zero (p q : List (List ℤ))
    (h : List.Forall₂ (fun a b => a.Perm b ∧ a.Pairwise (· ≤ ·)) p q)
    (hz : (q.map (pairs disorder)).sum = 0) : p = q := by
  induction h with
  | nil => rfl
  | @cons a b p q hh ht ih =>
    simp only [List.map_cons,List.sum_cons,Nat.add_eq_zero_iff] at hz
    have hab : a = b := hh.1.eq_of_pairwise' hh.2 ((disorder_zero_iff b).mp hz.1)
    exact congrArg₂ List.cons hab (ih hz.2)

end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.AffineWindow
variable {N : ℕ}
lemma mem_slice (p : Fin N → ℤ) (a b : Fin (N+1)) (x : ℤ) :
    x ∈ slice p a b ↔ ∃ r : Fin N, a.val ≤ r.val ∧ r.val < b.val ∧ p r = x := by
  rw [slice,List.mem_ofFn]
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨⟨a.val+r.val,by have := r.isLt; have := b.isLt; omega⟩,by simp,?_,hr⟩
    have := r.isLt
    dsimp only
    omega
  · rintro ⟨r,ha,hb,hr⟩
    refine ⟨⟨r.val-a.val,by omega⟩,?_⟩
    dsimp only
    have he : (⟨a.val+(r.val-a.val),by omega⟩ : Fin N) = r := Fin.ext (by dsimp only; omega)
    simpa only [he] using hr
lemma slice_nodup (p : Fin N → ℤ) (hp : Function.Injective p) (a b : Fin (N+1)) :
    (slice p a b).Nodup := by
  apply List.nodup_ofFn.mpr
  intro r s he
  have hv := congrArg Fin.val (hp he)
  apply Fin.ext
  dsimp only at hv
  omega
lemma slice_eq_take_drop (p : Fin N → ℤ) (a b : Fin (N+1)) :
    slice p a b = ((List.ofFn p).drop a.val).take (b.val-a.val) := by
  apply List.ext_getElem
  · simp only [slice,List.length_ofFn,List.length_take,List.length_drop]
    have := b.isLt
    omega
  · intro i hi hri
    simp only [slice,List.getElem_ofFn,List.getElem_take,List.getElem_drop]
lemma slice_pairwise (p : Fin N → ℤ) (a b : Fin (N+1)) (R : ℤ → ℤ → Prop)
    (h : ∀ i j : Fin N, a.val ≤ i.val → j.val < b.val → i < j → R (p i) (p j)) :
    (slice p a b).Pairwise R := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  apply h
  · simp
  · have := j.isLt; dsimp only; omega
  · change a.val+i.val < a.val+j.val
    exact Nat.add_lt_add_left hij _
end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
variable (C D : ResidueChamber (K := K) (N := N))
lemma shared_stage_prefix (ht : C.top = D.top) (r : Fin (N+1))
    (hr : C.stage r = D.stage r) (i : Fin N) :
    (C.word.symm i).val < r.val ↔ (D.word.symm i).val < r.val := by
  classical
  have hc := C.stage_degree r i
  have hd := D.stage_degree r i
  simp only [ht,hr] at hc
  by_cases hci : (C.word.symm i).val < r.val <;>
    by_cases hdi : (D.word.symm i).val < r.val <;> simp_all
  omega
lemma same_top_window (ht : C.top = D.top) (r : Fin N) :
    C.window r = D.window (D.word.symm (C.word r)) := by
  simp only [window,Equiv.apply_symm_apply,ht]
lemma window_injective (C : ResidueChamber (K := K) (N := N)) : Function.Injective C.window := by
  intro r s he
  have hN : 0 < N := (r.isLt).trans_le' (Nat.zero_le _)
  have hh := congrArg (· % (N : ℤ)) he
  rw [C.window_mod hN,C.window_mod hN] at hh
  exact C.word.injective (Fin.ext (by exact_mod_cast hh))

theorem window_slice_perm (ht : C.top = D.top) (a b : Fin (N+1))
    (ha : C.stage a = D.stage a) (hb : C.stage b = D.stage b) :
    (AffineWindow.slice C.window a b).Perm (AffineWindow.slice D.window a b) := by
  classical
  apply (List.perm_ext_iff_of_nodup (AffineWindow.slice_nodup _ C.window_injective a b)
    (AffineWindow.slice_nodup _ D.window_injective a b)).mpr
  intro x
  rw [AffineWindow.mem_slice,AffineWindow.mem_slice]
  constructor
  · rintro ⟨r,har,hrb,hrx⟩
    refine ⟨D.word.symm (C.word r),?_,?_,(C.same_top_window D ht r).symm.trans hrx⟩
    · have hh := C.shared_stage_prefix D ht a ha (C.word r)
      simp only [Equiv.symm_apply_apply] at hh
      omega
    · have hh := C.shared_stage_prefix D ht b hb (C.word r)
      simp only [Equiv.symm_apply_apply] at hh
      exact hh.mp hrb
  · rintro ⟨r,har,hrb,hrx⟩
    refine ⟨C.word.symm (D.word r),?_,?_,(D.same_top_window C ht.symm r).symm.trans hrx⟩
    · have hh := D.shared_stage_prefix C ht.symm a ha.symm (D.word r)
      simp only [Equiv.symm_apply_apply] at hh
      omega
    · have hh := D.shared_stage_prefix C ht.symm b hb.symm (D.word r)
      simp only [Equiv.symm_apply_apply] at hh
      exact hh.mp hrb
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.AffineWindow
variable {N L : ℕ}
lemma slice_append (p : Fin N → ℤ) (a b c : Fin (N+1)) (hab : a ≤ b) (hbc : b ≤ c) :
    slice p a b ++ slice p b c = slice p a c := by
  rw [slice_eq_take_drop,slice_eq_take_drop,slice_eq_take_drop]
  have he : c.val-a.val = (b.val-a.val)+(c.val-b.val) := by
    change a.val ≤ b.val at hab
    change b.val ≤ c.val at hbc
    omega
  rw [he,List.take_add,List.drop_drop]
  have hh : a.val+(b.val-a.val) = b.val := Nat.add_sub_of_le hab
  rw [hh]
lemma slice_self (p : Fin N → ℤ) (a : Fin (N+1)) : slice p a a = [] := by simp [slice]
lemma slice_full (p : Fin N → ℤ) : slice p 0 (Fin.last N) = List.ofFn p := by
  simp [slice_eq_take_drop]
lemma flatten_blocks (p : Fin N → ℤ) (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c) :
    (blocks p c).flatten = slice p (c 0) (c (Fin.last L)) := by
  induction L with
  | zero => simp [blocks,slice_self]
  | succ L ih =>
    rw [blocks,List.ofFn_succ,List.flatten_cons]
    have hh := ih (fun j => c j.succ) (fun i j hij => hc (Fin.succ_le_succ_iff.mpr hij))
    change (blocks p (fun j => c j.succ)).flatten = _ at hh
    change slice p (c 0) (c (Fin.succ 0)) ++ (blocks p (fun j => c j.succ)).flatten = _
    rw [hh]
    apply slice_append
    · exact hc (show (0 : Fin (L+2)) ≤ (0 : Fin (L+1)).succ from Fin.zero_le _)
    · exact hc (Fin.succ_le_succ_iff.mpr (Fin.zero_le _))
lemma blocks_forall₂ {p q : Fin N → ℤ} (c : Fin (L+1) → Fin (N+1))
    (R : List ℤ → List ℤ → Prop)
    (h : ∀ r : Fin L, R (slice p (c r.castSucc) (c r.succ)) (slice q (c r.castSucc) (c r.succ))) :
    List.Forall₂ R (blocks p c) (blocks q c) := by
  suffices hh : ∀ (n : ℕ) (f g : Fin n → List ℤ), (∀ i, R (f i) (g i)) →
      List.Forall₂ R (List.ofFn f) (List.ofFn g) from hh L _ _ h
  intro n
  induction n with
  | zero => intro f g hh; simp
  | succ n ih =>
    intro f g hh
    rw [List.ofFn_succ,List.ofFn_succ]
    exact List.Forall₂.cons (hh 0) (ih _ _ (fun i => hh i.succ))
end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open AffineWindow
variable {K : Type} [Field K] {N L : ℕ}
variable (C D : ResidueChamber (K := K) (N := N))

theorem fixed_stage_length (hN : 0 < N) (ht : C.top = D.top)
    (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (hstage : ∀ r, C.stage (c r) = D.stage (c r))
    (hsorted : ∀ r : Fin L, (slice C.window (c r.castSucc) (c r.succ)).Pairwise (· ≤ ·)) :
    D.length = C.length + ((blocks D.window c).map (pairs disorder)).sum := by
  have h : List.Forall₂ (fun a b => a.Perm b ∧ a.Pairwise (· ≤ ·) ∧
      b.Pairwise (fun x y => x % (N : ℤ) ≠ y % (N : ℤ))) (blocks C.window c) (blocks D.window c) := by
    apply blocks_forall₂
    intro r
    refine ⟨C.window_slice_perm D ht _ _ (hstage _) (hstage _),hsorted r,?_⟩
    apply slice_pairwise
    intro i j _ _ hij he
    rw [D.window_mod hN,D.window_mod hN] at he
    exact (ne_of_lt hij) (D.word.injective (Fin.ext (by exact_mod_cast he)))
  have he := inversion_sorted_blocks hN _ _ h [] []
  rw [flatten_blocks _ _ hc,flatten_blocks _ _ hc,h0,hl,slice_full,slice_full] at he
  simpa only [length,List.nil_append,List.append_nil] using he

theorem fixed_stage_minimum (hN : 0 < N) (ht : C.top = D.top)
    (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (hstage : ∀ r, C.stage (c r) = D.stage (c r))
    (hsorted : ∀ r : Fin L, (slice C.window (c r.castSucc) (c r.succ)).Pairwise (· ≤ ·)) :
    C.length ≤ D.length := by
  have he := C.fixed_stage_length D hN ht c hc h0 hl hstage hsorted
  omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.AffineWindow
variable {N L : ℕ}
lemma fin_mono_of_steps {A : Type} [Preorder A] {m : ℕ} (f : Fin m → A)
    (h : ∀ i j, i.val+1 = j.val → f i ≤ f j) : Monotone f := by
  cases m with
  | zero => intro i; exact Fin.elim0 i
  | succ m => exact Fin.monotone_iff_le_succ.mpr (fun i => h i.castSucc i.succ rfl)

lemma slices_sorted_of_descents (hN : 0 < N) (p : Fin N → ℤ)
    (c : Fin (L+1) ↪o Fin (N+1))
    (hdes : ∀ r ∈ descents hN p, r.succ ∈ Set.range c) (r : Fin L) :
    (slice p (c r.castSucc) (c r.succ)).Pairwise (· ≤ ·) := by
  classical
  let a := c r.castSucc
  let b := c r.succ
  let f : Fin (b.val-a.val) → ℤ := fun i => p ⟨a.val+i.val,by have := i.isLt; have := b.isLt; omega⟩
  have hm : Monotone f := by
    apply fin_mono_of_steps
    intro i j hij
    dsimp only [f]
    by_contra hn
    let v : Fin N := ⟨a.val+i.val,by have := i.isLt; have := b.isLt; omega⟩
    have hjN : a.val+j.val < N := by have := j.isLt; have := b.isLt; omega
    have hv : v.val+1 < N := by dsimp only [v]; omega
    have hd : v ∈ descents hN p := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [periodicEnd,dite_eq_left (show v.succ.val < N from hv)]
      have he : (⟨v.succ.val,hv⟩ : Fin N) = ⟨a.val+j.val,hjN⟩ := Fin.ext (by dsimp only [v]; simp only [Fin.val_succ]; omega)
      rw [he]
      exact lt_of_not_ge hn
    obtain ⟨t,ht⟩ := hdes v hd
    have hat : c r.castSucc < c t := by
      rw [ht]
      change a.val < a.val+i.val+1
      omega
    have htb : c t < c r.succ := by
      rw [ht]
      change a.val+i.val+1 < b.val
      have := j.isLt
      omega
    have h₁ := c.lt_iff_lt.mp hat
    have h₂ := c.lt_iff_lt.mp htb
    change r.val < t.val at h₁
    change t.val < r.val+1 at h₂
    omega
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact hm hij.le

lemma cuts_enumeration (hN : 0 < N) (p : Fin N → ℤ) :
    ∃ L : ℕ, ∃ c : Fin (L+1) ↪o Fin (N+1),
      c 0 = 0 ∧ c (Fin.last L) = Fin.last N ∧ Set.range c = cutSet hN p := by
  classical
  let S := cutSet hN p
  have h0 : (0 : Fin (N+1)) ∈ S := Finset.mem_insert_self _ _
  have hn : Fin.last N ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨0,h0⟩
  have hcard : S.card = (S.card-1)+1 := by omega
  let c := S.orderEmbOfFin hcard
  have hr : Set.range c = S := Finset.range_orderEmbOfFin S hcard
  obtain ⟨i,hi⟩ : ∃ i, c i = 0 := by exact (hr ▸ h0 : (0 : Fin (N+1)) ∈ Set.range c)
  obtain ⟨j,hj⟩ : ∃ j, c j = Fin.last N := by exact (hr ▸ hn : Fin.last N ∈ Set.range c)
  refine ⟨S.card-1,c,?_,?_,hr⟩
  · apply le_antisymm _ (Fin.zero_le _)
    exact hi ▸ c.monotone (Fin.zero_le i)
  · apply le_antisymm (Fin.le_last _) _
    exact hj ▸ c.monotone (Fin.le_last j)
end CoboundaryExpanders.AffineWindow

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open AffineWindow
variable {K : Type} [Field K] {N : ℕ}
variable (C D : ResidueChamber (K := K) (N := N))

theorem descent_minimum (hN : 0 < N) (ht : C.top = D.top)
    (hstage : ∀ r ∈ descents hN C.window, C.stage r.succ = D.stage r.succ) : C.length ≤ D.length := by
  classical
  obtain ⟨L,c,hc0,hcN,hcrange⟩ := cuts_enumeration hN C.window
  refine C.fixed_stage_minimum D hN ht c c.monotone hc0 hcN ?_ ?_
  · intro r
    have hr : c r ∈ cutSet hN C.window := by
      change c r ∈ (↑(cutSet hN C.window) : Set _)
      rw [← hcrange]
      exact Set.mem_range_self r
    rcases Finset.mem_insert.mp hr with he | hr
    · rw [he,C.initial,D.initial,ht]
    · rcases Finset.mem_insert.mp hr with he | hr
      · rw [he,C.terminal,D.terminal,ht]
      · obtain ⟨s,hs,he⟩ := Finset.mem_image.mp hr
        rw [← he]
        exact hstage s hs
  · apply slices_sorted_of_descents hN C.window c
    intro r hr
    rw [hcrange]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r,hr,rfl⟩))
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
lemma increments_card (C : ResidueChamber (K := K) (N := N)) (r : Fin (N+1)) :
    (incrementSet C.top (C.stage r) C.hasTop (C.hasStage r)).card = r.val := by
  classical
  induction r using Fin.induction with
  | zero => simp only [C.increments,Fin.val_zero,Nat.not_lt_zero,Finset.filter_false,Finset.card_empty]
  | succ r ih => rw [(C.word_spec r).1,Finset.card_insert_of_notMem (C.word_spec r).2,ih]; rfl
lemma stage_index_eq (C D : ResidueChamber (K := K) (N := N)) (ht : C.top = D.top)
    (r s : Fin (N+1)) (he : C.stage r = D.stage s) : r = s := by
  apply Fin.ext
  have hc := C.increments_card r
  have hd := D.increments_card s
  simp only [ht,he] at hc
  exact hc.symm.trans hd
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {N : ℕ}
lemma vertex_index_eq (C D : ResidueChamber (K := K) (N := N))
    (hC : PolyBounded C.top) (hD : PolyBounded D.top) (hN : 0 < N)
    (ht : C.top = D.top) (r s : Fin N)
    (he : vertex C hC hN r = vertex D hD hN s) : r = s := by
  exact Fin.castSucc_injective _ (C.stage_index_eq D ht _ _
    (stage_eq_of_vertex_eq C D hC hD hN ht r s he))
lemma shared_vertex_stage (C D : ResidueChamber (K := K) (N := N))
    (hC : PolyBounded C.top) (hD : PolyBounded D.top) (hN : 0 < N)
    (ht : C.top = D.top) (r : Fin N) (hr : vertex C hC hN r ∈ face D hD hN) :
    C.stage r.castSucc = D.stage r.castSucc := by
  obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hr
  have he := vertex_index_eq C D hC hD hN ht r s hs.symm
  subst s
  exact stage_eq_of_vertex_eq C D hC hD hN ht r r hs.symm

lemma full_descentCore {M : ℕ} (E : FullChamber K (M+2) (by omega)) :
    descentCore E.polynomialChamber (polyBounded_vertex _) = E.descentCore := by
  unfold descentCore FullChamber.descentCore
  congr 1
  funext r
  exact full_vertex E _

theorem core_minimum_same_top {M : ℕ} (C D : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) (hD : PolyBounded D.top) (ht : C.top = D.top)
    (hcore : descentCore C hC ⊆ face D hD (by omega)) : C.length ≤ D.length := by
  apply C.descent_minimum D (by omega) ht
  intro r hr
  by_cases hlast : r.val = M+1
  · have he : r.succ = Fin.last (M+2) := Fin.ext (by change r.val+1 = M+2; omega)
    rw [he,C.terminal,D.terminal,ht]
  · have hlt : r.val < M+1 := by have := r.isLt; omega
    have hh := hcore (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
    rw [finRotate_of_lt hlt] at hh
    exact shared_vertex_stage C D hC hD (by omega) ht ⟨r.val+1,by omega⟩ hh
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open AffineWindow
variable {K : Type} [Field K] {M : ℕ}
lemma rotate_window_of_lt (C : ResidueChamber (K := K) (N := M+2))
    (r : Fin (M+2)) (hr : r.val < M+1) :
    (C.rotate (by omega)).window r = C.window ⟨r.val+1,by omega⟩ :=
  C.rotate_window_castSucc ⟨r.val,hr⟩
lemma rotate_descent_iff (C : ResidueChamber (K := K) (N := M+2)) (r : Fin (M+2)) :
    r ∈ descents (by omega) (C.rotate (by omega)).window ↔
      finRotate (M+2) r ∈ descents (by omega) C.window := by
  classical
  simp only [descents,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hr : r.val < M+1
  · rw [finRotate_of_lt hr,C.rotate_window_of_lt r hr]
    rw [periodicEnd,dite_eq_left (show r.succ.val < M+2 by change r.val+1 < M+2; omega)]
    by_cases hrr : r.val+1 < M+1
    · rw [C.rotate_window_of_lt _ hrr]
      rw [periodicEnd,dite_eq_left (show (⟨r.val+1,by omega⟩ : Fin (M+2)).succ.val < M+2 by change r.val+1+1 < M+2; omega)]
      rfl
    · have he : (⟨r.succ.val,by change r.val+1 < M+2; omega⟩ : Fin (M+2)) = Fin.last (M+1) :=
        Fin.ext (by change r.val+1 = M+1; omega)
      rw [he,C.rotate_window_last]
      rw [periodicEnd,dite_eq_right (show ¬ (⟨r.val+1,by omega⟩ : Fin (M+2)).succ.val < M+2 by change ¬ r.val+1+1 < M+2; omega)]
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      rfl
  · have he : r = Fin.last (M+1) := Fin.ext (by have := r.isLt; change r.val = M+1; omega)
    subst r
    rw [finRotate_last,C.rotate_window_last,periodicEnd,dite_eq_right (by simp)]
    change (C.rotate (by omega)).window 0 + (↑(M+2) : ℤ) < _ ↔ _
    rw [C.rotate_window_of_lt 0 (by simp)]
    rw [periodicEnd,dite_eq_left (by simp)]
    simp only [Fin.val_zero,Fin.val_succ,zero_add]
    omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow
variable {K : Type} [Field K] {M : ℕ}
lemma scale_descentCore (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) (m : ℕ) :
    descentCore (C.scale m) (hC.powerShift m) = descentCore C hC := by
  classical
  have hd : descents (by omega) (C.scale m).window = descents (by omega) C.window := by
    ext r
    simp only [descents,Finset.mem_filter,Finset.mem_univ,true_and,C.scale_window]
    unfold periodicEnd
    split_ifs <;> rw [C.scale_window] <;> omega
  unfold descentCore
  rw [hd]
  congr 1
  funext r
  exact scale_vertex C hC m (by omega) _
lemma rotate_descentCore (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) :
    descentCore (C.rotate (by omega)) (rotate_bounded C hC _) = descentCore C hC := by
  classical
  ext v
  simp only [descentCore,Finset.mem_image]
  constructor
  · rintro ⟨r,hr,he⟩
    refine ⟨finRotate (M+2) r,(C.rotate_descent_iff r).mp hr,?_⟩
    rw [rotate_vertex] at he
    exact he
  · rintro ⟨r,hr,he⟩
    obtain ⟨s,hs⟩ := (finRotate (M+2)).surjective r
    refine ⟨s,(C.rotate_descent_iff s).mpr (hs ▸ hr),?_⟩
    rw [rotate_vertex,hs]
    exact he
lemma reroot_descentCore (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) (j : ℕ) :
    descentCore (C.reroot (by omega) j) (reroot_bounded C hC _ j) = descentCore C hC := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [C.reroot_succ]
    exact (rotate_descentCore _ (reroot_bounded C hC _ j)).trans ih
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow
variable {K : Type} [Field K] {M : ℕ}
lemma descentCore_subset (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) : descentCore C hC ⊆ face C hC (by omega) := by
  intro v hv
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨finRotate (M+2) r,Finset.mem_univ _,rfl⟩
lemma descentCore_nonempty (C : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) (hp : 0 < C.length) : (descentCore C hC).Nonempty := by
  apply Finset.Nonempty.image
  apply descents_nonempty
  · intro r s he
    dsimp only at he
    rw [C.window_mod (by omega),C.window_mod (by omega)] at he
    exact C.word.injective (Fin.ext (by exact_mod_cast he))
  · exact hp

theorem core_minimum (C D : ResidueChamber (K := K) (N := M+2))
    (hC : PolyBounded C.top) (hD : PolyBounded D.top)
    (hcore : descentCore C hC ⊆ face D hD (by omega)) : C.length ≤ D.length := by
  classical
  by_cases hz : C.length = 0
  · rw [hz]; exact Nat.zero_le _
  obtain ⟨A,hA⟩ := descentCore_nonempty C hC (by omega)
  obtain ⟨r,_,hr⟩ := Finset.mem_image.mp (descentCore_subset C hC hA)
  obtain ⟨s,_,hs⟩ := Finset.mem_image.mp (hcore hA)
  let R := C.reroot (by omega) r.val
  let S := D.reroot (by omega) s.val
  have hR : PolyBounded R.top := reroot_bounded C hC _ _
  have hS : PolyBounded S.top := reroot_bounded D hD _ _
  have hrt : R.top = C.stage r.castSucc := C.reroot_top _ r.val r.isLt.le
  have hst : S.top = D.stage s.castSucc := D.reroot_top _ s.val s.isLt.le
  have hh : Homothetic (shift K (M+2)) (R.top.map (polynomialEmbedding K (M+2)))
      (S.top.map (polynomialEmbedding K (M+2))) := by
    rw [hrt,hst]
    exact homothetic_trans _ (vertex_homothetic C hC (by omega) r)
      (hr ▸ hs ▸ homothetic_symm _ (vertex_homothetic D hD (by omega) s))
  obtain ⟨u,v,huv⟩ := hh
  have ht : (R.scale u).top = (S.scale v).top := by
    apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+2))
    change (powerShift R.top u).map _ = (powerShift S.top v).map _
    rw [powerShift_map_embedding,powerShift_map_embedding]
    exact huv
  have hc := core_minimum_same_top (R.scale u) (S.scale v) (hR.powerShift u) (hS.powerShift v) ht
    (by
      rw [scale_descentCore R hR u,scale_face S hS v (by omega)]
      change descentCore (C.reroot _ r.val) _ ⊆ face (D.reroot _ s.val) _ _
      rw [reroot_descentCore C hC r.val,reroot_face D hD s.val]
      exact hcore)
  simpa only [ResidueChamber.scale_length,R,S,ResidueChamber.reroot_length] using hc
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.FullChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
theorem core_minimum (C D : FullChamber K (M+2) (by omega))
    (hcore : C.descentCore ⊆ D.face) : C.length ≤ D.length := by
  apply BoundedChamber.core_minimum C.polynomialChamber D.polynomialChamber
    (polyBounded_vertex _) (polyBounded_vertex _)
  rwa [BoundedChamber.full_descentCore,BoundedChamber.full_face]
theorem core_not_previous (C : FullChamber K (M+2) (by omega)) (hp : 0 < C.length) :
    C.descentCore ∉ codistanceStage K (M+2) (by omega) (C.length-1) := by
  rintro ⟨D,hD,hcore⟩
  have hh := C.core_minimum D hcore
  omega

theorem previous_iff_missing_core (C : FullChamber K (M+2) (by omega))
    (hp : 0 < C.length) {s : Finset (Vertex K (M+2))} (hs : s ⊆ C.face) :
    s ∈ codistanceStage K (M+2) (by omega) (C.length-1) ↔ ¬ C.descentCore ⊆ s := by
  constructor
  · intro h hc
    exact C.core_not_previous hp (codistanceStage_downward _ _ _ _ h hc)
  · exact C.face_missing_descent_previous hs
end CoboundaryExpanders.RationalLattices.FullChamber

namespace CoboundaryExpanders.RationalLattices.FullChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
lemma core_eq_of_contains (C D : FullChamber K (M+2) (by omega))
    (hp : 0 < C.length) (hlen : C.length = D.length)
    (hcore : C.descentCore ⊆ D.face) : C.descentCore = D.descentCore := by
  classical
  have hpD : 0 < D.length := hlen ▸ hp
  have hn : C.descentCore ∉ codistanceStage K (M+2) (by omega) (D.length-1) := by
    rw [← hlen]; exact C.core_not_previous hp
  have hDC : D.descentCore ⊆ C.descentCore := by
    by_contra hh
    exact hn (D.face_missing_descent_previous hcore hh)
  apply Finset.Subset.antisymm _ hDC
  by_contra hh
  have hh' := C.face_missing_descent_previous (hDC.trans C.descentCore_subset) hh
  rw [hlen] at hh'
  exact D.core_not_previous hpD hh'
lemma core_eq_of_new_intersection (C D : FullChamber K (M+2) (by omega))
    (hp : 0 < C.length) (hlen : C.length = D.length)
    {s : Finset (Vertex K (M+2))} (hC : s ⊆ C.face) (hD : s ⊆ D.face)
    (hs : s ∉ codistanceStage K (M+2) (by omega) (C.length-1)) :
    C.descentCore = D.descentCore := by
  classical
  have hh : C.descentCore ⊆ s := by
    by_contra hh
    exact hs (C.face_missing_descent_previous hC hh)
  exact C.core_eq_of_contains D hp hlen (hh.trans hD)
end CoboundaryExpanders.RationalLattices.FullChamber

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
lemma codistanceBlock_downward (m : ℕ) (A : Finset (Vertex K (M+2)))
    {s t : Finset (Vertex K (M+2))} (hs : s ∈ codistanceBlock m A) (ht : t ⊆ s) :
    t ∈ codistanceBlock m A := by
  obtain ⟨C,hC,hA,hs⟩ := hs
  exact ⟨C,hC,hA,ht.trans hs⟩
lemma codistanceBlock_old_iff (m : ℕ) (A : Finset (Vertex K (M+2)))
    {s : Finset (Vertex K (M+2))} (hs : s ∈ codistanceBlock m A) :
    s ∈ codistanceStage K (M+2) (by omega) m ↔ ¬ A ⊆ s := by
  obtain ⟨C,hC,rfl,hs⟩ := hs
  have hh := C.previous_iff_missing_core (by omega) hs
  simpa only [hC,Nat.add_sub_cancel] using hh
lemma codistanceBlock_intersection (m : ℕ) (A B : Finset (Vertex K (M+2))) (hne : A ≠ B) :
    codistanceBlock m A ∩ codistanceBlock m B ⊆ codistanceStage K (M+2) (by omega) m := by
  classical
  intro s hs
  by_contra hn
  obtain ⟨C,hC,hA,hsC⟩ := hs.1
  obtain ⟨D,hD,hB,hsD⟩ := hs.2
  apply hne
  rw [← hA,← hB]
  exact C.core_eq_of_new_intersection D (by omega) (hC.trans hD.symm) hsC hsD
    (by simpa only [hC,Nat.add_sub_cancel] using hn)
theorem codistanceStage_successor (m : ℕ) :
    codistanceStage K (M+2) (by omega) (m+1) =
      codistanceStage K (M+2) (by omega) m ∪ ⋃ A, codistanceBlock m A := by
  ext s
  constructor
  · rintro ⟨C,hC,hs⟩
    by_cases he : C.length = m+1
    · exact Or.inr (Set.mem_iUnion.mpr ⟨C.descentCore,C,he,rfl,hs⟩)
    · exact Or.inl ⟨C,by omega,hs⟩
  · rintro (⟨C,hC,hs⟩ | hs)
    · exact ⟨C,by omega,hs⟩
    · obtain ⟨A,C,hC,_,hs⟩ := Set.mem_iUnion.mp hs
      exact ⟨C,by omega,hs⟩

lemma codistanceBlock_join (m : ℕ) (A s : Finset (Vertex K (M+2))) :
    s ∈ codistanceBlock m A ↔ ∃ u v, u ⊆ A ∧ v ∈ codistanceLink m A ∧ s = u ∪ v := by
  classical
  constructor
  · intro hs
    refine ⟨s ∩ A,s \ A,Finset.inter_subset_right,⟨(by apply Finset.disjoint_left.mpr; intro v hv hv'; exact (Finset.mem_sdiff.mp hv').2 hv),
      codistanceBlock_downward m A hs Finset.sdiff_subset⟩,?_⟩
    ext v
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  · rintro ⟨u,v,hu,⟨_,C,hC,hA,hv⟩,rfl⟩
    refine ⟨C,hC,hA,Finset.union_subset ?_ hv⟩
    exact hu.trans (hA ▸ C.descentCore_subset)
end CoboundaryExpanders.RationalLattices

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Joins
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Binary and finite joins, augmented exactness, and bounded cone constructions.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains.Join

section
open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma prepend_boundary (B : Finset V) (c : Raw W) :
    rawBoundary (prepend B c) = prepend B (rawBoundary c) +
      ∑ v ∈ B, prepend (B.erase v) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, Finset.sum_add_distrib]; abel
  | single A a =>
    rw [prepend_single, boundary_disjSum_single, rawBoundary_single, map_sum]
    simp only [prepend_single]

omit [DecidableEq V] [DecidableEq W] in
lemma leftAction_prepend (T : Raw W →ₗ[k] Raw W) (B : Finset V) (c : Raw W) :
    leftAction T (prepend B c) = prepend B (T c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single A a => simp

lemma leftAction_homotopy (T : Raw W →ₗ[k] Raw W) (A : Finset W) (B : Finset V) :
    rawBoundary (leftAction T (Finsupp.single (A.disjSum B) 1)) +
      leftAction T (rawBoundary (Finsupp.single (A.disjSum B) 1)) =
        prepend B (rawBoundary (T (Finsupp.single A 1)) + T (rawBoundary (Finsupp.single A 1))) := by
  rw [show Finsupp.single (A.disjSum B) (1 : k) = prepend B (Finsupp.single A 1) by simp]
  rw [leftAction_prepend, prepend_boundary, prepend_boundary, map_add, map_sum]
  simp only [leftAction_prepend]
  rw [map_add]
  have hz := twice (∑ v ∈ B, prepend (B.erase v) (T (Finsupp.single A 1)))
  have he : ∀ a b c : Raw (W ⊕ V), (a+b)+(c+b) = (a+c)+(b+b) := by intros; abel
  rw [he, hz, add_zero]

lemma left_contraction {X : CoboundaryExpanders.InfiniteChains.Complex W} {n R : ℕ} (H : BoundedCone X n R)
    (s : Finset (W ⊕ V)) (hs : s.toLeft ∈ X.faces) (hn : s.toLeft.card ≤ n) :
    rawBoundary (leftAction H.hom (Finsupp.single s 1)) +
      leftAction H.hom (rawBoundary (Finsupp.single s 1)) = Finsupp.single s 1 := by
  rw [← Finset.toLeft_disjSum_toRight (u := s)]
  rw [leftAction_homotopy]
  rw [H.contraction s.toLeft hs hn, prepend_single]

lemma leftAction_graded {X : CoboundaryExpanders.InfiniteChains.Complex W} (Y : CoboundaryExpanders.InfiniteChains.Complex V) {n R : ℕ}
    (H : BoundedCone X n R) (r : ℕ) (c : Raw (W ⊕ V))
    (hc : c ∈ supported (graded {s | s ∈ (complex X Y).faces ∧ s.toLeft.card ≤ n} r)) :
    leftAction H.hom c ∈ supported (graded (complex X Y).faces (r+1)) := by
  apply map_supported _ _ _ _ c hc
  intro s hs a
  rw [leftAction_single]
  have hH := H.map_graded s.toLeft.card hs.1.2 (Finsupp.single s.toLeft a)
    (single_mem_supported (P := graded X.faces s.toLeft.card) ⟨hs.1.1.1, rfl⟩ a)
  apply map_supported (prepend s.toRight) (graded X.faces (s.toLeft.card+1))
    (graded (complex X Y).faces (r+1)) _ _ hH
  intro A hA b
  rw [prepend_single]
  apply single_mem_supported
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa using hA.1
  · simpa using hs.1.1.2
  · rw [Finset.card_disjSum, hA.2]
    have he := Finset.card_toLeft_add_card_toRight (u := s)
    dsimp [graded] at hs
    omega

lemma fill_small_left {X : CoboundaryExpanders.InfiniteChains.Complex W} (Y : CoboundaryExpanders.InfiniteChains.Complex V) {n R : ℕ}
    (H : BoundedCone X n R) (r : ℕ) (c : Raw (W ⊕ V))
    (hc : c ∈ supported (graded {s | s ∈ (complex X Y).faces ∧ s.toLeft.card ≤ n} r))
    (hz : rawBoundary c = 0) :
    ∃ b ∈ supported (graded (complex X Y).faces (r+1)), rawBoundary b = c := by
  refine ⟨leftAction H.hom c, leftAction_graded Y H r c hc, ?_⟩
  have he := linear_eq_on_supported
    (rawBoundary.comp (leftAction H.hom) + (leftAction H.hom).comp rawBoundary)
    LinearMap.id (graded {s | s ∈ (complex X Y).faces ∧ s.toLeft.card ≤ n} r)
    (fun s hs => left_contraction H s hs.1.1.1 hs.1.2) c hc
  change rawBoundary (leftAction H.hom c) + leftAction H.hom (rawBoundary c) = c at he
  simpa only [hz, map_zero, add_zero] using he

end

open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
lemma truncated_downward (X : CoboundaryExpanders.InfiniteChains.Complex W) (Y : CoboundaryExpanders.InfiniteChains.Complex V) (M : ℕ) :
    ∀ {s t}, s ∈ truncated X Y M → t ⊆ s → t ∈ truncated X Y M := by
  intro s t hs ht
  exact ⟨(complex X Y).downward hs.1 ht,
    (Finset.card_le_card (Finset.toLeft_subset_toLeft ht)).trans hs.2⟩

lemma relative_enlarge_old (P O Q : Set (Finset V)) (r : ℕ)
    (hQ : ∀ {s t}, s ∈ Q → t ⊆ s → t ∈ Q)
    (hOP : O ⊆ P) (hPQ : P ∩ Q ⊆ O) (h : RelativeExactIn O Q r) :
    RelativeExactIn P Q r := by
  intro c hc hz
  have hb := boundary_supported Q hQ c (graded_forget Q r hc)
  have hδ : rawBoundary c ∈ supported O := by
    rw [mem_supported] at hz hb ⊢
    exact fun s hs => hPQ ⟨hz s hs, hb s hs⟩
  obtain ⟨b, hbc, hres⟩ := h c hc hδ
  exact ⟨b, hbc, supported_mono (P := graded O r) (Q := graded P r) (fun s hs => ⟨hOP hs.1, hs.2⟩) hres⟩

lemma relativeExactIn_self (P : Set (Finset V)) (r : ℕ) : RelativeExactIn P P r := by
  intro c hc _
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  simpa using hc

lemma truncated_step (X : CoboundaryExpanders.InfiniteChains.Complex W) (Y : CoboundaryExpanders.InfiniteChains.Complex V) (M r m : ℕ)
    (hr : r ≤ M+m+1) (hY : ∀ j ≤ m, ExactIn Y.faces j) :
    RelativeExactIn (truncated X Y M) (truncated X Y (M+1)) r := by
  classical
  let I := {F : Finset W // F ∈ X.faces ∧ F.card = M+1}
  let A : I → Set (Finset (W ⊕ V)) := fun F => joinFaces F.val Y
  have hAP (F : I) : RelativeExactIn (truncated X Y M) (A F) r := by
    apply relative_enlarge_old (truncated X Y M) (oldFaces F.val Y) (A F) r
      (joinFaces_downward F.val Y)
    · intro s hs
      refine ⟨⟨X.downward F.property.1 hs.1.1, hs.1.2⟩, ?_⟩
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs.1.1, hs.2⟩)
      rw [F.property.2] at hlt
      omega
    · intro s hs
      refine ⟨hs.2, ?_⟩
      intro he
      have hn := hs.1.2
      rw [he, F.property.2] at hn
      omega
    · apply relativeExactIn_join
      intro hf
      exact hY (r-F.val.card) (by rw [F.property.2]; omega)
  have hAA (F G : I) (hFG : F ≠ G) : A F ∩ A G ⊆ truncated X Y M := by
    intro s hs
    refine ⟨⟨X.downward F.property.1 hs.1.1, hs.1.2⟩, ?_⟩
    have hle := Finset.card_le_card hs.1.1
    rw [F.property.2] at hle
    by_contra hnot
    have he : s.toLeft.card = M+1 := by omega
    have hF : s.toLeft = F.val := Finset.eq_of_subset_of_card_le hs.1.1 (by omega)
    have hG : s.toLeft = G.val := Finset.eq_of_subset_of_card_le hs.2.1 (by rw [G.property.2, he])
    exact hFG (Subtype.ext (hF.symm.trans hG))
  have hU := relativeExactIn_iUnion (truncated X Y M) A r
    (fun F => joinFaces_downward F.val Y) hAA hAP
  have he : truncated X Y (M+1) = truncated X Y M ∪ ⋃ F : I, A F := by
    ext s
    constructor
    · intro hs
      by_cases hn : s.toLeft.card ≤ M
      · exact Or.inl ⟨hs.1, hn⟩
      · apply Or.inr
        exact Set.mem_iUnion.mpr ⟨⟨s.toLeft, hs.1.1, by have := hs.2; omega⟩,
          ⟨Finset.Subset.refl _, hs.1.2⟩⟩
    · intro hs
      rcases hs with hs | hs
      · exact ⟨hs.1, hs.2.trans (by omega)⟩
      · obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hs
        exact ⟨⟨X.downward F.property.1 hF.1, hF.2⟩,
          (Finset.card_le_card hF.1).trans_eq F.property.2⟩
  rw [he]
  apply relativeExactIn_union _ _ _ r (truncated_downward X Y M) _
    (fun _ hs => hs.1) (relativeExactIn_self _ r) hU
  intro s t hs ht
  obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hs
  exact Set.mem_iUnion.mpr ⟨F, joinFaces_downward F.val Y hF ht⟩

theorem exactIn_join {X : CoboundaryExpanders.InfiniteChains.Complex W} (Y : CoboundaryExpanders.InfiniteChains.Complex V) {n R : ℕ}
    (H : BoundedCone X n R) (m : ℕ) (hY : ∀ j ≤ m, ExactIn Y.faces j)
    (r : ℕ) (hr : r ≤ n+m+1) : ExactIn (complex X Y).faces r := by
  have hf (M : ℕ) : ∀ c ∈ supported (graded (truncated X Y (n+M)) r),
      rawBoundary c = 0 → ∃ b ∈ supported (graded (complex X Y).faces (r+1)),
        rawBoundary b = c := by
    induction M with
    | zero =>
      intro c hc hz
      exact fill_small_left Y H r c (by simpa only [Nat.add_zero, truncated] using hc) hz
    | succ M ih =>
      intro c hc hz
      obtain ⟨e, he, hres⟩ := truncated_step X Y (n+M) r m (by omega) hY c
        (by simpa only [Nat.add_assoc, Nat.succ_eq_add_one] using hc) (by rw [hz]; exact Submodule.zero_mem _)
      have hzres : rawBoundary (c-rawBoundary e) = 0 := by
        rw [map_sub, hz]
        have hh := LinearMap.congr_fun (rawBoundary_squared (V := W ⊕ V)) e
        change rawBoundary (rawBoundary e) = 0 at hh
        rw [hh, sub_self]
      obtain ⟨b, hb, hbc⟩ := ih (c-rawBoundary e) hres hzres
      refine ⟨e+b, Submodule.add_mem _ ?_ hb, ?_⟩
      · exact supported_mono (P := graded (truncated X Y (n+M+1)) (r+1))
          (Q := graded (complex X Y).faces (r+1)) (fun s hs => ⟨hs.1.1, hs.2⟩) he
      · rw [map_add, hbc]
        abel
  intro c hc hz
  apply hf r c _ hz
  rw [mem_supported] at hc ⊢
  intro s hs
  refine ⟨⟨(hc s hs).1, ?_⟩, (hc s hs).2⟩
  have he := Finset.card_toLeft_add_card_toRight (u := s)
  have hcard := (hc s hs).2
  omega

end CoboundaryExpanders.InfiniteChains.Join

end

open scoped Polynomial BigOperators

namespace CoboundaryExpanders.InfiniteChains.Join

section
open Attachment Cone
open scoped BigOperators
variable {V : Type} [DecidableEq V]
lemma split_left {L : ℕ} (s : Finset (Fin (L+1) × V)) :
    (s.image (splitEquiv L)).toLeft = fiber s 0 := by
  ext v
  rw [Finset.mem_toLeft,mem_fiber]
  constructor
  · rintro hh
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hh
    have he' : x = (0,v) := (splitEquiv L).injective (he.trans (splitEquiv_zero L v).symm)
    exact he' ▸ hx
  · intro hh
    exact Finset.mem_image.mpr ⟨(0,v),hh,rfl⟩
lemma split_right_fiber {L : ℕ} (s : Finset (Fin (L+1) × V)) (i : Fin L) :
    fiber (s.image (splitEquiv L)).toRight i = fiber s i.succ := by
  ext v
  rw [mem_fiber,Finset.mem_toRight,mem_fiber]
  constructor
  · rintro hh
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hh
    have he' : x = (i.succ,v) := (splitEquiv L).injective (he.trans (splitEquiv_succ L i v).symm)
    exact he' ▸ hx
  · intro hh
    exact Finset.mem_image.mpr ⟨(i.succ,v),hh,rfl⟩
lemma finiteComplex_split {L : ℕ} (X : Fin (L+1) → CoboundaryExpanders.InfiniteChains.Complex V) (s : Finset (Fin (L+1) × V)) :
    s ∈ (finiteComplex X).faces ↔
      s.image (splitEquiv L) ∈ (complex (X 0) (finiteComplex (fun i => X i.succ))).faces := by
  change (∀ i, fiber s i ∈ (X i).faces) ↔
    (s.image (splitEquiv L)).toLeft ∈ (X 0).faces ∧
      ∀ i, fiber (s.image (splitEquiv L)).toRight i ∈ (X i.succ).faces
  simp only [split_left,split_right_fiber]
  constructor
  · exact fun h => ⟨h 0,fun i => h i.succ⟩
  · rintro ⟨h0,h⟩ i
    induction i using Fin.cases
    · exact h0
    · exact h _
lemma finiteComplex_one (X : Fin 1 → CoboundaryExpanders.InfiniteChains.Complex V) (s : Finset (Fin 1 × V)) :
    s ∈ (finiteComplex X).faces ↔ s.image Prod.snd ∈ (X 0).faces := by
  have h : fiber s 0 = s.image Prod.snd := by
    unfold fiber
    congr 1
    apply Finset.filter_true_of_mem
    intro x hx
    exact Subsingleton.elim _ _
  change (∀ i, fiber s i ∈ (X i).faces) ↔ _
  simp only [Fin.forall_fin_one,h]
end

section
open Attachment Cone
variable {V W : Type} [DecidableEq V] [DecidableEq W]
lemma exactIn_empty_left [Nonempty W] (X : CoboundaryExpanders.InfiniteChains.Complex V) (Y : CoboundaryExpanders.InfiniteChains.Complex W)
    (hX : ∀ s ∈ X.faces, s = ∅) (r : ℕ) (hY : ExactIn Y.faces r) :
    ExactIn (complex X Y).faces r := by
  classical
  let f : V ⊕ W → W := Sum.elim (fun _ => Classical.choice (inferInstance : Nonempty W)) id
  have hret (s : Finset (V ⊕ W)) (hs : s ∈ (complex X Y).faces) :
      ∀ v ∈ s, Sum.inr (f v) = v := by
    intro v hv
    cases v with
    | inl v =>
      have hh : v ∈ s.toLeft := by simpa using hv
      rw [hX s.toLeft hs.1] at hh
      exact False.elim (Finset.notMem_empty _ hh)
    | inr w => rfl
  have him (s : Finset (V ⊕ W)) (hs : s ∈ (complex X Y).faces) : s.image f = s.toRight := by
    ext w
    constructor
    · rintro hh
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hh
      rw [Finset.mem_toRight,hret s hs v hv]
      exact hv
    · intro hh
      exact Finset.mem_image.mpr ⟨Sum.inr w,by simpa using hh,rfl⟩
  apply exactIn_retract f Sum.inr (complex X Y).faces Y.faces
    (fun s hs => (him s hs).symm ▸ hs.2) _ _ _ hret r hY
  · intro s hs
    change _ ∈ X.faces ∧ _ ∈ Y.faces
    have hl : (s.image (Sum.inr : W → V ⊕ W)).toLeft = ∅ := by ext v; simp [Finset.mem_toLeft]
    have hr : (s.image (Sum.inr : W → V ⊕ W)).toRight = s := by ext w; simp [Finset.mem_toRight]
    rw [hl,hr]
    exact ⟨X.empty_mem,hs⟩
  · intro s hs x hx y hy hh
    have he := congrArg (Sum.inr : W → V ⊕ W) hh
    rwa [hret s hs x hx,hret s hs y hy] at he
  · intro s hs
    exact Sum.inr_injective.injOn
lemma exactIn_empty_right [Nonempty V] (X : CoboundaryExpanders.InfiniteChains.Complex V) (Y : CoboundaryExpanders.InfiniteChains.Complex W)
    (hY : ∀ s ∈ Y.faces, s = ∅) (r : ℕ) (hX : ExactIn X.faces r) :
    ExactIn (complex X Y).faces r := by
  classical
  let f : V ⊕ W → V := Sum.elim id (fun _ => Classical.choice (inferInstance : Nonempty V))
  have hret (s : Finset (V ⊕ W)) (hs : s ∈ (complex X Y).faces) :
      ∀ v ∈ s, Sum.inl (f v) = v := by
    intro v hv
    cases v with
    | inr v =>
      have hh : v ∈ s.toRight := by simpa using hv
      rw [hY s.toRight hs.2] at hh
      exact False.elim (Finset.notMem_empty _ hh)
    | inl w => rfl
  have him (s : Finset (V ⊕ W)) (hs : s ∈ (complex X Y).faces) : s.image f = s.toLeft := by
    ext w
    constructor
    · rintro hh
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hh
      rw [Finset.mem_toLeft,hret s hs v hv]
      exact hv
    · intro hh
      exact Finset.mem_image.mpr ⟨Sum.inl w,by simpa using hh,rfl⟩
  apply exactIn_retract f Sum.inl (complex X Y).faces X.faces
    (fun s hs => (him s hs).symm ▸ hs.1) _ _ _ hret r hX
  · intro s hs
    change _ ∈ X.faces ∧ _ ∈ Y.faces
    have hl : (s.image (Sum.inl : V → V ⊕ W)).toLeft = s := by ext v; simp [Finset.mem_toLeft]
    have hr : (s.image (Sum.inl : V → V ⊕ W)).toRight = ∅ := by ext w; simp [Finset.mem_toRight]
    rw [hl,hr]
    exact ⟨hs,Y.empty_mem⟩
  · intro s hs x hx y hy hh
    have he := congrArg (Sum.inl : V → V ⊕ W) hh
    rwa [hret s hs x hx,hret s hs y hy] at he
  · intro s hs
    exact Sum.inl_injective.injOn
end

open Attachment Cone
open scoped BigOperators
variable {V : Type} [DecidableEq V]
lemma finiteComplex_only_empty {L : ℕ} (X : Fin L → CoboundaryExpanders.InfiniteChains.Complex V)
    (hX : ∀ i s, s ∈ (X i).faces → s = ∅)
    (s : Finset (Fin L × V)) (hs : s ∈ (finiteComplex X).faces) : s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨i,v⟩ hv
  have hh : v ∈ fiber s i := (mem_fiber s i v).mpr hv
  rw [hX i (fiber s i) (hs i)] at hh
  exact Finset.notMem_empty _ hh

theorem exactIn_finiteComplex_all [Nonempty V] (L : ℕ) (X : Fin (L+1) → CoboundaryExpanders.InfiniteChains.Complex V)
    (a : Fin (L+1) → ℕ)
    (hcones : ∀ i, 0 < a i → ∃ R : ℕ, Nonempty (BoundedCone (X i) (a i-1) R))
    (hzero : ∀ i, a i = 0 → ∀ s ∈ (X i).faces, s = ∅)
    (r : ℕ) (hr : r < ∑ i, a i) : ExactIn (finiteComplex X).faces r := by
  induction L generalizing r with
  | zero =>
    have he : (∑ i, a i) = a 0 := Fin.sum_univ_one a
    rw [he] at hr
    obtain ⟨R,⟨H⟩⟩ := hcones 0 (by omega)
    apply exactIn_equivalence oneEquiv _ (X 0).faces (finiteComplex_one X) r
    exact H.exactIn r (by omega)
  | succ L ih =>
    let b : ℕ := ∑ i : Fin (L+1), a i.succ
    rw [Fin.sum_univ_succ] at hr
    change r < a 0 + b at hr
    apply exactIn_equivalence (splitEquiv (L+1)) _ _ (finiteComplex_split X) r
    by_cases h0 : a 0 = 0
    · apply exactIn_empty_left (X 0) (finiteComplex (fun i => X i.succ)) (hzero 0 h0) r
      exact ih (fun i => X i.succ) (fun i => a i.succ) (fun i => hcones i.succ)
        (fun i => hzero i.succ) r (by change r < b; omega)
    · obtain ⟨R,⟨H⟩⟩ := hcones 0 (by omega)
      by_cases hb : b = 0
      · have hz (i : Fin (L+1)) : a i.succ = 0 := by
          have he := Finset.sum_eq_zero_iff.mp hb
          exact he i (Finset.mem_univ _)
        apply exactIn_empty_right (X 0) (finiteComplex (fun i => X i.succ))
          (finiteComplex_only_empty _ (fun i => hzero i.succ (hz i))) r
        exact H.exactIn r (by omega)
      · have hY : ∀ j ≤ b-1, ExactIn (finiteComplex (fun i : Fin (L+1) => X i.succ)).faces j := by
          intro j hj
          exact ih (fun i => X i.succ) (fun i => a i.succ) (fun i => hcones i.succ)
            (fun i => hzero i.succ) j (by change j < b; omega)
        apply exactIn_join _ H (b-1) hY r
        omega
end CoboundaryExpanders.InfiniteChains.Join

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_ChamberCones
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite pivots, polynomial residue-chamber links, and exactness via finite joins.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.FinitePivots
open scoped BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma leading_single (i : Fin N) : Leading (Pi.single i (1 : K)) i := by
  classical
  simp only [Leading,Pi.single_eq_same,ne_eq,one_ne_zero,not_false_eq_true,true_and]
  intro j hj
  simpa only [Pi.single_apply] using (ite_eq_right (ne_of_gt hj) : (if j = i then (1 : K) else 0) = 0)

lemma eq_top_of_pivots (W : Submodule K (Fin N → K))
    (h : ∀ i, HasPivot W i) : W = ⊤ := by
  classical
  have hmem' : ∀ n, ∀ i : Fin N, i.val = n → Pi.single i (1 : K) ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hei
      obtain ⟨v,hv,hvl⟩ := h i
      have hs : (∑ j ∈ Finset.univ.erase i, v j • Pi.single j (1 : K)) ∈ W := by
        apply W.sum_mem
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        rcases lt_or_gt_of_ne hji with hlt | hgt
        · exact W.smul_mem _ (ih j.val (by omega) j rfl)
        · simp [hvl.2 j hgt]
      have he : v = (∑ j ∈ Finset.univ.erase i, v j • Pi.single j (1 : K)) +
          v i • Pi.single i (1 : K) := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        ext j
        simp [Finset.sum_apply,Pi.single_apply]
      have hh := W.sub_mem hv hs
      rw [show v - (∑ j ∈ Finset.univ.erase i, v j • Pi.single j (1 : K)) =
          v i • Pi.single i 1 by rw [sub_eq_iff_eq_add]; simpa [add_comm] using he] at hh
      have hh' := W.smul_mem (v i)⁻¹ hh
      rw [smul_smul,inv_mul_cancel₀ hvl.1,one_smul] at hh'
      exact hh'
  have hmem (i : Fin N) := hmem' i.val i rfl
  apply top_unique
  intro v _
  have he : v = ∑ i : Fin N, v i • Pi.single i (1 : K) := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  rw [he]
  exact W.sum_mem fun i _ => W.smul_mem _ (hmem i)

lemma disjoint_prefix_iff (W : Submodule K (Fin N → K)) (k : ℕ) :
    Disjoint W (prefSpace K N k) ↔ ∀ i, HasPivot W i → k ≤ i.val := by
  rw [Submodule.disjoint_def]
  constructor
  · intro h i ⟨v,hv,hvl⟩
    by_contra hn
    have hp : v ∈ prefSpace K N k := by
      intro j hj
      exact hvl.2 j (by change i.val < j.val; omega)
    have hz := h v hv hp
    exact hvl.1 (congr_fun hz i)
  · intro h v hv hp
    by_contra hz
    obtain ⟨i,hi⟩ := exists_leading hz
    have hh := h i ⟨v,hv,hi⟩
    exact hi.1 (hp i hh)

theorem isCompl_prefix_iff (W : Submodule K (Fin N → K)) (k : ℕ) :
    IsCompl W (prefSpace K N k) ↔ ∀ i, HasPivot W i ↔ k ≤ i.val := by
  classical
  constructor
  · intro h i
    refine ⟨(disjoint_prefix_iff W k).mp h.disjoint i,?_⟩
    intro hi
    have hm : Pi.single i (1 : K) ∈ W ⊔ prefSpace K N k := by rw [h.sup_eq_top]; trivial
    obtain ⟨w,hw,z,hz,he⟩ := Submodule.mem_sup.mp hm
    refine ⟨w,hw,?_,?_⟩
    · have hze := hz i hi
      have hei := congr_fun he i
      simp only [Pi.add_apply,Pi.single_eq_same,hze,add_zero] at hei
      exact hei ▸ one_ne_zero
    · intro j hj
      have hze := hz j (by change i.val < j.val at hj; omega)
      have hej := congr_fun he j
      simpa [hze,Pi.single_eq_of_ne (ne_of_gt hj)] using hej
  · intro h
    have hd := (disjoint_prefix_iff W k).mpr fun i hi => (h i).mp hi
    have ht : W ⊔ prefSpace K N k = ⊤ := by
      apply eq_top_of_pivots
      intro i
      by_cases hi : k ≤ i.val
      · obtain ⟨v,hv,hl⟩ := (h i).mpr hi
        exact ⟨v,(show W ≤ W ⊔ prefSpace K N k from le_sup_left) hv,hl⟩
      · refine ⟨Pi.single i 1,(show prefSpace K N k ≤ W ⊔ prefSpace K N k from le_sup_right) ?_,leading_single i⟩
        intro j hj
        have hji : j ≠ i := by intro he; subst j; omega
        simp [hji]
    exact ⟨hd, codisjoint_iff.mpr ht⟩

end CoboundaryExpanders.FinitePivots

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

theorem selectedResidue_pivot_iff (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val))
    (D : Submodule K[X] (V K N)) (hD : HasPivots D)
    (hCD : diagonalModule b (Finset.univ.image σ) ≤ D)
    (hDA : D ≤ Submodule.span K[X] (Set.range b)) (r : Fin M) :
    FinitePivots.HasPivot (selectedResidue b σ D) r ↔ pivotDegree D hD (σ r) = a (σ r) := by
  classical
  have hmon : a (σ r) ≤ pivotDegree D hD (σ r) := by
    have := pivotDegree_antitone (span_hasPivots b a hb) hD hDA (σ r)
    rwa [span_pivotDegree b a hb (σ r)] at this
  constructor
  · rintro ⟨x,hx,hxl⟩
    have hm : selectedSection b σ x ∈ D := hx
    exact le_antisymm (pivotDegree_min D hD (σ r) hm (selectedSection_leading b a hb σ hσ x r hxl)) hmon
  · intro he
    obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp (hDA (pivot_mem D hD (σ r)))
    have hl : Leading (∑ i, f i • b i) (σ r) (a (σ r)) := by
      rw [hf,← he]
      exact pivot_leading D hD (σ r)
    obtain ⟨hfi,hdeg,hhigh⟩ := combination_lowest_pivot b a hb f (σ r) hl
    refine ⟨fun j => (f (σ j)).coeff 0,?_,?_,?_⟩
    · apply selectedSection_mem_of_combination b σ
        (fun i j hij => hσ.injective (congrArg (fun t => N*a t+t.val) hij)) D hCD f
      rw [hf]
      exact pivot_mem D hD (σ r)
    · intro hz
      dsimp only at hz
      apply hfi
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg,hz,Polynomial.C_0]
    · intro j hj
      dsimp only
      rw [hhigh (σ j) (hσ hj)]
      simp

theorem selectedResidue_opposed_iff (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val))
    (D : Submodule K[X] (V K N)) (hD : HasPivots D)
    (hCD : diagonalModule b (Finset.univ.image σ) ≤ D)
    (hDA : D ≤ Submodule.span K[X] (Set.range b)) (k : ℕ) :
    IsCompl (selectedResidue b σ D) (FinitePivots.prefSpace K M k) ↔
      ∀ r, pivotDegree D hD (σ r) = a (σ r) ↔ k ≤ r.val := by
  rw [FinitePivots.isCompl_prefix_iff]
  simp only [selectedResidue_pivot_iff b a hb σ hσ D hD hCD hDA]

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N M : ℕ}

lemma prefixPattern_iff_good (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) (D : SelectedInterval b σ) :
    PrefixPattern b a hb σ D ↔
      (FinitePivots.prefixFlag K M).Good (selectedIntervalEquiv b a hb σ hσ D) := by
  let W := selectedResidue b σ D.val
  have hop (k : ℕ) := selectedResidue_opposed_iff b a hb σ hσ D.val
    (selectedInterval_hasPivots b a hb σ D) D.property.1 D.property.2 k
  change PrefixPattern b a hb σ D ↔ 0 < finrank K W ∧ finrank K W < M ∧
    IsCompl W (FinitePivots.prefSpace K M (M-finrank K W))
  constructor
  · rintro ⟨k,hk,hkM,hpat⟩
    have hc := (hop k).mpr hpat
    have hr := Submodule.finrank_add_eq_of_isCompl hc
    rw [FinitePivots.prefSpace_finrank k hkM.le] at hr
    simp only [Module.finrank_pi,Fintype.card_fin] at hr
    have hdim : finrank K W + k = M := hr
    have he : M-finrank K W = k := by omega
    exact ⟨by omega,by omega,he ▸ hc⟩
  · rintro ⟨hpos,hlt,hc⟩
    refine ⟨M-finrank K W,by omega,by omega,(hop _).mp hc⟩

lemma prefixPattern_faces_equiv (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val)) (s : Finset (SelectedInterval b σ)) :
    s ∈ (prefixPatternComplex b a hb σ).faces ↔
      s.image (selectedIntervalEquiv b a hb σ hσ) ∈ (FinitePivots.prefixFlag K M).complex.faces := by
  classical
  let e := selectedIntervalEquiv b a hb σ hσ
  constructor
  · intro hs
    constructor
    · rintro W hW
      obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hW
      exact (prefixPattern_iff_good b a hb σ hσ D).mp (hs.1 D hD)
    · intro W hW Z hZ hne
      obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hW
      obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hZ
      rcases hs.2 hD hE (fun h => hne (congrArg e h)) with h | h
      · exact Or.inl (e.monotone h)
      · exact Or.inr (e.monotone h)
  · intro hs
    constructor
    · intro D hD
      exact (prefixPattern_iff_good b a hb σ hσ D).mpr
        (hs.1 (e D) (Finset.mem_image.mpr ⟨D,hD,rfl⟩))
    · intro D hD E hE hne
      have h := hs.2 (Finset.mem_image.mpr ⟨D,hD,rfl⟩)
        (Finset.mem_image.mpr ⟨E,hE,rfl⟩) (fun h => hne (e.injective h))
      exact h.imp e.le_iff_le.mp e.le_iff_le.mp

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))
lemma block_weight (a z : Fin (N+1)) (r : Fin (z.val-a.val)) :
    (N*C.blockDegree a (wordSlice C.word a z r)+(wordSlice C.word a z r).val : ℕ) =
      N*pivotDegree C.top C.hasTop (C.word ⟨a.val+r.val,by have := r.isLt; have := z.isLt; omega⟩)+
        (C.word ⟨a.val+r.val,by have := r.isLt; have := z.isLt; omega⟩).val := by
  simp only [wordSlice,blockDegree,Equiv.symm_apply_apply,Fin.val_mk]
  rw [ite_eq_right (by omega),Nat.add_zero]
lemma sorted_block_selection (a z : Fin (N+1))
    (hs : (AffineWindow.slice C.window a z).Pairwise (· ≤ ·)) :
    StrictMono (fun r => N*C.blockDegree a (wordSlice C.word a z r)+(wordSlice C.word a z r).val) := by
  intro r s hrs
  have hh := (List.pairwise_ofFn.mp hs) hrs
  have he : C.window ⟨a.val+r.val,by have := r.isLt; have := z.isLt; omega⟩ ≠
      C.window ⟨a.val+s.val,by have := s.isLt; have := z.isLt; omega⟩ := by
    intro h
    have hv := congrArg Fin.val (C.window_injective h)
    change a.val+r.val = a.val+s.val at hv
    exact (ne_of_lt hrs) (Fin.ext (by omega))
  have hl := lt_of_le_of_ne hh he
  dsimp only
  unfold window at hl
  rw [C.block_weight,C.block_weight]
  exact_mod_cast hl
end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open AffineWindow
variable {K : Type} [Field K] {N L : ℕ}
variable (C D : ResidueChamber (K := K) (N := N))
theorem fixed_stage_minimum_iff_window (hN : 0 < N) (ht : C.top = D.top)
    (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (hstage : ∀ r, C.stage (c r) = D.stage (c r))
    (hsorted : ∀ r : Fin L, (slice C.window (c r.castSucc) (c r.succ)).Pairwise (· ≤ ·)) :
    D.length = C.length ↔ D.window = C.window := by
  constructor
  · intro he
    have hlen := C.fixed_stage_length D hN ht c hc h0 hl hstage hsorted
    have hz : ((blocks D.window c).map (pairs disorder)).sum = 0 := by omega
    have hb : blocks C.window c = blocks D.window c := by
      apply sorted_blocks_eq_of_zero _ _ _ hz
      apply blocks_forall₂
      intro r
      exact ⟨C.window_slice_perm D ht _ _ (hstage _) (hstage _),hsorted r⟩
    have hh := congrArg List.flatten hb
    rw [flatten_blocks _ _ hc,flatten_blocks _ _ hc,h0,hl,slice_full,slice_full] at hh
    exact (List.ofFn_inj.mp hh).symm
  · intro he
    simp only [length,he]
lemma word_eq_of_window_eq (hN : 0 < N) (hw : D.window = C.window) : D.word = C.word := by
  apply Equiv.ext
  intro i
  have hh := congrArg (fun f : Fin N → ℤ => f i % (N : ℤ)) hw
  rw [D.window_mod hN,C.window_mod hN] at hh
  exact Fin.ext (by exact_mod_cast hh)
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

theorem finite_simultaneous_basis (A : Submodule K[X] (V K N)) (hA : HasPivots A)
    (s : Finset (Submodule K[X] (V K N))) (hAs : A ∈ s)
    (hs : (s : Set (Submodule K[X] (V K N))).Pairwise (fun D E => D ≤ E ∨ E ≤ D))
    (hinterval : ∀ D ∈ s, powerShift A 1 ≤ D ∧ D ≤ A) :
    ∃ b : Fin N → V K N,
      (∀ i, Leading (b i) i (pivotDegree A hA i)) ∧
      Submodule.span K[X] (Set.range b) = A ∧
      ∀ D ∈ s, ∀ hP : HasPivots D,
        Submodule.span K[X] (Set.range fun i =>
          if pivotDegree D hP i = pivotDegree A hA i then b i else (Polynomial.X : K[X]) • b i) = D := by
  classical
  have hP (D : Submodule K[X] (V K N)) (hD : D ∈ s) : HasPivots D := by
    intro i
    obtain ⟨m,v,hv,hl⟩ := powerShift_hasPivots A hA 1 i
    exact ⟨m,v,(hinterval D hD).1 hv,hl⟩
  let S (i : Fin N) : Finset (Submodule K[X] (V K N)) :=
    s.filter fun D => ∃ hD : HasPivots D, pivotDegree D hD i = pivotDegree A hA i
  have hS (i : Fin N) : (S i).Nonempty := by
    refine ⟨A,Finset.mem_filter.mpr ⟨hAs,hA,rfl⟩⟩
  have hmin (i : Fin N) : ∃ D, Minimal (fun D => D ∈ S i) D :=
    ((S i).finite_toSet.isPWO.exists_minimal (hS i))
  choose B hB using hmin
  have hBs (i : Fin N) : B i ∈ s := (Finset.mem_filter.mp (hB i).1).1
  have hdeg (i : Fin N) : pivotDegree (B i) (hP (B i) (hBs i)) i = pivotDegree A hA i :=
    (Finset.mem_filter.mp (hB i).1).2.choose_spec
  let b (i : Fin N) := pivot (B i) (hP (B i) (hBs i)) i
  have hb (i : Fin N) : Leading (b i) i (pivotDegree A hA i) := by
    rw [← hdeg i]
    exact pivot_leading _ _ _
  have hmem (i : Fin N) : b i ∈ A := (hinterval _ (hBs i)).2 (pivot_mem _ _ _)
  have hspan (D : Submodule K[X] (V K N)) (hD : D ∈ s) (hPD : HasPivots D) :
      Submodule.span K[X] (Set.range fun i =>
        if pivotDegree D hPD i = pivotDegree A hA i then b i else (Polynomial.X : K[X]) • b i) = D := by
    let c (i : Fin N) := if pivotDegree D hPD i = pivotDegree A hA i then b i else (Polynomial.X : K[X]) • b i
    have hinc (i : Fin N) := interval_pivot_increment hA hPD (hinterval D hD).2 (hinterval D hD).1 i
    have hc (i : Fin N) : c i ∈ D := by
      dsimp only [c]
      split_ifs with he
      · have hDi : D ∈ S i := Finset.mem_filter.mpr ⟨hD,hPD,he⟩
        have hBD : B i ≤ D := by
          by_cases heq : B i = D
          · exact heq.le
          · rcases hs (hBs i) hD heq with h | h
            · exact h
            · exact (hB i).2 hDi h
        exact hBD (pivot_mem _ _ _)
      · apply (hinterval D hD).1
        refine ⟨b i,hmem i,?_⟩
        simp [powerLinear]
    have hcl (i : Fin N) : Leading (c i) i (pivotDegree D hPD i) := by
      dsimp only [c]
      split_ifs with he
      · rw [he]; exact hb i
      · have hh : pivotDegree D hPD i = pivotDegree A hA i+1 := (hinc i).resolve_left he
        rw [hh]
        simpa using leading_X_pow (hb i) 1
    exact span_of_minimal D c (pivotDegree D hPD) hc hcl (fun hv hl => pivotDegree_min _ _ _ hv hl)
  refine ⟨b,hb,?_,hspan⟩
  simpa only [ite_true] using hspan A hAs hA

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))

theorem face_prescribed_refinement
    (s : Finset (Submodule K[X] (V K N))) (htop : C.top ∈ s)
    (hs : (s : Set (Submodule K[X] (V K N))).Pairwise (fun D E => D ≤ E ∨ E ≤ D))
    (hi : ∀ D ∈ s, powerShift C.top 1 ≤ D ∧ D ≤ C.top)
    (hp : ∀ D ∈ s, ∃ (r : Fin (N+1)) (hP : HasPivots D),
      ∀ i, pivotDegree D hP i = pivotDegree C.top C.hasTop i +
        if (C.word.symm i).val < r.val then 1 else 0) :
    ∃ E : ResidueChamber (K := K) (N := N), E.top = C.top ∧ E.window = C.window ∧
      ∀ D ∈ s, ∃ r, E.stage r = D := by
  classical
  obtain ⟨b,hb,hspan,hDs⟩ := finite_simultaneous_basis C.top C.hasTop s htop hs hi
  let E := diagonalChamber b (pivotDegree C.top C.hasTop) hb C.word
  refine ⟨E,hspan,?_,?_⟩
  · funext r
    exact diagonalChamber_window b (pivotDegree C.top C.hasTop) hb C.word r
  · intro D hD
    obtain ⟨r,hP,hdegree⟩ := hp D hD
    refine ⟨r,?_⟩
    change diagonalModule b (wordPrefix C.word r) = D
    rw [← hDs D hD hP]
    unfold diagonalModule
    congr 2
    funext i
    rw [hdegree i]
    simp only [diagonalFamily,wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> simp_all
end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
variable (C : ResidueChamber (K := K) (N := N))
lemma stage_hasProfile (r : Fin (N+1)) : C.HasProfile (C.stage r) r := ⟨C.hasStage r,C.stage_degree r⟩
lemma profile_increments {D : Submodule K[X] (V K N)} {r : Fin (N+1)} (h : C.HasProfile D r) :
    ∃ hD : HasPivots D, incrementSet C.top D C.hasTop hD =
      incrementSet C.top (C.stage r) C.hasTop (C.hasStage r) := by
  obtain ⟨hD,hdeg⟩ := h
  refine ⟨hD,?_⟩
  ext i
  simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and,hdeg,C.stage_degree]
lemma profile_unique {D : Submodule K[X] (V K N)} {r s : Fin (N+1)}
    (hr : C.HasProfile D r) (hs : C.HasProfile D s) : r = s := by
  obtain ⟨hD,hri⟩ := C.profile_increments hr
  obtain ⟨_,hsi⟩ := C.profile_increments hs
  have h := congrArg Finset.card (hri.symm.trans hsi)
  rw [C.increments_card,C.increments_card] at h
  exact Fin.ext h
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open InfiniteChains AffineWindow
variable {K : Type} [Field K] {N L : ℕ}
variable (C : ResidueChamber (K := K) (N := N))
lemma profile_stage_le_top (r : Fin (N+1)) : C.stage r ≤ C.top := by
  rw [← C.initial]
  exact C.strict.antitone (Fin.zero_le _)
lemma stage_hasProfile_of_window (E : ResidueChamber (K := K) (N := N)) (hN : 0 < N)
    (ht : E.top = C.top) (hw : E.window = C.window) (r : Fin (N+1)) :
    C.HasProfile (E.stage r) r := by
  refine ⟨E.hasStage r,?_⟩
  intro i
  have he := C.word_eq_of_window_eq E hN hw
  simpa only [ht,he] using E.stage_degree r i
lemma cuts_interval (c : Fin (L+1) → Fin (N+1)) (_ : StrictMono c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (r : Fin (N+1)) (hr : r ∉ Finset.univ.image c) :
    ∃ j : Fin L, c j.castSucc < r ∧ r < c j.succ := by
  classical
  let S : Finset (Fin (L+1)) := Finset.univ.filter (fun j => c j ≤ r)
  have hS : S.Nonempty := ⟨0,by simp [S,h0]⟩
  let j := S.max' hS
  have hj : c j ≤ r := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hneq (k : Fin (L+1)) : r ≠ c k := by
    intro he
    exact hr (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,he.symm⟩)
  have hjL : j.val < L := by
    by_contra hh
    have he : j = Fin.last L := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    rw [he,hl] at hj
    exact hneq (Fin.last L) ((le_antisymm (Fin.le_last r) hj).trans hl.symm)
  let k : Fin L := ⟨j.val,hjL⟩
  have hk : k.castSucc = j := Fin.ext rfl
  refine ⟨k,?_,?_⟩
  · rw [hk]; exact lt_of_le_of_ne hj (hneq j).symm
  · by_contra hh
    have hmem : k.succ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_of_not_gt hh⟩
    have hle := Finset.le_max' S k.succ hmem
    change k.val+1 ≤ j.val at hle
    dsimp only [k] at hle
    omega

lemma intervalProfile_interval (c : Fin (L+1) → Fin (N+1)) {D : Submodule K[X] (V K N)}
    (hD : C.IntervalProfile c D) : powerShift C.top 1 ≤ D ∧ D ≤ C.top := by
  obtain ⟨j,hlo,hup,r,_,_,_⟩ := hD
  exact ⟨(C.lower _).trans hlo,hup.trans (C.profile_stage_le_top _)⟩
lemma intervalProfile_compare_fixed (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c)
    {D : Submodule K[X] (V K N)} (hD : C.IntervalProfile c D) (k : Fin (L+1)) :
    D ≤ C.stage (c k) ∨ C.stage (c k) ≤ D := by
  obtain ⟨j,hlo,hup,r,_,_,_⟩ := hD
  by_cases hk : k ≤ j.castSucc
  · exact Or.inl (hup.trans (C.strict.antitone (hc hk)))
  · exact Or.inr ((C.strict.antitone (hc (show j.succ ≤ k from by
      change j.val+1 ≤ k.val
      change ¬k.val ≤ j.val at hk
      omega))).trans hlo)
lemma intervalProfile_not_fixed (c : Fin (L+1) → Fin (N+1)) (hc : StrictMono c)
    {D : Submodule K[X] (V K N)} (hD : C.IntervalProfile c D) : D ∉ C.fixedStages c := by
  classical
  obtain ⟨j,_,_,r,har,hrz,hp⟩ := hD
  rintro hm
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hm
  have he : r = c k := C.profile_unique hp (hk ▸ C.stage_hasProfile (c k))
  rw [he] at har hrz
  have h1 := hc.lt_iff_lt.mp har
  have h2 := hc.lt_iff_lt.mp hrz
  change j.val < k.val at h1
  change k.val < j.val+1 at h2
  omega

theorem rootedMinimumLink_iff (hN : 0 < N)
    (c : Fin (L+1) → Fin (N+1)) (hc : StrictMono c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (hsorted : ∀ j : Fin L, (slice C.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·))
    (s : Finset (Submodule K[X] (V K N))) :
    s ∈ (C.rootedMinimumLink c).faces ↔
      (∀ D ∈ s, C.IntervalProfile c D) ∧
      (s : Set (Submodule K[X] (V K N))).Pairwise (fun D E => D ≤ E ∨ E ≤ D) := by
  classical
  constructor
  · rintro ⟨hd,E,ht,hEl,hfix,hface⟩
    have hw := (C.fixed_stage_minimum_iff_window E hN ht.symm c hc.monotone h0 hl
      (fun j => (hfix j).symm) hsorted).mp hEl
    constructor
    · intro D hD
      obtain ⟨r,rfl⟩ := hface D hD
      have hn : r ∉ Finset.univ.image c := by
        rintro hh
        obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hh
        exact Finset.disjoint_left.mp hd hD (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,(hfix k).symm⟩)
      obtain ⟨j,hjr,hrj⟩ := cuts_interval c hc h0 hl r hn
      refine ⟨j,?_,?_,r,hjr,hrj,C.stage_hasProfile_of_window E hN ht hw r⟩
      · rw [← hfix]; exact E.strict.antitone hrj.le
      · rw [← hfix]; exact E.strict.antitone hjr.le
    · intro D hD F hF hne
      obtain ⟨r,rfl⟩ := hface D hD
      obtain ⟨t,rfl⟩ := hface F hF
      rcases le_total r t with h | h
      · exact Or.inr (E.strict.antitone h)
      · exact Or.inl (E.strict.antitone h)
  · rintro ⟨hprof,hchain⟩
    let u := s ∪ C.fixedStages c
    have htop : C.top ∈ u := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,by rw [h0,C.initial]⟩
    have hu : (u : Set (Submodule K[X] (V K N))).Pairwise (fun D E => D ≤ E ∨ E ≤ D) := by
      intro D hD E hE hne
      rcases Finset.mem_union.mp hD with hD | hD <;> rcases Finset.mem_union.mp hE with hE | hE
      · exact hchain hD hE hne
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hE
        exact C.intervalProfile_compare_fixed c hc.monotone (hprof D hD) j
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
        exact (C.intervalProfile_compare_fixed c hc.monotone (hprof E hE) j).symm
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
        obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hE
        rcases le_total (c j) (c k) with h | h
        · exact Or.inr (C.strict.antitone h)
        · exact Or.inl (C.strict.antitone h)
    have hi : ∀ D ∈ u, powerShift C.top 1 ≤ D ∧ D ≤ C.top := by
      intro D hD
      rcases Finset.mem_union.mp hD with hD | hD
      · exact C.intervalProfile_interval c (hprof D hD)
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
        exact ⟨C.lower _,C.profile_stage_le_top _⟩
    have hp : ∀ D ∈ u, ∃ r, C.HasProfile D r := by
      intro D hD
      rcases Finset.mem_union.mp hD with hD | hD
      · obtain ⟨j,_,_,r,_,_,hp⟩ := hprof D hD
        exact ⟨r,hp⟩
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
        exact ⟨c j,C.stage_hasProfile _⟩
    obtain ⟨E,ht,hw,hE⟩ := C.face_prescribed_refinement u htop hu hi hp
    refine ⟨Finset.disjoint_left.mpr (fun D hD => C.intervalProfile_not_fixed c hc (hprof D hD)),
      E,ht,?_,?_,fun D hD => hE D (Finset.mem_union_left _ hD)⟩
    · simp only [length,hw]
    · intro j
      obtain ⟨r,hr⟩ := hE (C.stage (c j)) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
      have he : r = c j := C.profile_unique
        (hr ▸ C.stage_hasProfile_of_window E hN ht hw r) (C.stage_hasProfile (c j))
      exact he ▸ hr
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N M : ℕ}

theorem uniform_polynomial_residue_cones (n : ℕ) :
    ∃ Q R : ℕ, ∀ (K : Type) [Field K] [Fintype K] (N M : ℕ)
      (b : Fin N → V K N) (a : Fin N → ℕ) (hb : ∀ i, Leading (b i) i (a i))
      (σ : Fin M → Fin N), StrictMono (fun i => N*a (σ i)+(σ i).val) →
      n+2 ≤ M → Q < Fintype.card K →
        Nonempty (BoundedCone (prefixPatternComplex b a hb σ) n R) := by
  classical
  obtain ⟨Q,R,h⟩ := SphericalOpposition.CompleteFlag.exists_uniform_cones n
  refine ⟨Q,R,?_⟩
  intro K _ _ N M b a hb σ hσ hM hq
  let e := selectedIntervalEquiv b a hb σ hσ
  let X := prefixPatternComplex b a hb σ
  let Y := (FinitePivots.prefixFlag K M).complex
  have he : ∀ s, s ∈ X.faces ↔ s.image e ∈ Y.faces := prefixPattern_faces_equiv b a hb σ hσ
  have hg (s) (hs : s ∈ Y.faces) : s.image e.symm ∈ X.faces := by
    apply (he _).mpr
    simpa only [Finset.image_image,Function.comp_def,OrderIso.apply_symm_apply,Finset.image_id'] using hs
  exact ⟨(h K (Fin M → K) M (FinitePivots.prefixFlag K M) hM hq).some.retract e e.symm
    (fun s hs => (he s).mp hs) hg (fun _ _ => e.injective.injOn)
    (fun _ _ => e.symm.injective.injOn) (fun _ _ _ _ => e.symm_apply_apply _)⟩
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N : ℕ}
variable (C : ResidueChamber (K := K) (N := N))
lemma profileInterval_empty (a z : Fin (N+1)) (h : z.val ≤ a.val+1)
    (s : Finset (Submodule K[X] (V K N))) (hs : s ∈ (C.profileIntervalComplex a z).faces) : s = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro D hD
  obtain ⟨_,_,r,har,hrz,_⟩ := hs.1 D hD
  change a.val < r.val at har
  change r.val < z.val at hrz
  omega

theorem uniform_profileInterval_cones (n : ℕ) :
    ∃ Q R : ℕ, ∀ (K : Type) [Field K] [Fintype K] (N : ℕ)
      (C : ResidueChamber (K := K) (N := N)) (a z : Fin (N+1)),
      n+2 ≤ z.val-a.val → (AffineWindow.slice C.window a z).Pairwise (· ≤ ·) →
      Q < Fintype.card K → Nonempty (BoundedCone (C.profileIntervalComplex a z) n R) := by
  classical
  obtain ⟨Q,R,h⟩ := uniform_polynomial_residue_cones n
  refine ⟨Q,R,?_⟩
  intro K _ _ N C a z hdim hsorted hq
  obtain ⟨b,hb,_,_,hstage⟩ := C.diagonal_representation
  have haz : a ≤ z := by change a.val ≤ z.val; omega
  exact ⟨C.profileIntervalCone b hb hstage a z haz
    (h K N (z.val-a.val) (C.blockBasis b a) (C.blockDegree a)
      (C.blockBasis_leading b hb a) (wordSlice C.word a z)
      (C.sorted_block_selection a z hsorted) hdim hq).some⟩
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N L : ℕ}
variable (C : ResidueChamber (K := K) (N := N))
lemma profileBetween_unique (c : Fin (L+1) → Fin (N+1)) (hc : StrictMono c)
    {i j : Fin L} {D : Submodule K[X] (V K N)}
    (hi : C.ProfileBetween (c i.castSucc) (c i.succ) D)
    (hj : C.ProfileBetween (c j.castSucc) (c j.succ) D) : i = j := by
  obtain ⟨_,_,r,hir,hri,hr⟩ := hi
  obtain ⟨_,_,t,hjt,htj,ht⟩ := hj
  have he : r = t := C.profile_unique hr ht
  subst t
  have h1 : j.castSucc < i.succ := hc.lt_iff_lt.mp (hjt.trans hri)
  have h2 : i.castSucc < j.succ := hc.lt_iff_lt.mp (hir.trans htj)
  apply Fin.ext
  change j.val < i.val+1 at h1
  change i.val < j.val+1 at h2
  omega
lemma profileBetween_compare (c : Fin (L+1) → Fin (N+1)) (hc : Monotone c)
    {i j : Fin L} {D E : Submodule K[X] (V K N)} (hij : i < j)
    (hi : C.ProfileBetween (c i.castSucc) (c i.succ) D)
    (hj : C.ProfileBetween (c j.castSucc) (c j.succ) E) : E ≤ D := by
  apply hj.2.1.trans
  apply (C.strict.antitone (hc (show i.succ ≤ j.castSucc from by
    change i.val+1 ≤ j.val
    change i.val < j.val at hij
    omega))).trans hi.1

theorem rootedMinimumLink_exact_of_join (hN : 0 < N)
    (c : Fin (L+1) → Fin (N+1)) (hc : StrictMono c)
    (h0 : c 0 = 0) (hl : c (Fin.last L) = Fin.last N)
    (hsorted : ∀ j : Fin L, (AffineWindow.slice C.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·))
    (r : ℕ) (H : ExactIn (Join.finiteComplex
      (fun j : Fin L => C.profileIntervalComplex (c j.castSucc) (c j.succ))).faces r) :
    ExactIn (C.rootedMinimumLink c).faces r := by
  classical
  have hL : 0 < L := by
    by_contra hh
    have he : Fin.last L = (0 : Fin (L+1)) := Fin.ext (by simp; omega)
    rw [he,h0] at hl
    have hh := congrArg Fin.val hl
    simp at hh
    omega
  let tag : Submodule K[X] (V K N) → Fin L := fun D =>
    if h : C.IntervalProfile c D then h.choose else ⟨0,hL⟩
  have htag (D) (hD : C.IntervalProfile c D) :
      C.ProfileBetween (c (tag D).castSucc) (c (tag D).succ) D := by
    simpa only [tag,dite_eq_left hD,ProfileBetween] using hD.choose_spec
  let f : Submodule K[X] (V K N) → Fin L × Submodule K[X] (V K N) := fun D => (tag D,D)
  let X := Join.finiteComplex (fun j : Fin L => C.profileIntervalComplex (c j.castSucc) (c j.succ))
  have hf (s) (hs : s ∈ (C.rootedMinimumLink c).faces) : s.image f ∈ X.faces := by
    have hh := (C.rootedMinimumLink_iff hN c hc h0 hl hsorted s).mp hs
    intro j
    constructor
    · intro D hD
      have hm := (Join.mem_fiber (s.image f) j D).mp hD
      obtain ⟨E,hE,he⟩ := Finset.mem_image.mp hm
      have he2 : E = D := congrArg Prod.snd he
      subst E
      have ht : tag D = j := congrArg Prod.fst he
      exact ht ▸ htag D (hh.1 D hE)
    · intro D hD E hE hne
      have hin (F) (hF : F ∈ Join.fiber (s.image f) j) : F ∈ s := by
        obtain ⟨G,hG,hg⟩ := Finset.mem_image.mp ((Join.mem_fiber (s.image f) j F).mp hF)
        have he : G = F := congrArg Prod.snd hg
        exact he ▸ hG
      exact hh.2 (hin D hD) (hin E hE) hne
  have hg (s) (hs : s ∈ X.faces) : s.image Prod.snd ∈ (C.rootedMinimumLink c).faces := by
    apply (C.rootedMinimumLink_iff hN c hc h0 hl hsorted _).mpr
    constructor
    · intro D hD
      obtain ⟨⟨i,E⟩,hE,rfl⟩ := Finset.mem_image.mp hD
      exact ⟨i,(hs i).1 E ((Join.mem_fiber s i E).mpr hE)⟩
    · intro D hD E hE hne
      obtain ⟨⟨i,D⟩,hDi,rfl⟩ := Finset.mem_image.mp hD
      obtain ⟨⟨j,E⟩,hEj,rfl⟩ := Finset.mem_image.mp hE
      have hi := (hs i).1 D ((Join.mem_fiber s i D).mpr hDi)
      have hj := (hs j).1 E ((Join.mem_fiber s j E).mpr hEj)
      rcases lt_trichotomy i j with hij | hij | hij
      · exact Or.inr (C.profileBetween_compare c hc.monotone hij hi hj)
      · subst j
        exact (hs i).2 ((Join.mem_fiber s i D).mpr hDi) ((Join.mem_fiber s i E).mpr hEj) hne
      · exact Or.inl (C.profileBetween_compare c hc.monotone hij hj hi)
  apply exactIn_retract f Prod.snd _ X.faces hf hg ?_ ?_ (by intros; rfl) r H
  · intro s hs D hD E hE hh
    exact congrArg Prod.snd hh
  · intro s hs x hx y hy hh
    rcases x with ⟨i,D⟩
    rcases y with ⟨j,E⟩
    change D = E at hh
    subst E
    have hi := (hs i).1 D ((Join.mem_fiber s i D).mpr hx)
    have hj := (hs j).1 D ((Join.mem_fiber s j D).mpr hy)
    have he := C.profileBetween_unique c hc hi hj
    exact congrArg (fun k => (k,D)) he
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

namespace CoboundaryExpanders.PolynomialVectors.ResidueChamber
open scoped Polynomial BigOperators
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
private lemma sum_gaps {L : ℕ} (c : Fin (L+1) → ℕ) (hc : Monotone c) :
    (∑ j : Fin L, (c j.succ - c j.castSucc)) + c 0 = c (Fin.last L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Fin.sum_univ_succ]
    have ht := ih (fun i : Fin (L+1) => c i.succ) (fun i j hij => hc (Fin.succ_le_succ_iff.mpr hij))
    have hle := hc (Fin.zero_le (1 : Fin (L+2)))
    change (c 1-c 0)+(∑ j : Fin L, (c j.succ.succ - c j.castSucc.succ))+c 0 = c (Fin.last (L+1))
    change (∑ j : Fin L, (c j.succ.succ - c j.castSucc.succ))+c 1 = c (Fin.last (L+1)) at ht
    omega

theorem uniform_rootedMinimumLink_exact (N : ℕ) :
    ∃ Q : ℕ, ∀ (K : Type) [Field K] [Fintype K]
      (C : ResidueChamber (K := K) (N := N)) (L : ℕ)
      (c : Fin (L+1) → Fin (N+1)),
      0 < N → StrictMono c → c 0 = 0 → c (Fin.last L) = Fin.last N →
      (∀ j : Fin L, (AffineWindow.slice C.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·)) →
      Q < Fintype.card K → ∀ r < N-L, ExactIn (C.rootedMinimumLink c).faces r := by
  classical
  choose Q R h using uniform_profileInterval_cones
  let T := (Finset.range (N+1)).sup Q
  refine ⟨T,?_⟩
  intro K _ _ C L c hN hc h0 hl hsort hq r hr
  let a : Fin L → ℕ := fun j => (c j.succ).val-(c j.castSucc).val-1
  have hstep (j : Fin L) : (c j.castSucc).val < (c j.succ).val := hc (by exact Fin.castSucc_lt_succ)
  have hsum : (∑ j, a j) + L = N := by
    have hg := sum_gaps (fun j => (c j).val) (fun i j hij => hc.monotone hij)
    rw [h0,hl] at hg
    simp only [Fin.val_zero,Fin.val_last,Nat.add_zero] at hg
    have he : (∑ j : Fin L, (a j+1)) = (∑ j : Fin L, ((c j.succ).val-(c j.castSucc).val)) := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [a]
      have hh := hstep j
      omega
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using he.trans hg
  apply C.rootedMinimumLink_exact_of_join hN c hc h0 hl hsort r
  have hr' : r < ∑ j, a j := by omega
  cases L with
  | zero => simp at hr'
  | succ L =>
    apply Join.exactIn_finiteComplex_all L _ a ?_ ?_ r hr'
    · intro j hj
      have hd := (c j.succ).isLt
      have hs := hstep j
      have hwide : (a j-1)+2 ≤ (c j.succ).val-(c j.castSucc).val := by dsimp [a] at *; omega
      have hn : a j-1 < N+1 := by dsimp [a] at *; omega
      have hqn : Q (a j-1) ≤ T := Finset.le_sup (f := Q) (Finset.mem_range.mpr hn)
      exact ⟨R (a j-1),h (a j-1) K N C (c j.castSucc) (c j.succ) hwide (hsort j) (hqn.trans_lt hq)⟩
    · intro j hj s hs
      apply C.profileInterval_empty (c j.castSucc) (c j.succ) _ s hs
      dsimp [a] at hj
      omega
end CoboundaryExpanders.PolynomialVectors.ResidueChamber

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_LatticeCones
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bounded-chamber and codistance attachments, lattice acyclicity, and uniform positive coset exactness.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}

theorem based_at (P : Submodule K[X] (PolynomialVectors.V K (M+2))) (hP : PolyBounded P)
    (D : FullChamber K (M+2) (by omega))
    (hroot : normalizedPolynomial (by omega) P hP ∈ D.face) :
    ∃ E : ResidueChamber (K := K) (N := M+2), ∃ hE : PolyBounded E.top,
      E.top = P ∧ face E hE (by omega) = D.face ∧ E.length = D.length ∧
      descentCore E hE = D.descentCore := by
  classical
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hroot
  obtain ⟨m,hm⟩ := normalizedPolynomial_spec (by omega) P hP
  let E := (D.polynomialChamber.reroot (by omega) j.val).scale m
  have hE : PolyBounded E.top := (reroot_bounded D.polynomialChamber (polyBounded_vertex _) (by omega) j.val).powerShift m
  refine ⟨E,hE,?_,?_,?_,?_⟩
  · apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+2))
    change (powerShift (D.polynomialChamber.reroot (by omega) j.val).top m).map _ = _
    rw [powerShift_map_embedding,D.polynomialChamber.reroot_top (by omega) j.val j.isLt.le]
    change level (shift K (M+2)) ((D.stage j.castSucc).map _) m = _
    rw [D.stage_castSucc,polynomialLattice_map,hj]
    exact hm.symm
  · change face ((D.polynomialChamber.reroot (by omega) j.val).scale m) _ _ = _
    rw [scale_face _ (reroot_bounded D.polynomialChamber (polyBounded_vertex _) (by omega) j.val) m (by omega),
      reroot_face D.polynomialChamber (polyBounded_vertex _) j.val,full_face]
  · change ((D.polynomialChamber.reroot (by omega) j.val).scale m).length = _
    rw [ResidueChamber.scale_length,ResidueChamber.reroot_length]
    rfl
  · change descentCore ((D.polynomialChamber.reroot (by omega) j.val).scale m) _ = _
    rw [scale_descentCore _ (reroot_bounded D.polynomialChamber (polyBounded_vertex _) (by omega) j.val) m,
      reroot_descentCore D.polynomialChamber (polyBounded_vertex _) j.val,full_descentCore]

theorem normalization_core (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top) :
    ∃ E : FullChamber K (M+2) (by omega), E.face = face C hC (by omega) ∧
      E.length = C.length ∧ E.descentCore = descentCore C hC := by
  classical
  obtain ⟨E,hf,hl⟩ := normalization C hC
  have hroot : normalizedPolynomial (by omega) C.top hC ∈ E.face := by
    rw [hf]
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,by
      change normalizedPolynomial _ (C.stage 0) _ = _
      simp only [C.initial]⟩
  obtain ⟨R,hR,ht,hface,_,hcore⟩ := based_at C.top hC E hroot
  have he : R = C := eq_of_face_of_top R C hR hC (by omega) ht (hface.trans hf)
  exact ⟨E,hf,hl,he ▸ hcore.symm⟩
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
variable (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
lemma normalizeModule_of_bounded (D : Submodule K[X] (PolynomialVectors.V K (M+2))) (hD : PolyBounded D) :
    normalizeModule C hC D = normalizedPolynomial (by omega) D hD := by
  simp only [normalizeModule,dite_eq_left hD]
include hC in
lemma rootInterval_bounded {D : Submodule K[X] (PolynomialVectors.V K (M+2))}
    (hD : RootInterval C D) : PolyBounded D := (hC.powerShift 1).mono hD.1
lemma normalizeModule_stage (E : ResidueChamber (K := K) (N := M+2)) (hE : PolyBounded E.top)
    (r : Fin (M+2)) : normalizeModule C hC (E.stage r.castSucc) = vertex E hE (by omega) r := by
  exact normalizeModule_of_bounded C hC _ (stage_bounded E hE _)
lemma normalizeModule_initial : normalizeModule C hC C.top = vertex C hC (by omega) 0 := by
  rw [← C.initial]
  exact normalizeModule_stage C hC C hC 0
lemma normalizeModule_terminal : normalizeModule C hC (powerShift C.top 1) = vertex C hC (by omega) 0 := by
  rw [normalizeModule_of_bounded C hC _ (hC.powerShift 1),normalizedPolynomial_power]
  exact (normalizeModule_of_bounded C hC _ hC).symm.trans (normalizeModule_initial C hC)
lemma rootInterval_stage (E : ResidueChamber (K := K) (N := M+2)) (ht : E.top = C.top)
    (r : Fin (M+2)) : RootInterval C (E.stage r.castSucc) := by
  rw [RootInterval,← ht]
  exact ⟨E.lower _,E.profile_stage_le_top _,nonterminal_ne E r⟩
lemma normalizeModule_injective : Set.InjOn (normalizeModule C hC) (RootInterval C) := by
  intro D hD E hE he
  have hd := rootInterval_bounded C hC hD
  have hε := rootInterval_bounded C hC hE
  rw [normalizeModule_of_bounded C hC D hd,normalizeModule_of_bounded C hC E hε] at he
  apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+2))
  apply homothetic_interval_eq (C.top.map (polynomialEmbedding K (M+2)))
  · exact Submodule.map_mono hD.2.1
  · exact Submodule.map_mono hE.2.1
  · change level (shift K (M+2)) (C.top.map _) 1 ≤ _
    rw [← powerShift_map_embedding]
    exact Submodule.map_mono hD.1
  · change level (shift K (M+2)) (C.top.map _) 1 ≤ _
    rw [← powerShift_map_embedding]
    exact Submodule.map_mono hE.1
  · intro hh
    apply hD.2.2
    apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+2))
    rw [powerShift_map_embedding]
    exact hh
  · intro hh
    apply hE.2.2
    apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+2))
    rw [powerShift_map_embedding]
    exact hh
  · exact homothetic_trans _ (normalizedPolynomial_homothetic (by omega) D hd)
      (he ▸ homothetic_symm _ (normalizedPolynomial_homothetic (by omega) E hε))
lemma liftModule_normalize {D : Submodule K[X] (PolynomialVectors.V K (M+2))} (hD : RootInterval C D) :
    liftModule C hC (normalizeModule C hC D) = D := by
  classical
  have hex : ∃ E, RootInterval C E ∧ normalizeModule C hC E = normalizeModule C hC D := ⟨D,hD,rfl⟩
  rw [liftModule,dite_eq_left hex]
  exact normalizeModule_injective C hC hex.choose_spec.1 hD hex.choose_spec.2
lemma liftModule_vertex (E : ResidueChamber (K := K) (N := M+2)) (hE : PolyBounded E.top)
    (ht : E.top = C.top) (r : Fin (M+2)) :
    liftModule C hC (vertex E hE (by omega) r) = E.stage r.castSucc := by
  rw [← normalizeModule_stage C hC E hE r]
  exact liftModule_normalize C hC (rootInterval_stage C E ht r)
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow
variable {K : Type} [Field K] {M L : ℕ}
variable (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
lemma normalizeModule_stage_succ (r : Fin (M+2)) :
    normalizeModule C hC (C.stage r.succ) = vertex C hC (by omega) (finRotate (M+2) r) := by
  by_cases hr : r.val < M+1
  · rw [finRotate_of_lt hr]
    exact normalizeModule_stage C hC C hC ⟨r.val+1,by omega⟩
  · have he : r = Fin.last (M+1) := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
    subst r
    rw [finRotate_last]
    change normalizeModule C hC (C.stage (Fin.last (M+2))) = _
    rw [C.terminal]
    exact normalizeModule_terminal C hC
lemma descentCore_card : (descentCore C hC).card = (descents (by omega) C.window).card := by
  classical
  apply Finset.card_image_of_injective
  exact (vertex_injective C hC (by omega)).comp (finRotate (M+2)).injective
lemma root_mem_core_iff : vertex C hC (by omega) 0 ∈ descentCore C hC ↔
    Fin.last (M+1) ∈ descents (by omega) C.window := by
  classical
  constructor
  · intro hh
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hh
    have hh := vertex_injective C hC (by omega) he
    have hr' : r = Fin.last (M+1) := (finRotate (M+2)).injective (hh.trans finRotate_last.symm)
    exact hr' ▸ hr
  · intro hh
    exact Finset.mem_image.mpr ⟨Fin.last (M+1),hh,by rw [finRotate_last]⟩
lemma fixedStages_image (c : Fin (L+1) → Fin (M+3))
    (hc : Set.range c = cutSet (by omega) C.window) :
    (C.fixedStages c).image (normalizeModule C hC) = insert (vertex C hC (by omega) 0) (descentCore C hC) := by
  classical
  have hmem (r : Fin (M+3)) : (∃ j, c j = r) ↔ r ∈ cutSet (by omega) C.window := by
    change r ∈ Set.range c ↔ _
    rw [hc]
    rfl
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    have hr := (hmem (c j)).mp ⟨j,rfl⟩
    rcases Finset.mem_insert.mp hr with hz | hr
    · rw [hz,C.initial,normalizeModule_initial]
      exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.mp hr with hz | hr
      · rw [hz,C.terminal,normalizeModule_terminal]
        exact Finset.mem_insert_self _ _
      · obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hr
        rw [← he,normalizeModule_stage_succ]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
  · intro v hv
    rcases Finset.mem_insert.mp hv with he | hv
    · obtain ⟨j,hj⟩ := (hmem 0).mpr (Finset.mem_insert_self _ _)
      apply Finset.mem_image.mpr
      refine ⟨C.top,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by rw [hj,C.initial]⟩,?_⟩
      exact (normalizeModule_initial C hC).trans he.symm
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j,hj⟩ := (hmem r.succ).mpr (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r,hr,rfl⟩)))
      exact Finset.mem_image.mpr ⟨C.stage r.succ,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by rw [hj]⟩,
        normalizeModule_stage_succ C hC r⟩
lemma cut_rank_eq_core_card (c : Fin (L+1) ↪o Fin (M+3))
    (hc : Set.range c = cutSet (by omega) C.window)
    (hroot : vertex C hC (by omega) 0 ∈ descentCore C hC) : L = (descentCore C hC).card := by
  classical
  have hl := (root_mem_core_iff C hC).mp hroot
  have he : Finset.univ.image c = cutSet (by omega) C.window := by
    ext r
    simpa only [Finset.mem_image,Finset.mem_univ,true_and] using
      (show (∃ j, c j = r) ↔ r ∈ cutSet (by omega) C.window from by
        change r ∈ Set.range c ↔ _
        rw [hc]
        rfl)
  have hcard := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ c.injective,Finset.card_univ,Fintype.card_fin] at hcard
  have hn : Fin.last (M+2) ∈ (descents (by omega) C.window).image Fin.succ :=
    Finset.mem_image.mpr ⟨Fin.last (M+1),hl,rfl⟩
  have hz : (0 : Fin (M+3)) ∉ (descents (by omega) C.window).image Fin.succ := by simp
  rw [cutSet,Finset.insert_eq_of_mem hn,Finset.card_insert_of_notMem hz,
    Finset.card_image_of_injective _ (Fin.succ_injective _)] at hcard
  rw [descentCore_card]
  omega
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow
variable {K : Type} [Field K] {M L : ℕ}
variable (C E : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top) (hE : PolyBounded E.top)
lemma fixed_stages_of_core (ht : E.top = C.top)
    (c : Fin (L+1) → Fin (M+3)) (hc : Set.range c = cutSet (by omega) C.window)
    (hcore : descentCore C hC ⊆ face E hE (by omega)) : ∀ j, E.stage (c j) = C.stage (c j) := by
  intro j
  have hr : c j ∈ cutSet (by omega) C.window := by change c j ∈ (cutSet (by omega) C.window : Set _); rw [← hc]; exact Set.mem_range_self j
  rcases Finset.mem_insert.mp hr with hz | hr
  · rw [hz,E.initial,C.initial,ht]
  · rcases Finset.mem_insert.mp hr with hz | hr
    · rw [hz,E.terminal,C.terminal,ht]
    · obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hr
      rw [← he]
      by_cases hh : r.val < M+1
      · have hmem := hcore (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
        rw [finRotate_of_lt hh] at hmem
        exact (shared_vertex_stage C E hC hE (by omega) ht.symm ⟨r.val+1,by omega⟩ hmem).symm
      · have heq : r.succ = Fin.last (M+2) := Fin.ext (by have := r.isLt; change r.val+1=M+2; omega)
        rw [heq,E.terminal,C.terminal,ht]
lemma core_eq_of_window_fixed (ht : E.top = C.top) (hw : E.window = C.window)
    (c : Fin (L+1) → Fin (M+3)) (hc : Set.range c = cutSet (by omega) C.window)
    (hfix : ∀ j, E.stage (c j) = C.stage (c j)) : descentCore E hE = descentCore C hC := by
  classical
  unfold descentCore
  rw [hw]
  apply Finset.image_congr
  intro r hr
  dsimp only
  by_cases hh : r.val < M+1
  · have hmem : r.succ ∈ cutSet (by omega) C.window :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r,hr,rfl⟩))
    change r.succ ∈ (cutSet (by omega) C.window : Set _) at hmem
    rw [← hc] at hmem
    obtain ⟨j,hj⟩ := hmem
    have hs : E.stage r.succ = C.stage r.succ := hj ▸ hfix j
    rw [finRotate_of_lt hh]
    change normalizedPolynomial _ (E.stage _) _ = normalizedPolynomial _ (C.stage _) _
    have hi : (⟨r.val+1,by omega⟩ : Fin (M+2)).castSucc = r.succ := Fin.ext rfl
    simp only [hi,hs]
  · have he : r = Fin.last (M+1) := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
    subst r
    rw [finRotate_last]
    change normalizedPolynomial _ (E.stage 0) _ = normalizedPolynomial _ (C.stage 0) _
    simp only [E.initial,C.initial,ht]
lemma fixedStages_top (c : Fin (L+1) → Fin (M+3)) (h0 : c 0 = 0) : C.top ∈ C.fixedStages c := by
  classical
  exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,by rw [h0,C.initial]⟩
lemma fixedStages_bottom (c : Fin (L+1) → Fin (M+3)) (hl : c (Fin.last L) = Fin.last (M+2)) :
    powerShift C.top 1 ∈ C.fixedStages c := by
  classical
  exact Finset.mem_image.mpr ⟨Fin.last L,Finset.mem_univ _,by rw [hl,C.terminal]⟩
lemma fixedStages_interval (c : Fin (L+1) → Fin (M+3)) {D : Submodule K[X] (PolynomialVectors.V K (M+2))}
    (hD : D ∈ C.fixedStages c) (hne : D ≠ powerShift C.top 1) : RootInterval C D := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
  exact ⟨C.lower _,C.profile_stage_le_top _,hne⟩
lemma core_has_fixed_representative (c : Fin (L+1) → Fin (M+3)) (h0 : c 0 = 0)
    (hc : Set.range c = cutSet (by omega) C.window) {v : Vertex K (M+2)}
    (hv : v ∈ descentCore C hC) :
    ∃ D ∈ C.fixedStages c, RootInterval C D ∧ normalizeModule C hC D = v := by
  classical
  have hh : v ∈ (C.fixedStages c).image (normalizeModule C hC) := by
    rw [fixedStages_image C hC c hc]
    exact Finset.mem_insert_of_mem hv
  obtain ⟨D,hD,hvD⟩ := Finset.mem_image.mp hh
  by_cases he : D = powerShift C.top 1
  · refine ⟨C.top,fixedStages_top C c h0,?_,?_⟩
    · have hh := rootInterval_stage C C rfl 0
      change RootInterval C (C.stage 0) at hh
      rwa [C.initial] at hh
    · rw [normalizeModule_initial]
      rwa [he,normalizeModule_terminal] at hvD
  · exact ⟨D,hD,fixedStages_interval C c hD he,hvD⟩
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow InfiniteChains InfiniteChains.Cone InfiniteChains.Attachment
variable {K : Type} [Field K] {M L m : ℕ}
variable (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
lemma lift_link_witness (hroot : vertex C hC (by omega) 0 ∈ descentCore C hC)
    (hlen : C.length = m+1) {s : Finset (Vertex K (M+2))}
    (hs : s ∈ codistanceLink m (descentCore C hC)) :
    ∃ E : ResidueChamber (K := K) (N := M+2), ∃ hE : PolyBounded E.top,
      E.top = C.top ∧ E.length = C.length ∧ descentCore E hE = descentCore C hC ∧
      s ⊆ face E hE (by omega) := by
  obtain ⟨hd,D,hD,hcore,hface⟩ := hs
  have hr : normalizedPolynomial (by omega) C.top hC ∈ D.face := by
    have hh := D.descentCore_subset (hcore ▸ hroot)
    simpa only [vertex,C.initial,Fin.castSucc_zero] using hh
  obtain ⟨E,hE,ht,hf,hl,hδ⟩ := based_at C.top hC D hr
  exact ⟨E,hE,ht,hl.trans (hD.trans hlen.symm),hδ.trans hcore,hf ▸ hface⟩
lemma normalized_link_lift (hroot : vertex C hC (by omega) 0 ∈ descentCore C hC)
    (hlen : C.length = m+1) (c : Fin (L+1) → Fin (M+3))
    (hc : Set.range c = (cutSet (by omega) C.window : Set _))
    {s : Finset (Vertex K (M+2))} (hs : s ∈ codistanceLink m (descentCore C hC)) :
    s.image (liftModule C hC) ∈ (C.rootedMinimumLink c).faces := by
  classical
  obtain ⟨E,hE,ht,hl,hcore,hface⟩ := lift_link_witness C hC hroot hlen hs
  have hfix := fixed_stages_of_core C E hC hE ht c hc (hcore ▸ descentCore_subset E hE)
  have hret {v} (hv : v ∈ s) : normalizeModule C hC (liftModule C hC v) = v := by
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp (hface hv)
    rw [liftModule_vertex C hC E hE ht,normalizeModule_stage]
  refine ⟨?_,E,ht,hl,hfix,?_⟩
  · apply Finset.disjoint_left.mpr
    intro D hD hfixed
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hD
    have hn : normalizeModule C hC (liftModule C hC v) ∈
        (C.fixedStages c).image (normalizeModule C hC) := Finset.mem_image_of_mem _ hfixed
    rw [fixedStages_image C hC c hc,Finset.insert_eq_of_mem hroot,hret hv] at hn
    exact Finset.disjoint_left.mp hs.1 hn hv
  · intro D hD
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp (hface hv)
    exact ⟨r.castSucc,(liftModule_vertex C hC E hE ht r).symm⟩
lemma rooted_link_interval (c : Fin (L+1) → Fin (M+3))
    (hlast : c (Fin.last L) = Fin.last (M+2))
    {s : Finset (Submodule K[X] (PolynomialVectors.V K (M+2)))}
    (hs : s ∈ (C.rootedMinimumLink c).faces) {D} (hD : D ∈ s) : RootInterval C D := by
  obtain ⟨hd,E,ht,_,_,hface⟩ := hs
  obtain ⟨r,rfl⟩ := hface D hD
  refine ⟨ht ▸ E.lower r,ht ▸ E.profile_stage_le_top r,?_⟩
  intro he
  exact Finset.disjoint_left.mp hd hD (he ▸ fixedStages_bottom C c hlast)
lemma normalized_link_map (hlen : C.length = m+1)
    (c : Fin (L+1) → Fin (M+3)) (hmono : StrictMono c) (h0 : c 0 = 0)
    (hlast : c (Fin.last L) = Fin.last (M+2))
    (hc : Set.range c = (cutSet (by omega) C.window : Set _))
    (hsorted : ∀ j : Fin L, (slice C.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·))
    {s : Finset (Submodule K[X] (PolynomialVectors.V K (M+2)))}
    (hs : s ∈ (C.rootedMinimumLink c).faces) :
    s.image (normalizeModule C hC) ∈ codistanceLink m (descentCore C hC) := by
  classical
  obtain ⟨hd,E,ht,hl,hfix,hface⟩ := hs
  have hE : PolyBounded E.top := ht ▸ hC
  have hw := (C.fixed_stage_minimum_iff_window E (by omega) ht.symm c hmono.monotone h0 hlast
    (fun j => (hfix j).symm) hsorted).mp hl
  have hcore := core_eq_of_window_fixed C E hC hE ht hw c hc hfix
  obtain ⟨B,hBf,hBl,hBcore⟩ := normalization_core E hE
  refine ⟨?_,B,hBl.trans (hl.trans hlen),hBcore.trans hcore,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hv'
    obtain ⟨F,hF,hFI,hFn⟩ := core_has_fixed_representative C hC c h0 hc hv
    have hDI := rooted_link_interval C c hlast ⟨hd,E,ht,hl,hfix,hface⟩ hD
    have he := normalizeModule_injective C hC hFI hDI hFn
    exact Finset.disjoint_left.mp hd hD (he ▸ hF)
  · intro v hv
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨r,rfl⟩ := hface D hD
    have hr : r.val < M+2 := by
      by_contra hh
      have he : r = Fin.last (M+2) := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
      have hn := (rooted_link_interval C c hlast ⟨hd,E,ht,hl,hfix,hface⟩ hD).2.2
      apply hn
      rw [he,E.terminal,ht]
    let t : Fin (M+2) := ⟨r.val,hr⟩
    have he : r = t.castSucc := Fin.ext rfl
    rw [he,normalizeModule_stage C hC E hE,hBf]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
theorem codistanceLink_exact_of_rooted (hroot : vertex C hC (by omega) 0 ∈ descentCore C hC)
    (hlen : C.length = m+1)
    (c : Fin (L+1) → Fin (M+3)) (hmono : StrictMono c) (h0 : c 0 = 0)
    (hlast : c (Fin.last L) = Fin.last (M+2))
    (hc : Set.range c = (cutSet (by omega) C.window : Set _))
    (hsorted : ∀ j : Fin L, (slice C.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·))
    (r : ℕ) (H : ExactIn (C.rootedMinimumLink c).faces r) :
    ExactIn (codistanceLink m (descentCore C hC)) r := by
  classical
  have hret (s) (hs : s ∈ codistanceLink m (descentCore C hC)) (v) (hv : v ∈ s) :
      normalizeModule C hC (liftModule C hC v) = v := by
    obtain ⟨E,hE,ht,_,_,hface⟩ := lift_link_witness C hC hroot hlen hs
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (hface hv)
    rw [liftModule_vertex C hC E hE ht,normalizeModule_stage]
  apply exactIn_retract (liftModule C hC) (normalizeModule C hC) _ _
    (fun _ hs => normalized_link_lift C hC hroot hlen c hc hs)
    (fun _ hs => normalized_link_map C hC hlen c hmono h0 hlast hc hsorted hs) ?_ ?_ hret r H
  · intro s hs v hv w hw hh
    rw [← hret s hs v hv,← hret s hs w hw,hh]
  · intro s hs D hD E hE he
    exact normalizeModule_injective C hC (rooted_link_interval C c hlast hs hD)
      (rooted_link_interval C c hlast hs hE) he
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone

theorem uniform_codistanceLink_exact (M : ℕ) :
    ∃ Q : ℕ, ∀ (K : Type) [Field K] [Fintype K], Q < Fintype.card K →
      ∀ (m : ℕ) (C : FullChamber K (M+2) (by omega)), C.length = m+1 →
      ∀ r < M+2-C.descentCore.card, ExactIn (codistanceLink m C.descentCore) r := by
  classical
  obtain ⟨Q,hQ⟩ := ResidueChamber.uniform_rootedMinimumLink_exact (M+2)
  refine ⟨Q,?_⟩
  intro K _ _ hq m C hlen r hr
  obtain ⟨v,hv⟩ := C.descentCore_nonempty (by omega)
  obtain ⟨E,hE,ht,hface,hl,hcore⟩ := BoundedChamber.based_at
    (polynomialLattice K (M+2) v) (polyBounded_vertex v) C
    (by rw [normalizedPolynomial_vertex]; exact C.descentCore_subset hv)
  have hroot : BoundedChamber.vertex E hE (by omega) 0 ∈ BoundedChamber.descentCore E hE := by
    rw [hcore]
    have he : BoundedChamber.vertex E hE (by omega) 0 = v := by
      change normalizedPolynomial _ (E.stage 0) _ = _
      simp only [E.initial,ht,normalizedPolynomial_vertex]
    rwa [he]
  obtain ⟨L,c,h0,hlast,hc⟩ := cuts_enumeration (by omega) E.window
  have hsort : ∀ j : Fin L, (slice E.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·) := by
    apply slices_sorted_of_descents (by omega) E.window c
    intro a ha
    rw [hc]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
  have hL := BoundedChamber.cut_rank_eq_core_card E hE c hc hroot
  rw [hcore] at hL
  have hlenE : E.length = m+1 := hl.trans hlen
  rw [← hcore]
  apply BoundedChamber.codistanceLink_exact_of_rooted E hE hroot hlenE c c.strictMono h0 hlast hc hsort r
  exact hQ K E L c (by omega) c.strictMono h0 hlast hsort hq r (by omega)
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {M : ℕ}

theorem codistanceBlock_relative_of_link (m : ℕ) (C : FullChamber K (M+2) (by omega))
    (hlen : C.length = m+1) (r : ℕ)
    (H : C.descentCore.card ≤ r → ExactIn (codistanceLink m C.descentCore) (r-C.descentCore.card)) :
    RelativeExactIn (codistanceStage K (M+2) (by omega) m) (codistanceBlock m C.descentCore) r := by
  classical
  let A := C.descentCore
  let O : InfiniteChains.Complex (Vertex K (M+2)) := {
    faces := codistanceLink m A
    empty_mem := ⟨Finset.disjoint_empty_right _,C,hlen,rfl,Finset.empty_subset _⟩
    downward := by
      intro s t hs ht
      exact ⟨hs.1.mono_right ht,codistanceBlock_downward m A hs.2 ht⟩ }
  have hf (s) (hs : s ∈ codistanceBlock m A) : s.image (tagBy A) ∈ joinFaces A O := by
    constructor
    · rw [tagBy_left]; exact Finset.inter_subset_right
    · rw [tagBy_right]
      exact ⟨(by apply Finset.disjoint_left.mpr; intro v hv hv'; exact (Finset.mem_sdiff.mp hv').2 hv),codistanceBlock_downward m A hs Finset.sdiff_subset⟩
  have hg (s) (hs : s ∈ joinFaces A O) : s.image (Sum.elim id id) ∈ codistanceBlock m A := by
    rw [untag_image,codistanceBlock_join]
    exact ⟨s.toLeft,s.toRight,hs.1,hs.2,rfl⟩
  have hgi (s) (hs : s ∈ joinFaces A O) : Set.InjOn (Sum.elim id id) (s : Set (Vertex K (M+2) ⊕ Vertex K (M+2))) := by
    intro x hx y hy he
    rcases x with x|x <;> rcases y with y|y
    · exact congrArg Sum.inl he
    · change x = y at he
      exact (Finset.disjoint_left.mp hs.2.1 (hs.1 (Finset.mem_toLeft.mpr hx))
        (he.symm ▸ Finset.mem_toRight.mpr hy)).elim
    · change x = y at he
      exact (Finset.disjoint_left.mp hs.2.1 (hs.1 (Finset.mem_toLeft.mpr hy))
        (he ▸ Finset.mem_toRight.mpr hx)).elim
    · exact congrArg Sum.inr he
  apply relativeExactIn_retract (tagBy A) (Sum.elim id id)
    (codistanceStage K (M+2) (by omega) m) (codistanceBlock m A) (oldFaces A O) (joinFaces A O)
    (codistanceBlock_downward m A) hf hg ?_ ?_
    (fun _ _ => (tagBy_injective A).injOn) hgi (fun _ hs => hs.1)
    (fun _ _ v _ => untag_tagBy A v) r (relativeExactIn_join A O r H)
  · intro s hs
    refine ⟨hf s hs.2,?_⟩
    rw [tagBy_left]
    intro he
    have hn := (codistanceBlock_old_iff m A hs.2).mp hs.1
    apply hn
    rw [← he]
    exact Finset.inter_subset_left
  · intro s hs
    apply (codistanceBlock_old_iff m A (hg s hs.1)).mpr
    rw [untag_image]
    intro hA
    apply hs.2
    apply Finset.Subset.antisymm hs.1.1
    intro v hv
    rcases Finset.mem_union.mp (hA hv) with hh|hh
    · exact hh
    · exact (Finset.disjoint_left.mp hs.1.2.1 hv hh).elim
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {M : ℕ}
theorem codistanceStage_relative_of_links (m r : ℕ)
    (H : ∀ (C : FullChamber K (M+2) (by omega)), C.length = m+1 →
      C.descentCore.card ≤ r → ExactIn (codistanceLink m C.descentCore) (r-C.descentCore.card)) :
    RelativeExactIn (codistanceStage K (M+2) (by omega) m)
      (codistanceStage K (M+2) (by omega) (m+1)) r := by
  classical
  have hblocks (A : Finset (Vertex K (M+2))) :
      RelativeExactIn (codistanceStage K (M+2) (by omega) m) (codistanceBlock m A) r := by
    by_cases hex : ∃ C : FullChamber K (M+2) (by omega), C.length = m+1 ∧ C.descentCore = A
    · obtain ⟨C,hC,rfl⟩ := hex
      exact codistanceBlock_relative_of_link m C hC r (H C hC)
    · have he : codistanceBlock m A = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro s ⟨C,hC,hA,_⟩
        exact hex ⟨C,hC,hA⟩
      rw [he]
      exact relativeExactIn_empty _ _
  have hU := relativeExactIn_iUnion (codistanceStage K (M+2) (by omega) m)
    (codistanceBlock m) r (fun A => codistanceBlock_downward m A)
    (codistanceBlock_intersection m) hblocks
  rw [codistanceStage_successor]
  apply relativeExactIn_union _ _ _ r (codistanceStage_downward K (M+2) (by omega) m) ?_
    (fun _ hs => hs.1) (Join.relativeExactIn_self _ r) hU
  intro s t hs ht
  obtain ⟨A,hA⟩ := Set.mem_iUnion.mp hs
  exact Set.mem_iUnion.mpr ⟨A,codistanceBlock_downward m A hA ht⟩

theorem uniform_codistanceStage_zero_exact (M : ℕ) :
    ∃ Q : ℕ, ∀ (K : Type) [Field K] [Fintype K], Q < Fintype.card K →
      ∀ r < M, ExactIn (codistanceStage K (M+2) (by omega) 0) (r+1) := by
  obtain ⟨Q,hQ⟩ := uniform_codistanceLink_exact M
  refine ⟨Q,?_⟩
  intro K _ _ hq r hr
  apply exactIn_initial_of_filtration _ (codistanceStage_mono K (M+2) (by omega)) (r+1)
  · intro m
    apply codistanceStage_relative_of_links m (r+1+1)
    intro C hC hc
    exact hQ K hq m C hC _ (by omega)
  · rw [codistanceStage_exhaust]
    exact building_exact K (M+2) (by omega) r
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.Construction
open CoboundaryExpanders.RationalLattices CoboundaryExpanders.AffineLattices
variable (p n : ℕ) [Fact p.Prime]

lemma oppositionVertex_injective (hn : 1 ≤ n) : Function.Injective (oppositionVertex p n hn) := by
  rintro ⟨c,g⟩ ⟨d,h⟩ he
  induction g using Quotient.inductionOn with | h g =>
  induction h using Quotient.inductionOn with | h h =>
  obtain ⟨hcd,hgh⟩ := (act_cut_eq_iff p n hn g h c d).mp he
  subst d
  congr 1
  exact Quotient.sound (QuotientGroup.leftRel_apply.mpr hgh)

lemma opposition_mem_image (hn : 1 ≤ n) (s : Finset (RationalLattices.Vertex (ZMod p) (n+1))) :
    s ∈ (opposition p n).faces ↔ ∃ t ∈ (TypedCosetFaces.complex (uLocalGroup p n hn)).faces,
      t.image (oppositionVertex p n hn) = s := by
  constructor
  · rintro ⟨g,A,rfl⟩
    exact ⟨TypedCosetFaces.face (uLocalGroup p n hn) g A,⟨g,A,rfl⟩,by
      rw [TypedCosetFaces.face,Finset.image_image]; rfl⟩
  · rintro ⟨t,⟨g,A,rfl⟩,rfl⟩
    exact ⟨g,A,by rw [TypedCosetFaces.face,Finset.image_image]; rfl⟩

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Construction
open RationalLattices InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable (p n : ℕ) [Fact p.Prime]
theorem opposition_faces_eq_codistance_zero :
    (opposition p n).faces = codistanceStage (ZMod p) (n+1) (by omega) 0 := by
  ext s
  rw [codistanceStage_zero,← common_orbit_iff_induced]
  constructor
  · rintro ⟨g,A,hA⟩
    refine ⟨g.val,?_,A,hA⟩
    have hg := g.property
    change ∀ i j : Fin (n+1), j ≤ i → Polynomial.eval 0 (g.val i j) = (1 : Matrix _ _ (ZMod p)) i j at hg
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hg
  · rintro ⟨g,hg,A,hA⟩
    have hu : g ∈ U p (n+1) := by
      change ∀ i j : Fin (n+1), j ≤ i → Polynomial.eval 0 (g i j) = (1 : Matrix _ _ (ZMod p)) i j
      simpa only [Polynomial.coeff_zero_eq_eval_zero] using hg
    exact ⟨⟨g,hu⟩,A,hA⟩

theorem uniform_infinite_coset_exact (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Q < p →
      ∀ r < n-1, ExactIn (TypedCosetFaces.complex (uLocalGroup p n (by omega))).faces (r+1) := by
  classical
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n = k+2 := ⟨n-2,by omega⟩
  obtain ⟨Q,hQ⟩ := uniform_codistanceStage_zero_exact (k+2-1)
  refine ⟨Q,?_⟩
  intro p _ hq r hr
  have hh := hQ (ZMod p) (by simpa only [ZMod.card] using hq) r hr
  rw [← opposition_faces_eq_codistance_zero] at hh
  have hk : 1 ≤ k+2 := by omega
  let : Nonempty (TypedCosetFaces.Vertex (uLocalGroup p (k+2) hk)) :=
    ⟨TypedCosetFaces.vertex (uLocalGroup p (k+2) hk) 1 0⟩
  apply exactIn_of_image (oppositionVertex p (k+2) hk) (oppositionVertex_injective p (k+2) hk)
    _ _ ?_ ?_ (r+1) hh
  · intro s hs
    exact (opposition_mem_image p (k+2) hk _).mpr ⟨s,hs,rfl⟩
  · intro s hs
    exact (opposition_mem_image p (k+2) hk s).mp hs

theorem uniform_infinite_coset_positive_oai (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Q < p →
      ∀ j : ℕ, 0 < j → j < n-1 →
        (TypedCosetFaces.complex (uLocalGroup p n (by omega))).chainComplex.ExactAt j := by
  obtain ⟨Q,hQ⟩ := uniform_infinite_coset_exact n hn
  refine ⟨Q,?_⟩
  intro p _ hq j hj hjn
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact chainComplex_exactAt_of_exactIn _ r (hQ p hq (r+1) hjn)
end CoboundaryExpanders.Construction

end

end OAI
end

theorem solution : type_of% @OAI.CoboundaryExpanders.Construction.uniform_infinite_coset_positive_oai := @OAI.CoboundaryExpanders.Construction.uniform_infinite_coset_positive_oai
