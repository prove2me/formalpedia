-- Prove2me | solution 1 for OAI.CoboundaryExpanders.uniform_gamma_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:30:50.175312+00:00
-- url     : https://prove2.me/submissions/c3aa912c-ae36-4502-845e-4c476293575b

import Mathlib
import Definitions.Def_OAIQ3Cb002
import Theorems.Thm_OAI_CoboundaryExpanders_Construction_uniform_infinite_coset_positive

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

section
variable {V : Type} [DecidableEq V]

namespace Complex
variable (X : CoboundaryExpanders.InfiniteChains.Complex V)

lemma embed_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    (X.embed (n+1)).comp (X.cone a ha n) = (rawCone a).comp (X.embed n) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, cone,
    Finsupp.linearCombination_single, embed_single, rawCone_single]
  by_cases h : a ∈ s.val
  · rw [dite_eq_left h, smul_zero, map_zero, ite_eq_left h]
  · rw [dite_eq_right h, map_smul, embed_single, ite_eq_right h]
    simp

lemma contraction (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    (X.boundary (n+1)).comp (X.cone a ha (n+1)) +
      (X.cone a ha n).comp (X.boundary n) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply X.embed_injective (n+1)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add]
  change (X.embed (n+1)).comp (X.boundary (n+1)) (X.cone a ha (n+1) c) +
    (X.embed (n+1)).comp (X.cone a ha n) (X.boundary n c) = _
  rw [embed_boundary, embed_cone]
  change rawBoundary ((X.embed (n+2)).comp (X.cone a ha (n+1)) c) +
    rawCone a ((X.embed n).comp (X.boundary n) c) = _
  rw [embed_boundary, embed_cone]
  exact LinearMap.congr_fun (raw_contraction a) (X.embed (n+1) c)

lemma boundary_exact_of_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    Function.Exact (X.boundary (n+1)) (X.boundary n) := by
  intro c
  constructor
  · intro hc
    refine ⟨X.cone a ha (n+1) c, ?_⟩
    have hh := LinearMap.congr_fun (X.contraction a ha n) c
    simpa [hc] using hh
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (X.boundary_squared n) b

open CategoryTheory

lemma chainComplex_exactAt_of_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    X.chainComplex.ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (X.chainComplex.d (n+2) (n+1)) (X.chainComplex.d (n+1) n)
  rw [chainComplex_d, chainComplex_d]
  exact (X.boundary_exact_of_cone a ha (n+1))

lemma chainComplex_homology_isZero_of_cone (a : V) (ha : X.IsConePoint a) (n : ℕ) :
    Limits.IsZero (X.chainComplex.homology (n+1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (X.chainComplex_exactAt_of_cone a ha n)

lemma full_isConePoint (a : V) : (full V).IsConePoint a := fun _ _ => Set.mem_univ _

omit [DecidableEq V] in
lemma embed_zero (c : X.Chains 0) :
    X.embed 0 c = Finsupp.single ∅ (X.sumCoefficients 0 c) := by
  have hh : X.embed 0 = (Finsupp.lsingle ∅).comp (X.sumCoefficients 0) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, embed_single, sumCoefficients_single]
    have hs : s.val = ∅ := Finset.card_eq_zero.mp s.property.2
    rw [hs]
  exact LinearMap.congr_fun hh c

omit [DecidableEq V] in
lemma sumCoefficients_zero_injective : Function.Injective (X.sumCoefficients 0) := by
  intro c d he
  apply X.embed_injective 0
  rw [embed_zero, embed_zero, he]

end Complex
end

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
-- module Solutions.OAIQ3_Cob.Coboundary_Frames
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.faceMulAction _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Unimodular frames, bad-simplex transport, height reduction, and partial-basis exactness.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CoboundaryExpanders.Unimodular
variable {R M S T : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable [Fintype S]

variable [Fintype T]

theorem frame_sum_iff (f : S → M) (r : M →ₗ[R] (S → R))
    (hr : ∀ i, r (f i) = Pi.single i 1) (g : T → M) :
    IsFrame R (Sum.elim f g) ↔ IsFrame R (fun j => quotientProjection f r hr (g j)) := by
  classical
  constructor
  · rintro ⟨l, hl⟩
    let q : M →ₗ[R] (T → R) := LinearMap.pi (fun j => (LinearMap.proj (Sum.inr j)).comp l)
    have hqf (i : S) : q (f i) = 0 := by
      ext j
      have hh := congrFun (hl (Sum.inl i)) (Sum.inr j)
      simpa [q, Pi.single_apply] using hh
    have hqg (i : T) : q (g i) = Pi.single i 1 := by
      ext j
      have hh := congrFun (hl (Sum.inr i)) (Sum.inr j)
      simpa [q, Pi.single_apply] using hh
    refine ⟨q.domRestrict r.ker, ?_⟩
    intro i
    change q (g i - combine f (r (g i))) = _
    simp [combine_apply, map_sum, hqf, hqg]
  · rintro ⟨l, hl⟩
    let q := quotientProjection f r hr
    let a : M →ₗ[R] (T → R) := l.comp q
    have haf (i : S) : a (f i) = 0 := by simp [a, q]
    have hag (i : T) : a (g i) = Pi.single i 1 := hl i
    let b : M →ₗ[R] (S → R) := r - (r.comp (combine g)).comp a
    have hbf (i : S) : b (f i) = Pi.single i 1 := by simp [b, haf, hr]
    have hbg (i : T) : b (g i) = 0 := by simp [b, hag]
    refine ⟨LinearMap.pi (Sum.elim (fun i => (LinearMap.proj i).comp b)
      (fun j => (LinearMap.proj j).comp a)), ?_⟩
    intro i
    ext j
    cases i <;> cases j <;> simp [haf, hag, hbf, hbg, Pi.single_apply]

end CoboundaryExpanders.Unimodular

end

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains.BadSimplex
open Attachment
variable {W V : Type} [DecidableEq W] [DecidableEq V]

omit [DecidableEq W] [DecidableEq V] in
lemma block_faces (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (F : Finset W)
    (hF : F.disjSum (∅ : Finset V) ∈ X.faces) :
    joinFaces F (goodLink X F hF) ⊆ X.faces := by
  intro s hs
  have hh : s.toLeft.disjSum s.toRight ⊆ F.disjSum s.toRight :=
    Finset.disjSum_mono hs.1 (by rfl)
  rw [Finset.toLeft_disjSum_toRight] at hh
  exact X.downward hs.2 hh

omit [DecidableEq W] [DecidableEq V] in
lemma block_stage (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) (F : Finset W)
    (hF : F.disjSum (∅ : Finset V) ∈ X.faces) (hcard : F.card ≤ r) :
    joinFaces F (goodLink X F hF) ⊆ (stage X r).faces := by
  intro s hs
  exact ⟨block_faces X F hF hs, (Finset.card_le_card hs.1).trans hcard⟩

omit [DecidableEq W] [DecidableEq V] in
lemma old_stage (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) (F : Finset W)
    (hF : F.disjSum (∅ : Finset V) ∈ X.faces) (hcard : F.card = r+1) :
    oldFaces F (goodLink X F hF) ⊆ (stage X r).faces := by
  intro s hs
  refine ⟨block_faces X F hF hs.1, ?_⟩
  have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs.1.1, hs.2⟩)
  omega

lemma block_relative (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r n : ℕ) (F : Finset W)
    (hF : F.disjSum (∅ : Finset V) ∈ X.faces) (hcard : F.card = r+1)
    (hL : F.card ≤ n → ExactIn (goodLink X F hF).faces (n-F.card)) :
    RelativeExactIn (stage X r).faces (joinFaces F (goodLink X F hF)) n := by
  intro c hc hd
  have hdblock := boundary_supported _ (joinFaces_downward F (goodLink X F hF)) c
    (graded_forget _ n hc)
  have hdold : rawBoundary c ∈ supported (oldFaces F (goodLink X F hF)) := by
    rw [mem_supported] at hd hdblock ⊢
    intro s hs
    refine ⟨hdblock s hs, ?_⟩
    intro he
    have hh := (hd s hs).2
    change s.toLeft.card ≤ r at hh
    rw [he, hcard] at hh
    omega
  obtain ⟨b, hb, he⟩ := relativeExactIn_join F (goodLink X F hF) n hL c hc hdold
  refine ⟨b, hb, supported_mono (P := graded (oldFaces F (goodLink X F hF)) n)
    (Q := graded (stage X r).faces n) (fun s hs => ⟨old_stage X r F hF hcard hs.1, hs.2⟩) he⟩

omit [DecidableEq W] [DecidableEq V] in
lemma stage_succ (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) :
    (stage X (r+1)).faces = (stage X r).faces ∪
      ⋃ F : BadFaces X r, joinFaces F.val (goodLink X F.val F.property.1) := by
  ext s
  constructor
  · rintro ⟨hs, hr⟩
    by_cases h : s.toLeft.card ≤ r
    · exact Or.inl ⟨hs, h⟩
    · refine Or.inr (Set.mem_iUnion.mpr ⟨⟨s.toLeft, ?_, by omega⟩, ?_⟩)
      · apply X.downward hs
        conv_rhs => rw [← Finset.toLeft_disjSum_toRight (u := s)]
        exact Finset.disjSum_mono (by rfl) (Finset.empty_subset _)
      · refine ⟨Finset.Subset.refl _, ?_⟩
        change s.toLeft.disjSum s.toRight ∈ X.faces
        rw [Finset.toLeft_disjSum_toRight]
        exact hs
  · rintro (hs | hs)
    · exact ⟨hs.1, hs.2.trans (Nat.le_succ r)⟩
    · obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hs
      exact block_stage X (r+1) F.val F.property.1 F.property.2.le hF

omit [DecidableEq W] [DecidableEq V] in
lemma blocks_inter (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r : ℕ) (F G : BadFaces X r)
    (hFG : F ≠ G) :
    joinFaces F.val (goodLink X F.val F.property.1) ∩
      joinFaces G.val (goodLink X G.val G.property.1) ⊆ (stage X r).faces := by
  intro s hs
  refine ⟨block_faces X F.val F.property.1 hs.1, ?_⟩
  by_contra hh
  have hc : s.toLeft.card = r+1 := by
    have := Finset.card_le_card hs.1.1
    rw [F.property.2] at this
    omega
  have hf : s.toLeft = F.val := Finset.eq_of_subset_of_card_le hs.1.1 (by omega)
  have hg : s.toLeft = G.val := Finset.eq_of_subset_of_card_le hs.2.1 (by omega)
  exact hFG (Subtype.ext (hf.symm.trans hg))

lemma relative_self (P : Set (Finset V)) (n : ℕ) : RelativeExactIn P P n := by
  intro c hc _
  exact ⟨0, Submodule.zero_mem _, by simpa using hc⟩

lemma relative_stage_succ (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (r n : ℕ)
    (hL : ∀ F : BadFaces X r, F.val.card ≤ n →
      ExactIn (goodLink X F.val F.property.1).faces (n-F.val.card)) :
    RelativeExactIn (stage X r).faces (stage X (r+1)).faces n := by
  rw [stage_succ]
  apply relativeExactIn_union _ _ _ n (stage X r).downward
  · intro s t hs ht
    obtain ⟨F, hF⟩ := Set.mem_iUnion.mp hs
    exact Set.mem_iUnion.mpr ⟨F, joinFaces_downward _ _ hF ht⟩
  · intro s hs
    exact hs.1
  · exact relative_self _ n
  · apply relativeExactIn_iUnion
    · intro F
      exact joinFaces_downward _ _
    · exact blocks_inter X r
    · intro F
      exact block_relative X r n F.val F.property.1 F.property.2 (hL F)

lemma relative_trans {Z : Type} [DecidableEq Z]
    (P Q T : Set (Finset Z)) (hPQ : P ⊆ Q) (hQT : Q ⊆ T) (n : ℕ)
    (hP : RelativeExactIn P Q n) (hQ : RelativeExactIn Q T n) : RelativeExactIn P T n := by
  intro c hc hd
  obtain ⟨b, hb, hcb⟩ := hQ c hc (supported_mono hPQ hd)
  have hdd : rawBoundary (c - rawBoundary b) = rawBoundary c := by
    rw [map_sub]
    have hh := LinearMap.congr_fun (rawBoundary_squared (V := Z)) b
    change rawBoundary (rawBoundary b) = 0 at hh
    rw [hh, sub_zero]
  obtain ⟨a, ha, he⟩ := hP _ hcb (by rw [hdd]; exact hd)
  refine ⟨a+b, Submodule.add_mem _
    (supported_mono (P := graded Q (n+1)) (Q := graded T (n+1))
      (fun s hs => ⟨hQT hs.1, hs.2⟩) ha) hb, ?_⟩
  have heq : c - rawBoundary (a+b) = (c-rawBoundary b)-rawBoundary a := by
    rw [map_add]; abel
  rw [heq]
  exact he

theorem relative (X : CoboundaryExpanders.InfiniteChains.Complex (W ⊕ V)) (n : ℕ)
    (hlinks : ∀ F : Finset W, ∀ hF : F.disjSum (∅ : Finset V) ∈ X.faces,
      F.Nonempty → F.card ≤ n → ExactIn (goodLink X F hF).faces (n-F.card)) :
    RelativeExactIn (stage X 0).faces X.faces n := by
  have stages (r : ℕ) : RelativeExactIn (stage X 0).faces (stage X r).faces n := by
    induction r with
    | zero => exact relative_self _ n
    | succ r ih =>
      apply relative_trans (stage X 0).faces (stage X r).faces (stage X (r+1)).faces
        (fun s hs => ⟨hs.1, hs.2.trans (Nat.zero_le r)⟩)
        (fun s hs => ⟨hs.1, hs.2.trans (Nat.le_succ r)⟩) n ih
      apply relative_stage_succ
      intro F hn
      exact hlinks F.val F.property.1
        (Finset.card_pos.mp (by rw [F.property.2]; omega)) hn
  intro c hc hd
  have hcn : c ∈ supported (graded (stage X n).faces n) := by
    rw [mem_supported] at hc ⊢
    intro s hs
    obtain ⟨hx, hn⟩ := hc s hs
    refine ⟨⟨hx, ?_⟩, hn⟩
    have hh := Finset.card_toLeft_add_card_toRight (u := s)
    omega
  obtain ⟨b, hb, he⟩ := stages n c hcn hd
  exact ⟨b, supported_mono (P := graded (stage X n).faces (n+1))
    (Q := graded X.faces (n+1)) (fun s hs => ⟨hs.1.1, hs.2⟩) hb, he⟩

end CoboundaryExpanders.InfiniteChains.BadSimplex

end

noncomputable section


namespace CoboundaryExpanders.InfiniteChains.ChainTransport
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma relabel_supported (f : V → W) (P : Set (Finset V)) (Q : Set (Finset W))
    (h : ∀ s ∈ P, s.image f ∈ Q) (c : Raw V) (hc : c ∈ supported P) :
    relabel f c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs a
  rw [relabel_single]
  exact single_mem_supported (h s hs) a

omit [DecidableEq V] in
lemma relabel_graded (f : V → W) (P : Set (Finset V)) (Q : Set (Finset W)) (r : ℕ)
    (h : ∀ s ∈ P, s.image f ∈ Q)
    (hinj : ∀ s ∈ P, Set.InjOn f (s : Set V))
    (c : Raw V) (hc : c ∈ supported (graded P r)) :
    relabel f c ∈ supported (graded Q r) := by
  apply relabel_supported f (graded P r) (graded Q r) _ c hc
  intro s hs
  exact ⟨h s hs.1, (Finset.card_image_of_injOn (hinj s hs.1)).trans hs.2⟩

lemma relabel_boundary (f : V → W) (hf : Function.Injective f) :
    rawBoundary.comp (relabel f) = (relabel f).comp rawBoundary := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, relabel_single,
    rawBoundary_single, map_sum, Finset.sum_image, hf.injOn]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.image_erase hf]

omit [DecidableEq V] in
lemma relabel_comp {U : Type} [DecidableEq U] (f : V → W) (g : W → U) :
    (relabel g).comp (relabel f) = relabel (g ∘ f) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp [Finset.image_image]

lemma relabel_id : relabel (id : V → V) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp

lemma relabel_equiv_cancel (e : V ≃ W) (c : Raw V) :
    relabel e.symm (relabel e c) = c := by
  have hh := LinearMap.congr_fun (relabel_comp e e.symm) c
  change relabel e.symm (relabel e c) = relabel (e.symm ∘ e) c at hh
  rw [hh]
  have he : e.symm ∘ e = id := by funext x; simp
  rw [he, relabel_id]
  rfl

lemma relabel_boundary_apply (f : V → W) (hf : Function.Injective f) (c : Raw V) :
    rawBoundary (relabel f c) = relabel f (rawBoundary c) :=
  LinearMap.congr_fun (relabel_boundary f hf) c

theorem relativeIn_equiv (e : V ≃ W) (P Q : Set (Finset V)) (P' Q' : Set (Finset W))
    (hP : ∀ s, s ∈ P ↔ s.image e ∈ P')
    (hQ : ∀ s, s ∈ Q ↔ s.image e ∈ Q') (n : ℕ)
    (hR : RelativeExactIn P' Q' n) : RelativeExactIn P Q n := by
  intro c hc hd
  have hce := relabel_graded e Q Q' n (fun s hs => (hQ s).mp hs)
    (fun _ _ => e.injective.injOn) c hc
  have hde : rawBoundary (relabel e c) ∈ supported P' := by
    rw [relabel_boundary_apply e e.injective]
    exact relabel_supported e P P' (fun s hs => (hP s).mp hs) _ hd
  obtain ⟨b, hb, he⟩ := hR _ hce hde
  have inverse (A : Set (Finset V)) (A' : Set (Finset W))
      (hA : ∀ s, s ∈ A ↔ s.image e ∈ A') (s : Finset W) (hs : s ∈ A') :
      s.image e.symm ∈ A := by
    apply (hA _).mpr
    simpa [Finset.image_image, Function.comp_def] using hs
  refine ⟨relabel e.symm b,
    relabel_graded e.symm Q' Q (n+1) (inverse Q Q' hQ)
      (fun _ _ => e.symm.injective.injOn) b hb, ?_⟩
  have ht := relabel_graded e.symm P' P n (inverse P P' hP)
    (fun _ _ => e.symm.injective.injOn) _ he
  rw [map_sub, relabel_equiv_cancel] at ht
  rw [relabel_boundary_apply e.symm e.symm.injective]
  exact ht

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

lemma exactIn_of_extend (P Q : Set (Finset V)) (a : V)
    (ha : ∀ s ∈ P, a ∉ s → insert a s ∈ Q) (n : ℕ) :
    ∀ c ∈ supported (graded P n), rawBoundary c = 0 →
      ∃ b ∈ supported (graded Q (n+1)), rawBoundary b = c := by
  intro c hc hz
  refine ⟨rawCone a c, rawCone_graded a P Q n ha c hc, ?_⟩
  have hh := LinearMap.congr_fun (raw_contraction a) c
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hz, map_zero, add_zero] using hh

end CoboundaryExpanders.InfiniteChains.ChainTransport

end

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CoboundaryExpanders.Unimodular
open InfiniteChains InfiniteChains.Attachment
variable {R M V W : Type} [CommRing R] [AddCommGroup M] [Module R M]
variable [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma frame_image (f : W → M) (e : V ↪ W) (s : Finset V) :
    s.image e ∈ (complex R f).faces ↔ s ∈ (complex R (f ∘ e)).faces := by
  rw [← Finset.map_eq_image]
  exact (frame_equiv (R := R) (f := fun w : s.map e => f w) (Finset.equivMap e s)).symm

omit [DecidableEq V] [DecidableEq W] in
lemma frame_disjSum (f : V ⊕ W → M) (s : Finset V) (t : Finset W) :
    s.disjSum t ∈ (complex R f).faces ↔
      IsFrame R (Sum.elim (fun v : s => f (Sum.inl v)) (fun w : t => f (Sum.inr w))) := by
  change IsFrame R (fun x : s.disjSum t => f x) ↔ _
  rw [← frame_equiv (R := R) (f := fun x : s.disjSum t => f x) (disjSumEquiv s t)]
  have he : (fun x : s.disjSum t => f x) ∘ disjSumEquiv s t =
      Sum.elim (fun v : s => f (Sum.inl v)) (fun w : t => f (Sum.inr w)) := by
    funext x
    cases x <;> rfl
  rw [he]

omit [DecidableEq V] [DecidableEq W] in
lemma frame_inl (f : V ⊕ W → M) (s : Finset V) :
    s.disjSum (∅ : Finset W) ∈ (complex R f).faces ↔
      IsFrame R (fun v : s => f (Sum.inl v)) := by
  rw [Finset.disjSum_empty]
  exact (frame_equiv (R := R) (f := fun x : s.map (@Function.Embedding.inl V W) => f x.val)
    (Finset.equivMap (@Function.Embedding.inl V W) s)).symm

lemma frame_adjoin {S : Type} [Fintype S] (f : S → M) (hf : IsFrame R f)
    (a : M) (φ : M →ₗ[R] R) (ha : φ a = 1) (hfφ : ∀ i, φ (f i) = 0) :
    IsFrame R (Sum.elim (fun _ : Unit => a) f) := by
  obtain ⟨r, hr⟩ := hf
  let l : M →ₗ[R] (Unit → R) := LinearMap.pi (fun _ => φ)
  have hl (i : Unit) : l a = Pi.single i 1 := by ext j; cases i; cases j; simpa [l] using ha
  apply (frame_sum_iff (fun _ : Unit => a) l (by intro i; ext j; cases i; cases j; simpa [l] using ha) f).mpr
  refine ⟨r.domRestrict l.ker, ?_⟩
  intro i
  change r (f i - combine (fun _ : Unit => a) (l (f i))) = Pi.single i 1
  have hz : l (f i) = 0 := by ext j; exact hfφ i
  rw [hz, map_zero, sub_zero, hr]

lemma insert_mem (f : V → M) (s : Finset V) (hs : s ∈ (complex R f).faces)
    (a : V) (ha : a ∉ s) (φ : M →ₗ[R] R) (hφa : φ (f a) = 1)
    (hφs : ∀ v ∈ s, φ (f v) = 0) : insert a s ∈ (complex R f).faces := by
  change IsFrame R (fun v : ↥(insert a s) => f v)
  apply (frame_equiv (R := R) (f := fun v : ↥(insert a s) => f v) (insertEquiv a s ha)).mp
  have he : (fun v : ↥(insert a s) => f v) ∘ insertEquiv a s ha =
      Sum.elim (fun _ : Unit => f a) (fun v : s => f v) := by
    funext x
    cases x <;> rfl
  rw [he]
  exact frame_adjoin (fun v : s => f v) hs (f a) φ hφa (fun v => hφs v.val v.property)

lemma fill_zero_coordinate (f : V → M) (φ : M →ₗ[R] R) (a : V)
    (ha : φ (f a) = 1) (n : ℕ) :
    ∀ c ∈ supported (graded {s | s ∈ (complex R f).faces ∧ ∀ v ∈ s, φ (f v) = 0} n),
      rawBoundary c = 0 → ∃ b ∈ supported (graded (complex R f).faces (n+1)), rawBoundary b = c := by
  apply InfiniteChains.ChainTransport.exactIn_of_extend _ _ a
  intro s hs has
  exact insert_mem f s hs.1 a has φ ha hs.2

end CoboundaryExpanders.Unimodular

end

noncomputable section


namespace CoboundaryExpanders.InfiniteChains.HeightReduction
open Attachment BadSimplex ChainTransport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type} [DecidableEq V]

lemma stage0_iff (X : CoboundaryExpanders.InfiniteChains.Complex V) (h : V → ℕ) (H : ℕ)
    (s : Finset (Bad h H ⊕ Good h H)) :
    s ∈ (stage (splitComplex X h H) 0).faces ↔
      s.image (split h H) ∈ X.faces ∧ ∀ v ∈ s.image (split h H), h v < H := by
  constructor
  · rintro ⟨⟨hs, hb⟩, hz⟩
    refine ⟨hs, ?_⟩
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    cases x with
    | inl x =>
      have hm : x ∈ s.toLeft := by simpa using hx
      have he : s.toLeft = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [he] at hm
    | inr x => exact Nat.lt_of_not_ge x.property
  · rintro ⟨hs, hb⟩
    refine ⟨⟨hs, fun v hv => (hb v hv).le⟩, ?_⟩
    have he : s.toLeft = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hm : Sum.inl x ∈ s := by simpa using hx
      have hh := hb x.val (Finset.mem_image.mpr ⟨Sum.inl x, hm, rfl⟩)
      exact (Nat.not_lt_of_ge x.property) hh
    simp [he]

lemma relative_lower (X : CoboundaryExpanders.InfiniteChains.Complex V) (h : V → ℕ) (H n : ℕ)
    (hlinks : ∀ F : Finset (Bad h H),
      ∀ hF : F.disjSum (∅ : Finset (Good h H)) ∈ (splitComplex X h H).faces,
      F.Nonempty → F.card ≤ n →
      ExactIn (goodLink (splitComplex X h H) F hF).faces (n-F.card)) :
    RelativeExactIn {s | s ∈ X.faces ∧ ∀ v ∈ s, h v < H} (bounded X h H).faces n := by
  apply relativeIn_equiv (split h H).symm _ _ (stage (splitComplex X h H) 0).faces
    (splitComplex X h H).faces
  · intro s
    rw [stage0_iff]
    simp [Finset.image_image, Function.comp_def]
  · intro s
    change s ∈ (bounded X h H).faces ↔
      (s.image (split h H).symm).image (split h H) ∈ (bounded X h H).faces
    simp [Finset.image_image, Function.comp_def]
  · exact BadSimplex.relative _ n hlinks

theorem exactIn (X : CoboundaryExpanders.InfiniteChains.Complex V) (h : V → ℕ) (n : ℕ)
    (hzero : ∀ c ∈ supported (graded (bounded X h 0).faces n),
      rawBoundary c = 0 → ∃ b ∈ supported (graded X.faces (n+1)), rawBoundary b = c)
    (hlinks : ∀ H : ℕ, 0 < H → ∀ F : Finset (Bad h H),
      ∀ hF : F.disjSum (∅ : Finset (Good h H)) ∈ (splitComplex X h H).faces,
      F.Nonempty → F.card ≤ n →
      ExactIn (goodLink (splitComplex X h H) F hF).faces (n-F.card)) :
    ExactIn X.faces n := by
  have fill (H : ℕ) : ∀ c ∈ supported (graded (bounded X h H).faces n),
      rawBoundary c = 0 → ∃ b ∈ supported (graded X.faces (n+1)), rawBoundary b = c := by
    induction H using Nat.strong_induction_on with
    | h H ih =>
      intro c hc hz
      by_cases hH : H = 0
      · subst H; exact hzero c hc hz
      · have hp : 0 < H := Nat.pos_of_ne_zero hH
        obtain ⟨b, hb, he⟩ := relative_lower X h H n (hlinks H hp) c hc
          (by rw [hz]; exact Submodule.zero_mem _)
        have hl : c - rawBoundary b ∈ supported (graded (bounded X h (H-1)).faces n) := by
          apply supported_mono (P := graded {s | s ∈ X.faces ∧ ∀ v ∈ s, h v < H} n) _ he
          intro s hs
          exact ⟨⟨hs.1.1, fun v hv => by have := hs.1.2 v hv; omega⟩, hs.2⟩
        have hcycle : rawBoundary (c - rawBoundary b) = 0 := by
          rw [map_sub, hz]
          have hh := LinearMap.congr_fun (rawBoundary_squared (V := V)) b
          change rawBoundary (rawBoundary b) = 0 at hh
          rw [hh, sub_self]
        obtain ⟨a, ha, hea⟩ := ih (H-1) (by omega) _ hl hcycle
        refine ⟨a+b, Submodule.add_mem _ ha ?_, ?_⟩
        · exact supported_mono (P := graded (bounded X h H).faces (n+1))
            (Q := graded X.faces (n+1)) (fun s hs => ⟨hs.1.1, hs.2⟩) hb
        · rw [map_add, hea, sub_add_cancel]
  intro c hc hz
  apply fill (c.support.sup (fun s => s.sup h)) c _ hz
  rw [mem_supported] at hc ⊢
  intro s hs
  exact ⟨⟨(hc s hs).1, fun v hv => (Finset.le_sup (f := h) hv).trans
      (Finset.le_sup (f := fun t : Finset V => t.sup h) (Finsupp.mem_support_iff.mpr hs))⟩,
    (hc s hs).2⟩

end CoboundaryExpanders.InfiniteChains.HeightReduction

end

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CoboundaryExpanders.Unimodular
open InfiniteChains InfiniteChains.Attachment InfiniteChains.BadSimplex
open InfiniteChains.HeightReduction

variable {R M V : Type} [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq V]

lemma split_frame (f : V → M) (h : V → ℕ) (H : ℕ) (F : Finset (Bad h H))
    (hF : F.disjSum (∅ : Finset (Good h H)) ∈ (splitComplex (complex R f) h H).faces) :
    IsFrame R (fun v : F => f v.val.val) := by
  have hi := (frame_image (R := R) f (split h H).toEmbedding
    (F.disjSum (∅ : Finset (Good h H)))).mp hF.1
  exact (frame_inl (R := R) (f ∘ split h H) F).mp hi

lemma goodLink_eq (f : V → M) (h : V → ℕ) (H : ℕ) (F : Finset (Bad h H))
    (hF : F.disjSum (∅ : Finset (Good h H)) ∈ (splitComplex (complex R f) h H).faces)
    (r : M →ₗ[R] (F → R)) (hr : ∀ i, r (f i.val.val) = standardCoordinate (R := R) i) :
    (goodLink (splitComplex (complex R f) h H) F hF).faces =
      (complex R (fun v : Good h H => quotientProjection (fun i : F => f i.val.val) r hr (f v.val))).faces := by
  ext t
  change ((F.disjSum t).image (split h H) ∈ (complex R f).faces ∧
    ∀ v ∈ (F.disjSum t).image (split h H), h v ≤ H) ↔ _
  have bound : ∀ v ∈ (F.disjSum t).image (split h H), h v ≤ H := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    cases x with
    | inl x =>
      apply hF.2
      exact Finset.mem_image.mpr ⟨Sum.inl x, by simpa using hx, rfl⟩
    | inr x => exact (Nat.lt_of_not_ge x.property).le
  rw [and_iff_left bound]
  apply (frame_image (R := R) f (split h H).toEmbedding (F.disjSum t)).trans
  apply (frame_disjSum (R := R) (f ∘ split h H) F t).trans
  exact frame_sum_iff (fun i : F => f i.val.val) r hr (fun v : t => f v.val.val)

lemma reduced_projection_surjective (δ : EuclideanHeight R) (f : V → M)
    (hf : Function.Surjective f) (φ : M →ₗ[R] R) (H : ℕ) (hH : 0 < H)
    (F : Finset (Bad (fun v => δ.height (φ (f v))) H))
    (hF : F.disjSum (∅ : Finset (Good (fun v => δ.height (φ (f v))) H)) ∈
      (splitComplex (complex R f) (fun v => δ.height (φ (f v))) H).faces)
    (hFn : F.Nonempty) (r : M →ₗ[R] (F → R))
    (hr : ∀ i, r (f i.val.val) = standardCoordinate (R := R) i) :
    Function.Surjective (fun v : Good (fun v => δ.height (φ (f v))) H =>
      quotientProjection (fun i : F => f i.val.val) r hr (f v.val)) := by
  obtain ⟨v,hv⟩ := hFn
  let i : F := ⟨v,hv⟩
  have hp : H ≤ δ.height (φ (f v.val)) := v.property
  have hneq : φ (f v.val) ≠ 0 := by
    intro hz
    have hh := (δ.zero_iff _).mpr hz
    omega
  intro y
  obtain ⟨q,hq⟩ := δ.reduce (φ (y : M)) (φ (f v.val)) hneq
  have hmax : δ.height (φ (f v.val)) ≤ H := by
    apply hF.2
    exact Finset.mem_image.mpr ⟨Sum.inl v, by simpa using hv, rfl⟩
  obtain ⟨x,hx⟩ := hf ((y : M) - q • f v.val)
  have hgood : ¬ H ≤ δ.height (φ (f x)) := by
    rw [hx, map_sub, map_smul, smul_eq_mul]
    omega
  refine ⟨⟨x,hgood⟩, ?_⟩
  change quotientProjection (fun j : F => f j.val.val) r hr (f x) = y
  rw [hx, map_sub, map_smul]
  have hz := quotientProjection_family (fun j : F => f j.val.val) r hr i
  change quotientProjection (fun j : F => f j.val.val) r hr (f v.val) = 0 at hz
  rw [quotientProjection_ker, hz, smul_zero, sub_zero]

theorem exactIn_complex (δ : EuclideanHeight R) [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R M] [Module.Finite R M] (f : V → M) (hf : Function.Surjective f)
    (n : ℕ) (hn : n < Module.finrank R M) : ExactIn (complex R f).faces n := by
  have ranks (d : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M]
      [Module.Free R M] [Module.Finite R M], Module.finrank R M = d →
      ∀ (V : Type) [DecidableEq V] (f : V → M), Function.Surjective f →
      ∀ n : ℕ, n < d → ExactIn (complex R f).faces n := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro M _ _ _ _ hdim V _ f hf n hn
      have hpos : 0 < Module.finrank R M := by omega
      have hidx : Nonempty (Module.Free.ChooseBasisIndex R M) := by
        apply Fintype.card_pos_iff.mp
        rw [← Module.finrank_eq_card_chooseBasisIndex]
        exact hpos
      let i := Classical.choice hidx
      let b := Module.Free.chooseBasis R M
      let φ : M →ₗ[R] R := b.coord i
      obtain ⟨a,ha⟩ := hf (b i)
      have hφa : φ (f a) = 1 := by rw [ha]; simp [φ, Module.Basis.coord_apply]
      apply HeightReduction.exactIn (complex R f) (fun v => δ.height (φ (f v))) n
      · intro c hc hz
        apply fill_zero_coordinate f φ a hφa n c _ hz
        apply supported_mono (P := graded (bounded (complex R f) (fun v => δ.height (φ (f v))) 0).faces n) _ hc
        intro s hs
        refine ⟨⟨hs.1.1, ?_⟩, hs.2⟩
        intro v hv
        exact (δ.zero_iff _).mp (Nat.eq_zero_of_le_zero (hs.1.2 v hv))
      · intro H hH F hF hFn hnF
        obtain ⟨r,hr⟩ := split_frame (R := R) f (fun v => δ.height (φ (f v))) H F hF
        have hd := frame_rank_split (fun v : F => f v.val.val) r hr
        rw [Fintype.card_coe, hdim] at hd
        have hc : 0 < F.card := Finset.card_pos.mpr hFn
        have hrlt : Module.finrank R r.ker < d := by omega
        rw [goodLink_eq f (fun v => δ.height (φ (f v))) H F hF r hr]
        apply ih (Module.finrank R r.ker) hrlt r.ker rfl
          (Good (fun v => δ.height (φ (f v))) H)
          (fun v => quotientProjection (fun i : F => f i.val.val) r hr (f v.val))
        · exact reduced_projection_surjective δ f hf φ H hH F hF hFn r hr
        · omega
  exact ranks (Module.finrank R M) M rfl V f hf n hn

theorem polynomial_exact (K V : Type) [Field K] [DecidableEq V] (r : ℕ)
    (f : V → (Fin r → Polynomial K)) (hf : Function.Surjective f)
    (n : ℕ) (hn : n < r) : ExactIn (complex (Polynomial K) f).faces n := by
  apply exactIn_complex (polynomialHeight K) f hf n
  simpa using hn

theorem field_exact (K V : Type) [Field K] [DecidableEq V] (r : ℕ)
    (f : V → (Fin r → K)) (hf : Function.Surjective f)
    (n : ℕ) (hn : n < r) : ExactIn (complex K f).faces n := by
  apply exactIn_complex (fieldHeight K) f hf n
  simpa using hn

end CoboundaryExpanders.Unimodular

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Basic
attribute [-instance] _root_.OAI.CoboundaryExpanders.Blocks.gammaNormal _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Polynomial congruence groups, truncation ideals, and finite nilpotent quotients.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix

namespace CoboundaryExpanders.Construction

section

theorem matrix_nilpotent_of_entries {A : Type*} [CommRing A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : A) (hx : IsNilpotent x)
    (M : Matrix ι ι A) (hM : ∀ i j, x ∣ M i j) : IsNilpotent M := by
  classical
  choose B hB using hM
  let B' : Matrix ι ι A := B
  have he : M = x • B' := by ext i j; exact hB i j
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, ?_⟩
  rw [he, smul_pow, hr, zero_smul]

theorem prime_cast_trunc (p m : ℕ) : (p : Trunc p m) = 0 := by
  have h : (p : R p) = 0 := by simp
  rw [← map_natCast (Ideal.Quotient.mk (powerIdeal p m)), h, map_zero]

theorem reduction_sub_one_nilpotent (q a m : ℕ)
    (A : Matrix.SpecialLinearGroup (Fin a) (R q)) (hA : A ∈ Gamma q a 1) :
    IsNilpotent
      ((Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal q m)) A :
        Matrix (Fin a) (Fin a) (Trunc q m)) - 1) := by
  apply matrix_nilpotent_of_entries (tbar q m) ⟨m, tbar_pow q m⟩
  intro i j
  have hd := (mem_gamma_iff q a 1 A).mp hA i j
  rw [pow_one] at hd
  obtain ⟨b, hb⟩ := hd
  refine ⟨Ideal.Quotient.mk (powerIdeal q m) b, ?_⟩
  have he := congrArg (Ideal.Quotient.mk (powerIdeal q m)) hb
  simp only [map_sub, map_mul] at he
  simpa [Matrix.sub_apply, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply, tbar] using he

theorem reduction_prime_power (p a m : ℕ) (hp : p.Prime)
    (A : Matrix.SpecialLinearGroup (Fin a) (R p)) (hA : A ∈ Gamma p a 1) :
    ∃ r : ℕ, (Matrix.SpecialLinearGroup.map
      (Ideal.Quotient.mk (powerIdeal p m)) A) ^ p ^ r = 1 := by
  let B := Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) A
  have hc : (p : Matrix (Fin a) (Fin a) (Trunc p m)) = 0 := by
    ext i j
    simp [Matrix.natCast_apply, prime_cast_trunc]
  obtain ⟨r, hr⟩ := exists_prime_power_unipotent hp hc
    ((B : Matrix (Fin a) (Fin a) (Trunc p m)) - 1)
    (reduction_sub_one_nilpotent p a m A hA)
  refine ⟨r, ?_⟩
  apply Subtype.ext
  simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    add_sub_cancel] using hr

theorem upperUnitriangular_isPGroup (p a : ℕ) (hp : p.Prime) [NeZero p] :
    IsPGroup p (upperUnitriangular p a) := by
  intro g
  have hn : IsNilpotent ((g.val : Matrix (Fin a) (Fin a) (ZMod p)) - 1) := by
    refine ⟨a, strict_upper_pow_zero a _ ?_⟩
    intro i j hij
    rw [Matrix.sub_apply, g.property i j hij, sub_self]
  have hc : (p : Matrix (Fin a) (Fin a) (ZMod p)) = 0 := by
    ext i j
    simp [Matrix.natCast_apply]
  obtain ⟨r, hr⟩ := exists_prime_power_unipotent hp hc _ hn
  refine ⟨r, Subtype.ext (Subtype.ext ?_)⟩
  simpa only [Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow,
    Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, add_sub_cancel] using hr

theorem gquot_isPGroup (p a m : ℕ) (hp : p.Prime) [NeZero p] : IsPGroup p (Gquot p a m) := by
  have himage : IsPGroup p (uReduction p a m).range := by
    intro g
    obtain ⟨A, hA⟩ := g.property
    have hpU := upperUnitriangular_isPGroup p a hp
      ⟨evalZero p a A.val, A.property⟩
    obtain ⟨r, hr⟩ := hpU
    have hgamma : A.val ^ p ^ r ∈ Gamma p a 1 := by
      rw [gamma_one_eq_ker_evalZero, MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val hr
    obtain ⟨s, hs⟩ := reduction_prime_power p a m hp _ hgamma
    refine ⟨r + s, Subtype.ext ?_⟩
    change g.val ^ p ^ (r + s) = 1
    rw [← hA, pow_add, pow_mul]
    simpa only [map_pow, uReduction, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype] using hs
  exact himage.of_surjective
    (QuotientGroup.quotientKerEquivRange (uReduction p a m)).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivRange (uReduction p a m)).symm.surjective

theorem odd_gquot_card (p a m : ℕ) (hp : p.Prime) (hodd : Odd p) [NeZero p] :
    Odd (Nat.card (Gquot p a m)) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := (gquot_isPGroup p a m hp).exists_card_eq
  rw [hr]
  exact hodd.pow

end

variable (p n : ℕ) [Fact p.Prime]

theorem localQuotientMap_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (cut : Fin (n + 1)) : Function.Injective (localQuotientMap p n hn m cut) := by
  intro A B h
  apply Subtype.ext
  apply localGroups_reduction_injective p n hn hm cut cut A B
  exact congrArg (fun g : Gquot p (n + 1) m =>
    (QuotientGroup.quotientKerEquivRange (uReduction p (n + 1) m) g).val) h

theorem localGroup_isPGroup (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    IsPGroup p (localGroup p n hn cut) :=
  (gquot_isPGroup p (n + 1) 2 Fact.out).of_injective
    (localQuotientMap p n hn 2 cut) (localQuotientMap_injective p n hn le_rfl cut)

theorem localGroup_odd (hn : 1 ≤ n) (hp : Odd p) (cut : Fin (n + 1)) :
    Odd (Nat.card (localGroup p n hn cut)) := by
  obtain ⟨r, hr⟩ := (localGroup_isPGroup p n hn cut).exists_card_eq
  rw [hr]
  exact hp.pow

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Elementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Elementary matrices, Euclidean generation, block matrices, and residue-field pivot arguments.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Elementary
variable {A : Type*} [CommRing A] {n : ℕ}

theorem E_upper_one_mem (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) A))
    (hE : ∀ i j (h : i.val + 1 = j.val), E (show i ≠ j by intro he; subst j; omega) (1 : A) ∈ H)
    {i j : Fin n} (hij : i < j) : E hij.ne (1 : A) ∈ H := by
  generalize hdiff : j.val - i.val = r
  induction r using Nat.strong_induction_on generalizing i j with
  | h r ih =>
    by_cases hadj : i.val + 1 = j.val
    · exact hE i j hadj
    · let k : Fin n := ⟨j.val - 1, by omega⟩
      have hik : i < k := by dsimp [k]; change i.val < j.val - 1; omega
      have hkj : k.val + 1 = j.val := by dsimp [k]; omega
      have hkj' : k < j := by change k.val < j.val; omega
      have hk := ih (k.val - i.val) (by omega) hik rfl
      simpa only [mul_one] using E_path_mem H hik.ne hkj'.ne hij.ne hk (hE k j hkj)

end CoboundaryExpanders.Elementary

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

end

section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Elementary

section
variable {F : Type*} [Field F] {n : ℕ}

theorem lower_column_nonzero (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F))
    (j : Fin n) (hg : ColumnPrefix g j.val) :
    ∃ a : Fin n, j ≤ a ∧ g a j ≠ 0 := by
  classical
  by_contra! h
  have hs := inverse_column_sum g j j
  rw [ite_eq_left rfl] at hs
  have hz : (∑ a, g⁻¹ j a * g a j) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hja : j ≤ a
    · rw [h a hja, mul_zero]
    · rw [inverse_prefix_zero g hg (show a.val < j.val from lt_of_not_ge hja)
        (ne_of_gt (lt_of_not_ge hja)), zero_mul]
  exact zero_ne_one (hz.symm.trans hs)

theorem exists_unit_pivot
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F)))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (j : Fin n)
    (hg : ColumnPrefix g j.val) :
    ∃ e ∈ H, ColumnPrefix (e * g) j.val ∧ IsUnit ((e * g) j j) := by
  classical
  let P : ℕ → Prop := fun r => ∃ e ∈ H, ColumnPrefix (e * g) j.val ∧
    (e * g) j j ≠ 0 ∧ ((e * g) j j).natDegree = r
  have hex : ∃ r, P r := by
    obtain ⟨a, hja, ha⟩ := lower_column_nonzero g j hg
    by_cases haj : a = j
    · subst a
      exact ⟨(g j j).natDegree, 1, H.one_mem, by simpa using hg, by simpa using ha,
        by simp⟩
    · refine ⟨(g a j).natDegree, W (Ne.symm haj), W_mem H hE (Ne.symm haj),
        columnPrefix_W_mul hg (Ne.symm haj) le_rfl hja, ?_, ?_⟩
      · simpa [W_mul_apply] using ha
      · simp [W_mul_apply]
  obtain ⟨e, he, hpref, hp, hdegree⟩ := Nat.find_spec hex
  have hdiv : ∀ a : Fin n, j ≤ a → (e * g) j j ∣ (e * g) a j := by
    intro a hja
    by_cases haj : a = j
    · subst a; exact dvd_refl _
    · apply (EuclideanDomain.mod_eq_zero).mp
      by_contra hmod
      let c : (Polynomial F) := -((e * g) a j / (e * g) j j)
      let e' := W (Ne.symm haj) * E haj c * e
      have he' : e' ∈ H := H.mul_mem (H.mul_mem (W_mem H hE (Ne.symm haj)) (hE _ _ _ _)) he
      have hpre' : ColumnPrefix (e' * g) j.val := by
        dsimp only [e']
        rw [mul_assoc, mul_assoc]
        exact columnPrefix_W_mul (columnPrefix_E_mul hpref haj le_rfl c)
          (Ne.symm haj) le_rfl hja
      have hpiv : (e' * g) j j = (e * g) a j % (e * g) j j := by
        dsimp only [e']
        rw [mul_assoc, mul_assoc, W_mul_apply, ite_eq_left rfl, E_mul_apply, ite_eq_left rfl]
        rw [EuclideanDomain.mod_eq_sub_mul_div]
        dsimp [c]
        ring
      have hnew : P (((e * g) a j % (e * g) j j).natDegree) :=
        ⟨e', he', hpre', by rw [hpiv]; exact hmod, by rw [hpiv]⟩
      have hlt : (((e * g) a j % (e * g) j j).natDegree) < Nat.find hex := by
        rw [← hdegree]
        exact Polynomial.natDegree_lt_natDegree hmod (Polynomial.degree_mod_lt _ hp)
      exact Nat.find_min hex hlt hnew
  refine ⟨e, he, hpref, isUnit_of_dvd_one ?_⟩
  have hs := inverse_column_sum (e * g) j j
  rw [ite_eq_left rfl] at hs
  apply (show (e * g) j j ∣ ∑ a, (e * g)⁻¹ j a * (e * g) a j from ?_).trans
    (dvd_of_eq hs)
  apply Finset.dvd_sum
  intro a ha
  by_cases hja : j ≤ a
  · exact dvd_mul_of_dvd_right (hdiv a hja) _
  · rw [inverse_prefix_zero (e * g) hpref (show a.val < j.val from lt_of_not_ge hja)
      (ne_of_gt (lt_of_not_ge hja)), zero_mul]
    exact dvd_zero _

end

section
variable {F : Type*} [Field F] {n : ℕ}

theorem diagonalize_polynomial
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F)))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) :
    ∃ e ∈ H, ∀ i j, i ≠ j → (e * g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n → ∃ e ∈ H, ColumnPrefix (e * g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1, H.one_mem, by intro a b h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨e, he, hpref⟩ := ih (by omega)
      let j : Fin n := ⟨k, by omega⟩
      obtain ⟨h, hh, hpref', hpiv⟩ := exists_unit_pivot H hE (e * g) j hpref
      obtain ⟨r, hr, hcol⟩ := clear_column H hE (h * (e * g)) j hpref' hpiv
      exact ⟨r * h * e, H.mul_mem (H.mul_mem hr hh) he, by simpa [mul_assoc, j] using hcol⟩
  obtain ⟨e, he, hpref⟩ := hsteps n le_rfl
  exact ⟨e, he, fun i j hij => hpref i j j.isLt hij⟩

end

section
variable {F : Type*} [Field F]

theorem polynomial_SL_mem_of_roots (n : ℕ)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F)))
    (hE : ∀ i j (h : i ≠ j) c, E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) : g ∈ H := by
  cases n with
  | zero =>
    have hg : g = 1 := by ext i; exact Fin.elim0 i
    rw [hg]; exact H.one_mem
  | succ n =>
    obtain ⟨e, he, hd⟩ := diagonalize_polynomial H hE g
    have hm := diagonal_mem_of_roots H hE (e * g) hd
    simpa only [inv_mul_cancel_left] using H.mul_mem (H.inv_mem he) hm

end

end CoboundaryExpanders.Elementary

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.Elementary
open Polynomial
variable {F : Type*} [Field F] {n : ℕ}

theorem restricted_euclidean_descent (a b : Polynomial F)
    (ha : a.constantCoeff = 1) (hb : b.constantCoeff = 0)
    (hmod : b % a ≠ 0) :
    ∃ c d : Polynomial F, c.constantCoeff = 0 ∧
      (a + d * (b + c*a)).natDegree < a.natDegree := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let q := b / a
  let r := b % a
  have hr : r ≠ 0 := hmod
  have hdeg : r.natDegree < a.natDegree :=
    Polynomial.natDegree_lt_natDegree hmod (Polynomial.degree_mod_lt b ha0)
  have heq : b + (-q)*a = r := by
    dsimp [q,r]
    rw [EuclideanDomain.mod_eq_sub_mul_div]
    ring
  by_cases hq : q.constantCoeff = 0
  · refine ⟨-q, -(a/r), by simpa using hq, ?_⟩
    rw [heq]
    have heq' : a + (-(a/r))*r = a % r := by
      rw [EuclideanDomain.mod_eq_sub_mul_div]
      ring
    rw [heq']
    have hr0 : r.constantCoeff = 0 := by
      rw [← heq]
      simp only [map_add,map_mul,map_neg,hb,hq,zero_mul,neg_zero,add_zero]
    have hrem : a % r ≠ 0 := by
      intro h
      have hc := congrArg Polynomial.constantCoeff h
      rw [EuclideanDomain.mod_eq_sub_mul_div] at hc
      simp only [map_sub,map_mul,ha,hr0,zero_mul,sub_zero,map_zero] at hc
      exact one_ne_zero hc
    exact (Polynomial.natDegree_lt_natDegree hrem (Polynomial.degree_mod_lt a hr)).trans hdeg
  · let c := -q + C q.constantCoeff
    let d := C (-q.constantCoeff⁻¹)
    refine ⟨c,d,by simp [c],?_⟩
    have heq' : a + d*(b+c*a) = d*r := by
      have hc : b+c*a = r + C q.constantCoeff * a := by
        dsimp [c]
        rw [← heq]
        ring
      rw [hc]
      have hd : d * C q.constantCoeff = -1 := by
        dsimp only [d]
        rw [← map_mul, neg_mul, inv_mul_cancel₀ hq]
        simp
      calc
        a + d*(r+C q.constantCoeff*a) = a + (d*C q.constantCoeff)*a + d*r := by ring
        _ = d*r := by rw [hd]; ring
    rw [heq']
    apply lt_of_le_of_lt (Polynomial.natDegree_mul_le) _
    simpa [d] using hdeg

theorem exists_unit_pivot_iwahori
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hgB : g ∈ B)
    (j : Fin n) (hg : ColumnPrefix g j.val) :
    ∃ e ∈ H, ColumnPrefix (e*g) j.val ∧ IsUnit ((e*g) j j) := by
  classical
  let P : ℕ → Prop := fun r => ∃ e ∈ H, ColumnPrefix (e*g) j.val ∧ ((e*g) j j).natDegree = r
  have hex : ∃ r, P r := ⟨(g j j).natDegree,1,H.one_mem,by simpa using hg,by simp⟩
  obtain ⟨e,he,hpref,hdegree⟩ := Nat.find_spec hex
  have hegB : e*g ∈ B := B.mul_mem (hHB he) hgB
  have hconst : ((e*g) j j).constantCoeff = 1 := by simpa using hB (e*g) hegB j j le_rfl
  have hdiv : ∀ a : Fin n, j ≤ a → (e*g) j j ∣ (e*g) a j := by
    intro a hja
    by_cases haj : a=j
    · subst a; exact dvd_refl _
    · apply (EuclideanDomain.mod_eq_zero).mp
      by_contra hmod
      have hja' : j < a := lt_of_le_of_ne hja (Ne.symm haj)
      have hb : ((e*g) a j).constantCoeff = 0 := by simpa [haj] using hB (e*g) hegB a j hja
      obtain ⟨c,d,hc,hlt⟩ := restricted_euclidean_descent ((e*g) j j) ((e*g) a j) hconst hb hmod
      let e' := E (Ne.symm haj) d * E haj c * e
      have he' : e' ∈ H := H.mul_mem (H.mul_mem
        (hE j a (Ne.symm haj) d (by intro h; exact False.elim (not_lt_of_ge hja h)))
        (hE a j haj c (by intro _; exact hc))) he
      have hpre' : ColumnPrefix (e'*g) j.val := by
        dsimp only [e']
        rw [mul_assoc,mul_assoc]
        exact columnPrefix_E_mul (columnPrefix_E_mul hpref haj le_rfl c) (Ne.symm haj) hja d
      have hpiv : (e'*g) j j = (e*g) j j + d*((e*g) a j + c*(e*g) j j) := by
        dsimp only [e']
        simp only [mul_assoc,E_mul_apply,ite_eq_right (Ne.symm haj),add_zero,ite_true]
      have hnew : P (((e*g) j j + d*((e*g) a j+c*(e*g) j j)).natDegree) :=
        ⟨e',he',hpre',by rw [hpiv]⟩
      apply Nat.find_min hex _ hnew
      simpa only [← hdegree] using hlt
  refine ⟨e,he,hpref,isUnit_of_dvd_one ?_⟩
  have hs := inverse_column_sum (e*g) j j
  rw [ite_eq_left rfl] at hs
  apply (show (e*g) j j ∣ ∑ a, (e*g)⁻¹ j a * (e*g) a j from ?_).trans (dvd_of_eq hs)
  apply Finset.dvd_sum
  intro a _
  by_cases hja : j ≤ a
  · exact dvd_mul_of_dvd_right (hdiv a hja) _
  · rw [inverse_prefix_zero (e*g) hpref (show a.val < j.val from lt_of_not_ge hja)
      (ne_of_gt (lt_of_not_ge hja)),zero_mul]
    exact dvd_zero _

theorem clear_column_iwahori
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hgB : g ∈ B)
    (j : Fin n) (hg : ColumnPrefix g j.val) (hu : IsUnit (g j j)) :
    ∃ e ∈ H, ColumnPrefix (e*g) (j.val+1) := by
  classical
  obtain ⟨u,hu⟩ := hu
  have hclear : ∀ s : Finset (Fin n), (∀ a ∈ s, a ≠ j) →
      ∃ e ∈ H, ColumnPrefix (e*g) j.val ∧ (e*g) j j = (u : Polynomial F) ∧
        ∀ a ∈ s, (e*g) a j = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1,H.one_mem,by simpa using hg,by simpa using hu.symm,by simp⟩
    | @insert a s has ih =>
      intro hs
      obtain ⟨e,he,hpref,hpiv,hz⟩ := ih (fun b hb => hs b (Finset.mem_insert_of_mem hb))
      have haj : a ≠ j := hs a (Finset.mem_insert_self _ _)
      let c : Polynomial F := -((e*g) a j) * (↑(u⁻¹) : Polynomial F)
      have hc : E haj c ∈ H := by
        apply hE
        intro hja
        dsimp only [c]
        rw [map_mul,map_neg,hB (e*g) (B.mul_mem (hHB he) hgB) a j hja.le,ite_eq_right haj]
        simp
      refine ⟨E haj c * e,H.mul_mem hc he,?_,?_,?_⟩
      · rw [mul_assoc]
        exact columnPrefix_E_mul hpref haj le_rfl c
      · rw [mul_assoc,E_mul_apply,ite_eq_right (Ne.symm haj),add_zero,hpiv]
      · intro b hb
        rw [mul_assoc,E_mul_apply]
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [ite_eq_left rfl,hpiv]
          dsimp [c]
          rw [mul_assoc,Units.inv_mul,mul_one,add_neg_cancel]
        · rw [ite_eq_right (by intro h; subst b; exact has hb),add_zero]
          exact hz b hb
  obtain ⟨e,he,hpref,_,hz⟩ := hclear (Finset.univ.erase j) (by simp)
  refine ⟨e,he,?_⟩
  intro a b hb hab
  by_cases hbj : b.val < j.val
  · exact hpref a b hbj hab
  · have hbe : b=j := Fin.ext (by omega)
    subst b
    exact hz a (by simp [hab])

theorem diagonalize_polynomial_iwahori
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hg : g ∈ B) :
    ∃ e ∈ H, ∀ i j, i ≠ j → (e*g) i j = 0 := by
  have hsteps : ∀ k, k ≤ n → ∃ e ∈ H, ColumnPrefix (e*g) k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1,H.one_mem,by intro a b h; omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨e,he,hpref⟩ := ih (by omega)
      let j : Fin n := ⟨k,by omega⟩
      have heg := B.mul_mem (hHB he) hg
      obtain ⟨h,hh,hpref',hpiv⟩ := exists_unit_pivot_iwahori B H hHB hB hE (e*g) heg j hpref
      obtain ⟨r,hr,hcol⟩ := clear_column_iwahori B H hHB hB hE (h*(e*g))
        (B.mul_mem (hHB hh) heg) j hpref' hpiv
      exact ⟨r*h*e,H.mul_mem (H.mul_mem hr hh) he,by simpa [mul_assoc,j] using hcol⟩
  obtain ⟨e,he,hpref⟩ := hsteps n le_rfl
  exact ⟨e,he,fun i j hij => hpref i j j.isLt hij⟩

theorem polynomial_iwahori_mem_of_roots
    (B H : Subgroup (Matrix.SpecialLinearGroup (Fin n) (Polynomial F))) (hHB : H ≤ B)
    (hB : ∀ g ∈ B, ∀ i j, j ≤ i → (g i j).constantCoeff = if i=j then 1 else 0)
    (hE : ∀ i j (h : i ≠ j) (c : Polynomial F),
      (j < i → c.constantCoeff = 0) → E h c ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin n) (Polynomial F)) (hg : g ∈ B) : g ∈ H := by
  obtain ⟨e,he,hdiag⟩ := diagonalize_polynomial_iwahori B H hHB hB hE g hg
  have heg : e*g = 1 := by
    ext i j
    by_cases hij : i=j
    · subst j
      have hunit := column_diagonal_unit (e*g) i (fun a ha => hdiag a i ha)
      obtain ⟨c,hc,hc'⟩ := Polynomial.isUnit_iff.mp hunit
      have hconst := hB (e*g) (B.mul_mem (hHB he) hg) i i le_rfl
      rw [← hc'] at hconst
      have hc1 : c=1 := by simpa using hconst
      simp [← hc',hc1]
    · simp [hdiag i j hij, hij]
  rw [eq_inv_of_mul_eq_one_right heg]
  exact H.inv_mem he

end CoboundaryExpanders.Elementary

end

open scoped BigOperators Matrix
attribute [local instance] Classical.decEq

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Mixing
attribute [-instance] _root_.OAI.CoboundaryExpanders.Blocks.gammaNormal _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Small-set expansion, local spectral descent, connectedness, and uniform coset mixing.
-/

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Construction

section
open Elementary
variable (p n : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem cycleRoot_mem_generated (hn : 1 ≤ n) (j : Fin (n + 1)) :
    cycleRoot p n hn j ∈ cycleGenerated p n hn :=
  Subgroup.subset_closure ⟨j, rfl⟩

theorem cycleGenerated_le_U (hn : 1 ≤ n) : cycleGenerated p n hn ≤ U p (n + 1) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact cycleRoot_mem_U p n hn j

omit [Fact p.Prime] in
theorem upper_adjacent_mem_generated (hn : 1 ≤ n) (i j : Fin (n + 1))
    (hij : i.val + 1 = j.val) :
    E (show i ≠ j by intro he; subst j; omega) (1 : R p) ∈ cycleGenerated p n hn := by
  have hj : j ≠ 0 := by intro he; subst j; simp at hij
  have hs : edgeSource n j = i := by
    apply Fin.ext
    simp only [edgeSource, dite_eq_right hj, Fin.val_mk]
    omega
  simpa only [cycleRoot, ite_eq_right hj, hs] using cycleRoot_mem_generated p n hn j

omit [Fact p.Prime] in
theorem upper_one_mem_generated (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : i < j) :
    E hij.ne (1 : R p) ∈ cycleGenerated p n hn :=
  E_upper_one_mem _ (upper_adjacent_mem_generated p n hn) hij

omit [Fact p.Prime] in
theorem lower_X_mem_generated (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : j < i) :
    E hij.ne.symm (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
  have hlast0 : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro he
    have := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  have hbase : E hlast0 (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
    simpa [cycleRoot, edgeSource, E] using
      cycleRoot_mem_generated p n hn 0
  have hlastj : j < Fin.last n := by change j.val < n; have := i.isLt; omega
  have hlast : E hlastj.ne.symm (Polynomial.X : R p) ∈ cycleGenerated p n hn := by
    by_cases hj : j = 0
    · subst j; exact hbase
    · have h0j : (0 : Fin (n + 1)) < j := Fin.pos_iff_ne_zero.mpr hj
      simpa only [mul_one] using E_path_mem (cycleGenerated p n hn)
        hlast0 h0j.ne hlastj.ne.symm hbase (upper_one_mem_generated p n hn h0j)
  by_cases hi : i = Fin.last n
  · subst i; exact hlast
  · have hilast : i < Fin.last n := by change i.val < n; have := i.isLt; have := Fin.ext_iff.not.mp hi; simp only [Fin.val_last] at this; omega
    simpa only [one_mul] using E_path_mem (cycleGenerated p n hn)
      hilast.ne hlastj.ne.symm hij.ne.symm (upper_one_mem_generated p n hn hilast) hlast

omit [Fact p.Prime] in
theorem X_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j) :
    E hij (Polynomial.X : R p) ∈ cycleGenerated p n (by omega) := by
  have hn1 : 1 ≤ n := by omega
  by_cases hji : j < i
  · exact lower_X_mem_generated p n hn1 hji
  have hij' : i < j := lt_of_le_of_ne (le_of_not_gt hji) hij
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = Fin.last n
    · subst j
      let k : Fin (n + 1) := ⟨1, by omega⟩
      have h0k : (0 : Fin (n + 1)) < k := by change (0 : ℕ) < 1; omega
      have hklast : k < Fin.last n := by change 1 < n; omega
      have hk0 := lower_X_mem_generated p n hn1 h0k
      have h0last := upper_one_mem_generated p n hn1 hij'
      have hklastX : E hklast.ne (Polynomial.X : R p) ∈ cycleGenerated p n hn1 := by
        simpa only [mul_one] using E_path_mem (cycleGenerated p n hn1)
          h0k.ne.symm hij'.ne hklast.ne hk0 h0last
      simpa only [one_mul] using E_path_mem (cycleGenerated p n hn1)
        h0k.ne hklast.ne hij (upper_one_mem_generated p n hn1 h0k) hklastX
    · have hjlast : j < Fin.last n := by
        change j.val < n
        have := j.isLt
        have := Fin.ext_iff.not.mp hj
        simp only [Fin.val_last] at this
        omega
      have h0last : (0 : Fin (n + 1)) < Fin.last n := by change 0 < n; omega
      simpa only [one_mul] using E_path_mem (cycleGenerated p n hn1)
        h0last.ne hjlast.ne.symm hij (upper_one_mem_generated p n hn1 h0last)
        (lower_X_mem_generated p n hn1 hjlast)
  · have h0i : (0 : Fin (n + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
    have h0j : (0 : Fin (n + 1)) < j := h0i.trans hij'
    simpa only [mul_one] using E_path_mem (cycleGenerated p n hn1)
      h0i.ne.symm h0j.ne hij (lower_X_mem_generated p n hn1 h0i)
      (upper_one_mem_generated p n hn1 h0j)

omit [Fact p.Prime] in
theorem X_pow_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j) (r : ℕ) :
    E hij (Polynomial.X ^ (r + 1) : R p) ∈ cycleGenerated p n (by omega) := by
  induction r generalizing i j with
  | zero => simpa only [zero_add, pow_one] using X_mem_generated p n hn hij
  | succ r ih =>
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    simpa only [pow_succ] using E_path_mem (cycleGenerated p n (by omega))
      hki.symm hkj hij (ih hki.symm) (X_mem_generated p n hn hkj)

theorem scalar_root_mem (hn : 1 ≤ n) {i j : Fin (n + 1)} (hij : i ≠ j)
    {f : R p} (hf : E hij f ∈ cycleGenerated p n hn) (c : ZMod p) :
    E hij (Polynomial.C c * f) ∈ cycleGenerated p n hn := by
  have hc : Polynomial.C c = (c.val : R p) := by
    calc Polynomial.C c = Polynomial.C (c.val : ZMod p) :=
           congrArg Polynomial.C (ZMod.natCast_zmod_val c).symm
         _ = _ := map_natCast Polynomial.C _
  rw [hc, E_natCast_mul]
  exact (cycleGenerated p n hn).pow_mem hf _

theorem upper_polynomial_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)}
    (hij : i < j) (f : R p) : E hij.ne f ∈ cycleGenerated p n (by omega) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    change Matrix.SpecialLinearGroup.transvection hij.ne (f + g) ∈ _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    exact (cycleGenerated p n (by omega)).mul_mem hf hg
  | monomial r c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    apply scalar_root_mem
    cases r with
    | zero => simpa using upper_one_mem_generated p n (by omega) hij
    | succ r => exact X_pow_mem_generated p n hn hij.ne r

theorem X_polynomial_mem_generated (hn : 2 ≤ n) {i j : Fin (n + 1)}
    (hij : i ≠ j) (f : R p) :
    E hij (Polynomial.X * f) ∈ cycleGenerated p n (by omega) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [mul_add]
    change Matrix.SpecialLinearGroup.transvection hij (_ + _) ∈ _
    rw [Matrix.SpecialLinearGroup.transvection_add]
    exact (cycleGenerated p n (by omega)).mul_mem hf hg
  | monomial r c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    rw [mul_left_comm, ← pow_succ']
    exact scalar_root_mem p n (by omega) hij (X_pow_mem_generated p n hn hij r) c

end

open Elementary

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Odd-index transfer, comparison of bar resolutions, and homology-coinvariant models.
-/

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory

namespace CoboundaryExpanders.Transfer

section
open CategoryTheory Representation Finsupp
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

omit [S.Normal] [Fintype (G ⧸ S)] in
theorem chain_factorization :
    CoinvariantModel.chainsIso.hom ≫ barCoinvariantInclusion (k := k) S ≫
      chainInclusion S (Rep.barComplex k G) =
    groupHomology.chainsMap S.subtype (trivialInclusion (k := k) S) ≫
      (CoinvariantModel.chainsIso (k := k) (G := G)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x r
  change inclusion (Representation.free k G (Fin n → G)) S
    (Representation.Coinvariants.map _ _ (BarComparison.inclusionF (k := k) S n).hom
      ((CoinvariantModel.chainsIso (k := k) (G := S)).hom.f n (single x r))) =
    (CoinvariantModel.chainsIso (k := k) (G := G)).hom.f n
      ((groupHomology.chainsMap S.subtype (trivialInclusion (k := k) S)).f n (single x r))
  rw [CoinvariantModel.chainsIso_hom_single, Coinvariants.map_mk,
    BarComparison.inclusionF_single, inclusion_mk,
    groupHomology.chainsMap_f_single, CoinvariantModel.chainsIso_hom_single]
  rfl

theorem homology_surjective_of_homotopyEquiv
    {C D : ChainComplex (ModuleCat k) ℕ} (e : HomotopyEquiv C D) (j : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap e.hom j) := by
  have h : HomologicalComplex.homologyMap e.inv j ≫
      HomologicalComplex.homologyMap e.hom j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp,
      e.homotopyInvHomId.homologyMap_eq j, HomologicalComplex.homologyMap_id]
  intro y
  refine ⟨HomologicalComplex.homologyMap e.inv j y, ?_⟩
  exact congrArg (fun f => ModuleCat.Hom.hom f y) h

omit [DecidableEq G] [S.Normal] [Fintype (G ⧸ S)] in
theorem homology_barCoinvariantInclusion_surjective (j : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap
      (barCoinvariantInclusion (k := k) S) j) :=
  homology_surjective_of_homotopyEquiv
    ((Rep.coinvariantsFunctor k S).mapHomotopyEquiv (BarComparison.inclusionEquiv S)) j

end

open Representation
universe u
variable {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

theorem normTransfer_inclusion (V : Type*) [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :
    normTransfer ρ S ∘ₗ inclusion ρ S = ∑ q : G ⧸ S, ρ.quotientToCoinvariants S q := by
  apply Coinvariants.hom_ext
  ext v
  simp [LinearMap.comp_apply, LinearMap.sum_apply]

theorem chainInclusion_transfer (C : ChainComplex (Rep k G) ℕ) :
    chainInclusion S C ≫ chainTransfer S C = ∑ q : G ⧸ S, chainQuotientAction S C q := by
  apply HomologicalComplex.hom_ext
  intro n
  have hsum : (∑ q : G ⧸ S, chainQuotientAction (k := k) S C q).f n =
      ∑ q : G ⧸ S, (chainQuotientAction S C q).f n :=
    map_sum (HomologicalComplex.Hom.fAddMonoidHom n) _ _
  rw [hsum]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum]
  change normTransfer (C.X n).ρ S ∘ₗ inclusion (C.X n).ρ S =
    ∑ q : G ⧸ S, (C.X n).ρ.quotientToCoinvariants S q
  exact normTransfer_inclusion S _ _

theorem homology_chainInclusion_injective (C : ChainComplex (Rep k G) ℕ)
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ)
    (htriv : ∀ q, HomologicalComplex.homologyMap (chainQuotientAction S C q) j = 𝟙 _) :
    Function.Injective (HomologicalComplex.homologyMap (chainInclusion S C) j) := by
  have hh : HomologicalComplex.homologyMap (chainInclusion S C) j ≫
      HomologicalComplex.homologyMap (chainTransfer S C) j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, chainInclusion_transfer]
    change (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) j).map
      (∑ q : G ⧸ S, chainQuotientAction S C q) = _
    rw [Functor.map_sum]
    change (∑ q : G ⧸ S, HomologicalComplex.homologyMap (chainQuotientAction S C q) j) = _
    simp only [htriv, Finset.sum_const, Finset.card_univ]
    ext v
    change (Fintype.card (G ⧸ S)) • v = v
    rw [← Nat.cast_smul_eq_nsmul k, hindex, one_smul]
  intro x y hxy
  have hx := congrArg (fun f => ModuleCat.Hom.hom f x) hh
  have hy := congrArg (fun f => ModuleCat.Hom.hom f y) hh
  exact hx.symm.trans ((congrArg (HomologicalComplex.homologyMap (chainTransfer S C) j) hxy).trans hy)

end CoboundaryExpanders.Transfer

namespace CoboundaryExpanders.Transfer
open Representation Finsupp
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

omit [DecidableEq G] [S.Normal] [Fintype (G ⧸ S)] in
theorem homology_adjusted (g : G) (j : ℕ) :
    HomologicalComplex.homologyMap (barCoinvariantAdjusted (k := k) S g) j =
      HomologicalComplex.homologyMap (barCoinvariantInclusion (k := k) S) j :=
  ((Rep.coinvariantsFunctor k S).mapHomotopy (BarComparison.adjustedHomotopy S g)).homologyMap_eq j

omit [Fintype (G ⧸ S)] in
theorem chain_conjugation_factorization (g : G) :
    (CoinvariantModel.chainsIso (k := k) (G := S)).hom ≫ barCoinvariantAdjusted S g ≫
      chainQuotientAction S (Rep.barComplex k G) (g : G ⧸ S) =
    groupHomology.chainsMap (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) ≫
      (CoinvariantModel.chainsIso (k := k) (G := S)).hom ≫ barCoinvariantInclusion S := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x r
  change (Representation.free k G (Fin n → G)).quotientToCoinvariants S (g : G ⧸ S)
    (Coinvariants.map _ _ (BarComparison.adjustedF (k := k) S g n).hom
      ((CoinvariantModel.chainsIso (k := k) (G := S)).hom.f n (single x r))) =
    Coinvariants.map _ _ (BarComparison.inclusionF (k := k) S n).hom
      ((CoinvariantModel.chainsIso (k := k) (G := S)).hom.f n
        ((groupHomology.chainsMap (MulAut.conjNormal (H := S) g).toMonoidHom
          (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom)).f n (single x r)))
  rw [CoinvariantModel.chainsIso_hom_single, Coinvariants.map_mk,
    BarComparison.adjustedF_single, quotient_action_mk,
    Representation.free_single_single,
    groupHomology.chainsMap_f_single, CoinvariantModel.chainsIso_hom_single,
    Coinvariants.map_mk, BarComparison.inclusionF_single]
  simp only [Subgroup.coe_one, one_mul, mul_inv_cancel]
  rfl

omit [Fintype (G ⧸ S)] in
theorem homology_quotientAction_eq_id (j : ℕ)
    (hconj : ∀ g : G, groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j = 𝟙 _) :
    ∀ q : G ⧸ S, HomologicalComplex.homologyMap
      (chainQuotientAction S (Rep.barComplex k G) q) j = 𝟙 _ := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hf := congrArg (fun f => HomologicalComplex.homologyMap f j)
      (chain_conjugation_factorization (k := k) S g)
    simp only [HomologicalComplex.homologyMap_comp, homology_adjusted] at hf
    change HomologicalComplex.homologyMap CoinvariantModel.chainsIso.hom j ≫
      HomologicalComplex.homologyMap (barCoinvariantInclusion S) j ≫
      HomologicalComplex.homologyMap (chainQuotientAction S (Rep.barComplex k G) (g : G ⧸ S)) j =
      groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
        (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j ≫
      HomologicalComplex.homologyMap CoinvariantModel.chainsIso.hom j ≫
      HomologicalComplex.homologyMap (barCoinvariantInclusion S) j at hf
    rw [hconj, Category.id_comp] at hf
    have hs := (homology_barCoinvariantInclusion_surjective (k := k) S j).comp
      (homology_surjective_of_homotopyEquiv
        (HomotopyEquiv.ofIso (CoinvariantModel.chainsIso (k := k) (G := S))) j)
    ext v
    obtain ⟨x, rfl⟩ := hs v
    exact congrArg (fun f => ModuleCat.Hom.hom f x) hf

theorem homology_injective_of_homotopyEquiv
    {C D : ChainComplex (ModuleCat k) ℕ} (e : HomotopyEquiv C D) (j : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap e.hom j) := by
  have hh : HomologicalComplex.homologyMap e.hom j ≫
      HomologicalComplex.homologyMap e.inv j = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp,
      e.homotopyHomInvId.homologyMap_eq j, HomologicalComplex.homologyMap_id]
  intro x y hxy
  have hx := congrArg (fun f => ModuleCat.Hom.hom f x) hh
  have hy := congrArg (fun f => ModuleCat.Hom.hom f y) hh
  exact hx.symm.trans ((congrArg (HomologicalComplex.homologyMap e.inv j) hxy).trans hy)

theorem groupHomology_inclusion_injective
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ)
    (hconj : ∀ g : G, groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j = 𝟙 _) :
    Function.Injective
      (groupHomology.map S.subtype (trivialInclusion (k := k) S) j) := by
  have hi := homology_chainInclusion_injective S (Rep.barComplex k G) hindex j
    (homology_quotientAction_eq_id S j hconj)
  have hb := homology_injective_of_homotopyEquiv
    ((Rep.coinvariantsFunctor k S).mapHomotopyEquiv (BarComparison.inclusionEquiv S)) j
  have hs := homology_injective_of_homotopyEquiv
    (HomotopyEquiv.ofIso (CoinvariantModel.chainsIso (k := k) (G := S))) j
  have hf := congrArg (fun f => HomologicalComplex.homologyMap f j)
    (chain_factorization (k := k) S)
  simp only [HomologicalComplex.homologyMap_comp] at hf
  intro x y hxy
  apply hs
  apply hb
  apply hi
  have hx := congrArg (fun f => ModuleCat.Hom.hom f x) hf
  have hy := congrArg (fun f => ModuleCat.Hom.hom f y) hf
  exact hx.trans ((congrArg
    (HomologicalComplex.homologyMap (CoinvariantModel.chainsIso (k := k) (G := G)).hom j)
    hxy).trans hy.symm)

theorem subgroup_homology_isZero_of_conjugation
    (hindex : (Fintype.card (G ⧸ S) : k) = 1) (j : ℕ)
    (hconj : ∀ g : G, groupHomology.map (MulAut.conjNormal (H := S) g).toMonoidHom
      (trivialCoefficients (k := k) (MulAut.conjNormal g).toMonoidHom) j = 𝟙 _)
    (hzero : Limits.IsZero (groupHomology (Rep.trivial k G k) j)) :
    Limits.IsZero (groupHomology (Rep.trivial k S k) j) := by
  let f := groupHomology.map S.subtype (trivialInclusion (k := k) S) j
  have : Mono f := (ModuleCat.mono_iff_injective f).mpr
    (groupHomology_inclusion_injective S hindex j hconj)
  exact Limits.IsZero.of_mono f hzero

end CoboundaryExpanders.Transfer

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Coinvariants
attribute [-instance] _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutVertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.kernelInvariant _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexAction _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Simplicial group actions, permutation modules, coset sums, and chain coinvariants.
-/

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra

namespace CoboundaryExpanders.TypedCosetFaces

section
open CategoryTheory
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

omit [DecidableEq I] in
lemma stabilizer_le (A : Finset I) {i : I} (hi : i ∈ A) : stabilizer H A ≤ H i :=
  fun _ hg => (mem_stabilizer H A _).mp hg i hi

omit [DecidableEq I] in
lemma stabilizer_finite [∀ i, Finite (H i)] (A : Finset I) (hA : A.Nonempty) :
    Finite (stabilizer H A) := by
  obtain ⟨i,hi⟩ := hA
  exact Finite.of_injective (Subgroup.inclusion (stabilizer_le H A hi))
    (Subgroup.inclusion_injective _)

omit [DecidableEq I] in
lemma stabilizer_odd (hH : ∀ i, Odd (Nat.card (H i))) (A : Finset I) (hA : A.Nonempty) :
    Odd (Nat.card (stabilizer H A)) := by
  obtain ⟨i,hi⟩ := hA
  exact (hH i).of_dvd_nat (Subgroup.card_dvd_of_le (stabilizer_le H A hi))

theorem projective_chains [∀ i, Finite (H i)] (hH : ∀ i, Odd (Nat.card (H i))) (j : ℕ) :
    Projective (((complex H).repComplex (G := G)).X j) := by
  let _ : ∀ A : Types (I := I) (j+1), Finite (stabilizer H A.val) :=
    fun A => stabilizer_finite H A.val (Finset.card_pos.mp (by omega))
  have hp := CosetSums.projective_of_odd_order
    (fun A : Types (I := I) (j+1) => stabilizer H A.val)
    (fun A => stabilizer_odd H hH A.val (Finset.card_pos.mp (by omega)))
  exact Projective.of_iso (chainsIso H (j+1)) hp

end

open InfiniteChains
open CategoryTheory
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

theorem coinvariant_homology_isZero [Nonempty I] (j : ℕ) :
    Limits.IsZero ((coinvariantComplex H).homology (j+1)) := by
  let a : I := Classical.choice inferInstance
  have hz := (Simplex (I := I)).chainComplex_homology_isZero_of_cone a
    (CoboundaryExpanders.InfiniteChains.Complex.full_isConePoint a) j
  exact hz.of_iso ((HomologicalComplex.homologyFunctor _ _ (j+1)).mapIso
    (coinvariantSimplexIso H))

end CoboundaryExpanders.TypedCosetFaces

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Stabilization
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Block stabilization, homology actions, quotient vanishing, and congruence cokernels.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Actions
universe u
variable {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]

theorem induced_equiv_surjective (e : H ≃* G) (j : ℕ) :
    Function.Surjective (induced (k := k) e.toMonoidHom j) := by
  have he := induced_comp (k := k) e.symm.toMonoidHom e.toMonoidHom j
  have hc : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [hc, induced_id] at he
  intro x
  refine ⟨induced e.symm.toMonoidHom j x, ?_⟩
  exact (congrArg (fun f => ModuleCat.Hom.hom f x) he).symm

end CoboundaryExpanders.Actions

namespace CoboundaryExpanders.QuotientVanishing
open CategoryTheory CoboundaryExpanders.Construction CoboundaryExpanders.Actions

variable (p a m : ℕ) [NeZero p]

theorem gammaInU_conj (hm : 1 ≤ m) (g : U p a) :
    (MulAut.conjNormal (H := K p a m) g).toMonoidHom.comp (gammaInU p a m hm).toMonoidHom =
    (gammaInU p a m hm).toMonoidHom.comp (MulAut.conjNormal (H := Gamma p a m) g.val).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem conjugation_in_U (hm : 1 ≤ m) (j : ℕ)
    (hconj : ∀ g : Matrix.SpecialLinearGroup (Fin a) (R p),
      conjugation (k := ZMod 2) (Gamma p a m) g j = 𝟙 _) (g : U p a) :
    conjugation (k := ZMod 2) (K p a m) g j = 𝟙 _ := by
  have hh := induced_congr (k := ZMod 2) (gammaInU_conj p a m hm g) j
  rw [induced_comp, induced_comp] at hh
  change induced (gammaInU p a m hm).toMonoidHom j ≫ conjugation (K p a m) g j =
    conjugation (Gamma p a m) g.val j ≫ induced (gammaInU p a m hm).toMonoidHom j at hh
  rw [hconj, Category.id_comp] at hh
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := induced_equiv_surjective (k := ZMod 2) (gammaInU p a m hm) j x
  exact congrArg (fun f => ModuleCat.Hom.hom f y) hh

theorem gamma_isZero_of_U_and_action (hp : p.Prime) (hodd : Odd p)
    (hm : 1 ≤ m) (j : ℕ)
    (hU : Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (U p a) (ZMod 2)) j))
    (hconj : ∀ g : Matrix.SpecialLinearGroup (Fin a) (R p),
      conjugation (k := ZMod 2) (Gamma p a m) g j = 𝟙 _) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j) := by
  have : Finite (U p a ⧸ K p a m) := inferInstanceAs (Finite (Gquot p a m))
  let : Fintype (U p a ⧸ K p a m) := Fintype.ofFinite _
  have hindex : (Fintype.card (U p a ⧸ K p a m) : ZMod 2) = 1 := by
    have h := odd_gquot_card p a m hp hodd
    change Odd (Nat.card (U p a ⧸ K p a m)) at h
    rw [Nat.card_eq_fintype_card] at h
    obtain ⟨r, hr⟩ := h
    rw [hr]
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, htwo, zero_mul, zero_add]
  have hz : Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (K p a m) (ZMod 2)) j) := by
    apply Transfer.subgroup_homology_isZero_of_conjugation (K p a m) hindex j
    · intro g
      exact conjugation_in_U p a m hm j hconj g
    · exact hU
  let f := induced (k := ZMod 2) (gammaInU p a m hm).symm.toMonoidHom j
  have : Epi f := (ModuleCat.epi_iff_surjective f).mpr
    (induced_equiv_surjective (k := ZMod 2) (gammaInU p a m hm).symm j)
  exact Limits.IsZero.of_epi f hz

end CoboundaryExpanders.QuotientVanishing

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Resolution
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype _root_.OAI.CoboundaryExpanders.MatrixOpposition.cutVertexFintype _root_.OAI.CoboundaryExpanders.TypedCosetFaces.vertexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Partial resolutions, orbit projectivity, and homology of finite congruence coset complexes.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.TypedCosetFaces
open CategoryTheory
open InfiniteChains
variable {G I : Type} [Group G] [DecidableEq G] [DecidableEq I] [Nonempty I]
  (H : I → Subgroup G)

theorem groupHomology_isZero_of_acyclic [∀ i, Finite (H i)]
    (hodd : ∀ i, Odd (Nat.card (H i))) (h : ℕ)
    (hexact : ∀ n, n < h → (complex H).chainComplex.ExactAt (n+1))
    (hzero : Function.Exact ((complex H).boundary 1) ((complex H).sumCoefficients 1))
    (j : ℕ) (hj : j+1 ≤ h) :
    Limits.IsZero (groupHomology (Rep.trivial k G k) (j+1)) := by
  let a : I := Classical.choice inferInstance
  let _ : Nonempty ((complex H).Face 1) :=
    ⟨baseFace H 1 ⟨{a},Set.mem_univ _,by simp⟩⟩
  let ε : ((complex H).repComplex (G := G)).X 0 ⟶ Rep.trivial k G k :=
    (complex H).augmentationRep
  let _ : Epi ε := (complex H).augmentationRep_epi
  have hε : ((complex H).repComplex (G := G)).d 1 0 ≫ ε = 0 := by
    change (complex H).boundaryRep 1 ≫ (complex H).augmentationRep = 0
    exact (complex H).augmentationRep_boundary
  have hz : (ShortComplex.mk (((complex H).repComplex (G := G)).d 1 0)
      ε hε).Exact := by
    change (ShortComplex.mk ((complex H).boundaryRep 1)
      (complex H).augmentationRep _).Exact
    exact (complex H).augmentationRep_exact hzero
  let e := CoinvariantHomology.homologyIso k G ((complex H).repComplex (G := G)) h
    ε hε
    (fun n _ => projective_chains H hodd n)
    (fun n hn => (complex H).repComplex_exactAt n (hexact n hn)) hz (j+1) hj
  exact (coinvariant_homology_isZero H j).of_iso e

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open CategoryTheory InfiniteChains
variable (p n : ℕ) [Fact p.Prime]

lemma uLocalGroup_odd (hn : 1 ≤ n) (hp : Odd p) (i : Fin (n+1)) :
    Odd (Nat.card (uLocalGroup p n hn i)) := by
  let f : uLocalGroup p n hn i →* localGroup p n hn i :=
    { toFun := uLocalEmbedding p n hn i
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (localGroup_odd p n hn hp i).of_dvd_nat
    (Subgroup.card_dvd_of_injective f (uLocalEmbedding p n hn i).injective)

theorem u_homology_isZero_of_opposition (hn : 2 ≤ n) (hp : Odd p)
    (hL : OppositionAcyclic p n (by omega)) (j : ℕ) (hj : 0 < j) (hjn : j < n-1) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (U p (n+1)) (ZMod 2)) j) := by
  classical
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  apply TypedCosetFaces.groupHomology_isZero_of_acyclic (uLocalGroup p n (by omega))
    (uLocalGroup_odd p n (by omega) hp) (n-2)
  · intro r hr
    exact hL.2 (r+1) (by omega) (by omega)
  · exact hL.1
  · omega

end CoboundaryExpanders.Construction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_ProStability
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive exactness, coefficient change, Bockstein groups, integral pro-stability support, and F2 reductions.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.Construction
open Elementary
variable (p n : ℕ) [Fact p.Prime]

theorem U_constantCoeff (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p))
    (hg : g ∈ U p (n+1)) (i j : Fin (n+1)) (hji : j ≤ i) :
    (g i j).constantCoeff = if i=j then 1 else 0 := by
  change IsUpperUnitriangular _ (evalZero p (n+1) g) at hg
  have h := hg i j hji
  change Polynomial.eval 0 (g i j) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod p)) i j at h
  change (g i j).coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa only [Matrix.one_apply] using h

theorem cycleGenerated_eq_U (hn : 2 ≤ n) :
    cycleGenerated p n (by omega) = U p (n+1) := by
  apply le_antisymm (cycleGenerated_le_U p n (by omega))
  intro g hg
  apply polynomial_iwahori_mem_of_roots (U p (n+1)) (cycleGenerated p n (by omega))
    (cycleGenerated_le_U p n (by omega)) (U_constantCoeff p n) _ g hg
  intro i j hij c hc
  by_cases hlt : i < j
  · exact upper_polynomial_mem_generated p n hn hlt c
  · have hjlt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
    have hzero := hc hjlt
    have hx : Polynomial.X ∣ c := Polynomial.X_dvd_iff.mpr (by simpa using hzero)
    obtain ⟨f,rfl⟩ := hx
    exact X_polynomial_mem_generated p n hn hij f

theorem infinite_locals_generate (hn : 2 ≤ n) :
    Subgroup.closure (⋃ i, (uLocalGroup p n (by omega) i : Set (U p (n+1)))) = ⊤ := by
  let K : Subgroup (U p (n+1)) :=
    Subgroup.closure (⋃ i, (uLocalGroup p n (by omega) i : Set (U p (n+1))))
  have hgen : cycleGenerated p n (by omega) ≤ K.map (U p (n+1)).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    obtain ⟨cut,hcut⟩ : ∃ cut : Fin (n+1), cut ≠ j := by
      by_cases hj : j=0
      · refine ⟨Fin.last n,?_⟩
        rw [hj]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last,Fin.val_zero] at this
        omega
      · exact ⟨0,fun h => hj h.symm⟩
    let u : U p (n+1) := ⟨cycleRoot p n (by omega) j,cycleRoot_mem_U p n (by omega) j⟩
    have hu : u ∈ uLocalGroup p n (by omega) cut :=
      Subgroup.subset_closure ⟨j,Ne.symm hcut,rfl⟩
    exact ⟨u,Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨cut,hu⟩),rfl⟩
  apply top_le_iff.mp
  intro u _
  have hu : u.val ∈ cycleGenerated p n (by omega) := by rw [cycleGenerated_eq_U p n hn]; exact u.property
  obtain ⟨v,hv,hvu⟩ := hgen hu
  have hvu' : v=u := Subtype.ext hvu
  exact hvu' ▸ hv

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

lemma boundary_pair (g : G) (i j : I) (hij : i ≠ j) :
    (complex H).boundary 1 (Finsupp.single (pairFace H g i j hij) 1) =
      Finsupp.single (singletonFace H g i) 1 + Finsupp.single (singletonFace H g j) 1 := by
  apply (complex H).embed_injective 1
  change ((complex H).embed 1).comp ((complex H).boundary 1) _ = _
  rw [(complex H).embed_boundary]
  simp only [LinearMap.comp_apply, CoboundaryExpanders.InfiniteChains.Complex.embed_single, map_add, rawBoundary_single]
  have hv : vertex H g i ≠ vertex H g j := fun h => hij (vertex_injective H g h)
  simp [pairFace,singletonFace,hv,Finset.erase_insert_of_ne,add_comm]

lemma component_same_chamber (g : G) (i j : I) : component H g i = component H g j := by
  by_cases hij : i = j
  · subst j; rfl
  have hh : component H g i + component H g j = 0 := by
    rw [component,component,← map_add,← boundary_pair H g i j hij]
    exact Submodule.Quotient.mk_eq_zero _ |>.mpr ⟨_,rfl⟩
  have hc : component H g j + component H g j = 0 := by
    have htwo : (1:k) + 1 = 0 := rfl
    calc
      _ = ((1:k)+1) • component H g j := by rw [add_smul,one_smul]
      _ = 0 := by rw [htwo,zero_smul]
  calc
    component H g i = (component H g i + component H g j) + component H g j := by rw [add_assoc,hc,add_zero]
    _ = component H g j := by rw [hh,zero_add]

lemma component_mul_local (g h : G) (i : I) (hh : h ∈ H i) :
    component H g i = component H (g*h) i := by
  have hv : vertex H g i = vertex H (g*h) i := by
    apply congrArg (Sigma.mk i)
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    simpa using hh
  unfold component
  congr 2
  apply Subtype.ext
  exact congrArg (fun v => ({v} : Finset (Vertex H))) hv

lemma component_mul_closure (h : G)
    (hh : h ∈ Subgroup.closure (⋃ i, (H i : Set G))) :
    ∀ g i j, component H g i = component H (g*h) j := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
    intro g i j
    exact (component_same_chamber H g i a).trans
      ((component_mul_local H g x a ha).trans (component_same_chamber H (g*x) a j))
  | one =>
    intro g i j
    simpa using component_same_chamber H g i j
  | mul a _ _ _ ia ib =>
    intro g i j
    exact (ia g i i).trans (by simpa [mul_assoc] using ib (g*a) i j)
  | inv a _ ia =>
    intro g i j
    simpa [mul_assoc] using (ia (g*a⁻¹) j i).symm

lemma component_constant (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤)
    (g h : G) (i j : I) : component H g i = component H h j := by
  have := component_mul_closure H (g⁻¹*h) (by rw [hgen]; trivial) g i j
  simpa using this

lemma singletonFace_surjective : Function.Surjective (fun gi : G × I => singletonFace H gi.1 gi.2) := by
  rintro ⟨s,⟨g,A,rfl⟩,hc⟩
  have hc' : A.card = 1 := by simpa using hc
  obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc'
  exact ⟨⟨g,i⟩,Subtype.ext (by simp [singletonFace,face])⟩

theorem augmentation_exact_of_generation [Nonempty I]
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) :
    Function.Exact ((complex H).boundary 1) ((complex H).sumCoefficients 1) := by
  let i : I := Classical.choice ‹Nonempty I›
  let π := (LinearMap.range ((complex H).boundary 1)).mkQ
  have hπ (c : (complex H).Chains 1) :
      π c = ((complex H).sumCoefficients 1 c) • component H 1 i := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add,hc,hd,add_smul]
    | single s r =>
      obtain ⟨⟨g,j⟩,rfl⟩ := singletonFace_surjective H s
      have hs : Finsupp.single (singletonFace H g j) r = r • Finsupp.single (singletonFace H g j) 1 := by simp
      rw [hs,map_smul]
      change r • component H g j = _
      rw [component_constant H hgen g 1 j i]
      simp
  intro c
  constructor
  · intro hc
    have hz : π c = 0 := by rw [hπ,hc,zero_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (complex H).augmentation_boundary b

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
variable (p n : ℕ) [Fact p.Prime]

theorem infinite_augmentation_exact (hn : 2 ≤ n) :
    Function.Exact ((infiniteCosetComplex p n (by omega)).boundary 1)
      ((infiniteCosetComplex p n (by omega)).sumCoefficients 1) :=
  TypedCosetFaces.augmentation_exact_of_generation _ (infinite_locals_generate p n hn)

theorem oppositionAcyclic_iff_positive (hn : 2 ≤ n) :
    OppositionAcyclic p n (by omega) ↔
      ∀ j : ℕ, 0 < j → j < n-1 →
        (infiniteCosetComplex p n (by omega)).chainComplex.ExactAt j := by
  exact ⟨And.right, fun h => ⟨infinite_augmentation_exact p n hn,h⟩⟩

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.ProCoefficientChange

attribute [instance] Tower.ab Tower.mod

end CoboundaryExpanders.ProCoefficientChange

namespace CoboundaryExpanders.GroupProStability
open ProCoefficientChange
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] ModuleCat.isModule

attribute [instance] Groups.grp

end CoboundaryExpanders.GroupProStability

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_OddHomology
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Permutation orbit parameters, locally finite odd groups, quotient coinvariants, and bar augmentations.
-/

namespace CoboundaryExpanders.FinsuppPermutation
open CategoryTheory

variable {k G X Y : Type} [CommRing k] [Group G] [MulAction G X]

namespace OrbitParam
variable (P : OrbitParam G X Y)

lemma H0_naturality {X' Y' : Type} [MulAction G X'] (Q : OrbitParam G X' Y')
    (d : rep k G X ⟶ rep k G X') (e : (Y →₀ k) →ₗ[k] (Y' →₀ k))
    (he : (Finsupp.lmapDomain k k Q.f).comp d.hom.toLinearMap =
      e.comp (Finsupp.lmapDomain k k P.f)) (x : groupHomology (rep k G X) 0) :
    Q.H0Equiv ((groupHomology.functor k G 0).map d x) = e (P.H0Equiv x) := by
  have hc : Q.coinEquiv.toLinearMap.comp
      (Representation.Coinvariants.map _ _ d.hom) = e.comp P.coinEquiv.toLinearMap := by
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro c
    change Q.coinEquiv (Representation.Coinvariants.mk (ρ k G X') (d.hom c)) =
      e (P.coinEquiv (Representation.Coinvariants.mk (ρ k G X) c))
    rw [coinEquiv_mk,coinEquiv_mk]
    exact LinearMap.congr_fun he c
  have hn := congrArg (fun z => z x) (groupHomology.map_id_comp_H0Iso_hom d)
  change (groupHomology.H0Iso (rep k G X')).hom
      ((groupHomology.functor k G 0).map d x) =
    (Rep.coinvariantsFunctor k G).map d ((groupHomology.H0Iso (rep k G X)).hom x) at hn
  change Q.coinEquiv ((groupHomology.H0Iso (rep k G X')).hom _) = _
  rw [hn]
  exact LinearMap.congr_fun hc ((groupHomology.H0Iso (rep k G X)).hom x)
end OrbitParam
end CoboundaryExpanders.FinsuppPermutation


section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains.Complex
variable {V W : Type} [DecidableEq V] [DecidableEq W]

namespace Reduction
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (r : Reduction X Y)

lemma image_erase (s : Finset V) (hs : s ∈ X.faces) (v : V) (hv : v ∈ s) :
    (s.erase v).image r.f = (s.image r.f).erase (r.f v) := by
  ext w
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨u,⟨huv,hu⟩,rfl⟩
    exact ⟨fun h => huv (r.injOn s hs hu hv h),u,hu,rfl⟩
  · rintro ⟨hw, u,hu,rfl⟩
    exact ⟨u,⟨fun h => hw (congrArg r.f h),hu⟩,rfl⟩

lemma raw_boundary (s : Finset V) (hs : s ∈ X.faces) (a : k) :
    Finsupp.lmapDomain k k (fun t : Finset V => t.image r.f)
      (rawBoundary (Finsupp.single s a)) =
    rawBoundary (Finsupp.single (s.image r.f) a) := by
  simp only [rawBoundary_single, map_sum, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  rw [Finset.sum_image (r.injOn s hs)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [r.image_erase s hs v hv]

omit [DecidableEq V] in
lemma embed_chains (n : ℕ) :
    (Y.embed n).comp (r.chains n) =
      (Finsupp.lmapDomain k k (fun t : Finset V => t.image r.f)).comp (X.embed n) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply,Finsupp.lsingle_apply,chains_single,embed_single,
    Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  rfl

lemma boundary (n : ℕ) :
    (r.chains n).comp (X.boundary n) = (Y.boundary n).comp (r.chains (n+1)) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  apply Y.embed_injective n
  change (Y.embed n).comp (r.chains n) (X.boundary n (Finsupp.single s a)) =
    (Y.embed n).comp (Y.boundary n) (r.chains (n+1) (Finsupp.single s a))
  rw [embed_chains,embed_boundary]
  change Finsupp.lmapDomain k k (fun t : Finset V => t.image r.f)
    ((X.embed n).comp (X.boundary n) (Finsupp.single s a)) =
    rawBoundary ((Y.embed (n+1)).comp (r.chains (n+1)) (Finsupp.single s a))
  rw [embed_boundary,embed_chains]
  simp only [LinearMap.comp_apply,embed_single,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  exact r.raw_boundary s.val s.property.1 a

end Reduction
end CoboundaryExpanders.InfiniteChains.Complex

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

end

section
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation

namespace CoboundaryExpanders.QuotientCoinvariants

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

lemma totalCoinvariantsIso_double_mk (X : Rep (ZMod 2) G) (x : X) :
    ((totalCoinvariantsIso N).hom.app X).hom
      (Coinvariants.mk (((L N).obj X).ρ) (Coinvariants.mk (X.ρ.comp N.subtype) x)) =
      Coinvariants.mk X.ρ x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (totalAdjunction N) (Rep.coinvariantsAdjunction (ZMod 2) G) X
  exact LinearMap.congr_fun (congrArg (fun f => f.hom.toLinearMap) h) x

end CoboundaryExpanders.QuotientCoinvariants

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory

end

section
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory

namespace CoboundaryExpanders.QuotientCoinvariants
open Representation
variable {G : Type} [Group G] [DecidableEq G] (N : Subgroup G) [N.Normal] [DecidableEq (G ⧸ N)]

omit [DecidableEq G] [DecidableEq (G ⧸ N)] in
lemma totalCoinvariantsIso_inv_mk (X : Rep.{0} (ZMod 2) G) (x : X) :
    ((totalCoinvariantsIso N).inv.app X).hom (Coinvariants.mk X.ρ x) =
      Coinvariants.mk (((L N).obj X).ρ) (Coinvariants.mk (X.ρ.comp N.subtype) x) := by
  apply ((ModuleCat.mono_iff_injective ((totalCoinvariantsIso N).hom.app X)).mp inferInstance)
  exact (ConcreteCategory.congr_hom ((totalCoinvariantsIso N).inv_hom_id_app X) _).trans
    (totalCoinvariantsIso_double_mk N X x).symm

theorem quotient_chain_factorization :
    (QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G)).hom ≫ coinvariantQuotient N =
      groupHomology.chainsMap (QuotientGroup.mk' N) (trivialQuotient N) ≫
        (QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G ⧸ N)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x r
  change Coinvariants.map _ _ (homFrom N (quotientBarF N n)).hom
    (((totalCoinvariantsIso N).inv.app (Rep.free (ZMod 2) G (Fin n → G))).hom
      ((QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G)).hom.f n (single x r))) =
    (QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G ⧸ N)).hom.f n
      ((groupHomology.chainsMap (QuotientGroup.mk' N) (trivialQuotient N)).f n (single x r))
  rw [QuotientCoinvariantModel.chainsIso_hom_single,totalCoinvariantsIso_inv_mk]
  change Coinvariants.mk (Representation.free (ZMod 2) (G ⧸ N) (Fin n → G ⧸ N))
    ((quotientBarF N n).hom (single x (.single 1 r))) = _
  rw [groupHomology.chainsMap_f_single,QuotientCoinvariantModel.chainsIso_hom_single]
  rw [quotientBarF_single]
  rfl

variable (H : ∀ s : Finset N, ∃ S : Subgroup N, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)

include H in
theorem quotient_map_isIso (j : ℕ) :
    IsIso (groupHomology.map (QuotientGroup.mk' N) (trivialQuotient N) j) := by
  have hf := congrArg (fun f => HomologicalComplex.homologyMap f j) (quotient_chain_factorization N)
  simp only [HomologicalComplex.homologyMap_comp] at hf
  have he : IsIso (HomologicalComplex.homologyMap (coinvariantQuotient N) j) := by
    change IsIso (HomologicalComplex.homologyMap (coinvariantQuotientEquiv N H).hom j)
    refine ⟨⟨HomologicalComplex.homologyMap (coinvariantQuotientEquiv N H).inv j, ?_, ?_⟩⟩
    · rw [← HomologicalComplex.homologyMap_comp,
        (coinvariantQuotientEquiv N H).homotopyHomInvId.homologyMap_eq j,
        HomologicalComplex.homologyMap_id]
    · rw [← HomologicalComplex.homologyMap_comp,
        (coinvariantQuotientEquiv N H).homotopyInvHomId.homologyMap_eq j,
        HomologicalComplex.homologyMap_id]
  have hi : IsIso (HomologicalComplex.homologyMap
      ((QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G)).hom) j ≫
        HomologicalComplex.homologyMap (coinvariantQuotient N) j) := inferInstance
  rw [hf] at hi
  change IsIso (HomologicalComplex.homologyMap
    (groupHomology.chainsMap (QuotientGroup.mk' N) (trivialQuotient N)) j)
  have hQ : IsIso (HomologicalComplex.homologyMap
      ((QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G ⧸ N)).hom) j) := inferInstance
  exact IsIso.of_isIso_comp_right _ (HomologicalComplex.homologyMap
    ((QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G ⧸ N)).hom) j)

end CoboundaryExpanders.QuotientCoinvariants

end

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory
open CategoryTheory

namespace CoboundaryExpanders.QuotientCoinvariants

section
variable {G K : Type} [Group G] [Group K]

theorem surjection_map_isIso (f : G →* K) (hf : Function.Surjective f)
    (H : ∀ s : Finset f.ker, ∃ S : Subgroup f.ker,
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S) (j : ℕ) :
    IsIso (groupHomology.map f (trivialMap f) j) := by
  classical
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hq : IsIso (groupHomology.map (QuotientGroup.mk' f.ker) (trivialQuotient f.ker) j) :=
    quotient_map_isIso f.ker H j
  have he : IsIso (groupHomology.map e.toMonoidHom (trivialMap e.toMonoidHom) j) := by
    let E := groupHomology.mapIso
      (A := Rep.trivial (ZMod 2) (G ⧸ f.ker) (ZMod 2))
      (B := Rep.trivial (ZMod 2) K (ZMod 2))
      e (LinearEquiv.refl (ZMod 2) (ZMod 2)) (fun _ => rfl) j
    have ht : groupHomology.map e.toMonoidHom (trivialMap e.toMonoidHom) j = E.hom :=
      groupHomology.map_congr rfl rfl j
    rw [ht]
    infer_instance
  have hfactor : groupHomology.map f (trivialMap f) j =
      groupHomology.map (QuotientGroup.mk' f.ker) (trivialQuotient f.ker) j ≫
        groupHomology.map e.toMonoidHom (trivialMap e.toMonoidHom) j := by
    rw [← groupHomology.map_comp]
    apply groupHomology.map_congr
    · ext g
      rfl
    · rfl
  rw [hfactor]
  infer_instance

end

end CoboundaryExpanders.QuotientCoinvariants

namespace CoboundaryExpanders.LocallyFiniteOdd

theorem vector_group_local_odd (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] :
    ∀ s : Finset (Multiplicative V), ∃ S : Subgroup (Multiplicative V),
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S := by
  classical
  intro s
  let t : Finset V := s.image Multiplicative.toAdd
  let W : Submodule (ZMod p) V := Submodule.span (ZMod p) (t : Set V)
  let S : Subgroup (Multiplicative V) :=
    { carrier := {g | Multiplicative.toAdd g ∈ W}
      one_mem' := W.zero_mem
      mul_mem' := fun ha hb => W.add_mem ha hb
      inv_mem' := fun ha => W.neg_mem ha }
  let e : S ≃ W :=
    { toFun := fun x => ⟨Multiplicative.toAdd x.val,x.property⟩
      invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : FiniteDimensional (ZMod p) W := FiniteDimensional.span_finset (ZMod p) t
  have hc : Nat.card W = p ^ Module.finrank (ZMod p) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_eq_fintype_card,ZMod.card]
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  refine ⟨S,Finite.of_equiv W e.symm,?_,?_⟩
  · rw [Nat.card_congr e,hc]
    exact hp.pow
  · intro g hg
    change Multiplicative.toAdd g ∈ W
    apply Submodule.subset_span
    change Multiplicative.toAdd g ∈ t
    exact Finset.mem_image.mpr ⟨g,hg,rfl⟩

end CoboundaryExpanders.LocallyFiniteOdd

namespace CoboundaryExpanders.QuotientCoinvariants

variable {G K : Type} [Group G] [Group K]

theorem localOdd_of_injective (f : G →* K) (hf : Function.Injective f)
    (H : ∀ s : Finset K, ∃ S : Subgroup K,
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S) :
    ∀ s : Finset G, ∃ S : Subgroup G,
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S := by
  classical
  intro s
  obtain ⟨S,hfin,hodd,hS⟩ := H (s.image f)
  have := hfin
  let T := S.comap f
  let g : T →* S :=
    { toFun := fun x => ⟨f x.val,x.property⟩
      map_one' := by apply Subtype.ext; exact f.map_one
      map_mul' x y := by apply Subtype.ext; exact f.map_mul x.val y.val }
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hxy
  refine ⟨T,Finite.of_injective g hg,?_,?_⟩
  · exact hodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)
  · intro x hx
    exact hS (f x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

end CoboundaryExpanders.QuotientCoinvariants

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Parabolic
attribute [-instance] _root_.OAI.CoboundaryExpanders.CongruenceFrames.invariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Actual parabolic stabilizers, F2 homological stability maps, and matrix duality.
-/

namespace CoboundaryExpanders.ActualParabolic
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory
open CategoryTheory
open scoped BigOperators Matrix


section
open Construction
variable (p a m : ℕ)

theorem project_surjective : Function.Surjective (project p a m) := by
  intro A
  exact ⟨sectionValue p a m A,by apply Subtype.ext; apply Subtype.ext; rfl⟩

theorem kernelColumn_injective : Function.Injective (kernelColumn p a m) := by
  intro A B h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [kernel_form p a m A,kernel_form p a m B]
  apply congrArg (fun v : Matrix (Fin a) Unit (R p) => Matrix.fromBlocks 1 v 0 1)
  funext i u
  cases u
  exact congrFun (congrArg Multiplicative.toAdd h) i

theorem project_homology_isIso [Fact p.Prime] (hp : Odd p) (j : ℕ) :
    CategoryTheory.IsIso (groupHomology.map (project p a m)
      (QuotientCoinvariants.trivialMap _) j) := by
  apply QuotientCoinvariants.surjection_map_isIso _ (project_surjective p a m)
  exact QuotientCoinvariants.localOdd_of_injective (kernelColumn p a m)
    (kernelColumn_injective p a m)
    (LocallyFiniteOdd.vector_group_local_odd p hp (Fin a → R p))

end

section
open Construction
variable (p a m : ℕ)

theorem inclusion_comp_section : (inclusion p a m).comp (sectionHom p a m) =
    Blocks.gammaStabilization p a 1 m := by
  apply MonoidHom.ext
  intro A
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  change Matrix.fromBlocks A.val.val 0 0 (1 : Matrix Unit Unit (R p))
      ((idxEquiv a).symm i) ((idxEquiv a).symm j) =
    Matrix.fromBlocks A.val.val 0 0 (1 : Matrix (Fin 1) (Fin 1) (R p))
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin 1 ≃ Fin (a+1)).surjective i
  obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin 1 ≃ Fin (a+1)).surjective j
  cases i <;> cases j <;> simp [idxEquiv,Matrix.one_apply]
  intro h
  exact (h (Subsingleton.elim _ _)).elim

end

open Construction CategoryTheory

end CoboundaryExpanders.ActualParabolic


section
open CategoryTheory
open scoped Matrix

namespace CoboundaryExpanders.F2Stability

variable {G H K : Type} [Group G] [Group H] [Group K]

lemma hom_comp (f : G →* H) (g : H →* K) (j : ℕ) :
    hom (g.comp f) j = hom f j ≫ hom g j := by
  rw [← groupHomology.map_comp]
  rfl

lemma hom_id (j : ℕ) : hom (MonoidHom.id G) j = 𝟙 _ :=
  groupHomology.map_id j

lemma endomorphism_hom_eq_id (π : G →* H) (α : G →* G)
    (hπ : π.comp α = π) (j : ℕ) [Mono (hom π j)] :
    hom α j = 𝟙 _ := by
  apply (cancel_mono (hom π j)).mp
  rw [Category.id_comp, ← hom_comp, hπ]

end CoboundaryExpanders.F2Stability

namespace CoboundaryExpanders.ActualParabolic
open Construction F2Stability
variable (p a m : ℕ)

lemma shear_inv (v : Matrix (Fin a) Unit (R p)) :
    (shear p a v)⁻¹ = shear p a (-v) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change Matrix.fromBlocks 1 v 0 1 * Matrix.fromBlocks 1 (-v) 0 1 = 1
  rw [Matrix.fromBlocks_multiply]
  simp

lemma project_comp_shearConj (v : Matrix (Fin a) Unit (R p)) :
    (project p a m).comp (shearConj p a m v) = project p a m := by
  apply MonoidHom.ext
  intro A
  apply Subtype.ext
  apply Subtype.ext
  change Matrix.toBlocks₁₁
    ((shear p a v).val * A.val.val * ((shear p a v)⁻¹).val) =
    Matrix.toBlocks₁₁ A.val.val
  rw [shear_inv, block_form p a m A]
  simp [shear, Matrix.fromBlocks_multiply]

theorem shearConj_homology_eq_id [Fact p.Prime] (hp : Odd p)
    (v : Matrix (Fin a) Unit (R p)) (j : ℕ) :
    hom (shearConj p a m v) j = 𝟙 _ := by
  have := project_homology_isIso p a m hp j
  exact endomorphism_hom_eq_id (project p a m) (shearConj p a m v)
    (project_comp_shearConj p a m v) j

attribute [local instance] OAI.CoboundaryExpanders.ActualParabolic.gammaNormal
lemma inclusion_comp_shearConj (v : Matrix (Fin a) Unit (R p)) :
    (inclusion p a m).comp (shearConj p a m v) =
      (MulAut.conjNormal (shearFin p a v) : MulAut (Gamma p (a+1) m)).toMonoidHom.comp
        (inclusion p a m) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change Blocks.reindexSL (idxEquiv a) ((shear p a v) * x.val * (shear p a v)⁻¹) =
    (Blocks.reindexSL (idxEquiv a) (shear p a v)) *
      (Blocks.reindexSL (idxEquiv a) x.val) *
      (Blocks.reindexSL (idxEquiv a) (shear p a v))⁻¹
  simp

theorem shearFin_fixes_stable_image [Fact p.Prime] (hp : Odd p)
    (v : Matrix (Fin a) Unit (R p)) (j : ℕ) :
    hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (MulAut.conjNormal (shearFin p a v) : MulAut (Gamma p (a+1) m)).toMonoidHom j =
    hom (Blocks.gammaStabilization p a 1 m) j := by
  rw [← inclusion_comp_section, F2Stability.hom_comp, Category.assoc, ← F2Stability.hom_comp,
    ← inclusion_comp_shearConj, F2Stability.hom_comp, shearConj_homology_eq_id p a m hp,
    Category.id_comp]

end CoboundaryExpanders.ActualParabolic

namespace CoboundaryExpanders.MatrixDual
variable {A B : Type*} [CommRing A] [CommRing B]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "SL" => Matrix.SpecialLinearGroup

lemma reindex_dual (e : ι ≃ κ) (x : SL ι A) :
    Blocks.reindexSL e (dual x) = dual (Blocks.reindexSL e x) := by
  simp only [dual_apply, ← map_inv]
  rfl

lemma block_dual (a b : ℕ) (x : SL (Fin a) A) :
    dual (Blocks.blockSL a b x) = Blocks.blockSL a b (dual x) := by
  change ((Blocks.blockSL a b x)⁻¹).transpose =
    Blocks.blockSL a b ((x⁻¹).transpose)
  rw [← map_inv]
  apply Subtype.ext
  change (Matrix.fromBlocks (x⁻¹).val 0 0 (1 : Matrix (Fin b) (Fin b) A)).transpose =
    Matrix.fromBlocks (x⁻¹).val.transpose 0 0 1
  rw [Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero, Matrix.transpose_one]

lemma stabilize_dual (a b : ℕ) (x : SL (Fin a) A) :
    dual (Blocks.stabilizeSL a b x) = Blocks.stabilizeSL a b (dual x) := by
  change dual (Blocks.reindexSL finSumFinEquiv (Blocks.blockSL a b x)) = _
  rw [← reindex_dual, block_dual]
  rfl

open Construction
variable (p a m : ℕ)

lemma gammaDual_stabilization (b : ℕ) :
    (gammaDual p (a+b) m).toMonoidHom.comp (Blocks.gammaStabilization p a b m) =
      (Blocks.gammaStabilization p a b m).comp (gammaDual p a m).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  exact Subtype.ext (stabilize_dual a b x.val)

end CoboundaryExpanders.MatrixDual

namespace CoboundaryExpanders.F2Stability
variable {G H : Type} [Group G] [Group H]

lemma hom_equiv_isIso (e : G ≃* H) (j : ℕ) : IsIso (hom e.toMonoidHom j) := by
  let i : groupHomology (Rep.trivial (ZMod 2) G (ZMod 2)) j ≅
      groupHomology (Rep.trivial (ZMod 2) H (ZMod 2)) j :=
    { hom := hom e.toMonoidHom j
      inv := hom e.symm.toMonoidHom j
      hom_inv_id := by
        rw [← hom_comp]
        have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext x; simp
        rw [he, hom_id]
      inv_hom_id := by
        rw [← hom_comp]
        have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by ext x; simp
        rw [he, hom_id] }
  exact i.isIso_hom

end CoboundaryExpanders.F2Stability

namespace CoboundaryExpanders.MatrixDual
open Construction F2Stability
variable (p a m : ℕ)

attribute [local instance] OAI.CoboundaryExpanders.MatrixDual.gammaNormal
lemma gammaDual_conj (g : Matrix.SpecialLinearGroup (Fin a) (R p)) :
    (gammaDual p a m).toMonoidHom.comp (MulAut.conjNormal g).toMonoidHom =
      (MulAut.conjNormal (dual g)).toMonoidHom.comp (gammaDual p a m).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change dual (g * x.val * g⁻¹) = dual g * dual x.val * (dual g)⁻¹
  simp

theorem dual_fixes_stable_image (g : Matrix.SpecialLinearGroup (Fin (a+1)) (R p)) (j : ℕ)
    (hg : hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (MulAut.conjNormal g : MulAut (Gamma p (a+1) m)).toMonoidHom j =
        hom (Blocks.gammaStabilization p a 1 m) j) :
    hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (MulAut.conjNormal (dual g) : MulAut (Gamma p (a+1) m)).toMonoidHom j =
        hom (Blocks.gammaStabilization p a 1 m) j := by
  have := hom_equiv_isIso (gammaDual p a m) j
  apply (cancel_epi (hom (gammaDual p a m).toMonoidHom j)).mp
  have hd : hom (gammaDual p a m).toMonoidHom j ≫
      hom (Blocks.gammaStabilization p a 1 m) j =
    hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (gammaDual p (a+1) m).toMonoidHom j := by
    rw [← F2Stability.hom_comp, ← F2Stability.hom_comp, gammaDual_stabilization]
  rw [← Category.assoc, hd, Category.assoc, ← F2Stability.hom_comp,
    ← gammaDual_conj, F2Stability.hom_comp, ← Category.assoc, hg]

end CoboundaryExpanders.MatrixDual

namespace CoboundaryExpanders.ActualParabolic
open Construction F2Stability
variable (p a m : ℕ)

attribute [local instance] OAI.CoboundaryExpanders.ActualParabolic.gammaNormalLast
theorem lowerShear_fixes_stable_image [Fact p.Prime] (hp : Odd p)
    (v : Matrix (Fin a) Unit (R p)) (j : ℕ) :
    hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (MulAut.conjNormal (MatrixDual.dual (shearFin p a v)) :
        MulAut (Gamma p (a+1) m)).toMonoidHom j =
    hom (Blocks.gammaStabilization p a 1 m) j :=
  MatrixDual.dual_fixes_stable_image p a m _ j
    (shearFin_fixes_stable_image p a m hp v j)

end CoboundaryExpanders.ActualParabolic

end

open CategoryTheory

namespace CoboundaryExpanders.ActualParabolic
open Construction Elementary F2Stability Actions
variable (p a m : ℕ)

lemma upperRoot_shear (i : Fin a) (c : R p) :
    E (show i.castSucc ≠ Fin.last a by exact Fin.castSucc_ne_last i) c =
      shearFin p a (fun j _ => if j = i then c else 0) := by
  apply Matrix.SpecialLinearGroup.ext
  intro x y
  obtain ⟨x,rfl⟩ := (idxEquiv a).surjective x
  obtain ⟨y,rfl⟩ := (idxEquiv a).surjective y
  change (Matrix.transvection i.castSucc (Fin.last a) c) _ _ =
    (Blocks.reindexSL (idxEquiv a) (shear p a (fun j _ => if j=i then c else 0))) _ _
  rw [Blocks.reindexSL_apply]
  cases x with
  | inl x => cases y with
    | inl y => simp [Matrix.transvection, Matrix.single, shear, Matrix.fromBlocks, Matrix.one_apply, (Fin.castSucc_ne_last _).symm]
    | inr y => cases y; simp [Matrix.transvection, Matrix.single, shear, Matrix.fromBlocks, eq_comm]
  | inr x => cases x; cases y with
    | inl y => simp [Matrix.transvection, Matrix.single, shear, Matrix.fromBlocks, (Fin.castSucc_ne_last _).symm]
    | inr y => cases y; simp [Matrix.transvection, Matrix.single, shear, Matrix.fromBlocks]

lemma dual_root {i j : Fin a} (hij : i ≠ j) (c : R p) :
    MatrixDual.dual (E hij c) = E hij.symm (-c) := by
  rw [MatrixDual.dual_apply, Matrix.SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (Matrix.transvection i j (-c)).transpose = Matrix.transvection j i (-c)
  simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_single]

attribute [local instance] OAI.CoboundaryExpanders.ActualParabolic.gammaNorm
lemma upper_root_mem [Fact p.Prime] (hp : Odd p) (i : Fin a) (c : R p) (j : ℕ) :
    E (Fin.castSucc_ne_last i) c ∈ stableFixed p a m j := by
  change hom (Blocks.gammaStabilization p a 1 m) j ≫
    hom (MulAut.conjNormal (E (Fin.castSucc_ne_last i) c)).toMonoidHom j = _
  rw [upperRoot_shear]
  exact shearFin_fixes_stable_image p a m hp _ j

lemma lower_root_mem [Fact p.Prime] (hp : Odd p) (i : Fin a) (c : R p) (j : ℕ) :
    E (Fin.castSucc_ne_last i).symm c ∈ stableFixed p a m j := by
  have ht := lowerShear_fixes_stable_image p a m hp (fun x _ => if x=i then -c else 0) j
  rw [← upperRoot_shear, dual_root, neg_neg] at ht
  exact ht

theorem polynomial_fixes_stable_image [Fact p.Prime] (hp : Odd p)
    (j : ℕ) (g : Matrix.SpecialLinearGroup (Fin (a+1)) (R p)) :
    hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (MulAut.conjNormal g : MulAut (Gamma p (a+1) m)).toMonoidHom j =
        hom (Blocks.gammaStabilization p a 1 m) j := by
  change g ∈ stableFixed p a m j
  apply polynomial_SL_mem_of_roots
  intro x y hxy c
  by_cases hx : x = Fin.last a
  · subst x
    obtain ⟨y,rfl⟩ := Fin.eq_castSucc_of_ne_last (Ne.symm hxy)
    exact lower_root_mem p a m hp y c j
  · by_cases hy : y = Fin.last a
    · subst y
      obtain ⟨x,rfl⟩ := Fin.eq_castSucc_of_ne_last hx
      exact upper_root_mem p a m hp x c j
    · obtain ⟨x,rfl⟩ := Fin.eq_castSucc_of_ne_last hx
      obtain ⟨y,rfl⟩ := Fin.eq_castSucc_of_ne_last hy
      simpa only [mul_one] using E_path_mem (stableFixed p a m j)
        (Fin.castSucc_ne_last x) (Fin.castSucc_ne_last y).symm hxy
        (upper_root_mem p a m hp x c j) (lower_root_mem p a m hp y 1 j)

end CoboundaryExpanders.ActualParabolic

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_CongruenceFrames
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Row-parabolic groups, row-frame actions, finite images, and congruence stabilizers.
-/

namespace CoboundaryExpanders.MultiParabolic
open scoped Matrix BigOperators

open Construction RowParabolic CategoryTheory
variable (p a b m : ℕ)

lemma project_surjective : Function.Surjective (project p a b m) := by
  intro A
  exact ⟨sectionValue p a b m A, by apply Subtype.ext; rfl⟩

lemma kernelBlock_injective : Function.Injective (kernelBlock p a b m) := by
  intro A B h
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  rw [kernel_form p a b m A, kernel_form p a b m B]
  exact congrArg (fun v : Matrix (Fin a) (Fin b) (R p) => Matrix.fromBlocks 1 v 0 1)
    (congrArg Multiplicative.toAdd h)

theorem project_homology_isIso [Fact p.Prime] (hp : Odd p) (j : ℕ) :
    IsIso (groupHomology.map (project p a b m)
      (QuotientCoinvariants.trivialMap _) j) := by
  apply QuotientCoinvariants.surjection_map_isIso _ (project_surjective p a b m)
  exact QuotientCoinvariants.localOdd_of_injective (kernelBlock p a b m)
    (kernelBlock_injective p a b m)
    (LocallyFiniteOdd.vector_group_local_odd p hp (Matrix (Fin a) (Fin b) (R p)))

lemma homology_isZero [Fact p.Prime] (hp : Odd p) (j : ℕ)
    (hz : CategoryTheory.Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j)) :
    CategoryTheory.Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (group p a b m) (ZMod 2)) j) := by
  have := project_homology_isIso p a b m hp j
  exact CategoryTheory.Limits.IsZero.of_mono
    (groupHomology.map (project p a b m) (QuotientCoinvariants.trivialMap _) j) hz
end CoboundaryExpanders.MultiParabolic


section
open scoped Matrix BigOperators CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CongruenceFrames
open Construction Unimodular InfiniteChains
variable (p n m : ℕ) [Fact p.Prime]

lemma target_exact (hm : 1 ≤ m) (b : ℕ) (hb : b < n) :
    Attachment.ExactIn (target p n m hm).faces b := by
  apply field_exact (ZMod p) (Fin n → Trunc p m) n (residueVector p n m hm) _ b hb
  intro v
  exact ⟨fun j => Ideal.Quotient.mk (powerIdeal p m) (Polynomial.C (v j)), by ext j; simp⟩

lemma source_exact (b : ℕ) (hb : b < n) : Attachment.ExactIn (source p n).faces b :=
  polynomial_exact (ZMod p) (Fin n → R p) n id Function.surjective_id b hb

end CoboundaryExpanders.CongruenceFrames

end

open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_HomologyEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Abstract augmented resolutions and bounded homology edge surjectivity.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.HomologyEdge

section
universe u
variable {k G : Type u} [CommRing k] [Group G]

namespace Bounded

variable {N : ℕ} (P : BoundedPieces (k := k) (G := G) N)

lemma delta_zero_of_mono (s : ℕ) (hs : s ≤ N) [Mono (Hmap (P.inc s) 0)] :
    groupHomology.δ (P.exact s hs) 1 0 rfl = 0 := by
  apply (groupHomology.mapShortComplex₁_exact (P.exact s hs) rfl).mono_g_iff.mp
  change Mono (Hmap (P.inc s) 0)
  infer_instance

theorem kernel_homology_isZero (e s : ℕ) (hN : s+e ≤ N)
    (hV : ∀ t ≤ e, IsZero (groupHomology (P.C (s+t)) (e+1-t)))
    (hb : Mono (Hmap (P.inc (s+e)) 0)) :
    IsZero (groupHomology (P.K s) (e+1)) := by
  induction e generalizing s with
  | zero =>
    have hs : s ≤ N := by omega
    have hv : IsZero (groupHomology (P.C s) 1) := by simpa using hV 0 (by omega)
    have : Mono (Hmap (P.inc s) 0) := by simpa using hb
    have := groupHomology.mono_δ_of_isZero (P.exact s hs) 0 hv
    exact IsZero.of_mono_eq_zero _ (delta_zero_of_mono P s hs)
  | succ e ih =>
    have hs : s ≤ N := by omega
    have hv : IsZero (groupHomology (P.C s) (e+2)) := by simpa using hV 0 (by omega)
    have := groupHomology.mono_δ_of_isZero (P.exact s hs) (e+1) hv
    apply IsZero.of_mono (groupHomology.δ (P.exact s hs) (e+2) (e+1) rfl)
    apply ih (s+1) (by omega)
    · intro t ht
      have hv' := hV (t+1) (by omega)
      have ha : s+(t+1) = s+1+t := by omega
      have hd : e+1+1-(t+1) = e+1-t := by omega
      rw [ha, hd] at hv'
      exact hv'
    · have ha : s+1+e = s+(e+1) := by omega
      rw [ha]
      exact hb

theorem epi_edge (q : ℕ) (hN : q ≤ N)
    (hV : ∀ t, 1 ≤ t → t ≤ q → IsZero (groupHomology (P.C t) (q+1-t)))
    (hb : Mono (Hmap (P.inc q) 0)) : Epi (Hmap (P.sur 0) (q+1)) := by
  apply (groupHomology.mapShortComplex₃_exact (P.exact 0 (by omega)) rfl).epi_f
  change groupHomology.δ (P.exact 0 (by omega)) (q+1) q rfl = 0
  cases q with
  | zero =>
    have := hb
    exact delta_zero_of_mono P 0 (by omega)
  | succ q =>
    apply IsZero.eq_zero_of_tgt
    apply kernel_homology_isZero P q 1 (by omega)
    · intro t ht
      have hv' := hV (1+t) (by omega) (by omega)
      have hd : q+1+1-(1+t) = q+1-t := by omega
      rw [hd] at hv'
      exact hv'
    · have ha : 1+q = q+1 := by omega
      rw [ha]
      exact hb

lemma mono_H0_inc (s : ℕ) (hN : s+1 ≤ N)
    (he : ∀ x : groupHomology (P.C (s+1)) 0,
      Hmap (P.sur (s+1) ≫ P.inc s) 0 x = 0 →
      ∃ y : groupHomology (P.C (s+2)) 0,
        Hmap (P.sur (s+2) ≫ P.inc (s+1)) 0 y = x) :
    Mono (Hmap (P.inc s) 0) := by
  have : Epi (P.sur (s+1)) := (P.exact (s+1) hN).epi_g
  have : Epi (Hmap (P.sur (s+1)) 0) := groupHomology.epi_map_0_of_epi _
  rw [ModuleCat.mono_iff_injective]
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y,hy⟩ := (ModuleCat.epi_iff_surjective (Hmap (P.sur (s+1)) 0)).mp inferInstance x
  have hz : Hmap (P.sur (s+1) ≫ P.inc s) 0 y = 0 := by
    simp only [Hmap, Functor.map_comp]
    change Hmap (P.inc s) 0 (Hmap (P.sur (s+1)) 0 y) = 0
    rw [hy]
    exact hx
  obtain ⟨z,hz⟩ := he y hz
  rw [← hy, ← hz]
  change (Hmap (P.sur (s+2) ≫ P.inc (s+1)) 0 ≫ Hmap (P.sur (s+1)) 0) z = 0
  simp only [Hmap, ← Functor.map_comp, Category.assoc, P.zero, comp_zero, Functor.map_zero]
  rfl

end Bounded
end

universe u
variable {k G : Type u} [CommRing k] [Group G]

namespace AugmentedData
variable (A : AugmentedData (k := k) (G := G))

lemma epi_edge (q : ℕ) (h0 : Epi (A.d 0))
    (he : ∀ s, s ≤ q → (ShortComplex.mk (A.d (s+1)) (A.d s) (A.square s)).Exact)
    (hV : ∀ t, 1 ≤ t → t ≤ q → IsZero (groupHomology (A.D (t+1)) (q+1-t)))
    (hq : ∀ x : groupHomology (A.D (q+2)) 0,
      Hmap (A.d (q+1)) 0 x = 0 → ∃ y : groupHomology (A.D (q+3)) 0,
        Hmap (A.d (q+2)) 0 y = x) : Epi (Hmap (A.d 0) (q+1)) := by
  let P := A.pieces (q+1) h0 (fun s hs => he s (by omega))
  have hmono : Mono (Bounded.Hmap (P.inc q) 0) := by
    apply Bounded.mono_H0_inc P q (by omega)
    change ∀ x : groupHomology (A.D (q+2)) 0,
      Hmap (A.sur (q+1) ≫ A.inc q) 0 x = 0 →
      ∃ y : groupHomology (A.D (q+3)) 0,
        Hmap (A.sur (q+2) ≫ A.inc (q+1)) 0 y = x
    simpa only [sur_inc] using hq
  exact Bounded.epi_edge P q (by omega) hV hmono
end AugmentedData
end CoboundaryExpanders.HomologyEdge

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_FrameHomology
attribute [-instance] _root_.OAI.CoboundaryExpanders.InfiniteChains.Complex.finiteFaceFintype _root_.OAI.CoboundaryExpanders.InfiniteChains.FiniteWeights.faceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Shapiro comparison, frame resolution homology, augmentation ranges, and triviality of conjugation.
-/

namespace CoboundaryExpanders.ActualShapiro
open CategoryTheory CategoryTheory.Limits Representation Rep Finsupp MonoidalCategory TensorProduct

variable {k G H : Type} [CommRing k] [Group G] [Group H]
variable [DecidableEq G] [DecidableEq H]

variable (S : Subgroup G)

variable (A : Rep k S)

lemma chain_factorization :
    (groupHomology.inhomogeneousChainsIso A).hom ≫ inducedChainMap S A =
      groupHomology.chainsMap S.subtype (indBase S A) ≫
        (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change Rep.coinvariantsTensorIndInv S.subtype A (Rep.free k G (Fin n → G))
    (((Rep.coinvariantsTensor k S).obj A).map (barF S.subtype n)
      (Rep.finsuppToCoinvariantsTensorFree A (Fin n → S) (single x a))) =
    Rep.finsuppToCoinvariantsTensorFree (Rep.ind S.subtype A) (Fin n → G)
      ((groupHomology.chainsMap S.subtype (indBase S A)).f n (single x a))
  rw [Rep.finsuppToCoinvariantsTensorFree_single, groupHomology.chainsMap_f_single,
    Rep.finsuppToCoinvariantsTensorFree_single]
  change Rep.coinvariantsTensorIndInv S.subtype A (Rep.free k G (Fin n → G))
    (Coinvariants.mk _ (a ⊗ₜ (barF S.subtype n).hom (single x (.single 1 1)))) = _
  rw [barF_single, map_one]
  exact Rep.coinvariantsTensorIndInv_mk_tmul_indMk (A := A) (B := Rep.free k G (Fin n → G)) S.subtype a
    (single (S.subtype ∘ x) (MonoidAlgebra.single (1 : G) (1 : k)))

theorem indBase_isIso (j : ℕ) : IsIso (groupHomology.map S.subtype (indBase S A) j) := by
  change IsIso (HomologicalComplex.homologyMap
    (groupHomology.chainsMap S.subtype (indBase S A)) j)
  have hf := congrArg (fun f => HomologicalComplex.homologyMap f j) (chain_factorization S A)
  simp only [HomologicalComplex.homologyMap_comp] at hf
  have he : IsIso (HomologicalComplex.homologyMap (inducedChainMap S A) j) := by
    change IsIso (HomologicalComplex.homologyMap (inducedChainEquiv S A).hom j)
    refine ⟨⟨HomologicalComplex.homologyMap (inducedChainEquiv S A).inv j, ?_, ?_⟩⟩
    · rw [← HomologicalComplex.homologyMap_comp,
        (inducedChainEquiv S A).homotopyHomInvId.homologyMap_eq j, HomologicalComplex.homologyMap_id]
    · rw [← HomologicalComplex.homologyMap_comp,
        (inducedChainEquiv S A).homotopyInvHomId.homologyMap_eq j, HomologicalComplex.homologyMap_id]
  have hi : IsIso (HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso A).hom j ≫
      HomologicalComplex.homologyMap (inducedChainMap S A) j) := inferInstance
  rw [hf] at hi
  exact IsIso.of_isIso_comp_right _
    (HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom j)

end CoboundaryExpanders.ActualShapiro


section
open CategoryTheory CategoryTheory.Limits Rep Representation Finsupp

namespace CoboundaryExpanders.CosetModules
variable {k G : Type} [Field k] [Group G] [DecidableEq G] (S : Subgroup G)

theorem base_isIso (j : ℕ) : IsIso (groupHomology.map S.subtype (base (k := k) S) j) := by
  have ht := groupHomology.map_comp (C := permutation (k := k) S) S.subtype (MonoidHom.id G)
    (ActualShapiro.indBase S (Rep.trivial k S k)) (indCosetIso (k := k) S).hom j
  have hc : ActualShapiro.indBase S (Rep.trivial k S k) ≫
      (resFunctor S.subtype).map (indCosetIso (k := k) S).hom = base S := indBase_comp_toCoset S
  change groupHomology.map S.subtype (ActualShapiro.indBase S (Rep.trivial k S k) ≫
    (resFunctor S.subtype).map (indCosetIso (k := k) S).hom) j = _ at ht
  rw [hc] at ht
  rw [ht]
  let f : groupHomology (Rep.trivial k S k) j ⟶
      (groupHomology.functor k G j).obj (Rep.ind S.subtype (Rep.trivial k S k)) :=
    groupHomology.map S.subtype (ActualShapiro.indBase S (Rep.trivial k S k)) j
  have : IsIso f := ActualShapiro.indBase_isIso S (Rep.trivial k S k) j
  change IsIso (f ≫ (groupHomology.functor k G j).map (indCosetIso (k := k) S).hom)
  infer_instance

end CoboundaryExpanders.CosetModules

open CategoryTheory CategoryTheory.Limits Rep Representation Finsupp
open scoped BigOperators
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CosetSums
variable {k G I : Type} [Field k] [Group G] (H : I → Subgroup G)

lemma inclusion_coeff (i : I) (f : CosetModules.permutation (k := k) (H i)) :
    (inclusion H i f).coeff = Finsupp.mapDomain (fun q => (⟨i,q⟩ : Basis H)) f.coeff := by
  have he : (MonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp (inclusion H i).hom.toLinearMap =
      (Finsupp.lmapDomain k k (fun q : G ⧸ H i => (⟨i,q⟩ : Basis H))).comp
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap := by
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro r
    change (inclusion H i (MonoidAlgebra.single q r)).coeff =
      Finsupp.mapDomain _ (Finsupp.single q r)
    rw [inclusion_single, Finsupp.mapDomain_single]
    rfl
  exact LinearMap.congr_fun he f

lemma sum_inclusion_projection (f : permutation (k := k) H) (F : Finset I)
    (hF : ∀ x ∈ f.coeff.support, x.1 ∈ F) :
    ∑ i ∈ F, inclusion H i (projection H i f) = f := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  have hi (i : I) : (inclusion H i (projection H i f)).coeff x =
      if h : x.1 = i then f.coeff x else 0 := by
    rw [inclusion_coeff]
    split_ifs with h
    · rcases x with ⟨j,q⟩
      dsimp at h
      subst j
      rw [Finsupp.mapDomain_apply
        (by intro left right equality; exact eq_of_heq (Sigma.mk.inj equality).2), projection_coeff]
    · apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨q,hq⟩
      exact h (congrArg Sigma.fst hq).symm
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, hi]
  by_cases hx : x.1 ∈ F
  · simp [hx]
  · have hz : f.coeff x = 0 := by
      by_contra hz
      exact hx (hF x (Finsupp.mem_support_iff.mpr hz))
    simp [hz]

open groupHomology

lemma chainsMap_eval {A B : Rep k G} (f : A ⟶ B) (n : ℕ)
    (c : (Fin n → G) →₀ A) (g : Fin n → G) :
    ((chainsMap (MonoidHom.id G) f).f n c) g = f.hom (c g) := by
  change (((chainsMap (MonoidHom.id G) f).f n).hom c) g = _
  rw [chainsMap_id_f_hom_eq_mapRange]
  rfl

theorem homology_generated (n : ℕ) (x : groupHomology (permutation (k := k) H) n) :
    ∃ F : Finset I, ∃ y : ∀ i, groupHomology (CosetModules.permutation (k := k) (H i)) n,
      ∑ i ∈ F, (groupHomology.functor k G n).map (inclusion H i) (y i) = x := by
  induction x using groupHomology_induction_on with | h c =>
    let cc := iCycles (permutation (k := k) H) n c
    let F : Finset I := cc.support.biUnion (fun g => (cc g).coeff.support.image Sigma.fst)
    have hF (g : Fin n → G) (z : Basis H) (hz : z ∈ (cc g).coeff.support) : z.1 ∈ F := by
      have hg : g ∈ cc.support := by
        rw [Finsupp.mem_support_iff]
        intro he
        simp [he] at hz
      exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
    have chain_eq : ∑ i ∈ F,
        (chainsMap (MonoidHom.id G) (inclusion (k := k) H i)).f n
          ((chainsMap (MonoidHom.id G) (projection (k := k) H i)).f n cc) = cc := by
      apply Finsupp.ext
      intro g
      simp only [Finsupp.finsetSum_apply]
      trans ∑ i ∈ F, inclusion H i (projection H i (cc g))
      · apply Finset.sum_congr rfl
        intro i hi
        exact (chainsMap_eval (inclusion H i) n _ g).trans
          (congrArg (fun z => inclusion H i z) (chainsMap_eval (projection H i) n cc g))
      · exact sum_inclusion_projection H (cc g) F (hF g)
    have cyc_eq : ∑ i ∈ F,
        cyclesMap (MonoidHom.id G) (inclusion (k := k) H i) n
          (cyclesMap (MonoidHom.id G) (projection (k := k) H i) n c) = c := by
      apply (ModuleCat.mono_iff_injective (iCycles (permutation (k := k) H) n)).mp inferInstance
      simp only [map_sum]
      have hn {A B : Rep k G} (f : A ⟶ B) (y : cycles A n) :
          iCycles B n (cyclesMap (MonoidHom.id G) f n y) =
            (chainsMap (MonoidHom.id G) f).f n (iCycles A n y) := by
        exact congrArg (fun z => z y) (HomologicalComplex.cyclesMap_i (chainsMap (MonoidHom.id G) f) n)
      simp only [hn]
      exact chain_eq
    refine ⟨F,fun i => (groupHomology.functor k G n).map (projection H i) (π _ n c),?_⟩
    have hn {A B : Rep k G} (f : A ⟶ B) (y : cycles A n) :
        (groupHomology.functor k G n).map f (π A n y) =
          π B n (cyclesMap (MonoidHom.id G) f n y) := by
      exact congrArg (fun z => z y) (π_map (MonoidHom.id G) f n)
    simp only [hn]
    exact (map_sum (π (permutation (k := k) H) n).hom _ F).symm.trans
      (congrArg (fun z => π (permutation (k := k) H) n z) cyc_eq)

theorem homology_isZero (n : ℕ)
    (hz : ∀ i, CategoryTheory.Limits.IsZero (groupHomology (Rep.trivial k (H i) k) n)) :
    CategoryTheory.Limits.IsZero (groupHomology (permutation (k := k) H) n) := by
  have hi (i : I) : CategoryTheory.Limits.IsZero
      (groupHomology (CosetModules.permutation (k := k) (H i)) n) := by
    have := CosetModules.base_isIso (k := k) (H i) n
    exact CategoryTheory.Limits.IsZero.of_epi
      (groupHomology.map (H i).subtype (CosetModules.base (H i)) n) (hz i)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices hh : ∀ x : groupHomology (permutation (k := k) H) n, x = 0 from
    ⟨fun x y => (hh x).trans (hh y).symm⟩
  intro x
  obtain ⟨F,y,rfl⟩ := homology_generated H n x
  apply Finset.sum_eq_zero
  intro i hiF
  have := (ModuleCat.isZero_iff_subsingleton).mp (hi i)
  have he : y i = 0 := Subsingleton.elim _ _
  rw [he]
  exact map_zero _

theorem map_range_le (n : ℕ) {A : Rep k G} (f : permutation (k := k) H ⟶ A)
    (P : Submodule k (groupHomology A n))
    (hP : ∀ i, ∀ y : groupHomology (Rep.trivial k (H i) k) n,
      groupHomology.map (H i).subtype
        (CosetModules.base (H i) ≫ (Rep.resFunctor (H i).subtype).map (inclusion H i ≫ f)) n y ∈ P)
    (x : groupHomology (permutation (k := k) H) n) :
    (groupHomology.functor k G n).map f x ∈ P := by
  obtain ⟨F,y,rfl⟩ := homology_generated H n x
  simp only [map_sum]
  apply Submodule.sum_mem
  intro i hiF
  have := CosetModules.base_isIso (k := k) (H i) n
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective
    (groupHomology.map (H i).subtype (CosetModules.base (H i)) n)).mp inferInstance (y i)
  have hc := groupHomology.map_comp (H i).subtype (MonoidHom.id G)
    (CosetModules.base (H i)) (inclusion H i ≫ f) n
  change groupHomology.map (H i).subtype
    (CosetModules.base (H i) ≫ (Rep.resFunctor (H i).subtype).map (inclusion H i ≫ f)) n =
    groupHomology.map (H i).subtype (CosetModules.base (H i)) n ≫
      (groupHomology.functor k G n).map (inclusion H i ≫ f) at hc
  have hp := hP i z
  rw [hc, CategoryTheory.Functor.map_comp] at hp
  change (groupHomology.functor k G n).map f
    ((groupHomology.functor k G n).map (inclusion H i)
      (groupHomology.map (H i).subtype (CosetModules.base (H i)) n z)) ∈ P at hp
  rw [hz] at hp
  exact hp

end CoboundaryExpanders.CosetSums

namespace CoboundaryExpanders.PermutationProjectivity
variable {k G X : Type} [Field k] [Group G] [MulAction G X]
theorem homology_isZero (n : ℕ)
    (hz : ∀ x : X, CategoryTheory.Limits.IsZero
      (groupHomology (Rep.trivial k (MulAction.stabilizer G x) k) n)) :
    CategoryTheory.Limits.IsZero (groupHomology (FinsuppPermutation.rep k G X) n) := by
  have hh := CosetSums.homology_isZero (k := k)
    (orbitStabilizer (G := G) (X := X)) n (fun q => hz q.out)
  exact hh.of_iso ((groupHomology.functor k G n).mapIso (chainsIso (k := k) (G := G) (X := X))).symm
end CoboundaryExpanders.PermutationProjectivity

end

section
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CongruenceFrames
open Construction Unimodular InfiniteChains RowFrames
variable (p n m : ℕ) [Fact p.Prime]

lemma stabilizer_homology_isZero (hm : 1 ≤ m) (hp : Odd p) {b : ℕ}
    (s : (source p n).Face b) (hb : b < n) (j : ℕ)
    (hz : IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (n-b) m) (ZMod 2)) j)) :
    IsZero (groupHomology (Rep.trivial (ZMod 2) (MulAction.stabilizer (Gamma p n m) s) (ZMod 2)) j) := by
  have hz' := MultiParabolic.homology_isZero p (n-b) b m hp j hz
  have := F2Stability.hom_equiv_isIso (stabilizerEquiv p n m hm s hb) j
  exact hz'.of_mono (F2Stability.hom (stabilizerEquiv p n m hm s hb).toMonoidHom j)

lemma chains_homology_isZero (hm : 1 ≤ m) (hp : Odd p) (b : ℕ) (hb : b < n) (j : ℕ)
    (hz : IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (n-b) m) (ZMod 2)) j)) :
    IsZero (groupHomology ((source p n).chainsRep (G := Gamma p n m) b) j) :=
  PermutationProjectivity.homology_isZero j (fun s =>
    stabilizer_homology_isZero p n m hm hp s hb j hz)
end CoboundaryExpanders.CongruenceFrames

end

section
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.MultiParabolic
open Construction F2Stability RowFrames
variable (p a b m : ℕ)

lemma project_section : (project p a b m).comp (sectionHom p a b m) = MonoidHom.id _ := by
  ext A; rfl

lemma section_homology_isIso [Fact p.Prime] (hp : Odd p) (j : ℕ) :
    IsIso (hom (sectionHom p a b m) j) := by
  have : IsIso (hom (project p a b m) j) := project_homology_isIso p a b m hp j
  have he : hom (sectionHom p a b m) j ≫ hom (project p a b m) j = 𝟙 _ := by
    rw [← F2Stability.hom_comp,project_section,F2Stability.hom_id]
  have : IsIso (hom (sectionHom p a b m) j ≫ hom (project p a b m) j) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right (hom (sectionHom p a b m) j) (hom (project p a b m) j)

lemma inclusion_section : (inclusion p a b m).comp (sectionHom p a b m) =
    Blocks.gammaStabilization p a b m := by
  ext A i j
  rfl

lemma inclusion_hom_range [Fact p.Prime] (hp : Odd p) (j : ℕ)
    (y : groupHomology (Rep.trivial (ZMod 2) (group p a b m) (ZMod 2)) j) :
    ∃ x, hom (Blocks.gammaStabilization p a b m) j x = hom (inclusion p a b m) j y := by
  have := section_homology_isIso p a b m hp j
  obtain ⟨x,hx⟩ := (ModuleCat.epi_iff_surjective (hom (sectionHom p a b m) j)).mp inferInstance y
  refine ⟨x,?_⟩
  rw [← inclusion_section,F2Stability.hom_comp]
  change hom (inclusion p a b m) j (hom (sectionHom p a b m) j x) = _
  rw [hx]
end CoboundaryExpanders.MultiParabolic

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CongruenceFrames
open Construction RowFrames F2Stability
variable (p a m : ℕ) [Fact p.Prime]

attribute [local instance] OAI.CoboundaryExpanders.CongruenceFrames.gammaNormal
lemma vertex_normalization_map (hm : 1 ≤ m) (s : (source p (a+1)).Face 1) (ha : 0 < a) :
    (MultiParabolic.inclusion p a 1 m).comp (stabilizerEquiv p (a+1) m hm s (by omega)).toMonoidHom =
    ((MulAut.conjNormal (vertexCompletion p a s ha) : MulAut (Gamma p (a+1) m)).toMonoidHom).comp
      (MulAction.stabilizer (Gamma p (a+1) m) s).subtype := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  change Blocks.reindexSL finSumFinEquiv
    (completion p (a+1) s (by omega) *
      (kernelReindex (Ideal.Quotient.mk (powerIdeal p m))
        (splitCoordinates (a+1) 1 (by omega)).symm g.val).val *
      (completion p (a+1) s (by omega))⁻¹) =
    vertexCompletion p a s ha * g.val.val * (vertexCompletion p a s ha)⁻¹
  have he : splitCoordinates (a+1) 1 (by omega) = (finSumFinEquiv : Fin a ⊕ Fin 1 ≃ Fin (a+1)) := by
    ext i; rfl
  rw [he,map_mul,map_mul,map_inv]
  change vertexCompletion p a s ha *
    (Blocks.reindexSL finSumFinEquiv (Blocks.reindexSL finSumFinEquiv.symm g.val.val)) * _ = _
  have hi : Blocks.reindexSL finSumFinEquiv (Blocks.reindexSL finSumFinEquiv.symm g.val.val) = g.val.val := by
    exact (Blocks.reindexSL finSumFinEquiv).apply_symm_apply g.val.val
  rw [hi]
  rfl

theorem vertex_image_stable (hm : 1 ≤ m) (hp : Odd p) (ha : 0 < a)
    (s : (source p (a+1)).Face 1) (j : ℕ)
    (y : groupHomology (Rep.trivial (ZMod 2) (MulAction.stabilizer (Gamma p (a+1) m) s) (ZMod 2)) j) :
    ∃ x, hom (Blocks.gammaStabilization p a 1 m) j x =
      hom (MulAction.stabilizer (Gamma p (a+1) m) s).subtype j y := by
  let E := stabilizerEquiv p (a+1) m hm s (by omega)
  obtain ⟨x,hx⟩ := MultiParabolic.inclusion_hom_range p a 1 m hp j (hom E.toMonoidHom j y)
  have hc := congrArg (fun f => hom f j) (vertex_normalization_map p a m hm s ha)
  rw [F2Stability.hom_comp,F2Stability.hom_comp] at hc
  have hy := congrArg (fun f => f y) hc
  change hom (MultiParabolic.inclusion p a 1 m) j (hom E.toMonoidHom j y) =
    hom (MulAut.conjNormal (vertexCompletion p a s ha) : MulAut (Gamma p (a+1) m)).toMonoidHom j
      (hom (MulAction.stabilizer (Gamma p (a+1) m) s).subtype j y) at hy
  refine ⟨x,?_⟩
  have hf := ActualParabolic.polynomial_fixes_stable_image p a m hp j (vertexCompletion p a s ha)
  have hfx := congrArg (fun f => f x) hf
  have := hom_equiv_isIso (MulAut.conjNormal (vertexCompletion p a s ha) : MulAut (Gamma p (a+1) m)) j
  apply (ModuleCat.mono_iff_injective
    (hom (MulAut.conjNormal (vertexCompletion p a s ha) : MulAut (Gamma p (a+1) m)).toMonoidHom j)).mp inferInstance
  exact hfx.trans (hx.trans hy)
end CoboundaryExpanders.CongruenceFrames

namespace CoboundaryExpanders.InfiniteChains.Complex
variable {V G : Type} [DecidableEq V] [Group G] [MulAction G V]
    (X : CoboundaryExpanders.InfiniteChains.Complex V) [Fact (X.Invariant (G := G))]

lemma augmentation_exact_of_exactIn (he : Attachment.ExactIn X.faces 1) :
    Function.Exact (X.boundary 1) (X.sumCoefficients 1) := by
  intro c
  have hh := (Attachment.exactIn_iff_boundary_exact X 0).mp he c
  rw [← X.augmentation_boundary_zero]
  change X.sumCoefficients 0 (X.boundary 0 c) = 0 ↔ _
  rw [← map_zero (X.sumCoefficients 0), X.sumCoefficients_zero_injective.eq_iff]
  exact hh

lemma augmentedData_exact (s : ℕ) (he : Attachment.ExactIn X.faces (s+1)) :
    (ShortComplex.mk ((X.augmentedData (G := G)).d (s+1))
      (X.augmentedData.d s) (X.augmentedData.square s)).Exact := by
  cases s with
  | zero => exact X.augmentationRep_exact (X.augmentation_exact_of_exactIn he)
  | succ s =>
    apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k))).mp
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    exact fun c hc => ((Attachment.exactIn_iff_boundary_exact X (s+1)).mp he c).mp hc
end CoboundaryExpanders.InfiniteChains.Complex

namespace CoboundaryExpanders.Unimodular
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
lemma singleton_mem (v : M) (φ : M →ₗ[R] R) (hv : φ v = 1) :
    {v} ∈ (complex R (id : M → M)).faces := by
  refine ⟨LinearMap.pi (fun _ => φ), ?_⟩
  intro x
  ext y
  have hx : x.val = v := Finset.mem_singleton.mp x.property
  have hy : x = y := Subtype.ext (hx.trans (Finset.mem_singleton.mp y.property).symm)
  simp [hv, hy, Finset.mem_singleton.mp y.property]
end CoboundaryExpanders.Unimodular

namespace CoboundaryExpanders.CongruenceFrames
open Construction Unimodular InfiniteChains HomologyEdge
variable (p n m : ℕ) [Fact p.Prime]
lemma source_vertex (hn : 0 < n) : Nonempty ((source p n).Face 1) := by
  let i : Fin n := ⟨0,hn⟩
  let v : Fin n → R p := Pi.single i 1
  exact ⟨⟨{v}, singleton_mem v (LinearMap.proj i) (by simp [v]), by simp⟩⟩

lemma H0_boundary (hm : 1 ≤ m) (b : ℕ) (hb : b+1 < n)
    (x : groupHomology ((source p n).chainsRep (G := Gamma p n m) (b+1)) 0) :
    (orbitParam p n m hm b (by omega)).H0Equiv
      ((groupHomology.functor (ZMod 2) (Gamma p n m) 0).map ((source p n).boundaryRep b) x) =
    (target p n m hm).boundary b ((orbitParam p n m hm (b+1) hb).H0Equiv x) := by
  apply FinsuppPermutation.OrbitParam.H0_naturality
  exact (reduction p n m hm).boundary b

lemma H0_exact (hm : 1 ≤ m) (b : ℕ) (hb : b+2 < n)
    (x : groupHomology ((source p n).chainsRep (G := Gamma p n m) (b+1)) 0)
    (hx : (groupHomology.functor (ZMod 2) (Gamma p n m) 0).map ((source p n).boundaryRep b) x = 0) :
    ∃ y : groupHomology ((source p n).chainsRep (G := Gamma p n m) (b+2)) 0,
      (groupHomology.functor (ZMod 2) (Gamma p n m) 0).map ((source p n).boundaryRep (b+1)) y = x := by
  let E := (orbitParam p n m hm (b+1) (by omega)).H0Equiv (k := ZMod 2)
  have hz : (target p n m hm).boundary b (E x) = 0 := by
    rw [← H0_boundary p n m hm b (by omega) x,hx]
    exact (orbitParam p n m hm b (by omega)).H0Equiv.map_zero
  obtain ⟨c,hc⟩ := ((Attachment.exactIn_iff_boundary_exact (target p n m hm) b).mp
    (target_exact p n m hm (b+1) (by omega)) (E x)).mp hz
  let F := (orbitParam p n m hm (b+2) hb).H0Equiv (k := ZMod 2)
  refine ⟨F.symm c, E.injective ?_⟩
  change (orbitParam p n m hm (b+1) _).H0Equiv _ = E x
  rw [H0_boundary p n m hm (b+1) (by omega)]
  simpa only [F,LinearEquiv.apply_symm_apply] using hc

theorem augmentation_homology_epi (hm : 1 ≤ m) (hp : Odd p) (q : ℕ) (hn : 2*(q+1)+2 ≤ n)
    (hz : ∀ t, 1 ≤ t → t ≤ q →
      IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (n-(t+1)) m) (ZMod 2)) (q+1-t))) :
    Epi ((groupHomology.functor (ZMod 2) (Gamma p n m) (q+1)).map
      ((source p n).augmentationRep)) := by
  have := source_vertex p n (by omega)
  apply ((source p n).augmentedData (G := Gamma p n m)).epi_edge q
  · exact (source p n).augmentationRep_epi
  · intro s hs
    exact (source p n).augmentedData_exact s (source_exact p n (s+1) (by omega))
  · intro t ht htq
    exact chains_homology_isZero p n m hm hp (t+1) (by omega) (q+1-t) (hz t ht htq)
  · exact H0_exact p n m hm (q+1) (by omega)
end CoboundaryExpanders.CongruenceFrames

end

section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.PermutationProjectivity
variable {k G X : Type} [Field k] [Group G] [MulAction G X]
lemma chainsIso_single (x : CosetSums.Basis (orbitStabilizer (G := G) (X := X))) (r : k) :
    (chainsIso (k := k)).hom (MonoidAlgebra.single x r) = Finsupp.single (orbitBasis x) r := by
  change (Finsupp.domLCongr orbitBasis : _ ≃ₗ[k] _) (Finsupp.single x r) = _
  exact Finsupp.domLCongr_single _ _ _
end CoboundaryExpanders.PermutationProjectivity

namespace CoboundaryExpanders.InfiniteChains.Complex
open PermutationProjectivity F2Stability
variable {V G : Type} [Group G] [MulAction G V]
  (X : CoboundaryExpanders.InfiniteChains.Complex V) [Fact (X.Invariant (G := G))]

lemma orbitBase_augmentation (q : Orbit (G := G) (X := X.Face 1)) :
    CosetModules.base (orbitStabilizer q) ≫
      (Rep.resFunctor (orbitStabilizer q).subtype).map
        (CosetSums.inclusion orbitStabilizer q ≫ (chainsIso (k := ZMod 2)).hom ≫ X.augmentationRep) =
      QuotientCoinvariants.trivialMap (orbitStabilizer q).subtype := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro r
  change X.sumCoefficients 1 ((chainsIso (k := ZMod 2)).hom
    (CosetSums.inclusion orbitStabilizer q (MonoidAlgebra.single (QuotientGroup.mk (1 : G)) r))) = r
  rw [CosetSums.inclusion_single,chainsIso_single,X.sumCoefficients_single]

theorem augmentation_range_le (j : ℕ)
    (P : Submodule (ZMod 2) (groupHomology (Rep.trivial (ZMod 2) G (ZMod 2)) j))
    (hP : ∀ s : X.Face 1, ∀ y : groupHomology (Rep.trivial (ZMod 2)
      (MulAction.stabilizer G s) (ZMod 2)) j,
      hom (MulAction.stabilizer G s).subtype j y ∈ P)
    (x : groupHomology (X.chainsRep (G := G) 1) j) :
    (groupHomology.functor (ZMod 2) G j).map X.augmentationRep x ∈ P := by
  let E := (groupHomology.functor (ZMod 2) G j).mapIso (chainsIso (k := ZMod 2) (G := G) (X := X.Face 1))
  have h := CosetSums.map_range_le (k := ZMod 2) (orbitStabilizer (G := G) (X := X.Face 1)) j
    ((chainsIso (k := ZMod 2)).hom ≫ X.augmentationRep) P (fun q y => ?_) (E.inv x)
  · rw [CategoryTheory.Functor.map_comp] at h
    change (groupHomology.functor (ZMod 2) G j).map X.augmentationRep (E.hom (E.inv x)) ∈ P at h
    have he : E.hom (E.inv x) = x := E.toLinearEquiv.apply_symm_apply x
    rwa [he] at h
  · rw [orbitBase_augmentation]
    exact hP q.out y
end CoboundaryExpanders.InfiniteChains.Complex

end

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CongruenceFrames
open Construction RowFrames F2Stability
variable (p a m : ℕ) [Fact p.Prime]
attribute [local instance] gammaNormal

theorem stabilization_surjective (hm : 1 ≤ m) (hp : Odd p) (q : ℕ) (hn : 2*(q+1)+2 ≤ a+1)
    (hz : ∀ t, 1 ≤ t → t ≤ q →
      IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (a+1-(t+1)) m) (ZMod 2)) (q+1-t))) :
    Function.Surjective (hom (Blocks.gammaStabilization p a 1 m) (q+1)) := by
  have : Epi ((groupHomology.functor (ZMod 2) (Gamma p (a+1) m) (q+1)).map
    ((source p (a+1)).augmentationRep)) := augmentation_homology_epi p (a+1) m hm hp q hn hz
  intro y
  obtain ⟨x,rfl⟩ := (ModuleCat.epi_iff_surjective ((groupHomology.functor (ZMod 2)
    (Gamma p (a+1) m) (q+1)).map ((source p (a+1)).augmentationRep))).mp inferInstance y
  exact (source p (a+1)).augmentation_range_le (q+1)
    (LinearMap.range (hom (Blocks.gammaStabilization p a 1 m) (q+1)).hom)
    (fun s z => vertex_image_stable p a m hm hp (by omega) s (q+1) z) x

theorem conjugation_trivial (hm : 1 ≤ m) (hp : Odd p) (q : ℕ) (hn : 2*(q+1)+2 ≤ a+1)
    (hz : ∀ t, 1 ≤ t → t ≤ q →
      IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (a+1-(t+1)) m) (ZMod 2)) (q+1-t)))
    (g : Matrix.SpecialLinearGroup (Fin (a+1)) (R p)) :
    hom (MulAut.conjNormal g : MulAut (Gamma p (a+1) m)).toMonoidHom (q+1) = 𝟙 _ := by
  have : Epi (hom (Blocks.gammaStabilization p a 1 m) (q+1)) :=
    (ModuleCat.epi_iff_surjective _).mpr (stabilization_surjective p a m hm hp q hn hz)
  apply (cancel_epi (hom (Blocks.gammaStabilization p a 1 m) (q+1))).mp
  rw [Category.comp_id]
  exact ActualParabolic.polynomial_fixes_stable_image p a m hp (q+1) g
end CoboundaryExpanders.CongruenceFrames

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform congruence homology vanishing and the complete bounded-degree coboundary-expander theorem.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders
open Construction

/-- A single prime threshold supplies all the finitely many ambient U-ranks
needed in an inductive homology argument. -/
theorem uniform_u_homology (N : ℕ) :
    ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Odd p → Q < p →
      ∀ a : ℕ, 4 ≤ a → a ≤ N → ∀ j : ℕ, 0 < j → j < a-2 →
        IsZero (groupHomology (Rep.trivial (ZMod 2) (U p a) (ZMod 2)) j) := by
  induction N with
  | zero => exact ⟨0,fun _ _ _ _ a ha hN => by omega⟩
  | succ N ih =>
    by_cases hN : 4 ≤ N+1
    · obtain ⟨Q₁,hQ₁⟩ := ih
      obtain ⟨Q₂,hQ₂⟩ := uniform_infinite_coset_positive N (by omega)
      refine ⟨max Q₁ Q₂,?_⟩
      intro p inst hp hQ a ha haN j hj hja
      rcases lt_or_eq_of_le haN with hlt | rfl
      · exact hQ₁ p hp (lt_of_le_of_lt (le_max_left _ _) hQ) a ha (by omega) j hj hja
      · apply u_homology_isZero_of_opposition p N (by omega) hp
          ((oppositionAcyclic_iff_positive p N (by omega)).mpr
            (hQ₂ p (lt_of_le_of_lt (le_max_right _ _) hQ))) j hj
        omega
    · exact ⟨0,fun _ _ _ _ a ha haN => by omega⟩

/-- The actual congruence-group vanishing follows by induction on homological
degree, using the ordinary partial-basis edge argument and odd-index transfer.
This does not assume integral pro-stability or a stability theorem. -/
theorem gamma_vanishing_of_u (p N : ℕ) [Fact p.Prime] (hp : Odd p)
    (hU : ∀ a : ℕ, 4 ≤ a → a ≤ N → ∀ j : ℕ, 0 < j → j < a-2 →
      IsZero (groupHomology (Rep.trivial (ZMod 2) (U p a) (ZMod 2)) j)) :
    ∀ j : ℕ, 0 < j → ∀ a : ℕ, 2*j+2 ≤ a → a ≤ N →
      ∀ m : ℕ, 1 ≤ m →
        IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj a ha haN m hm
    obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    apply QuotientVanishing.gamma_isZero_of_U_and_action p (a+1) m Fact.out hp hm (q+1)
    · exact hU (a+1) (by omega) haN (q+1) (by omega) (by omega)
    · intro g
      exact CongruenceFrames.conjugation_trivial p a m hm hp q ha (by
        intro t ht htq
        exact ih (q+1-t) (by omega) (by omega) (a+1-(t+1)) (by omega) (by omega) m hm) g

/-- Consequently, for sufficiently large odd primes the literal congruence
homology vanishes simultaneously in the finite rank window required by d. -/
theorem uniform_gamma_vanishing_oai (N : ℕ) :
    ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Odd p → Q < p →
      ∀ j : ℕ, 0 < j → ∀ a : ℕ, 2*j+2 ≤ a → a ≤ N →
        ∀ m : ℕ, 1 ≤ m →
          IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j) := by
  obtain ⟨Q,hQ⟩ := uniform_u_homology N
  exact ⟨Q,fun p _ hp hQp => gamma_vanishing_of_u p N hp (hQ p hp hQp)⟩

end CoboundaryExpanders

end

end OAI
end

theorem solution : type_of% @OAI.CoboundaryExpanders.uniform_gamma_vanishing_oai := @OAI.CoboundaryExpanders.uniform_gamma_vanishing_oai
