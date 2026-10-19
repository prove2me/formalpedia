-- Prove2me | solution 1 for OAI.LinearListHadwiger.Sampling.source_thinning_failure_structure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:48:18.737023+00:00
-- url     : https://prove2.me/submissions/149cf612-28de-4aa4-940a-a538b2a7dcaa

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000

section
-- module Solutions.OAIQW_ListHadwiger.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

theorem choosable_card {V : Type} [Fintype V] (G : SimpleGraph V) :
    Choosable G (Fintype.card V) := by
  classical
  intro Color L hL
  have hall : ∀ s : Finset V, s.card ≤ (s.biUnion L).card := by
    intro s
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    obtain ⟨v, hv⟩ := hs
    exact (Finset.card_le_univ s).trans ((hL v).trans
      (Finset.card_le_card (Finset.subset_biUnion_of_mem L hv)))
  obtain ⟨c, hc, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective L).mp hall
  exact ⟨c, hmem, fun _ _ hvw heq => hvw.ne (hc heq)⟩

lemma exists_separator {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) {k : ℕ} (hord : k < S.card) (hn : ¬KConnectedOn G S k) :
    ∃ V₁ Z V₂, Z.card < k ∧ SeparatorSplit G S V₁ Z V₂ := by
  classical
  obtain ⟨Z, hZS, hZk, hZ⟩ : ∃ Z ⊆ S,
      Z.card < k ∧ ¬(G.induce (↑(S \ Z) : Set V)).Connected := by
    simpa only [KConnectedOn, not_and, hord, forall_const, not_forall,
      exists_prop, Classical.not_imp] using hn
  let T := S \ Z
  let H := G.induce (↑T : Set V)
  have hT : T.Nonempty := by
    have heq := Finset.card_sdiff_add_card_eq_card hZS
    exact Finset.card_pos.mp (by dsimp [T]; omega)
  have hnpre : ¬H.Preconnected := by
    intro h
    apply hZ
    obtain ⟨v, hv⟩ := hT
    exact { preconnected := h, nonempty := ⟨⟨v, hv⟩⟩ }
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬H.Reachable u v := by
    simpa only [SimpleGraph.Preconnected, not_forall] using hnpre
  let V₁ := T.filter (fun x => ∃ hx : x ∈ T, H.Reachable u ⟨x, hx⟩)
  let V₂ := T \ V₁
  have h₁T : V₁ ⊆ T := Finset.filter_subset _ _
  have h₂T : V₂ ⊆ T := Finset.sdiff_subset
  have hu : u.val ∈ V₁ := by
    exact Finset.mem_filter.mpr ⟨u.property, u.property, SimpleGraph.Reachable.rfl⟩
  have hv : v.val ∈ V₂ := by
    refine Finset.mem_sdiff.mpr ⟨v.property, ?_⟩
    intro h
    obtain ⟨_, hx, hr⟩ := Finset.mem_filter.mp h
    exact huv hr
  refine ⟨V₁, Z, V₂, hZk, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ⟨u.val, hu⟩, ⟨v.val, hv⟩, ?_⟩
  · ext x
    simp only [Finset.mem_union]
    have hsub : x ∈ V₁ → x ∈ S ∧ x ∉ Z := fun hx => Finset.mem_sdiff.mp (h₁T hx)
    have hZsub : x ∈ Z → x ∈ S := fun hx => hZS hx
    simp only [V₂, T, Finset.mem_sdiff]
    tauto
  · exact Finset.disjoint_left.mpr (fun x hx hz => (Finset.mem_sdiff.mp (h₁T hx)).2 hz)
  · exact Finset.disjoint_left.mpr (fun x hx hx₂ => (Finset.mem_sdiff.mp hx₂).2 hx)
  · exact Finset.disjoint_left.mpr (fun x hz hx => (Finset.mem_sdiff.mp (h₂T hx)).2 hz)
  · intro x hx y hy hxy
    obtain ⟨_, hxT, hr⟩ := Finset.mem_filter.mp hx
    have hyT := h₂T hy
    have hay : H.Adj ⟨x, hxT⟩ ⟨y, hyT⟩ := hxy
    have hy₁ : y ∈ V₁ := Finset.mem_filter.mpr ⟨hyT, hyT, hr.trans hay.reachable⟩
    exact (Finset.mem_sdiff.mp hy).2 hy₁

lemma ValidOn.mono {V Color : Type} {G : SimpleGraph V} {S T : Finset V}
    {L : V → Finset Color} {c : V → Color} (h : ValidOn G S L c)
    (hTS : T ⊆ S) : ValidOn G T L c :=
  ⟨fun v hv => h.1 v (hTS hv), fun _ hv _ hw => h.2 (hTS hv) (hTS hw)⟩

lemma extend_from_choosable {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) (L B : V → Finset Color) (φ : V → Color)
    {m : ℕ} (hφ : ValidOn G A L φ)
    (hchoose : Choosable (G.induce (↑(S \ A) : Set V)) m)
    (hsizes : ∀ v ∈ S \ A, m + (B v).card + A.card ≤ (L v).card) :
    ∃ c, ValidOn G S L c ∧ (∀ v ∈ A, c v = φ v) ∧
      ∀ v ∈ S \ A, c v ∉ B v := by
  classical
  let L' : (↑(S \ A) : Set V) → Finset Color := fun v => L v \ (B v ∪ A.image φ)
  have hs : ∀ v, m ≤ (L' v).card := by
    intro v
    have h₁ : (L v.val).card ≤ (L v.val \ (B v.val ∪ A.image φ)).card +
        (B v.val ∪ A.image φ).card := Finset.card_le_card_sdiff_add_card
    have h₂ := Finset.card_union_le (B v.val) (A.image φ)
    have h₃ : (A.image φ).card ≤ A.card := Finset.card_image_le
    have h₄ := hsizes v.val v.property
    dsimp [L']
    omega
  obtain ⟨f, hf, hp⟩ := hchoose Color L' hs
  let c : V → Color := fun v => if hv : v ∈ S \ A then f ⟨v, hv⟩ else φ v
  have hcA : ∀ v ∈ A, c v = φ v := by
    intro v hv
    simp only [c, dite_eq_right (show v ∉ S \ A from fun h => (Finset.mem_sdiff.mp h).2 hv)]
  have hcmem : ∀ v ∈ S \ A, c v ∈ L v ∧ c v ∉ B v ∧ c v ∉ A.image φ := by
    intro v hv
    have hh := hf ⟨v, hv⟩
    simp only [c, dite_eq_left hv]
    simpa only [L', Finset.mem_sdiff, Finset.mem_union, not_or] using hh
  refine ⟨c, ⟨?_, ?_⟩, hcA, fun v hv => (hcmem v hv).2.1⟩
  · intro v hv
    by_cases ha : v ∈ A
    · rw [hcA v ha]
      exact hφ.1 v ha
    · exact (hcmem v (Finset.mem_sdiff.mpr ⟨hv, ha⟩)).1
  · intro v hv w hw hvw
    by_cases hva : v ∈ A <;> by_cases hwa : w ∈ A
    · rw [hcA v hva, hcA w hwa]
      exact hφ.2 hva hwa hvw
    · intro heq
      have hws : w ∈ S \ A := Finset.mem_sdiff.mpr ⟨hw, hwa⟩
      apply (hcmem w hws).2.2
      rw [← heq, hcA v hva]
      exact Finset.mem_image.mpr ⟨v, hva, rfl⟩
    · intro heq
      have hvs : v ∈ S \ A := Finset.mem_sdiff.mpr ⟨hv, hva⟩
      apply (hcmem v hvs).2.2
      rw [heq, hcA w hwa]
      exact Finset.mem_image.mpr ⟨w, hwa, rfl⟩
    · have hvs : v ∈ S \ A := Finset.mem_sdiff.mpr ⟨hv, hva⟩
      have hws : w ∈ S \ A := Finset.mem_sdiff.mpr ⟨hw, hwa⟩
      simpa only [c, dite_eq_left hvs, dite_eq_left hws] using
        (hp (v := ⟨v, hvs⟩) (w := ⟨w, hws⟩) hvw)

lemma constraintCost_eq {V Color : Type} [DecidableEq V] (S A : Finset V)
    (k : ℕ) (B : V → Finset Color) (hAS : A ⊆ S) :
    constraintCost S k A B = k * A.card + ∑ v ∈ S \ A, (B v).card := by
  classical
  have hA : ∑ v ∈ A, vertexCost k A B v = k * A.card := by
    calc
      _ = ∑ _v ∈ A, k := Finset.sum_congr rfl (fun v hv => by simp [vertexCost, hv])
      _ = _ := by simp [Nat.mul_comm]
  have hB : ∑ v ∈ S \ A, vertexCost k A B v = ∑ v ∈ S \ A, (B v).card := by
    apply Finset.sum_congr rfl
    intro v hv
    simp [vertexCost, (Finset.mem_sdiff.mp hv).2]
  unfold constraintCost
  rw [← Finset.sum_sdiff hAS, hA, hB, Nat.add_comm]

lemma constraintCost_card_bound {V Color : Type} [DecidableEq V]
    {S A : Finset V} {k : ℕ} {B : V → Finset Color} (hk : 1 ≤ k)
    (hAS : A ⊆ S) (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    A.card ≤ 2 * k := by
  rw [constraintCost_eq S A k B hAS] at hbudget
  apply Nat.le_of_mul_le_mul_left (c := k) _ hk
  calc
    k * A.card ≤ 2 * k ^ 2 := (Nat.le_add_right _ _).trans hbudget
    _ = k * (2 * k) := by ring

lemma promote_constraints {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) (L B : V → Finset Color)
    (φ : V → Color) {k m : ℕ} (hk : 1 ≤ k) (hAS : A ⊆ S)
    (hL : ∀ v ∈ S, m + 6 * k ≤ (L v).card)
    (hφ : ValidOn G A L φ)
    (hB : ∀ v ∈ S \ A, (B v).card < 3 * k)
    (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    ∃ A' φ', A ⊆ A' ∧ A' ⊆ S ∧ ValidOn G A' L φ' ∧
      (∀ v ∈ A, φ' v = φ v) ∧ (∀ v ∈ A' \ A, φ' v ∉ B v) ∧
      (∀ v ∈ S \ A', (B v).card < k) ∧
      constraintCost S k A' B ≤ constraintCost S k A B := by
  classical
  let A' := A ∪ S.filter (fun v => k ≤ (B v).card)
  have hAA' : A ⊆ A' := Finset.subset_union_left
  have hA'S : A' ⊆ S := Finset.union_subset hAS (Finset.filter_subset _ _)
  have hcost : constraintCost S k A' B ≤ constraintCost S k A B := by
    apply Finset.sum_le_sum
    intro v hv
    by_cases ha : v ∈ A
    · simp [vertexCost, ha, hAA' ha]
    · by_cases ha' : v ∈ A'
      · have hh : k ≤ (B v).card := by
          rcases Finset.mem_union.mp ha' with hh | hh
          · exact (ha hh).elim
          · exact (Finset.mem_filter.mp hh).2
        simpa [vertexCost, ha, ha'] using hh
      · simp [vertexCost, ha, ha']
  have hcard : A'.card ≤ 2 * k := constraintCost_card_bound hk hA'S (hcost.trans hbudget)
  have hchoose : Choosable (G.induce (↑(A' \ A) : Set V)) (A' \ A).card := by
    have hc := choosable_card (G.induce (↑(A' \ A) : Set V))
    change Choosable _ (Fintype.card ↥(A' \ A)) at hc
    rw [Fintype.card_coe] at hc
    exact hc
  have hsizes : ∀ v ∈ A' \ A, (A' \ A).card + (B v).card + A.card ≤ (L v).card := by
    intro v hv
    have hvA' := (Finset.mem_sdiff.mp hv).1
    have hh := hB v (Finset.mem_sdiff.mpr ⟨hA'S hvA', (Finset.mem_sdiff.mp hv).2⟩)
    have hl := hL v (hA'S hvA')
    have heq := Finset.card_sdiff_add_card_eq_card hAA'
    omega
  obtain ⟨φ', hφ', hagree, havoid⟩ :=
    extend_from_choosable G A' A L B φ hφ hchoose hsizes
  refine ⟨A', φ', hAA', hA'S, hφ', hagree, havoid, ?_, hcost⟩
  intro v hv
  have hvS := (Finset.mem_sdiff.mp hv).1
  have hn := (Finset.mem_sdiff.mp hv).2
  by_contra h
  apply hn
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvS, by omega⟩)

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Separators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

namespace SeparatorSplit

variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {S V₁ Z V₂ : Finset V}

lemma swap (h : SeparatorSplit G S V₁ Z V₂) : SeparatorSplit G S V₂ Z V₁ := by
  refine ⟨?_, h.sep_right.symm, h.left_right.symm, h.left_sep.symm,
    h.right_nonempty, h.left_nonempty, ?_⟩
  · simpa only [Finset.union_comm, Finset.union_left_comm, Finset.union_assoc] using h.union_eq
  · intro v hv w hw hadj
    exact h.anticomplete w hw v hv hadj.symm

lemma left_union_subset (h : SeparatorSplit G S V₁ Z V₂) : V₁ ∪ Z ⊆ S := by
  rw [← h.union_eq]
  exact Finset.subset_union_left

lemma right_subset (h : SeparatorSplit G S V₁ Z V₂) : V₂ ⊆ S := by
  rw [← h.union_eq]
  exact Finset.subset_union_right

lemma left_union_disjoint (h : SeparatorSplit G S V₁ Z V₂) : Disjoint (V₁ ∪ Z) V₂ :=
  Finset.disjoint_union_left.mpr ⟨h.left_right, h.sep_right⟩

lemma sum_eq (h : SeparatorSplit G S V₁ Z V₂) (f : V → ℕ) :
    ∑ v ∈ S, f v = (∑ v ∈ V₁, f v) + (∑ v ∈ Z, f v) + ∑ v ∈ V₂, f v := by
  rw [← h.union_eq, Finset.sum_union h.left_union_disjoint, Finset.sum_union h.left_sep]

lemma left_union_ssubset (h : SeparatorSplit G S V₁ Z V₂) : V₁ ∪ Z ⊂ S := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨h.left_union_subset, ?_⟩
  intro heq
  obtain ⟨v, hv⟩ := h.right_nonempty
  exact Finset.disjoint_left.mp h.left_union_disjoint (heq.symm ▸ h.right_subset hv) hv

end SeparatorSplit

lemma constraintCost_restrict {V Color : Type} [DecidableEq V]
    (S A : Finset V) (k : ℕ) (B : V → Finset Color) :
    constraintCost S k (A ∩ S) B = constraintCost S k A B := by
  apply Finset.sum_congr rfl
  intro v hv
  simp [vertexCost, hv]

lemma precolor_cost_le {V Color : Type} [DecidableEq V]
    (S A : Finset V) (k : ℕ) (B : V → Finset Color) :
    k * (A ∩ S).card ≤ constraintCost S k A B := by
  rw [← constraintCost_restrict S A k B, constraintCost_eq S (A ∩ S) k B Finset.inter_subset_right]
  exact Nat.le_add_right _ _

lemma exists_balanced_separator {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) (B : V → Finset Color) {k : ℕ}
    (hord : k < S.card) (hn : ¬KConnectedOn G S k)
    (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    ∃ V₁ Z V₂, Z.card < k ∧ SeparatorSplit G S V₁ Z V₂ ∧
      constraintCost V₂ k A B ≤ k ^ 2 := by
  obtain ⟨V₁, Z, V₂, hZ, hs⟩ := exists_separator G S hord hn
  have heq := hs.sum_eq (vertexCost k A B)
  change constraintCost S k A B = constraintCost V₁ k A B +
    constraintCost Z k A B + constraintCost V₂ k A B at heq
  by_cases hle : constraintCost V₂ k A B ≤ constraintCost V₁ k A B
  · exact ⟨V₁, Z, V₂, hZ, hs, by omega⟩
  · exact ⟨V₂, Z, V₁, hZ, hs.swap, by omega⟩

lemma extraForbidden_subset {V Color : Type} [DecidableEq V]
    (Z : Finset V) (B : V → Finset Color) (F : Finset Color) (v : V) :
    B v ⊆ extraForbidden Z B F v := by
  classical
  by_cases hv : v ∈ Z <;> simp [extraForbidden, hv]

lemma extraForbidden_cost {V Color : Type} [DecidableEq V]
    (S A Z : Finset V) (k : ℕ) (B : V → Finset Color) (F : Finset Color)
    (hZS : Z ⊆ S) :
    constraintCost S k A (extraForbidden Z B F) ≤
      constraintCost S k A B + Z.card * F.card := by
  classical
  have hpoint : ∀ v ∈ S, vertexCost k A (extraForbidden Z B F) v ≤
      vertexCost k A B v + (if v ∈ Z then F.card else 0) := by
    intro v _
    by_cases ha : v ∈ A <;> by_cases hz : v ∈ Z
    · simp [vertexCost, ha, hz]
    · simp [vertexCost, ha, hz]
    · simpa [vertexCost, extraForbidden, ha, hz] using Finset.card_union_le (B v) F
    · simp [vertexCost, extraForbidden, ha, hz]
  have heq : (∑ v ∈ S, if v ∈ Z then F.card else 0) = Z.card * F.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hZS]
    simp
  calc
    _ ≤ ∑ v ∈ S, (vertexCost k A B v + if v ∈ Z then F.card else 0) :=
      Finset.sum_le_sum hpoint
    _ = _ := by rw [Finset.sum_add_distrib, heq]; rfl

lemma first_side_cost {V Color : Type} [DecidableEq V] [DecidableEq Color]
    {G : SimpleGraph V} {S V₁ Z V₂ : Finset V}
    (hs : SeparatorSplit G S V₁ Z V₂) (A : Finset V) (B : V → Finset Color)
    (φ : V → Color) {k : ℕ} (hZ : Z.card ≤ k) :
    constraintCost (V₁ ∪ Z) k (A ∩ (V₁ ∪ Z))
      (extraForbidden Z B ((A ∩ V₂).image φ)) ≤ constraintCost S k A B := by
  classical
  rw [constraintCost_restrict]
  have heq : constraintCost (V₁ ∪ Z) k A B + constraintCost V₂ k A B =
      constraintCost S k A B := by
    unfold constraintCost
    rw [← Finset.sum_union hs.left_union_disjoint, hs.union_eq]
  calc
    _ ≤ constraintCost (V₁ ∪ Z) k A B + Z.card * ((A ∩ V₂).image φ).card :=
      extraForbidden_cost _ _ _ _ _ _ Finset.subset_union_right
    _ ≤ constraintCost (V₁ ∪ Z) k A B + k * (A ∩ V₂).card := by
      gcongr
      exact Finset.card_image_le
    _ ≤ constraintCost (V₁ ∪ Z) k A B + constraintCost V₂ k A B :=
      Nat.add_le_add_left (precolor_cost_le V₂ A k B) _
    _ = _ := heq

lemma second_side_cost {V Color : Type} [DecidableEq V]
    {G : SimpleGraph V} {S V₁ Z V₂ : Finset V}
    (hs : SeparatorSplit G S V₁ Z V₂) (A : Finset V) (B : V → Finset Color) (k : ℕ) :
    constraintCost (V₂ ∪ Z) k (Z ∪ (A ∩ V₂)) B =
      k * Z.card + constraintCost V₂ k A B := by
  classical
  unfold constraintCost
  rw [Finset.sum_union hs.sep_right.symm]
  have hright : (∑ v ∈ V₂, vertexCost k (Z ∪ (A ∩ V₂)) B v) =
      ∑ v ∈ V₂, vertexCost k A B v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hz : v ∉ Z := fun hz => Finset.disjoint_left.mp hs.sep_right hz hv
    simp [vertexCost, hv, hz]
  have hsep : (∑ v ∈ Z, vertexCost k (Z ∪ (A ∩ V₂)) B v) = k * Z.card := by
    calc
      _ = ∑ _v ∈ Z, k := Finset.sum_congr rfl (fun v hv => by simp [vertexCost, hv])
      _ = _ := by simp [Nat.mul_comm]
  rw [hright, hsep, Nat.add_comm]

lemma SeparatorSplit.glue {V Color : Type} [DecidableEq V]
    {G : SimpleGraph V} {S V₁ Z V₂ : Finset V}
    (hs : SeparatorSplit G S V₁ Z V₂) {L : V → Finset Color} {c₁ c₂ : V → Color}
    (h₁ : ValidOn G (V₁ ∪ Z) L c₁) (h₂ : ValidOn G (V₂ ∪ Z) L c₂)
    (hagree : ∀ v ∈ Z, c₁ v = c₂ v) :
    ∃ c, ValidOn G S L c ∧ (∀ v ∈ V₁ ∪ Z, c v = c₁ v) ∧
      ∀ v ∈ V₂ ∪ Z, c v = c₂ v := by
  classical
  let c : V → Color := fun v => if v ∈ V₂ then c₂ v else c₁ v
  have hc₁ : ∀ v ∈ V₁ ∪ Z, c v = c₁ v := by
    intro v hv
    have hn : v ∉ V₂ := fun hh => Finset.disjoint_left.mp hs.left_union_disjoint hv hh
    exact ite_eq_right hn
  have hc₂ : ∀ v ∈ V₂ ∪ Z, c v = c₂ v := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ite_eq_left hv
    · rw [hc₁ v (Finset.mem_union_right _ hv), hagree v hv]
  have hcover : ∀ v ∈ S, v ∈ V₁ ∪ Z ∨ v ∈ V₂ := by
    intro v hv
    rw [← hs.union_eq] at hv
    exact Finset.mem_union.mp hv
  refine ⟨c, ⟨?_, ?_⟩, hc₁, hc₂⟩
  · intro v hv
    rcases hcover v hv with hv | hv
    · rw [hc₁ v hv]
      exact h₁.1 v hv
    · rw [hc₂ v (Finset.mem_union_left _ hv)]
      exact h₂.1 v (Finset.mem_union_left _ hv)
  · intro v hv w hw hadj
    rcases hcover v hv with hv | hv <;> rcases hcover w hw with hw | hw
    · rw [hc₁ v hv, hc₁ w hw]
      exact h₁.2 hv hw hadj
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact (hs.anticomplete v hv w hw hadj).elim
      · have hv' : v ∈ V₂ ∪ Z := Finset.mem_union_right _ hv
        have hw' : w ∈ V₂ ∪ Z := Finset.mem_union_left _ hw
        rw [hc₂ v hv', hc₂ w hw']
        exact h₂.2 hv' hw' hadj
    · rcases Finset.mem_union.mp hw with hw | hw
      · exact (hs.anticomplete w hw v hv hadj.symm).elim
      · have hv' : v ∈ V₂ ∪ Z := Finset.mem_union_left _ hv
        have hw' : w ∈ V₂ ∪ Z := Finset.mem_union_right _ hw
        rw [hc₂ v hv', hc₂ w hw']
        exact h₂.2 hv' hw' hadj
    · have hv' : v ∈ V₂ ∪ Z := Finset.mem_union_left _ hv
      have hw' : w ∈ V₂ ∪ Z := Finset.mem_union_left _ hw
      rw [hc₂ v hv', hc₂ w hw']
      exact h₂.2 hv' hw' hadj

lemma separator_precolor {V Color : Type} [DecidableEq V]
    {G : SimpleGraph V} {S V₁ Z V₂ : Finset V}
    (hs : SeparatorSplit G S V₁ Z V₂) (A : Finset V) (L : V → Finset Color)
    (φ c₁ : V → Color) (hφ : ValidOn G A L φ) (h₁ : ValidOn G (V₁ ∪ Z) L c₁)
    (hcompat : ∀ v ∈ Z, ∀ w ∈ A ∩ V₂, G.Adj v w → c₁ v ≠ φ w) :
    ∃ φ₂, ValidOn G (Z ∪ (A ∩ V₂)) L φ₂ ∧
      (∀ v ∈ Z, φ₂ v = c₁ v) ∧ (∀ v ∈ A ∩ V₂, φ₂ v = φ v) := by
  classical
  let φ₂ := fun v => if v ∈ Z then c₁ v else φ v
  have hz : ∀ v ∈ Z, φ₂ v = c₁ v := fun v hv => ite_eq_left hv
  have hd : ∀ v ∈ A ∩ V₂, φ₂ v = φ v := by
    intro v hv
    exact ite_eq_right (fun hh => Finset.disjoint_left.mp hs.sep_right hh (Finset.mem_inter.mp hv).2)
  refine ⟨φ₂, ⟨?_, ?_⟩, hz, hd⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rw [hz v hv]
      exact h₁.1 v (Finset.mem_union_right _ hv)
    · rw [hd v hv]
      exact hφ.1 v (Finset.mem_inter.mp hv).1
  · intro v hv w hw hadj
    rcases Finset.mem_union.mp hv with hv | hv <;>
      rcases Finset.mem_union.mp hw with hw | hw
    · rw [hz v hv, hz w hw]
      exact h₁.2 (Finset.mem_union_right _ hv) (Finset.mem_union_right _ hw) hadj
    · rw [hz v hv, hd w hw]
      exact hcompat v hv w hw hadj
    · rw [hd v hv, hz w hw]
      exact (hcompat w hw v hv hadj.symm).symm
    · rw [hd v hv, hd w hw]
      exact hφ.2 (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hw).1 hadj

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Palette
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open scoped Classical

lemma ValidOn.glue {V Color : Type} [DecidableEq V]
    {G : SimpleGraph V} {S T : Finset V} {L : V → Finset Color} {c d : V → Color}
    (hc : ValidOn G S L c) (hd : ValidOn G T L d)
    (hst : Disjoint S T) (hcross : ∀ v ∈ S, ∀ w ∈ T, G.Adj v w → c v ≠ d w) :
    ValidOn G (S ∪ T) L (fun v => if v ∈ S then c v else d v) := by
  classical
  constructor
  · intro v hv
    by_cases hs : v ∈ S
    · simpa [hs] using hc.1 v hs
    · have ht : v ∈ T := (Finset.mem_union.mp hv).resolve_left hs
      simpa [hs] using hd.1 v ht
  · intro v hv w hw hadj
    by_cases hs : v ∈ S <;> by_cases hs' : w ∈ S
    · simpa only [ite_eq_left hs, ite_eq_left hs'] using hc.2 hs hs' hadj
    · have hwT := (Finset.mem_union.mp hw).resolve_left hs'
      simpa only [ite_eq_left hs, ite_eq_right (Finset.disjoint_right.mp hst hwT)] using
        hcross v hs w hwT hadj
    · simpa only [ite_eq_right hs, ite_eq_left hs'] using
        (hcross w hs' v ((Finset.mem_union.mp hv).resolve_left hs) hadj.symm).symm
    · simpa only [ite_eq_right hs, ite_eq_right hs'] using
        hd.2 ((Finset.mem_union.mp hv).resolve_left hs)
          ((Finset.mem_union.mp hw).resolve_left hs') hadj

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.FiniteConcentration
open scoped BigOperators

lemma mean_const {α : Type} [Fintype α] {w : α → ℝ} (hw : ∑ a, w a = 1) (c : ℝ) :
    mean w (fun _ => c) = c := by simp [mean, ← Finset.sum_mul, hw]

lemma mean_sub {α : Type} [Fintype α] (w f g : α → ℝ) :
    mean w (fun a => f a - g a) = mean w f - mean w g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mono {α : Type} [Fintype α] {w f g : α → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hfg : ∀ a, f a ≤ g a) : mean w f ≤ mean w g := by
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hfg a) (hw a)

lemma mean_sub_const {α : Type} [Fintype α] {w : α → ℝ}
    (hw : ∑ a, w a = 1) (f : α → ℝ) (c : ℝ) :
    mean w (fun a => f a - c) = mean w f - c := by
  rw [mean_sub, mean_const hw]

lemma mean_const_sub {α : Type} [Fintype α] {w : α → ℝ}
    (hw : ∑ a, w a = 1) (f : α → ℝ) (c : ℝ) :
    mean w (fun a => c - f a) = c - mean w f := by
  rw [mean_sub, mean_const hw]

lemma centered_bound {α : Type} [Fintype α] {w g : α → ℝ} {b : ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (hg : ∀ a a', |g a - g a'| ≤ b) (a : α) : |g a - mean w g| ≤ b := by
  rw [abs_le]
  have hl := mean_mono hw (fun a' => (abs_le.mp (hg a a')).1)
  have hu := mean_mono hw (fun a' => (abs_le.mp (hg a a')).2)
  rw [mean_const hs, mean_const_sub hs] at hl
  rw [mean_const hs, mean_const_sub hs] at hu
  exact ⟨hl, hu⟩

lemma centered_mgf {α : Type} [Fintype α] {w X : α → ℝ} {b : ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (hX : mean w X = 0)
    (hb : 0 < b) (hbound : ∀ a, |X a| ≤ b) (l : ℝ) :
    mean w (fun a => Real.exp (l * X a)) ≤ Real.exp (l ^ 2 * b ^ 2 / 2) := by
  let u : α → ℝ := fun a => (b + X a) / (2 * b)
  let v : α → ℝ := fun a => (b - X a) / (2 * b)
  have hu : ∀ a, 0 ≤ u a := by
    intro a; dsimp [u]; apply div_nonneg _ (by positivity)
    linarith [(abs_le.mp (hbound a)).1]
  have hv : ∀ a, 0 ≤ v a := by
    intro a; dsimp [v]; apply div_nonneg _ (by positivity)
    linarith [(abs_le.mp (hbound a)).2]
  have huv : ∀ a, u a + v a = 1 := by
    intro a; dsimp [u, v]; field_simp; ring
  have he : ∀ a, Real.exp (l * X a) ≤
      u a * Real.exp (l * b) + v a * Real.exp (-(l * b)) := by
    intro a
    have h := convexOn_exp.2 (Set.mem_univ (l * b)) (Set.mem_univ (-(l * b)))
      (hu a) (hv a) (huv a)
    simp only [smul_eq_mul] at h
    convert h using 1
    congr 1
    dsimp [u, v]
    field_simp
    ring
  have hmu : mean w u = 1 / 2 := by
    dsimp [mean, u]
    simp_rw [← mul_div_assoc, mul_add]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, hs]
    change (1 * b + mean w X) / (2 * b) = 1 / 2
    rw [hX]
    field_simp
    ring
  have hmv : mean w v = 1 / 2 := by
    dsimp [mean, v]
    simp_rw [← mul_div_assoc, mul_sub]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
    change (1 * b - mean w X) / (2 * b) = 1 / 2
    rw [hX]
    field_simp
    ring
  calc
    mean w (fun a => Real.exp (l * X a))
        ≤ mean w (fun a => u a * Real.exp (l * b) + v a * Real.exp (-(l * b))) :=
      mean_mono hw he
    _ = Real.cosh (l * b) := by
      simp only [mean, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
      change mean w u * Real.exp (l * b) + mean w v * Real.exp (-(l * b)) = _
      rw [hmu, hmv, Real.cosh_eq]
      ring
    _ ≤ Real.exp ((l * b) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
    _ = _ := by congr 1; ring

lemma mass_nonneg {α : Type} [Fintype α] {n : ℕ} {w : Fin n → α → ℝ}
    (hw : ∀ i a, 0 ≤ w i a) (x : Fin n → α) : 0 ≤ mass w x :=
  Finset.prod_nonneg fun i _ => hw i (x i)

lemma mass_sum {α : Type} [Fintype α] {n : ℕ} {w : Fin n → α → ℝ}
    (hw : ∀ i, ∑ a, w i a = 1) : ∑ x, mass w x = 1 := by
  simp only [mass]
  rw [← Fintype.prod_sum]
  simp [hw]

lemma sum_cons {α : Type} [Fintype α] {n : ℕ} (f : (Fin (n + 1) → α) → ℝ) :
    ∑ x, f x = ∑ a, ∑ y, f (Fin.cons a y) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => α)) f]
  rw [Fintype.sum_prod_type]
  rfl

lemma mass_cons {α : Type} [Fintype α] {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (a : α) (x : Fin n → α) :
    mass w (Fin.cons a x) = w 0 a * mass (fun i => w i.succ) x := by
  simp [mass, Fin.prod_univ_succ]

lemma mean_cons {α : Type} [Fintype α] {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (f : (Fin (n + 1) → α) → ℝ) :
    mean (mass w) f = mean (w 0) (fun a => mean (mass (fun i => w i.succ))
      (fun x => f (Fin.cons a x))) := by
  simp only [mean, sum_cons, mass_cons, mul_assoc, Finset.mul_sum]

lemma BoundedChanges.tail {α : Type} {n : ℕ} {f : (Fin (n + 1) → α) → ℝ} {b : ℝ}
    (h : BoundedChanges f b) (a : α) : BoundedChanges (fun x => f (Fin.cons a x)) b := by
  intro i x y hxy
  apply h i.succ
  intro j hj
  induction j using Fin.cases with
  | zero => simp
  | succ j =>
    simp only [Fin.cons_succ]
    apply hxy j
    intro he
    exact hj (congrArg Fin.succ he)

lemma BoundedChanges.head_mean {α : Type} [Fintype α] {n : ℕ}
    {f : (Fin (n + 1) → α) → ℝ} {b : ℝ} {w : Fin n → α → ℝ}
    (h : BoundedChanges f b) (hw : ∀ i a, 0 ≤ w i a) (hs : ∀ i, ∑ a, w i a = 1)
    (a a' : α) :
    |mean (mass w) (fun x => f (Fin.cons a x)) -
      mean (mass w) (fun x => f (Fin.cons a' x))| ≤ b := by
  have hd : ∀ x : Fin n → α, |f (Fin.cons a x) - f (Fin.cons a' x)| ≤ b := by
    intro x
    apply h 0
    intro j hj
    induction j using Fin.cases with
    | zero => exact (hj rfl).elim
    | succ j => simp
  rw [← mean_sub, abs_le]
  constructor
  · have hh := mean_mono (mass_nonneg hw) (fun x => (abs_le.mp (hd x)).1)
    simpa only [mean_const (mass_sum hs)] using hh
  · have hh := mean_mono (mass_nonneg hw) (fun x => (abs_le.mp (hd x)).2)
    simpa only [mean_const (mass_sum hs)] using hh

theorem bounded_changes_mgf {α : Type} [Fintype α] {n : ℕ}
    (w : Fin n → α → ℝ) (hw : ∀ i a, 0 ≤ w i a) (hs : ∀ i, ∑ a, w i a = 1)
    (f : (Fin n → α) → ℝ) {b : ℝ} (hb : 0 < b) (hf : BoundedChanges f b) (l : ℝ) :
    mean (mass w) (fun x => Real.exp (l * (f x - mean (mass w) f))) ≤
      Real.exp (n * l ^ 2 * b ^ 2 / 2) := by
  induction n with
  | zero => simp [mean, mass]
  | succ n ih =>
    let w' : Fin n → α → ℝ := fun i => w i.succ
    let g : α → ℝ := fun a => mean (mass w') (fun x => f (Fin.cons a x))
    have hmean : mean (mass w) f = mean (w 0) g := mean_cons w f
    have hg : ∀ a a', |g a - g a'| ≤ b :=
      hf.head_mean (fun i => hw i.succ) (fun i => hs i.succ)
    have hcenter : mean (w 0) (fun a => g a - mean (w 0) g) = 0 := by
      rw [mean_sub_const (hs 0), sub_self]
    have hhead := centered_mgf (hw 0) (hs 0) hcenter hb
      (centered_bound (hw 0) (hs 0) hg) l
    have htail : ∀ a, mean (mass w') (fun x =>
        Real.exp (l * (f (Fin.cons a x) - g a))) ≤
        Real.exp (n * l ^ 2 * b ^ 2 / 2) := by
      intro a
      exact ih w' (fun i => hw i.succ) (fun i => hs i.succ)
        (fun x => f (Fin.cons a x)) (hf.tail a)
    rw [mean_cons]
    let c := Real.exp (n * l ^ 2 * b ^ 2 / 2)
    calc
      mean (w 0) (fun a => mean (mass w')
          (fun x => Real.exp (l * (f (Fin.cons a x) - mean (mass w) f))))
          = mean (w 0) (fun a => Real.exp (l * (g a - mean (w 0) g)) *
            mean (mass w') (fun x => Real.exp (l * (f (Fin.cons a x) - g a)))) := by
        apply congrArg (mean (w 0))
        funext a
        rw [hmean]
        change (∑ x, mass w' x * Real.exp (l * (f (Fin.cons a x) - mean (w 0) g))) =
          Real.exp (l * (g a - mean (w 0) g)) *
            ∑ x, mass w' x * Real.exp (l * (f (Fin.cons a x) - g a))
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        have he : l * (f (Fin.cons a x) - mean (w 0) g) =
            l * (g a - mean (w 0) g) + l * (f (Fin.cons a x) - g a) := by ring
        rw [he, Real.exp_add]
        ring
      _ ≤ mean (w 0) (fun a => Real.exp (l * (g a - mean (w 0) g)) * c) :=
        mean_mono (hw 0) (fun a => mul_le_mul_of_nonneg_left (htail a) (by positivity))
      _ = mean (w 0) (fun a => Real.exp (l * (g a - mean (w 0) g))) * c := by
        simp only [mean, ← mul_assoc, Finset.sum_mul]
      _ ≤ Real.exp (l ^ 2 * b ^ 2 / 2) * c :=
        mul_le_mul_of_nonneg_right hhead (by dsimp [c]; positivity)
      _ = Real.exp ((n + 1 : ℕ) * l ^ 2 * b ^ 2 / 2) := by
        dsimp [c]
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

lemma exponential_markov {α : Type} [Fintype α] (w X : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) {l u : ℝ} (hl : 0 ≤ l) :
    probability w (fun a => u ≤ X a) ≤
      mean w (fun a => Real.exp (l * X a)) / Real.exp (l * u) := by
  classical
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  simp only [probability, mean, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with ha
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha hl)) (hw a)
  · simp only [zero_mul]
    exact mul_nonneg (hw a) (Real.exp_pos _).le

lemma probability_abs_le {α : Type} [Fintype α] (w X : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (u : ℝ) :
    probability w (fun a => u ≤ |X a|) ≤
      probability w (fun a => u ≤ X a) + probability w (fun a => u ≤ -X a) := by
  classical
  simp only [probability, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : u ≤ X a
  · simp only [h, ite_true]
    split_ifs <;> linarith [hw a]
  · by_cases h' : u ≤ -X a
    · simp only [h, h', ite_false, ite_true, zero_add]
      split_ifs <;> linarith [hw a]
    · have ha : ¬u ≤ |X a| := by
        have : |X a| < u := abs_lt.mpr ⟨by linarith, by linarith⟩
        exact not_le_of_gt this
      simp [h, h', ha]

theorem bounded_changes_upper {α : Type} [Fintype α] {n : ℕ} (hn : 1 ≤ n)
    (w : Fin n → α → ℝ) (hw : ∀ i a, 0 ≤ w i a) (hs : ∀ i, ∑ a, w i a = 1)
    (f : (Fin n → α) → ℝ) {b u : ℝ} (hb : 0 < b) (hu : 0 < u)
    (hf : BoundedChanges f b) :
    probability (mass w) (fun x => u ≤ f x - mean (mass w) f) ≤
      Real.exp (-u ^ 2 / (2 * n * b ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let l : ℝ := u / (n * b ^ 2)
  have hl : 0 < l := by dsimp [l]; positivity
  calc
    probability (mass w) (fun x => u ≤ f x - mean (mass w) f)
        ≤ mean (mass w) (fun x => Real.exp (l * (f x - mean (mass w) f))) /
          Real.exp (l * u) :=
      exponential_markov _ _ (mass_nonneg hw) hl.le
    _ ≤ Real.exp (n * l ^ 2 * b ^ 2 / 2) / Real.exp (l * u) :=
      div_le_div_of_nonneg_right (bounded_changes_mgf w hw hs f hb hf l) (by positivity)
    _ = _ := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [l]
      field_simp
      ring

lemma BoundedChanges.neg {α : Type} {n : ℕ} {f : (Fin n → α) → ℝ} {b : ℝ}
    (h : BoundedChanges f b) : BoundedChanges (fun x => -f x) b := by
  intro i x y hxy
  simpa only [neg_sub_neg, abs_sub_comm] using h i x y hxy

theorem bounded_differences {α : Type} [Fintype α] {n : ℕ} (hn : 1 ≤ n)
    (w : Fin n → α → ℝ) (hw : ∀ i a, 0 ≤ w i a) (hs : ∀ i, ∑ a, w i a = 1)
    (f : (Fin n → α) → ℝ) {b u : ℝ} (hb : 0 < b) (hu : 0 < u)
    (hf : BoundedChanges f b) :
    probability (mass w) (fun x => u ≤ |f x - mean (mass w) f|) ≤
      2 * Real.exp (-u ^ 2 / (2 * n * b ^ 2)) := by
  have hupp := bounded_changes_upper hn w hw hs f hb hu hf
  have hlow := bounded_changes_upper hn w hw hs (fun x => -f x) hb hu hf.neg
  have he : mean (mass w) (fun x => -f x) = -mean (mass w) f := by
    simp [mean, Finset.sum_neg_distrib]
  rw [he] at hlow
  have hevent : (fun x => u ≤ -f x - -mean (mass w) f) =
      (fun x => u ≤ -(f x - mean (mass w) f)) := by
    funext x; congr 1; ring
  rw [hevent] at hlow
  have h := probability_abs_le (mass w) (fun x => f x - mean (mass w) f) (mass_nonneg hw) u
  linarith

end LinearListHadwiger.FiniteConcentration

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.ConnectivityTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

namespace ConnectivityTests

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

lemma endpoints_card_le {V : Type} [Fintype V] [DecidableEq V] (E : Finset (V × V)) : (endpoints E).card ≤ 2 * E.card := by
  exact (Finset.card_union_le _ _).trans (by
    have h₁ := Finset.card_image_le (s := E) (f := Prod.fst)
    have h₂ := Finset.card_image_le (s := E) (f := Prod.snd)
    omega)

lemma IsCutMatching.fst_card {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {B : Finset V} {E : Finset (V × V)}
    (h : IsCutMatching G B E) : (E.image Prod.fst).card = E.card := by
  apply Finset.card_image_iff.mpr
  intro e he f hf heq
  by_contra hn
  exact (h.2 he hf hn).1 heq

lemma IsCutMatching.snd_card {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {B : Finset V} {E : Finset (V × V)}
    (h : IsCutMatching G B E) : (E.image Prod.snd).card = E.card := by
  apply Finset.card_image_iff.mpr
  intro e he f hf heq
  by_contra hn
  exact (h.2 he hf hn).2 heq

lemma IsCutMatching.endpoints_inter_left {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {B : Finset V}
    {E : Finset (V × V)} (h : IsCutMatching G B E) :
    endpoints E ∩ B = E.image Prod.fst := by
  ext v
  simp only [endpoints, Finset.mem_inter, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hmem, hv⟩
    rcases hmem with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · exact ⟨e, he, rfl⟩
    · exact False.elim ((h.1 e he).2.1 hv)
  · rintro ⟨e, he, rfl⟩
    exact ⟨Or.inl ⟨e, he, rfl⟩, (h.1 e he).1⟩

lemma IsCutMatching.endpoints_inter_right {G : SimpleGraph V} {B : Finset V}
    {E : Finset (V × V)} (h : IsCutMatching G B E) :
    endpoints E ∩ Bᶜ = E.image Prod.snd := by
  ext v
  simp only [endpoints, Finset.mem_inter, Finset.mem_union, Finset.mem_image,
    Finset.mem_compl]
  constructor
  · rintro ⟨hmem, hv⟩
    rcases hmem with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · exact False.elim (hv (h.1 e he).1)
    · exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨Or.inr ⟨e, he, rfl⟩, (h.1 e he).2.1⟩

lemma cross_edge_of_connected {W : Type} (H : SimpleGraph W) (hc : H.Connected)
    (P : W → Prop) (a b : W) (ha : P a) (hb : ¬P b) :
    ∃ x y, P x ∧ ¬P y ∧ H.Adj x y := by
  classical
  obtain ⟨p⟩ := hc.preconnected a b
  have step : ∀ {x y : W}, H.Walk x y → P x → ¬P y →
      ∃ u v, P u ∧ ¬P v ∧ H.Adj u v := by
    intro x y q
    induction q with
    | nil => exact fun hx hy => False.elim (hy hx)
    | @cons x z y hxz q ih =>
      intro hx hy
      by_cases hz : P z
      · exact ih hz hy
      · exact ⟨x, z, hx, hz, hxz⟩
  exact step p ha hb

lemma crossing_edge_avoiding (G : SimpleGraph V) (B X : Finset V) {k : ℕ}
    (hc : KConnectedOn G Finset.univ k) (hx : X.card < k)
    (hb : (X ∩ B).card < B.card) (hbc : (X ∩ Bᶜ).card < Bᶜ.card) :
    ∃ a ∈ B, ∃ b ∉ B, a ∉ X ∧ b ∉ X ∧ G.Adj a b := by
  have hba : ¬B ⊆ X := by
    intro hh
    rw [Finset.inter_eq_right.mpr hh] at hb
    exact (lt_self_iff_false _).mp hb
  have hbca : ¬Bᶜ ⊆ X := by
    intro hh
    rw [Finset.inter_eq_right.mpr hh] at hbc
    exact (lt_self_iff_false _).mp hbc
  obtain ⟨a, ha, hax⟩ := Finset.not_subset.mp hba
  obtain ⟨b, hb, hbx⟩ := Finset.not_subset.mp hbca
  have hconn := hc.2 X (Finset.subset_univ _) hx
  let a' : {v // v ∈ (Finset.univ \ X : Finset V)} := ⟨a, by simp [hax]⟩
  let b' : {v // v ∈ (Finset.univ \ X : Finset V)} := ⟨b, by simp [hbx]⟩
  obtain ⟨u, v, hu, hv, hadj⟩ := cross_edge_of_connected _ hconn
    (fun v => v.val ∈ B) a' b' ha (Finset.mem_compl.mp hb)
  exact ⟨u.val, hu, v.val, hv, (Finset.mem_sdiff.mp u.property).2,
    (Finset.mem_sdiff.mp v.property).2, hadj⟩

theorem exists_cut_matching (G : SimpleGraph V) (B : Finset V) {k m : ℕ}
    (hc : KConnectedOn G Finset.univ k) (hk : 2 * m ≤ k)
    (hb : m ≤ B.card) (hbc : m ≤ Bᶜ.card) :
    ∃ E : Finset (V × V), IsCutMatching G B E ∧ E.card = m := by
  classical
  induction m with
  | zero => exact ⟨∅, by simp [IsCutMatching], rfl⟩
  | succ m ih =>
    obtain ⟨E, he, hcard⟩ := ih (by omega) (by omega) (by omega)
    have hx : (endpoints E).card < k := (endpoints_card_le E).trans_lt (by omega)
    have hbl : (endpoints E ∩ B).card < B.card := by
      rw [he.endpoints_inter_left, he.fst_card, hcard]
      omega
    have hbr : (endpoints E ∩ Bᶜ).card < Bᶜ.card := by
      rw [he.endpoints_inter_right, he.snd_card, hcard]
      omega
    obtain ⟨a, ha, b, hb, hax, hbx, hadj⟩ := crossing_edge_avoiding G B (endpoints E)
      hc hx hbl hbr
    have hane : ∀ e ∈ E, a ≠ e.1 := by
      intro e heq heq'
      apply hax
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, heq, heq'.symm⟩)
    have hbne : ∀ e ∈ E, b ≠ e.2 := by
      intro e heq heq'
      apply hbx
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, heq, heq'.symm⟩)
    have hnot : (a,b) ∉ E := fun h => hane (a,b) h rfl
    refine ⟨insert (a,b) E, ⟨?_, ?_⟩, by simp [hnot, hcard]⟩
    · intro e heq
      rcases Finset.mem_insert.mp heq with rfl | heq
      · exact ⟨ha, hb, hadj⟩
      · exact he.1 e heq
    · intro e heq f hfq hne
      rcases Finset.mem_insert.mp heq with rfl | heq
      · rcases Finset.mem_insert.mp hfq with rfl | hfq
        · exact False.elim (hne rfl)
        · exact ⟨hane f hfq, hbne f hfq⟩
      · rcases Finset.mem_insert.mp hfq with rfl | hfq
        · exact ⟨(hane e heq).symm, (hbne e heq).symm⟩
        · exact he.2 heq hfq hne

theorem finite_hitting {α β : Type} [Fintype α] [Fintype β]
    (s : ℕ) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (R : β → α → Prop) [DecidableRel R] (p : ℝ) (hp : 0 ≤ p)
    (hrow : ∀ v, ∑ a, w a * (if ¬R v a then 1 else 0) ≤ p)
    (hsmall : (Fintype.card β : ℝ) * p ^ s < 1) :
    ∃ f : Fin s → α, ∀ v, ∃ i, R v (f i) := by
  classical
  let m : (Fin s → α) → ℝ := fun f => ∏ i, w (f i)
  let bad : β → (Fin s → α) → ℝ := fun v f => if ∀ i, ¬R v (f i) then 1 else 0
  have hm : ∀ f, 0 ≤ m f := fun f => Finset.prod_nonneg fun i _ => hw (f i)
  have hnorm : ∑ f, m f = 1 := by
    dsimp [m]
    rw [← Fintype.prod_sum]
    simp [hs]
  have hevent (v : β) : ∑ f, m f * bad v f ≤ p ^ s := by
    calc
      ∑ f, m f * bad v f = ∏ i : Fin s, ∑ a, w a * (if ¬R v a then 1 else 0) := by
        rw [Fintype.prod_sum]
        apply Finset.sum_congr rfl
        intro f _
        simp only [Finset.prod_mul_distrib, Finset.prod_boole, Finset.mem_univ,
          forall_const, m, bad]
      _ ≤ ∏ _i : Fin s, p := by
        have hnonneg : 0 ≤ ∑ a, w a * (if ¬R v a then 1 else 0) :=
          Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (by split_ifs <;> norm_num)
        have hprod (T : Finset (Fin s)) :
            (∏ _i ∈ T, ∑ a, w a * (if ¬R v a then 1 else 0)) ≤ ∏ _i ∈ T, p := by
          induction T using Finset.induction_on with
          | empty => simp
          | @insert index T hindex ih =>
            simp only [Finset.prod_insert hindex]
            exact mul_le_mul (hrow v) ih (Finset.prod_nonneg fun _ _ => hnonneg) hp
        exact hprod Finset.univ
      _ = p ^ s := by simp
  by_contra h
  have hbad : ∀ f : Fin s → α, ∃ v, ∀ i, ¬R v (f i) := by
    simpa only [not_exists, not_forall] using h
  have hone : 1 ≤ ∑ f, ∑ v, m f * bad v f := by
    rw [← hnorm]
    apply Finset.sum_le_sum
    intro f _
    obtain ⟨v, hv⟩ := hbad f
    calc
      m f = m f * bad v f := by simp [bad, hv]
      _ ≤ ∑ v, m f * bad v f := Finset.single_le_sum (f := fun v => m f * bad v f)
        (fun v _ => mul_nonneg (hm f) (by dsimp [bad]; split_ifs <;> norm_num))
        (Finset.mem_univ _)
  have hupper : (∑ f, ∑ v, m f * bad v f) ≤ (Fintype.card β : ℝ) * p ^ s := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _v : β, p ^ s := Finset.sum_le_sum fun v _ => hevent v
      _ = _ := by simp
  linarith

lemma sum_uniform_mask (A D : Finset V) (z : ℝ) :
    (∑ a : V, (if a ∈ A then z else 0) * (if a ∈ D then 1 else 0)) =
      ((A ∩ D).card : ℝ) * z := by
  calc
    _ = ∑ a : V, if a ∈ A ∩ D then z else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ A <;> by_cases hd : a ∈ D <;> simp [ha, hd]
    _ = _ := by rw [Finset.sum_ite_mem]; simp

theorem exists_neighborhood_cover (G : SimpleGraph V) (A : Finset V) [DecidableRel G.Adj]
    {n k : ℝ} (hn : 1 ≤ n) (hk : 0 < k) (ha : A.Nonempty)
    (hAn : (A.card : ℝ) ≤ n)
    (hd : ∀ v ∈ A, k / 3 ≤ ((A.filter (G.Adj v)).card : ℝ)) :
    ∃ R ⊆ A, R.card ≤ ⌈10 * (n / k) * Real.log (2 * n)⌉₊ ∧
      ∀ v ∈ A, ∃ r ∈ R, G.Adj v r := by
  classical
  let s := ⌈10 * (n / k) * Real.log (2 * n)⌉₊
  let c : ℝ := A.card
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast Finset.card_pos.mpr ha
  have hcn : c ≤ n := hAn
  let w : V → ℝ := fun a => if a ∈ A then c⁻¹ else 0
  have hw : ∀ a, 0 ≤ w a := fun a => by dsimp [w]; positivity
  have hs : ∑ a, w a = 1 := by
    dsimp [w]
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    change c * c⁻¹ = 1
    exact mul_inv_cancel₀ hc.ne'
  let rel : A → V → Prop := fun v a => a ∈ A ∧ G.Adj v.val a
  let p := Real.exp (-k / (3 * n))
  have hp : 0 ≤ p := (Real.exp_pos _).le
  have hrow : ∀ v : A, ∑ a, w a * (if ¬rel v a then 1 else 0) ≤ p := by
    intro v
    let D := A.filter fun a => ¬G.Adj v.val a
    have hsum : (∑ a, w a * (if ¬rel v a then 1 else 0)) = (D.card : ℝ) / c := by
      calc
        _ = ∑ a : V, (if a ∈ A then c⁻¹ else 0) * (if a ∈ D then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : a ∈ A <;> by_cases hadj : G.Adj v.val a <;>
            simp [w, rel, D, ha, hadj]
        _ = ((A ∩ D).card : ℝ) * c⁻¹ := sum_uniform_mask A D _
        _ = (D.card : ℝ) / c := by
          rw [Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]; rfl
    have hcard : ((A.filter (G.Adj v.val)).card : ℝ) + (D.card : ℝ) = c := by
      dsimp [D, c]
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := A) (G.Adj v.val)
    have hdegree := hd v.val v.property
    have hcpos : 0 < 3 * n := by linarith
    have hquot : (D.card : ℝ) / c ≤ 1 - k / (3 * n) := by
      apply (div_le_iff₀ hc).mpr
      have hkn : k / (3 * n) * c ≤ k / 3 := by
        calc
          _ ≤ k / (3 * n) * n := mul_le_mul_of_nonneg_left hcn (by positivity)
          _ = k / 3 := by field_simp
      nlinarith
    rw [hsum]
    exact hquot.trans (by simpa [p, neg_div] using Real.one_sub_le_exp_neg (k / (3 * n)))
  have hlog : 0 < Real.log (2 * n) := Real.log_pos (by linarith)
  have hsreal : 10 * (n / k) * Real.log (2 * n) ≤ (s : ℝ) := Nat.le_ceil _
  have hexponent : (s : ℝ) * (k / (3 * n)) ≥ Real.log (2 * n) := by
    have hh := mul_le_mul_of_nonneg_right hsreal (show 0 ≤ k by positivity)
    have heq : (10 * (n / k) * Real.log (2 * n)) * k = 10 * n * Real.log (2 * n) := by
      field_simp
    rw [heq] at hh
    have h3n : 0 < 3 * n := by linarith
    rw [← mul_div_assoc]
    apply (le_div_iff₀ h3n).mpr
    change Real.log (2 * n) * (3 * n) ≤ (s : ℝ) * k
    nlinarith
  have hsmall : (Fintype.card A : ℝ) * p ^ s < 1 := by
    have he : p ^ s ≤ (2 * n)⁻¹ := by
      dsimp [p]
      rw [← Real.exp_nat_mul]
      calc
        _ ≤ Real.exp (-Real.log (2 * n)) := by
          apply Real.exp_le_exp.mpr
          simp only [neg_div, mul_neg]
          linarith
        _ = (2 * n)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by linarith)]
    have hca : (Fintype.card A : ℝ) = c := by simp [c]
    rw [hca]
    calc
      c * p ^ s ≤ n * (2 * n)⁻¹ := mul_le_mul hcn he (pow_nonneg hp _) (by linarith)
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  obtain ⟨f, hf⟩ := finite_hitting s w hw hs rel p hp hrow hsmall
  let R := (Finset.univ.image f) ∩ A
  refine ⟨R, Finset.inter_subset_right, ?_, ?_⟩
  · exact (Finset.card_le_card Finset.inter_subset_left).trans
      ((Finset.card_image_le).trans (by simp [s]))
  · intro v hv
    obtain ⟨i, hiA, hiadj⟩ := hf ⟨v, hv⟩
    exact ⟨f i, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hiA⟩,
      hiadj⟩

lemma sum_powers_le (n s : ℕ) : ∑ i ∈ Finset.range (s + 1), n ^ i ≤ (n + 1) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have hh : n ^ s ≤ (n + 1) ^ s := Nat.pow_le_pow_left (by omega) s
    rw [pow_succ, pow_succ]
    nlinarith

lemma mem_smallSets {s : ℕ} {R : Finset V} : R ∈ smallSets s ↔ R.card ≤ s := by
  simp only [smallSets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨R.card, by omega, rfl⟩

lemma smallSets_card_le (s : ℕ) :
    (smallSets (V := V) s).card ≤ (Fintype.card V + 1) ^ (s + 1) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (s + 1), (Finset.univ.powersetCard i : Finset (Finset V)).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (s + 1), (Fintype.card V).choose i := by
      simp only [Finset.card_powersetCard, Finset.card_univ]
    _ ≤ ∑ i ∈ Finset.range (s + 1), (Fintype.card V) ^ i :=
      Finset.sum_le_sum fun i _ => Nat.choose_le_pow _ _
    _ ≤ (Fintype.card V + 1) ^ s := sum_powers_le _ _
    _ ≤ (Fintype.card V + 1) ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)

lemma IsCutMatching.card_le_cover {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {B : Finset V} {E : Finset (V × V)}
    (h : IsCutMatching G B E) (T : Finset V)
    (hcover : ∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) : E.card ≤ (endpoints E ∩ T).card := by
  let f : V × V → V := fun e => if e.1 ∈ T then e.1 else e.2
  have hf : Set.InjOn f (E : Set (V × V)) := by
    intro e he e' he' heq
    by_contra hn
    have hh := h.2 he he' hn
    by_cases heT : e.1 ∈ T <;> by_cases heT' : e'.1 ∈ T
    · exact hh.1 (by simpa [f, heT, heT'] using heq)
    · have heq' : e.1 = e'.2 := by simpa [f, heT, heT'] using heq
      exact (h.1 e' he').2.1 (heq' ▸ (h.1 e he).1)
    · have heq' : e.2 = e'.1 := by simpa [f, heT, heT'] using heq
      exact (h.1 e he).2.1 (heq' ▸ (h.1 e' he').1)
    · exact hh.2 (by simpa [f, heT, heT'] using heq)
  have hsub : E.image f ⊆ endpoints E ∩ T := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    by_cases heT : e.1 ∈ T
    · simp only [f, ite_eq_left heT]
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨e, he, rfl⟩), heT⟩
    · simp only [f, ite_eq_right heT]
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, he, rfl⟩), (hcover e he).resolve_left heT⟩
  rw [← Finset.card_image_iff.mpr hf]
  exact Finset.card_le_card hsub

lemma separator_neighbors_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S A Z A' : Finset V} (hsep : SeparatorSplit G S A Z A') {v : V} (hv : v ∈ A) :
    (S.filter (G.Adj v)).card ≤ (A.filter (G.Adj v)).card + Z.card := by
  have hi : S.filter (G.Adj v) ⊆ A.filter (G.Adj v) ∪ Z := by
    intro w hw
    obtain ⟨hwS, hadj⟩ := Finset.mem_filter.mp hw
    rw [← hsep.union_eq] at hwS
    rcases Finset.mem_union.mp hwS with hawz | haw'
    · rcases Finset.mem_union.mp hawz with haw | hwz
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haw, hadj⟩)
      · exact Finset.mem_union_right _ hwz
    · exact False.elim (hsep.anticomplete v hv w haw' hadj)
  exact (Finset.card_le_card hi).trans (Finset.card_union_le _ _)

lemma SeparatorSplit.swap_test {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {S A Z A' : Finset V}
    (h : SeparatorSplit G S A Z A') : SeparatorSplit G S A' Z A := by
  refine ⟨?_, h.sep_right.symm, h.left_right.symm, h.left_sep.symm,
    h.right_nonempty, h.left_nonempty, ?_⟩
  · rw [← h.union_eq]; ext v; simp only [Finset.mem_union]; tauto
  · intro v hv w hw hadj
    exact h.anticomplete w hw v hv hadj.symm

lemma mem_neighborhoodUnion {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {R : Finset V} {v : V} :
    v ∈ neighborhoodUnion G R ↔ ∃ r ∈ R, G.Adj r v := by
  classical
  simp [neighborhoodUnion]

theorem separator_test (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℝ} {k : ℕ} (hn : 1 ≤ n) (hk : 64 ≤ k) (horder : (Fintype.card V : ℝ) ≤ n)
    {U A Z A' : Finset V} (hsep : SeparatorSplit G (Finset.univ \ U) A Z A')
    (hz : Z.card < k / 32)
    (hdeg : ∀ v, k ≤ 2 * (((Finset.univ \ U).filter (G.Adj v)).card)) :
    ∃ R : Finset V, R.card ≤ ⌈10 * (n / k) * Real.log (2 * n)⌉₊ ∧
      k / 8 ≤ (neighborhoodUnion G R).card ∧
      k / 8 ≤ (neighborhoodUnion G R)ᶜ.card ∧
      ∀ E, IsCutMatching G (neighborhoodUnion G R) E → E.card = k / 8 →
        k ≤ 32 * (endpoints E ∩ U).card := by
  classical
  have hkin : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hZreal : 32 * (Z.card : ℝ) < (k : ℝ) := by exact_mod_cast (show 32 * Z.card < k by omega)
  have hinternal : ∀ v ∈ A, (k : ℝ) / 3 ≤ ((A.filter (G.Adj v)).card : ℝ) := by
    intro v hv
    have hd := hdeg v
    have hh := separator_neighbors_le G hsep hv
    have hd' : (k : ℝ) ≤ 2 * ((((Finset.univ \ U).filter (G.Adj v)).card : ℕ) : ℝ) := by
      exact_mod_cast hd
    have hh' : ((((Finset.univ \ U).filter (G.Adj v)).card : ℕ) : ℝ) ≤
        ((A.filter (G.Adj v)).card : ℝ) + (Z.card : ℝ) := by exact_mod_cast hh
    linarith
  have hinternal' : ∀ v ∈ A', (k : ℝ) / 3 ≤ ((A'.filter (G.Adj v)).card : ℝ) := by
    intro v hv
    have hd := hdeg v
    have hh := separator_neighbors_le G (SeparatorSplit.swap_test hsep) hv
    have hd' : (k : ℝ) ≤ 2 * ((((Finset.univ \ U).filter (G.Adj v)).card : ℕ) : ℝ) := by
      exact_mod_cast hd
    have hh' : ((((Finset.univ \ U).filter (G.Adj v)).card : ℕ) : ℝ) ≤
        ((A'.filter (G.Adj v)).card : ℝ) + (Z.card : ℝ) := by exact_mod_cast hh
    linarith
  have ha : (k : ℝ) / 3 ≤ (A.card : ℝ) := by
    obtain ⟨v, hv⟩ := hsep.left_nonempty
    exact (hinternal v hv).trans (by exact_mod_cast Finset.card_filter_le A (G.Adj v))
  have ha' : (k : ℝ) / 3 ≤ (A'.card : ℝ) := by
    obtain ⟨v, hv⟩ := hsep.right_nonempty
    exact (hinternal' v hv).trans (by exact_mod_cast Finset.card_filter_le A' (G.Adj v))
  obtain ⟨R, hRA, hRcard, hRAcover⟩ := exists_neighborhood_cover G A hn hkin hsep.left_nonempty
    ((by exact_mod_cast Finset.card_le_univ A : (A.card : ℝ) ≤ Fintype.card V).trans horder) hinternal
  have hAB : A ⊆ neighborhoodUnion G R := by
    intro v hv
    obtain ⟨r, hr, hadj⟩ := hRAcover v hv
    exact mem_neighborhoodUnion.mpr ⟨r, hr, hadj.symm⟩
  have hAB' : A' ⊆ (neighborhoodUnion G R)ᶜ := by
    intro v hv
    apply Finset.mem_compl.mpr
    intro hmem
    obtain ⟨r, hr, hadj⟩ := mem_neighborhoodUnion.mp hmem
    exact hsep.anticomplete r (hRA hr) v hv hadj
  have hma : k / 8 ≤ A.card := by
    have hh : (k : ℝ) ≤ 3 * A.card := by linarith
    have hh' : k ≤ 3 * A.card := by exact_mod_cast hh
    omega
  have hma' : k / 8 ≤ A'.card := by
    have hh : (k : ℝ) ≤ 3 * A'.card := by linarith
    have hh' : k ≤ 3 * A'.card := by exact_mod_cast hh
    omega
  refine ⟨R, hRcard, hma.trans (Finset.card_le_card hAB),
    hma'.trans (Finset.card_le_card hAB'), ?_⟩
  intro E he hecard
  have hcover : ∀ e ∈ E, e.1 ∈ U ∪ Z ∨ e.2 ∈ U ∪ Z := by
    intro e heE
    by_contra hncover
    have hleft : e.1 ∉ U ∪ Z := fun hh => hncover (Or.inl hh)
    have hright : e.2 ∉ U ∪ Z := fun hh => hncover (Or.inr hh)
    have heS : e.1 ∈ Finset.univ \ U := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hh => hleft (Finset.mem_union_left _ hh)
    have heS' : e.2 ∈ Finset.univ \ U := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hh => hright (Finset.mem_union_left _ hh)
    have heA : e.1 ∈ A := by
      rw [← hsep.union_eq] at heS
      rcases Finset.mem_union.mp heS with hh | hh
      · exact (Finset.mem_union.mp hh).resolve_right (fun h => hleft (Finset.mem_union_right _ h))
      · exact False.elim ((Finset.mem_compl.mp (hAB' hh)) (he.1 e heE).1)
    have heA' : e.2 ∈ A' := by
      rw [← hsep.union_eq] at heS'
      rcases Finset.mem_union.mp heS' with hh | hh
      · rcases Finset.mem_union.mp hh with h | h
        · exact False.elim ((he.1 e heE).2.1 (hAB h))
        · exact False.elim (hright (Finset.mem_union_right _ h))
      · exact hh
    exact hsep.anticomplete e.1 heA e.2 heA' (he.1 e heE).2.2
  have hehe := he.card_le_cover (U ∪ Z) hcover
  have hsub : endpoints E ∩ (U ∪ Z) ⊆ (endpoints E ∩ U) ∪ Z := by
    intro v hv
    obtain ⟨hvE, hv⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvE, hv⟩)
    · exact Finset.mem_union_right _ hv
  have hsize := hehe.trans ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
  rw [hecard] at hsize
  omega

theorem cut_test (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℝ} {k : ℕ}
    (hk : 64 ≤ k) (horder : (Fintype.card V : ℝ) ≤ n)
    (hc : KConnectedOn G Finset.univ k) :
    ∃ F : Finset (Finset (V × V)),
      (F.card : ℝ) ≤ (n + 1) ^ (⌈10 * (n / k) * Real.log (2 * n)⌉₊ + 1) ∧
      (∀ E ∈ F, E.card = k / 8 ∧ ∃ B, IsCutMatching G B E) ∧
      ∀ U : Finset V,
        (∀ v, k ≤ 2 * ((Finset.univ \ U).filter (fun w => G.Adj v w)).card) →
        (∀ E ∈ F, 32 * (endpoints E ∩ U).card < k) →
        KConnectedOn G (Finset.univ \ U) (k / 32) := by
  classical
  have hord : k < Fintype.card V := by simpa using hc.1
  have hn : 1 ≤ n := (by exact_mod_cast (show 1 ≤ Fintype.card V by omega) :
    (1 : ℝ) ≤ Fintype.card V).trans horder
  let s := ⌈10 * (n / k) * Real.log (2 * n)⌉₊
  let goodR := (smallSets (V := V) s).filter fun R =>
    k / 8 ≤ (neighborhoodUnion G R).card ∧ k / 8 ≤ (neighborhoodUnion G R)ᶜ.card
  have hM : ∀ R : goodR, ∃ E, IsCutMatching G (neighborhoodUnion G R.val) E ∧ E.card = k / 8 := by
    intro R
    obtain ⟨_, hleft, hright⟩ := Finset.mem_filter.mp R.property
    exact exists_cut_matching G _ hc (by omega) hleft hright
  choose f hf hcard using hM
  let F := Finset.univ.image f
  have hfF : ∀ R : goodR, f R ∈ F := fun R => Finset.mem_image.mpr ⟨R, Finset.mem_univ _, rfl⟩
  refine ⟨F, ?_, ?_, ?_⟩
  · have hnum : F.card ≤ (Fintype.card V + 1) ^ (s + 1) := by
      calc
        F.card ≤ (Finset.univ : Finset goodR).card := Finset.card_image_le
        _ = goodR.card := by simp
        _ ≤ (smallSets (V := V) s).card := Finset.card_filter_le _ _
        _ ≤ _ := smallSets_card_le s
    have hreal : (F.card : ℝ) ≤ ((Fintype.card V : ℝ) + 1) ^ (s + 1) := by exact_mod_cast hnum
    exact hreal.trans (by gcongr)
  · intro E he
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp he
    exact ⟨hcard R, neighborhoodUnion G R.val, hf R⟩
  · intro U hdeg htest
    have hresord : k / 32 < (Finset.univ \ U).card := by
      have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      let v : V := Classical.choice inferInstance
      have hd := hdeg v
      have hi : ((Finset.univ \ U).filter (fun w => G.Adj v w)).card ≤
          (Finset.univ \ U).card := Finset.card_filter_le _ _
      omega
    by_contra hres
    obtain ⟨A, Z, A', hz, hsep⟩ := exists_separator G (Finset.univ \ U) hresord hres
    obtain ⟨R, hR, hleft, hright, hdetect⟩ := separator_test G hn hk horder hsep hz hdeg
    have hRg : R ∈ goodR := Finset.mem_filter.mpr ⟨mem_smallSets.mpr hR, hleft, hright⟩
    let r : goodR := ⟨R, hRg⟩
    have hlarge := hdetect (f r) (hf r) (hcard r)
    have hsmall := htest (f r) (hfF r)
    omega

end ConnectivityTests

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.DistrictPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

lemma exists_rotation_few_conflicts {V : Type} [DecidableEq V]
    (S : Finset V) {n k : ℕ} (hn : k ≤ n) (hk : 0 < k)
    (d : V → Fin n) (R : Fin n ↪ Fin n) (B : V → Finset (Fin n))
    (hbudget : ∑ v ∈ S, (B v).card ≤ 2 * k ^ 2) :
    ∃ j : Fin n, (S.filter (fun v => R (d v + j) ∈ B v)).card ≤ 2 * k := by
  classical
  have : NeZero n := ⟨by omega⟩
  have hcount (v : V) :
      (Finset.univ.filter (fun j : Fin n => R (d v + j) ∈ B v)).card ≤ (B v).card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin n => R (d v + j))
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro i hi j hj heq
      exact add_left_cancel (R.injective heq)
  by_contra h
  push Not at h
  have hs : ∑ j : Fin n, (S.filter (fun v => R (d v + j) ∈ B v)).card ≤ 2 * k ^ 2 := by
    calc
      _ = ∑ v ∈ S, (Finset.univ.filter (fun j : Fin n => R (d v + j) ∈ B v)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
      _ ≤ ∑ v ∈ S, (B v).card := Finset.sum_le_sum (fun v _ => hcount v)
      _ ≤ _ := hbudget
  have hnpos : 0 < n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  have ht := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j (_ : j ∈ Finset.univ) => h j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at ht
  have hm : 2 * k ^ 2 ≤ n * (2 * k) := by nlinarith
  omega

lemma extend_from_ordinary {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) {k m : ℕ}
    (B : V → Finset (Fin (m + 6 * k))) (φ : V → Fin (m + 6 * k))
    (hk : 1 ≤ k) (hAS : A ⊆ S)
    (hcolor : (G.induce (↑S : Set V)).Colorable m)
    (hφ : ValidOn G A (fun _ => Finset.univ) φ)
    (hB : ∀ v ∈ S \ A, (B v).card < k)
    (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    ∃ c, ValidOn G S (fun _ => Finset.univ) c ∧ (∀ v ∈ A, c v = φ v) ∧
      ∀ v ∈ S \ A, c v ∉ B v := by
  classical
  obtain ⟨d₀⟩ := hcolor
  by_cases hS : S = ∅
  · subst S
    have hA : A = ∅ := Finset.subset_empty.mp hAS
    subst A
    exact ⟨φ, ⟨by simp, by simp [ProperOn]⟩, by simp, by simp⟩
  have hmc : 0 < m := by
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact (d₀ ⟨v, hv⟩).pos
  have hAc := constraintCost_card_bound hk hAS hbudget
  let P : Finset (Fin (m + 6 * k)) := Finset.univ \ A.image φ
  have hPc : m + 4 * k ≤ P.card := by
    have hc := Finset.card_image_le (f := φ) (s := A)
    have hd : (Finset.univ : Finset (Fin (m + 6 * k))).card ≤
        P.card + (A.image φ).card := Finset.card_le_card_sdiff_add_card
    simp only [Finset.card_univ, Fintype.card_fin] at hd
    omega
  have : NeZero P.card := ⟨by omega⟩
  have : NeZero m := ⟨by omega⟩
  let e : Fin P.card ≃ ↥P := (Finset.equivFin P).symm
  let d : V → Fin m := fun v => if hv : v ∈ S then d₀ ⟨v, hv⟩ else 0
  let f : V → Fin P.card := fun v => Fin.castLE (by omega : m ≤ P.card) (d v)
  let B' : V → Finset (Fin P.card) := fun v =>
    Finset.univ.filter (fun j => (e j).val ∈ B v)
  have hB' (v : V) : (B' v).card ≤ (B v).card := by
    apply Finset.card_le_card_of_injOn (fun i => (e i).val)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj heq
      exact e.injective (Subtype.ext heq)
  have hsum : ∑ v ∈ S \ A, (B' v).card ≤ 2 * k ^ 2 := by
    have hh := hbudget
    rw [constraintCost_eq S A k B hAS] at hh
    exact (Finset.sum_le_sum (fun v _ => hB' v)).trans (by omega)
  obtain ⟨j, hj⟩ := exists_rotation_few_conflicts (S \ A) (by omega : k ≤ P.card)
    (by omega : 0 < k) f (Function.Embedding.refl _) B' hsum
  let c₀ : V → Fin (m + 6 * k) := fun v => (e (f v + j)).val
  let D := (S \ A).filter (fun v => c₀ v ∈ B v)
  have hDc : D.card ≤ 2 * k := by simpa [D, c₀, B'] using hj
  have hDS : D ⊆ S \ A := Finset.filter_subset _ _
  have hc₀A (v : V) : c₀ v ∉ A.image φ := (Finset.mem_sdiff.mp (e (f v + j)).property).2
  have hc₀proper : ProperOn G S c₀ := by
    intro v hv w hw hadj heq
    have he : f v + j = f w + j := e.injective (Subtype.ext heq)
    have hf : d v = d w := Fin.castLE_injective _ (add_right_cancel he)
    have hvw := d₀.valid (show (G.induce (↑S : Set V)).Adj ⟨v,hv⟩ ⟨w,hw⟩ from hadj)
    apply hvw
    simpa [d, hv, hw] using hf
  have hc₀card : (S.image c₀).card ≤ m := by
    let g : Fin m → Fin (m + 6 * k) := fun a => (e (Fin.castLE (by omega) a + j)).val
    have hsub : S.image c₀ ⊆ Finset.univ.image g := by
      intro a ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨d v, Finset.mem_univ _, rfl⟩
    exact (Finset.card_le_card hsub).trans (by simpa using (Finset.card_image_le (s := Finset.univ) (f := g)))
  let L' : (↑D : Set V) → Finset (Fin (m + 6 * k)) := fun v =>
    Finset.univ \ (S.image c₀ ∪ A.image φ ∪ B v)
  have hL' : ∀ v, D.card ≤ (L' v).card := by
    intro v
    have hb := hB v (hDS v.property)
    have hu₁ := Finset.card_union_le (S.image c₀) (A.image φ)
    have hu₂ := Finset.card_union_le (S.image c₀ ∪ A.image φ) (B v)
    have ha := Finset.card_image_le (s := A) (f := φ)
    have hd : (Finset.univ : Finset (Fin (m + 6 * k))).card ≤
        (L' v).card + (S.image c₀ ∪ A.image φ ∪ B v).card := Finset.card_le_card_sdiff_add_card
    simp only [Finset.card_univ, Fintype.card_fin] at hd
    omega
  have q := choosable_card (G.induce (↑D : Set V))
  rw [show Fintype.card (↑D : Set V) = D.card from Fintype.card_coe D] at q
  obtain ⟨cD, hcD, hpD⟩ := q _ L' hL'
  let c : V → Fin (m + 6 * k) := fun v => if hv : v ∈ D then cD ⟨v,hv⟩ else
    if v ∈ A then φ v else c₀ v
  have hDcA : Disjoint D A := Finset.disjoint_left.mpr (fun v hv ha => (Finset.mem_sdiff.mp (hDS hv)).2 ha)
  have hDavoid (v : V) (hv : v ∈ D) :
      c v ∉ S.image c₀ ∧ c v ∉ A.image φ ∧ c v ∉ B v := by
    have hh := hcD ⟨v,hv⟩
    simpa only [L', Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      not_or, and_assoc, c, dite_eq_left hv] using hh
  have hcA : ∀ v ∈ A, c v = φ v := by
    intro v hv
    simp [c, Finset.disjoint_right.mp hDcA hv, hv]
  have hcN (v : V) (hvD : v ∉ D) (hvA : v ∉ A) : c v = c₀ v := by simp [c,hvD,hvA]
  refine ⟨c, ⟨by simp, ?_⟩, hcA, ?_⟩
  · intro v hv w hw hadj
    by_cases hvD : v ∈ D <;> by_cases hwD : w ∈ D
    · simpa only [c, dite_eq_left hvD, dite_eq_left hwD] using
        hpD (v := ⟨v,hvD⟩) (w := ⟨w,hwD⟩) hadj
    · by_cases hwA : w ∈ A
      · rw [hcA w hwA]
        exact fun heq => (hDavoid v hvD).2.1 (heq ▸ Finset.mem_image.mpr ⟨w,hwA,rfl⟩)
      · rw [hcN w hwD hwA]
        intro heq
        apply (hDavoid v hvD).1
        rw [heq]
        exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
    · by_cases hvA : v ∈ A
      · rw [hcA v hvA]
        intro heq
        apply (hDavoid w hwD).2.1
        rw [←heq]
        exact Finset.mem_image.mpr ⟨v,hvA,rfl⟩
      · rw [hcN v hvD hvA]
        intro heq
        apply (hDavoid w hwD).1
        rw [←heq]
        exact Finset.mem_image.mpr ⟨v,hv,rfl⟩
    · by_cases hvA : v ∈ A <;> by_cases hwA : w ∈ A
      · rw [hcA v hvA, hcA w hwA]
        exact hφ.2 hvA hwA hadj
      · rw [hcA v hvA, hcN w hwD hwA]
        intro heq
        apply hc₀A w
        rw [←heq]
        exact Finset.mem_image.mpr ⟨v,hvA,rfl⟩
      · rw [hcN v hvD hvA, hcA w hwA]
        intro heq
        apply hc₀A v
        rw [heq]
        exact Finset.mem_image.mpr ⟨w,hwA,rfl⟩
      · rw [hcN v hvD hvA, hcN w hwD hwA]
        exact hc₀proper hv hw hadj
  · intro v hv
    by_cases hvD : v ∈ D
    · exact (hDavoid v hvD).2.2
    · rw [hcN v hvD (Finset.mem_sdiff.mp hv).2]
      exact fun hh => hvD (Finset.mem_filter.mpr ⟨hv,hh⟩)

theorem ordinary_constrained_coloring_on {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) {k m : ℕ}
    (B : V → Finset (Fin (m + 6 * k))) (φ : V → Fin (m + 6 * k))
    (hk : 1 ≤ k) (hAS : A ⊆ S)
    (hconn : ∀ T ⊆ S, KConnectedOn G T k → (G.induce (↑T : Set V)).Colorable m)
    (hφ : ValidOn G A (fun _ => Finset.univ) φ)
    (hB : ∀ v ∈ S \ A, (B v).card < k)
    (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    ∃ c, ValidOn G S (fun _ => Finset.univ) c ∧ (∀ v ∈ A, c v = φ v) ∧
      ∀ v ∈ S \ A, c v ∉ B v := by
  classical
  let : DecidableEq (Fin (m + 6 * k)) := Classical.decEq _
  let L : V → Finset (Fin (m + 6 * k)) := fun _ => Finset.univ
  have hL (v : V) : m + 6 * k ≤ (L v).card := by simp [L]
  induction S using Finset.strongInductionOn generalizing A B φ with
  | _ S ih =>
    have hAc : A.card ≤ 2 * k := constraintCost_card_bound hk hAS hbudget
    by_cases hsmall : S.card ≤ 2 * k
    · have hchoose : Choosable (G.induce (↑(S \ A) : Set V)) (S \ A).card := by
        have hh := choosable_card (G.induce (↑(S \ A) : Set V))
        change Choosable _ (Fintype.card ↥(S \ A)) at hh
        rw [Fintype.card_coe] at hh
        exact hh
      apply extend_from_choosable G S A L B φ hφ hchoose
      intro v hv
      have hh := hB v hv
      have hl := hL v
      have heq := Finset.card_sdiff_add_card_eq_card hAS
      omega
    by_cases hc : KConnectedOn G S k
    · exact extend_from_ordinary G S A B φ hk hAS
        (hconn S Finset.Subset.rfl hc) hφ hB hbudget
    obtain ⟨V₁, Z, V₂, hZk, hs, hbal⟩ :=
      exists_balanced_separator G S A B (by omega) hc hbudget
    have hS₁ := hs.left_union_subset
    have hS₂ := hs.swap.left_union_subset
    let A₁ := A ∩ (V₁ ∪ Z)
    let B₁ := extraForbidden Z B ((A ∩ V₂).image φ)
    have hA₁ : A₁ ⊆ V₁ ∪ Z := Finset.inter_subset_right
    have hbudget₁ : constraintCost (V₁ ∪ Z) k A₁ B₁ ≤ 2 * k ^ 2 :=
      (first_side_cost hs A B φ hZk.le).trans hbudget
    have hB₁ : ∀ v ∈ (V₁ ∪ Z) \ A₁, (B₁ v).card < 3 * k := by
      intro v hv
      have hvS₁ := (Finset.mem_sdiff.mp hv).1
      have hvA : v ∉ A := fun ha => (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mpr ⟨ha, hvS₁⟩)
      have hb := hB v (Finset.mem_sdiff.mpr ⟨hS₁ hvS₁, hvA⟩)
      have hd : ((A ∩ V₂).image φ).card ≤ 2 * k :=
        Finset.card_image_le.trans ((Finset.card_le_card Finset.inter_subset_left).trans hAc)
      by_cases hz : v ∈ Z
      · have hu := Finset.card_union_le (B v) ((A ∩ V₂).image φ)
        simp only [B₁, extraForbidden, ite_eq_left hz]
        omega
      · simpa only [B₁, extraForbidden, ite_eq_right hz] using (show (B v).card < 3 * k by omega)
    obtain ⟨A₁', φ₁, hA₁A₁', hA₁'S₁, hφ₁, hext₁, hav₁, hlow₁, hcost₁⟩ :=
      promote_constraints G (V₁ ∪ Z) A₁ L B₁ φ hk hA₁
        (fun v _ => hL v) (hφ.mono Finset.inter_subset_left) hB₁ hbudget₁
    obtain ⟨c₁, hc₁, hc₁ext, hc₁av⟩ :=
      ih (V₁ ∪ Z) hs.left_union_ssubset A₁' B₁ φ₁ hA₁'S₁
        (fun T hT => hconn T (hT.trans hS₁))
        hφ₁ hlow₁ (hcost₁.trans hbudget₁)
    have hc₁orig : ∀ v ∈ A₁, c₁ v = φ v := fun v hv =>
      (hc₁ext v (hA₁A₁' hv)).trans (hext₁ v hv)
    have hc₁avoid : ∀ v ∈ (V₁ ∪ Z) \ A₁, c₁ v ∉ B₁ v := by
      intro v hv
      by_cases ha : v ∈ A₁'
      · rw [hc₁ext v ha]
        exact hav₁ v (Finset.mem_sdiff.mpr ⟨ha, (Finset.mem_sdiff.mp hv).2⟩)
      · exact hc₁av v (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, ha⟩)
    have hcompat : ∀ v ∈ Z, ∀ w ∈ A ∩ V₂, G.Adj v w → c₁ v ≠ φ w := by
      intro v hv w hw hadj
      have hvS₁ : v ∈ V₁ ∪ Z := Finset.mem_union_right _ hv
      by_cases ha : v ∈ A
      · rw [hc₁orig v (Finset.mem_inter.mpr ⟨ha, hvS₁⟩)]
        exact hφ.2 ha (Finset.mem_inter.mp hw).1 hadj
      · intro heq
        have hva₁ : v ∉ A₁ := fun hh => ha (Finset.mem_inter.mp hh).1
        apply hc₁avoid v (Finset.mem_sdiff.mpr ⟨hvS₁, hva₁⟩)
        rw [heq]
        simp only [B₁, extraForbidden, ite_eq_left hv]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    obtain ⟨φ₂, hφ₂, hφ₂Z, hφ₂D⟩ := separator_precolor hs A L φ c₁ hφ hc₁ hcompat
    let A₂ := Z ∪ (A ∩ V₂)
    have hA₂S₂ : A₂ ⊆ V₂ ∪ Z := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_right _ hv
      · exact Finset.mem_union_left _ (Finset.mem_inter.mp hv).2
    have hbudget₂ : constraintCost (V₂ ∪ Z) k A₂ B ≤ 2 * k ^ 2 := by
      rw [show A₂ = Z ∪ (A ∩ V₂) from rfl, second_side_cost hs A B k]
      have hmul : k * Z.card ≤ k ^ 2 := by
        calc
          k * Z.card ≤ k * k := Nat.mul_le_mul_left k hZk.le
          _ = k ^ 2 := by ring
      omega
    have hB₂ : ∀ v ∈ (V₂ ∪ Z) \ A₂, (B v).card < k := by
      intro v hv
      have hvS₂ := (Finset.mem_sdiff.mp hv).1
      have hn := (Finset.mem_sdiff.mp hv).2
      have hnZ : v ∉ Z := fun hh => hn (Finset.mem_union_left _ hh)
      have hvV₂ : v ∈ V₂ := (Finset.mem_union.mp hvS₂).resolve_right hnZ
      have hnA : v ∉ A := fun hh => hn (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hh, hvV₂⟩))
      exact hB v (Finset.mem_sdiff.mpr ⟨hS₂ hvS₂, hnA⟩)
    obtain ⟨c₂, hc₂, hc₂ext, hc₂av⟩ :=
      ih (V₂ ∪ Z) hs.swap.left_union_ssubset A₂ B φ₂ hA₂S₂
        (fun T hT => hconn T (hT.trans hS₂))
        hφ₂ hB₂ hbudget₂
    have hagree : ∀ v ∈ Z, c₁ v = c₂ v := by
      intro v hv
      rw [hc₂ext v (Finset.mem_union_left _ hv), hφ₂Z v hv]
    obtain ⟨c, hc, hcS₁, hcS₂⟩ := hs.glue hc₁ hc₂ hagree
    refine ⟨c, hc, ?_, ?_⟩
    · intro v hv
      have hvS := hAS hv
      rw [← hs.union_eq] at hvS
      rcases Finset.mem_union.mp hvS with hvS₁ | hvV₂
      · rw [hcS₁ v hvS₁]
        exact hc₁orig v (Finset.mem_inter.mpr ⟨hv, hvS₁⟩)
      · have hvD : v ∈ A ∩ V₂ := Finset.mem_inter.mpr ⟨hv, hvV₂⟩
        rw [hcS₂ v (Finset.mem_union_left _ hvV₂),
          hc₂ext v (Finset.mem_union_right _ hvD), hφ₂D v hvD]
    · intro v hv
      have hvS := (Finset.mem_sdiff.mp hv).1
      have hnA := (Finset.mem_sdiff.mp hv).2
      rw [← hs.union_eq] at hvS
      rcases Finset.mem_union.mp hvS with hvS₁ | hvV₂
      · rw [hcS₁ v hvS₁]
        have hnA₁ : v ∉ A₁ := fun hh => hnA (Finset.mem_inter.mp hh).1
        exact fun hh => hc₁avoid v (Finset.mem_sdiff.mpr ⟨hvS₁, hnA₁⟩)
          (extraForbidden_subset Z B ((A ∩ V₂).image φ) v hh)
      · have hvS₂ : v ∈ V₂ ∪ Z := Finset.mem_union_left _ hvV₂
        have hnZ : v ∉ Z := fun hh => Finset.disjoint_left.mp hs.sep_right hh hvV₂
        have hnA₂ : v ∉ A₂ := by
          intro hh
          rcases Finset.mem_union.mp hh with hh | hh
          · exact hnZ hh
          · exact hnA (Finset.mem_inter.mp hh).1
        rw [hcS₂ v hvS₂]
        exact hc₂av v (Finset.mem_sdiff.mpr ⟨hvS₂, hnA₂⟩)

theorem colorable_of_connected_induced {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k m : ℕ} (hk : 1 ≤ k)
    (hconn : ∀ T : Finset V, KConnectedOn G T k →
      (G.induce (↑T : Set V)).Colorable m) : G.Colorable (m + 6 * k) := by
  classical
  have : NeZero (m + 6 * k) := ⟨by omega⟩
  obtain ⟨c, hc, _, _⟩ := ordinary_constrained_coloring_on G Finset.univ ∅
    (fun _ => ∅) (fun _ => 0) hk (Finset.empty_subset _)
    (fun T _ => hconn T) ⟨by simp, by simp [ProperOn]⟩
    (by intro v hv; simpa using (show 0 < k by omega))
    (by simp [constraintCost, vertexCost])
  exact ⟨SimpleGraph.Coloring.mk c (fun {_ _} h => hc.2 (Finset.mem_univ _) (Finset.mem_univ _) h)⟩

lemma ordinary_chromatic_le_iff {V : Type} [Fintype V] (G : SimpleGraph V) (m : ℕ) :
    G.chromaticNumber.toNat ≤ m ↔ G.Colorable m := by
  constructor
  · exact fun h => SimpleGraph.Colorable.mono h G.colorable_chromaticNumber_of_fintype
  · intro h
    have hh := h.chromaticNumber_le
    exact ENat.toNat_le_of_le_natCast hh

theorem ordinary_connectivity_extraction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hlarge : 6 * k < G.chromaticNumber.toNat) :
    ∃ T : Finset V, KConnectedOn G T k ∧
      G.chromaticNumber.toNat - 6 * k ≤ (G.induce (↑T : Set V)).chromaticNumber.toNat := by
  classical
  by_contra hn
  push Not at hn
  let m := G.chromaticNumber.toNat - 6 * k - 1
  have hconn : ∀ T : Finset V, KConnectedOn G T k →
      (G.induce (↑T : Set V)).Colorable m := by
    intro T hT
    apply (ordinary_chromatic_le_iff _ _).mp
    have hh := hn T hT
    dsimp [m]
    omega
  have hcolor := colorable_of_connected_induced G hk hconn
  have hbound := (ordinary_chromatic_le_iff G _).mpr hcolor
  dsimp [m] at hbound
  omega

open SimpleGraph

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Fractional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

lemma Stable.mono {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {I J : Finset V} (h : Stable G I) (hJI : J ⊆ I) :
    Stable G J := fun v hv w hw => h v (hJI hv) w (hJI hw)

lemma cost_nonneg {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) : 0 ≤ cost μ :=
  Finset.sum_nonneg (fun I _ => h.1 I)

lemma singletonWeights_cover (G : SimpleGraph V) : Cover G singletonWeights := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro I
    exact Finset.sum_nonneg fun v _ => by split_ifs <;> norm_num
  · intro I hn
    apply Finset.sum_eq_zero
    intro v _
    rw [ite_eq_right]
    rintro rfl
    exact hn (stable_singleton G v)
  · intro v
    have hpos (I : Finset V) : 0 ≤ (if v ∈ I then singletonWeights I else 0) := by
      split_ifs
      · exact Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num
      · exact le_rfl
    have h := Finset.single_le_sum (fun I _ => hpos I) (Finset.mem_univ ({v} : Finset V))
    have hm : singletonWeights ({v} : Finset V) = 1 := by
      simp [singletonWeights,Finset.singleton_inj]
    simpa [hm] using h

lemma singletonWeights_cost : cost (singletonWeights (V := V)) = Fintype.card V := by
  classical
  simp only [cost,singletonWeights]
  rw [Finset.sum_comm]
  simp

lemma costs_nonempty (G : SimpleGraph V) :
    ({c : ℝ | ∃ μ, Cover G μ ∧ cost μ = c} : Set ℝ).Nonempty :=
  ⟨_,singletonWeights,singletonWeights_cover G,rfl⟩

lemma costs_bddBelow (G : SimpleGraph V) :
    BddBelow {c : ℝ | ∃ μ, Cover G μ ∧ cost μ = c} := by
  refine ⟨0,?_⟩
  rintro c ⟨μ,hμ,rfl⟩
  exact cost_nonneg hμ

lemma number_le_cost {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) :
    number G ≤ cost μ := csInf_le (costs_bddBelow G) ⟨μ,h,rfl⟩

lemma number_le_card (G : SimpleGraph V) : number G ≤ Fintype.card V := by
  simpa only [singletonWeights_cost] using number_le_cost (singletonWeights_cover G)

lemma Cover.clamp {G : SimpleGraph V} {μ : Finset V → ℝ} (h : Cover G μ) :
    Cover G (fun I => min (μ I) 1) := by
  classical
  refine ⟨fun I => le_min (h.1 I) zero_le_one,?_,?_⟩
  · intro I hn
    change min (μ I) 1 = 0
    rw [h.2.1 I hn]
    norm_num
  · intro v
    by_cases hall : ∀ I, v ∈ I → μ I ≤ 1
    · have heq : (∑ I, if v ∈ I then min (μ I) 1 else 0) =
          ∑ I, if v ∈ I then μ I else 0 := by
        apply Finset.sum_congr rfl
        intro I _
        split_ifs with hv
        · rw [min_eq_left (hall I hv)]
        · rfl
      rw [heq]
      exact h.2.2 v
    · push Not at hall
      obtain ⟨I,hv,hI⟩ := hall
      have hs := Finset.single_le_sum (s := (Finset.univ : Finset (Finset V)))
        (f := fun J => if v ∈ J then min (μ J) 1 else 0)
        (fun J _ => by split_ifs; exact le_min (h.1 J) zero_le_one; exact le_rfl)
        (Finset.mem_univ I)
      simpa only [ite_eq_left hv,min_eq_right (le_of_lt hI)] using hs

lemma cover_isClosed (G : SimpleGraph V) : IsClosed {μ : Finset V → ℝ | Cover G μ} := by
  change IsClosed ({μ : Finset V → ℝ | ∀ I, 0 ≤ μ I} ∩
    ({μ | ∀ I, ¬Stable G I → μ I = 0} ∩
     {μ | ∀ v, 1 ≤ ∑ I, if v ∈ I then μ I else 0}))
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun I => isClosed_le continuous_const (continuous_apply I)
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro I
    by_cases h : Stable G I
    · simp only [h,not_true_eq_false,false_implies,Set.ofPred_true]
      exact isClosed_univ
    · simp only [h,not_false_eq_true,true_implies]
      exact isClosed_eq (continuous_apply I) continuous_const
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    apply continuous_finsetSum
    intro I _
    by_cases hv : v ∈ I
    · simpa only [ite_eq_left hv] using continuous_apply I
    · simp only [ite_eq_right hv]
      exact continuous_const

lemma cost_continuous {V : Type} [Fintype V] [DecidableEq V] : Continuous (cost (V := V)) := by
  apply continuous_finsetSum
  intro I _
  exact continuous_apply I

theorem optimum_exists (G : SimpleGraph V) : ∃ μ, Cover G μ ∧ cost μ = number G := by
  classical
  let K : Set ((Finset V) → ℝ) := Set.Icc 0 1 ∩ {μ | Cover G μ}
  have hcomp : IsCompact K := isCompact_Icc.inter_right (cover_isClosed G)
  have hne : K.Nonempty := by
    refine ⟨fun I => min (singletonWeights I) 1,⟨?_,?_⟩,(singletonWeights_cover G).clamp⟩
    · intro I
      exact le_min ((singletonWeights_cover G).1 I) zero_le_one
    · intro I
      exact min_le_right _ _
  obtain ⟨μ,hμ,hmin⟩ := hcomp.exists_isMinOn hne cost_continuous.continuousOn
  refine ⟨μ,hμ.2,le_antisymm ?_ (number_le_cost hμ.2)⟩
  apply le_csInf (costs_nonempty G)
  rintro c ⟨ν,hν,rfl⟩
  apply (hmin (show (fun I => min (ν I) 1) ∈ K from ?_)).trans
    (Finset.sum_le_sum (fun I _ => min_le_left (ν I) 1))
  exact ⟨⟨fun I => le_min (hν.1 I) zero_le_one,fun I => min_le_right _ _⟩,hν.clamp⟩

lemma number_le_iff (G : SimpleGraph V) (r : ℝ) :
    number G ≤ r ↔ ∃ μ, Cover G μ ∧ cost μ ≤ r := by
  constructor
  · intro h
    obtain ⟨μ,hμ,heq⟩ := optimum_exists G
    exact ⟨μ,hμ,heq ▸ h⟩
  · rintro ⟨μ,hμ,hcost⟩
    exact (number_le_cost hμ).trans hcost

lemma Dual.le_one {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w) (v : V) : w v ≤ 1 := by
  simpa using hw.2 {v} (stable_singleton G v)

lemma dual_zero {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Dual G (fun _ => 0) := by
  simp [Dual]

lemma dual_isClosed {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : IsClosed {w : V → ℝ | Dual G w} := by
  classical
  change IsClosed ({w : V → ℝ | ∀ v, 0 ≤ w v} ∩
    {w | ∀ I, Stable G I → ∑ v ∈ I, w v ≤ 1})
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_apply v)
  · rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro I
    by_cases hI : Stable G I
    · simp only [hI,true_implies]
      apply isClosed_le _ continuous_const
      exact continuous_finsetSum I (fun v _ => continuous_apply v)
    · simp only [hI,false_implies,Set.ofPred_true]
      exact isClosed_univ

lemma dual_maximum (G : SimpleGraph V) :
    ∃ w, Dual G w ∧ ∀ z, Dual G z → ∑ v, z v ≤ ∑ v, w v := by
  classical
  have hc : IsCompact {w : V → ℝ | Dual G w} :=
    isCompact_Icc.of_isClosed_subset (dual_isClosed G) (by
      intro w hw
      exact ⟨hw.1,hw.le_one⟩)
  exact hc.exists_isMaxOn ⟨_,dual_zero G⟩
    (continuous_finsetSum Finset.univ (fun v _ => continuous_apply v)).continuousOn

lemma weak_duality {G : SimpleGraph V} {μ : Finset V → ℝ} {w : V → ℝ}
    (hμ : Cover G μ) (hw : Dual G w) : ∑ v, w v ≤ cost μ := by
  classical
  calc
    ∑ v, w v ≤ ∑ v, w v * ∑ I, if v ∈ I then μ I else 0 := by
      apply Finset.sum_le_sum
      intro v _
      simpa using mul_le_mul_of_nonneg_left (hμ.2.2 v) (hw.1 v)
    _ = ∑ I, μ I * ∑ v ∈ I, w v := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I _
      simp only [mul_ite,mul_zero,mul_comm (w _) (μ I),← Finset.mul_sum]
      simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
      rw [Finset.mul_sum]
    _ ≤ cost μ := by
      apply Finset.sum_le_sum
      intro I _
      by_cases hI : Stable G I
      · simpa using mul_le_mul_of_nonneg_left (hw.2 I hI) (hμ.1 I)
      · simp [hμ.2.1 I hI]

lemma dual_le_number {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w) :
    ∑ v, w v ≤ number G := by
  obtain ⟨μ,hμ,heq⟩ := optimum_exists G
  rw [← heq]
  exact weak_duality hμ hw

lemma constant_mem_hull_cover (G : SimpleGraph V) {r : ℝ} (hr : 0 < r)
    (hx : (fun _ : V => 1 / r) ∈ convexHull ℝ {x | ∃ I, Stable G I ∧ indicator I = x}) :
    ∃ μ, Cover G μ ∧ cost μ = r := by
  classical
  obtain ⟨ι,hi,w,z,hw,hws,hz,hx⟩ := mem_convexHull_iff_exists_fintype.mp hx
  choose I hI heq using hz
  let μ : Finset V → ℝ := fun J => ∑ i, if I i = J then r * w i else 0
  have hmass : cost μ = r := by
    unfold cost μ
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,← Finset.mul_sum,hws,mul_one]
  refine ⟨μ,⟨?_,?_,?_⟩,hmass⟩
  · intro J
    exact Finset.sum_nonneg fun i _ => by split_ifs; exact mul_nonneg hr.le (hw i); exact le_rfl
  · intro J hn
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right]
    intro he
    exact hn (he ▸ hI i)
  · intro v
    have hxv := congrFun hx v
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hxv
    have hzv (i : ι) : z i v = if v ∈ I i then 1 else 0 := congrFun (heq i).symm v
    simp only [hzv,mul_ite,mul_one,mul_zero] at hxv
    have hm : (∑ J, if v ∈ J then μ J else 0) = r * ∑ i, if v ∈ I i then w i else 0 := by
      have hdis (J : Finset V) : (if v ∈ J then μ J else 0) =
          ∑ i, if v ∈ J then (if I i = J then r * w i else 0) else 0 := by
        by_cases h : v ∈ J <;> simp [h,μ]
      simp only [hdis]
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have heq : (fun J : Finset V => if v ∈ J then if I i = J then r * w i else 0 else 0) =
          (fun J => if I i = J then (if v ∈ I i then r * w i else 0) else 0) := by
        funext J
        by_cases hh : I i = J
        · subst J; simp
        · simp [hh]
      rw [heq]
      simp [mul_ite]
    rw [hm,hxv]
    exact le_of_eq (by field_simp)

lemma functional_eq_sum (f : StrongDual ℝ (V → ℝ)) (x : V → ℝ) :
    f x = ∑ v, x v * f (Pi.single v 1) := by
  classical
  have hx : x = ∑ v, x v • Pi.single v 1 := by
    ext u
    simp [Pi.single_apply,smul_eq_mul,Finset.sum_apply]
  conv_lhs => rw [hx]
  simp

lemma functional_indicator (f : StrongDual ℝ (V → ℝ)) (I : Finset V) :
    f (indicator I) = ∑ v ∈ I, f (Pi.single v 1) := by
  classical
  rw [functional_eq_sum]
  simp only [indicator,ite_mul,one_mul,zero_mul,← Finset.sum_filter,
    Finset.filter_mem_eq_inter,Finset.univ_inter]

lemma dual_above (G : SimpleGraph V) {r : ℝ} (hr : 0 < r) (hrn : r < number G) :
    ∃ w, Dual G w ∧ r < ∑ v, w v := by
  classical
  let S : Set (V → ℝ) := {x | ∃ I, Stable G I ∧ indicator I = x}
  have hfin : S.Finite := (Set.finite_range (indicator (V := V))).subset (by
    rintro x ⟨I,hI,rfl⟩; exact ⟨I,rfl⟩)
  have hn : (fun _ : V => 1/r) ∉ convexHull ℝ S := by
    intro hx
    obtain ⟨μ,hμ,hm⟩ := constant_mem_hull_cover G hr hx
    have hh := number_le_cost hμ
    linarith
  obtain ⟨f,u,hf,hu⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ S) (hfin.isClosed_convexHull ℝ) hn
  have hi (I : Finset V) (hI : Stable G I) :
      ∑ v ∈ I, f (Pi.single v 1) < u := by
    rw [← functional_indicator]
    exact hf _ (subset_convexHull ℝ S ⟨I,hI,rfl⟩)
  have hup : 0 < u := by simpa using hi ∅ (stable_empty G)
  let a : V → ℝ := fun v => f (Pi.single v 1)
  let w : V → ℝ := fun v => max (a v) 0 / u
  refine ⟨w,⟨fun v => div_nonneg (le_max_right _ _) hup.le,?_⟩,?_⟩
  · intro I hI
    have hm : (∑ v ∈ I, max (a v) 0) = ∑ v ∈ I.filter (fun v => 0 ≤ a v), a v := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : 0 ≤ a v
      · simp [hv]
      · simp [hv,max_eq_right (le_of_not_ge hv)]
    have hb := hi (I.filter (fun v => 0 ≤ a v))
      (hI.mono (Finset.filter_subset _ _))
    change ∑ v ∈ I, max (a v) 0 / u ≤ 1
    rw [← Finset.sum_div,div_le_one hup]
    rw [hm]
    exact hb.le
  · have hconst : f (fun _ : V => 1/r) = (∑ v, a v) / r := by
      rw [functional_eq_sum]
      simp only [← Finset.mul_sum,div_eq_mul_inv,mul_comm,mul_one,a]
    rw [hconst] at hu
    have hbig : r * u < ∑ v, a v := by
      have := (lt_div_iff₀ hr).mp hu
      nlinarith
    have hle : (∑ v, a v) ≤ ∑ v, max (a v) 0 :=
      Finset.sum_le_sum (fun v _ => le_max_left _ _)
    change r < ∑ v, max (a v) 0 / u
    rw [← Finset.sum_div,lt_div_iff₀ hup]
    exact hbig.trans_le hle

theorem duality (G : SimpleGraph V) :
    ∃ w, Dual G w ∧ ∑ v, w v = number G := by
  classical
  obtain ⟨w,hw,hm⟩ := dual_maximum G
  refine ⟨w,hw,le_antisymm (dual_le_number hw) ?_⟩
  by_contra hh
  have hh' : (∑ v, w v) < number G := lt_of_not_ge hh
  have hn : 0 ≤ ∑ v, w v := Finset.sum_nonneg (fun v _ => hw.1 v)
  let r := ((∑ v, w v) + number G) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrn : r < number G := by dsimp [r]; linarith
  obtain ⟨z,hz,hrz⟩ := dual_above G hr hrn
  have hzw := hm z hz
  dsimp [r] at hrz
  linarith

lemma transport_expect {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (f : α → β) (X : β → ℝ) :
    (∑ b, transport μ f b * X b) = ∑ a, μ a * X (f a) := by
  classical
  simp only [transport,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul,zero_mul]
  simp

lemma transport_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (f : α → β) : ∑ b, transport μ f b = ∑ a, μ a := by
  simpa only [mul_one] using transport_expect μ f (fun _ => 1)

lemma transport_nonneg {α β : Type} [Fintype α] [DecidableEq β]
    {μ : α → ℝ} (hμ : ∀ a, 0 ≤ μ a) (f : α → β) (b : β) : 0 ≤ transport μ f b := by
  exact Finset.sum_nonneg fun a _ => by split_ifs; exact hμ a; exact le_rfl

lemma marginal_eq_expect (μ : Finset V → ℝ) (v : V) :
    marginal μ v = ∑ I, μ I * indicator I v := by
  classical
  simp [marginal,indicator,mul_ite]

lemma prune_cost (μ : Finset V → ℝ) (v : V) (p : ℝ) : cost (prune μ v p) = cost μ := by
  classical
  simp only [cost,prune,Finset.sum_add_distrib,← Finset.mul_sum,transport_sum]
  ring

lemma prune_marginal (μ : Finset V → ℝ) (v u : V) (p : ℝ) :
    marginal (prune μ v p) u = if u = v then p * marginal μ u else marginal μ u := by
  classical
  rw [marginal_eq_expect]
  simp only [prune,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum,
    transport_expect]
  rw [← marginal_eq_expect]
  by_cases huv : u = v
  · subst u
    simp [indicator]
  · have hInd (J : Finset V) : indicator (J.erase v) u = indicator J u := by
      simp [indicator,Finset.mem_erase,huv]
    simp only [hInd,← marginal_eq_expect,huv,ite_false]
    ring

lemma prune_cover {G : SimpleGraph V} {μ : Finset V → ℝ} (hμ : Cover G μ)
    (v : V) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hm : 1 ≤ p * marginal μ v) : Cover G (prune μ v p) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro I
    exact add_nonneg (mul_nonneg hp (hμ.1 I))
      (mul_nonneg (sub_nonneg.mpr hp1) (transport_nonneg hμ.1 _ I))
  · intro I hn
    have hz : transport μ (fun J => J.erase v) I = 0 := by
      apply Finset.sum_eq_zero
      intro J _
      split_ifs with hh
      · apply hμ.2.1 J
        intro hJ
        apply hn
        rw [← hh]
        exact hJ.mono (Finset.erase_subset _ _)
      · rfl
    simp [prune,hμ.2.1 I hn,hz]
  · intro u
    change 1 ≤ marginal (prune μ v p) u
    rw [prune_marginal]
    split_ifs with hu
    · simpa only [hu] using hm
    · exact hμ.2.2 u

lemma exact_cover (G : SimpleGraph V) {μ : Finset V → ℝ} (hμ : Cover G μ) :
    ∃ ν, Cover G ν ∧ cost ν = cost μ ∧ ∀ v, marginal ν v = 1 := by
  classical
  have step (s : Finset V) : ∃ ν, Cover G ν ∧ cost ν = cost μ ∧
      (∀ v ∈ s, marginal ν v = 1) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨μ,hμ,rfl,by simp⟩
    | @insert v s hvs ih =>
      obtain ⟨ν,hν,hcost,hex⟩ := ih
      let p := 1 / marginal ν v
      have hv : 1 ≤ marginal ν v := hν.2.2 v
      have hvp : 0 < marginal ν v := lt_of_lt_of_le zero_lt_one hv
      have hpp : 0 ≤ p := div_nonneg zero_le_one hvp.le
      have hp1 : p ≤ 1 := (div_le_one hvp).mpr hv
      have he : p * marginal ν v = 1 := by dsimp [p]; field_simp
      refine ⟨prune ν v p,prune_cover hν v hpp hp1 he.ge,?_,?_⟩
      · rw [prune_cost,hcost]
      · intro u hu
        rw [Finset.mem_insert] at hu
        rw [prune_marginal]
        rcases hu with rfl | hu
        · simpa using he
        · have huv : u ≠ v := by rintro rfl; exact hvs hu
          rw [ite_eq_right huv]
          exact hex u hu
  obtain ⟨ν,hν,hcost,hex⟩ := step Finset.univ
  exact ⟨ν,hν,hcost,fun v => hex v (Finset.mem_univ v)⟩

lemma marginal_sum (μ : Finset V → ℝ) :
    (∑ v, marginal μ v) = ∑ I, μ I * I.card := by
  classical
  simp only [marginal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  simp [mul_comm]

lemma partition_small {V : Type} [Fintype V] [DecidableEq V] (I : Finset V) {M : ℕ} (hM : 1 ≤ M) :
    ∃ P : Finset (Finset V),
      (∀ J ∈ P, J ⊆ I ∧ J.Nonempty ∧ J.card ≤ M) ∧
      (∀ v, (∑ J ∈ P, if v ∈ J then (1 : ℝ) else 0) = if v ∈ I then 1 else 0) ∧
      M * P.card < I.card + M := by
  classical
  induction I using Finset.strongInductionOn
  rename_i I ih
  by_cases hI : I = ∅
  · subst I
    exact ⟨∅,by simp,by simp,by simp; omega⟩
  by_cases hsmall : I.card ≤ M
  · refine ⟨{I},?_,?_,?_⟩
    · intro J hJ
      have : J = I := Finset.mem_singleton.mp hJ
      subst J
      exact ⟨Finset.Subset.refl _,Finset.nonempty_iff_ne_empty.mpr hI,hsmall⟩
    · intro v
      rw [Finset.sum_singleton]
    · have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hI)
      simp only [Finset.card_singleton,mul_one]
      omega
  have hlt : M < I.card := lt_of_not_ge hsmall
  obtain ⟨J,hJI,hJcard⟩ := Finset.exists_subset_card_eq hlt.le
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  have hdiff : (I \ J).card + M = I.card := by
    simpa [hJcard] using Finset.card_sdiff_add_card_eq_card hJI
  have hss : I \ J ⊂ I := by
    exact (Finset.ssubset_iff_subset_ne).mpr ⟨Finset.sdiff_subset,by
      intro he
      have hh := congrArg Finset.card he
      omega⟩
  obtain ⟨P,hP,hcover,hcard⟩ := ih (I \ J) hss
  have hJP : J ∉ P := by
    intro h
    obtain ⟨v,hv⟩ := hJne
    have hh := (hP J h).1 hv
    exact (Finset.mem_sdiff.mp hh).2 hv
  refine ⟨insert J P,?_,?_,?_⟩
  · intro K hK
    rcases Finset.mem_insert.mp hK with rfl | hK
    · exact ⟨hJI,hJne,hJcard.le⟩
    · exact ⟨(hP K hK).1.trans Finset.sdiff_subset,(hP K hK).2⟩
  · intro v
    rw [Finset.sum_insert hJP,hcover]
    by_cases hvJ : v ∈ J
    · have hvI := hJI hvJ
      simp [hvJ,hvI]
    · by_cases hvI : v ∈ I <;> simp [hvJ,hvI]
  · rw [Finset.card_insert_of_notMem hJP,mul_add,mul_one]
    omega

lemma partition_small_real (I : Finset V) {M : ℕ} (hM : 1 ≤ M) :
    ∃ P : Finset (Finset V),
      (∀ J ∈ P, J ⊆ I ∧ J.Nonempty ∧ J.card ≤ M) ∧
      (∀ v, (∑ J ∈ P, if v ∈ J then (1 : ℝ) else 0) = if v ∈ I then 1 else 0) ∧
      (P.card : ℝ) ≤ 1 + I.card / M := by
  obtain ⟨P,hP,hv,hc⟩ := partition_small I hM
  refine ⟨P,hP,hv,?_⟩
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hh : (M : ℝ) * P.card ≤ (I.card : ℝ) + M := by exact_mod_cast hc.le
  have he : (1 + (I.card : ℝ) / M) * M = I.card + M := by field_simp; ring
  nlinarith

lemma splitWeights_sum (μ : Finset V → ℝ) (P : Finset V → Finset (Finset V)) :
    cost (splitWeights μ P) = ∑ I, μ I * (P I).card := by
  classical
  unfold cost splitWeights
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  simp [mul_comm]

lemma splitWeights_marginal (μ : Finset V → ℝ) (P : Finset V → Finset (Finset V))
    (hP : ∀ I v, (∑ J ∈ P I, if v ∈ J then (1:ℝ) else 0) = if v ∈ I then 1 else 0)
    (v : V) : marginal (splitWeights μ P) v = marginal μ v := by
  classical
  rw [marginal_eq_expect]
  simp only [splitWeights,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  have he : (∑ J, (if J ∈ P I then μ I else 0) * indicator J v) =
      μ I * ∑ J ∈ P I, if v ∈ J then (1 : ℝ) else 0 := by
    simp only [ite_mul,zero_mul]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    rw [Finset.mul_sum]
    rfl
  rw [he,hP I v]
  simp only [mul_ite,mul_one,mul_zero]

lemma bounded_cover (G : SimpleGraph V) {r : ℝ} (hf : number G ≤ r)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ ν : Finset V → ℝ,
      (∀ J, 0 ≤ ν J) ∧
      (∀ J, ν J ≠ 0 → Stable G J ∧ J.card ≤ M) ∧
      (∀ v, marginal ν v = 1) ∧ cost ν ≤ r + Fintype.card V / M := by
  classical
  obtain ⟨μ,hμ,hm⟩ := (number_le_iff G r).mp hf
  obtain ⟨μ',hμ',hcost,hexact⟩ := exact_cover G hμ
  have hc : cost μ' ≤ r := hcost ▸ hm
  choose P hP hvertex hpbound using fun I : Finset V => partition_small_real I hM
  let ν := splitWeights μ' P
  have hpos (J : Finset V) : 0 ≤ ν J :=
    Finset.sum_nonneg (fun I _ => by split_ifs; exact hμ'.1 I; exact le_rfl)
  refine ⟨ν,hpos,?_,?_,?_⟩
  · intro J hJ
    by_contra hbad
    apply hJ
    apply Finset.sum_eq_zero
    intro I _
    split_ifs with hh
    · apply hμ'.2.1 I
      intro hI
      exact hbad ⟨hI.mono (hP I J hh).1,(hP I J hh).2.2⟩
    · rfl
  · intro v
    rw [splitWeights_marginal μ' P hvertex]
    exact hexact v
  · rw [splitWeights_sum]
    calc
      ∑ I, μ' I * (P I).card ≤ ∑ I, μ' I * (1 + I.card / M) := by
        exact Finset.sum_le_sum (fun I _ => mul_le_mul_of_nonneg_left (hpbound I) (hμ'.1 I))
      _ = cost μ' + (∑ I, μ' I * I.card) / M := by
        simp only [mul_add,mul_one,mul_div_assoc,Finset.sum_add_distrib,Finset.sum_div,cost]
      _ = cost μ' + Fintype.card V / M := by
        rw [← marginal_sum]
        simp only [hexact,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
      _ ≤ r + Fintype.card V / M := by linarith

theorem bounded_sampling (G : SimpleGraph V) {n r : ℝ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (horder : (Fintype.card V : ℝ) ≤ n)
    (hf : number G ≤ r) :
    ∃ π : Finset V → ℝ,
      (∀ I, 0 ≤ π I) ∧ (∑ I, π I = 1) ∧
      (∀ I, π I ≠ 0 → Stable G I ∧ I.card ≤ ⌈n/r⌉₊) ∧
      ∀ v, marginal π v = 1 / (2*r) := by
  classical
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hd : 0 < 2*r := by positivity
  let M : ℕ := ⌈n/r⌉₊
  have hM : 1 ≤ M := Nat.ceil_pos.mpr (div_pos (lt_of_lt_of_le zero_lt_one hn) hrp)
  have hMp : (0:ℝ) < M := by exact_mod_cast hM
  have hnr : n / r ≤ (M : ℝ) := Nat.le_ceil _
  have hquot : (Fintype.card V : ℝ) / M ≤ r := by
    apply (div_le_iff₀ hMp).mpr
    have hh := (div_le_iff₀ hrp).mp hnr
    nlinarith
  obtain ⟨ν,hν,hstab,hv,hcost⟩ := bounded_cover G hf hM
  have hmass : cost ν ≤ 2*r := by linarith
  let π : Finset V → ℝ := fun I =>
    (ν I + if I = ∅ then 2*r - cost ν else 0) / (2*r)
  refine ⟨π,?_,?_,?_,?_⟩
  · intro I
    exact div_nonneg (add_nonneg (hν I) (by split_ifs; linarith; exact le_rfl)) hd.le
  · dsimp [π]
    rw [← Finset.sum_div,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    change (cost ν + (2*r - cost ν)) / (2*r) = 1
    field_simp
    ring
  · intro I hI
    by_cases he : I = ∅
    · subst I
      exact ⟨stable_empty G,by simp⟩
    · exact hstab I (by intro hh; apply hI; simp [π,he,hh])
  · intro v
    have he (I : Finset V) : (if v ∈ I then π I else 0) =
        (if v ∈ I then ν I else 0) / (2*r) := by
      by_cases hvI : v ∈ I
      · have hi : I ≠ ∅ := by rintro rfl; simp at hvI
        simp [π,hvI,hi]
      · simp [hvI]
    simp only [marginal,he,← Finset.sum_div]
    change marginal ν v / (2*r) = 1 / (2*r)
    rw [hv]

lemma Dual.comap {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w) (f : W → V)
    (hf : Function.Injective f) : Dual (G.comap f) (fun v => w (f v)) := by
  classical
  refine ⟨fun v => hw.1 (f v),?_⟩
  intro I hI
  have hstable : Stable G (I.image f) := by
    intro u hu v hv hadj
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    exact hI a ha b hb hadj
  have hh := hw.2 (I.image f) hstable
  simpa only [Finset.sum_image (fun _ _ _ _ h => hf h)] using hh

end LinearListHadwiger.Fractional

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.FractionalSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

lemma Dual.extend {G : SimpleGraph V} {S : Set V} [DecidablePred (· ∈ S)] {w : S → ℝ}
    (h : Dual (G.induce S) w) :
    Dual G (fun v => if hv : v ∈ S then w ⟨v,hv⟩ else 0) := by
  classical
  refine ⟨?_,?_⟩
  · intro v
    dsimp only
    split_ifs
    · exact h.1 _
    · exact le_rfl
  · intro I hI
    let J : Finset S := Finset.univ.filter fun v => v.val ∈ I
    have hJ : Stable (G.induce S) J := by
      intro v hv u hu hadj
      exact hI _ (Finset.mem_filter.mp hv).2 _ (Finset.mem_filter.mp hu).2 hadj
    have hs : (∑ v ∈ I, if hv : v ∈ S then w ⟨v,hv⟩ else 0) = ∑ v ∈ J, w v := by
      calc
        _ = ∑ v ∈ I.filter (· ∈ S), if hv : v ∈ S then w ⟨v,hv⟩ else 0 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : v ∈ S <;> simp [hv]
        _ = _ := by
          apply Finset.sum_bij (fun v hv => (⟨v,(Finset.mem_filter.mp hv).2⟩ : S))
          · intro v hv
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).1⟩
          · intro v hv u hu he
            exact congrArg Subtype.val he
          · intro v hv
            exact ⟨v.val,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,v.property⟩,rfl⟩
          · intro v hv
            simp only [dite_eq_left (Finset.mem_filter.mp hv).2]
    rw [hs]
    exact h.2 J hJ

theorem induced_duality (G : SimpleGraph V) (S : Finset V) :
    ∃ w : V → ℝ, Dual G w ∧ (∀ v ∉ S, w v = 0) ∧
      (∑ v ∈ S, w v) = number (G.induce (S : Set V)) := by
  classical
  obtain ⟨w,hw,heq⟩ := duality (G.induce (S : Set V))
  refine ⟨fun v => if hv : v ∈ S then w ⟨v,hv⟩ else 0,hw.extend,?_,?_⟩
  · intro v hv
    simp [hv]
  · rw [← heq]
    calc
      _ = ∑ v : (S : Set V), (if hv : v.val ∈ S then w ⟨v.val,hv⟩ else 0) :=
        (Finset.sum_coe_sort S _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        split_ifs with hv
        · rfl
        · exact (hv v.property).elim

lemma Dual.restrict_sum {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w)
    (S : Finset V) : (∑ v ∈ S, w v) ≤ number (G.induce (S : Set V)) := by
  classical
  obtain ⟨μ,hμ,hcost⟩ := optimum_exists (G.induce (S : Set V))
  have h := weak_duality hμ (hw.comap Subtype.val Subtype.val_injective)
  rw [hcost] at h
  have he : (∑ v : (S : Set V), w v.val) = ∑ v ∈ S, w v :=
    (Finset.sum_subtype S (fun v => Iff.rfl) w).symm
  rw [he] at h
  exact h

lemma induced_number_le (G : SimpleGraph V) (S T : Finset V) :
    number (G.induce (S : Set V)) ≤ number (G.induce (T : Set V)) + (S \ T).card := by
  classical
  obtain ⟨w,hw,hzero,hmax⟩ := induced_duality G S
  have hsplit : (∑ v ∈ S, w v) = (∑ v ∈ S ∩ T, w v) + ∑ v ∈ S \ T, w v := by
    have hd : Disjoint (S ∩ T) (S \ T) := by
      apply Finset.disjoint_left.mpr
      intro v hv ht
      exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_inter.mp hv).2
    rw [← Finset.sum_union hd]
    congr 1
    ext v
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hT : (∑ v ∈ S ∩ T, w v) ≤ number (G.induce (T : Set V)) := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun v _ _ => hw.1 v)).trans (hw.restrict_sum T)
  have hD : (∑ v ∈ S \ T, w v) ≤ (S \ T).card := by
    calc
      _ ≤ ∑ _v ∈ S \ T, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hw.le_one v)
      _ = _ := by simp
  rw [← hmax,hsplit]
  linarith

lemma induced_number_abs_sub_le (G : SimpleGraph V) (S T : Finset V) :
    |number (G.induce (S : Set V)) - number (G.induce (T : Set V))| ≤
      (S \ T).card + (T \ S).card := by
  have hST := induced_number_le G S T
  have hTS := induced_number_le G T S
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (S \ T).card,
    Nat.cast_nonneg (α := ℝ) (T \ S).card]

end LinearListHadwiger.Fractional

namespace LinearListHadwiger.Sampling
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

lemma productMass_nonneg {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι] {μ : ι → Ω → ℝ} (h : ∀ i ω, 0 ≤ μ i ω) (x : ι → Ω) :
    0 ≤ productMass μ x := Finset.prod_nonneg (fun i _ => h i _)

lemma productMass_sum {μ : ι → Ω → ℝ} (h : ∀ i, ∑ ω, μ i ω = 1) :
    ∑ x, productMass μ x = 1 := by
  classical
  change (∑ x : ι → Ω, ∏ i, μ i (x i)) = 1
  rw [← Fintype.prod_sum]
  simp [h]

lemma expectation_product (μ f : ι → Ω → ℝ) :
    expectation (productMass μ) (fun x => ∏ i, f i (x i)) =
      ∏ i, expectation (μ i) (f i) := by
  classical
  simp only [expectation,productMass,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (ι := ι) (κ := fun _ => Ω) (fun i a => μ i a * f i a)).symm

lemma expectation_coordinate {μ : ι → Ω → ℝ} (h : ∀ i, ∑ ω, μ i ω = 1)
    (i : ι) (f : Ω → ℝ) :
    expectation (productMass μ) (fun x => f (x i)) = expectation (μ i) f := by
  classical
  have he (x : ι → Ω) : (∏ j : ι, if j = i then f (x j) else 1) = f (x i) := by simp
  calc
    _ = expectation (productMass μ) (fun x => ∏ j, if j = i then f (x j) else 1) := by
      congr 1
      funext x
      exact (he x).symm
    _ = ∏ j, expectation (μ j) (fun ω => if j = i then f ω else 1) :=
      expectation_product μ (fun j ω => if j = i then f ω else 1)
    _ = expectation (μ i) f := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hji
        simp [expectation,hji,h]
      · simp

lemma expectation_pair {μ : ι → Ω → ℝ} (h : ∀ i, ∑ ω, μ i ω = 1)
    {i j : ι} (hij : i ≠ j) (f g : Ω → ℝ) :
    expectation (productMass μ) (fun x => f (x i) * g (x j)) =
      expectation (μ i) f * expectation (μ j) g := by
  classical
  have he (x : ι → Ω) :
      (∏ k : ι, (if k = i then f (x k) else 1) * (if k = j then g (x k) else 1)) =
        f (x i) * g (x j) := by rw [Finset.prod_mul_distrib]; simp
  calc
    _ = expectation (productMass μ) (fun x => ∏ k,
        (if k = i then f (x k) else 1) * (if k = j then g (x k) else 1)) := by
      congr 1
      funext x
      exact (he x).symm
    _ = ∏ k, expectation (μ k) (fun ω =>
        (if k = i then f ω else 1) * (if k = j then g ω else 1)) := expectation_product μ
          (fun k ω => (if k = i then f ω else 1) * (if k = j then g ω else 1))
    _ = ∏ k, (if k = i then expectation (μ i) f else 1) *
        (if k = j then expectation (μ j) g else 1) := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k; simp [hij,expectation]
      · by_cases hkj : k = j
        · subst k; simp [hki,expectation]
        · simp [hki,hkj,expectation,h]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

lemma expectation_nonneg {μ f : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ expectation μ f := Finset.sum_nonneg fun ω _ => mul_nonneg (hμ ω) (hf ω)

lemma expectation_mono {μ f g : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hfg : ∀ ω, f ω ≤ g ω) :
    expectation μ f ≤ expectation μ g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (hμ ω)

lemma expectation_sum {κ : Type} (s : Finset κ) (μ : Ω → ℝ) (f : κ → Ω → ℝ) :
    expectation μ (fun ω => ∑ k ∈ s, f k ω) = ∑ k ∈ s, expectation μ (f k) := by
  simp only [expectation,Finset.mul_sum]
  exact Finset.sum_comm

lemma probability_eq_expectation (μ : Ω → ℝ) (A : Ω → Prop) [DecidablePred A] :
    probability μ A = expectation μ (fun ω => if A ω then 1 else 0) := by
  classical
  simp only [probability,expectation]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

lemma probability_mono {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) {A B : Ω → Prop}
    (hAB : ∀ ω, A ω → B ω) : probability μ A ≤ probability μ B := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · simp [hA,hAB ω hA]
  · simp only [hA,ite_false]
    split_ifs; exact hμ ω; exact le_rfl

lemma probability_coordinate {μ : ι → Ω → ℝ} (h : ∀ i, ∑ ω, μ i ω = 1)
    (i : ι) (A : Ω → Prop) :
    probability (productMass μ) (fun x => A (x i)) = probability (μ i) A := by
  classical
  simp_rw [probability_eq_expectation]
  exact expectation_coordinate h i (fun ω => if A ω then (1 : ℝ) else 0)

lemma probability_union_le {κ : Type} [Fintype κ] {μ : Ω → ℝ}
    (hμ : ∀ ω, 0 ≤ μ ω) (A : κ → Ω → Prop) :
    probability μ (fun ω => ∃ k, A k ω) ≤ ∑ k, probability μ (A k) := by
  classical
  simp only [probability]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : ∃ k, A k ω
  · obtain ⟨k,hk⟩ := hA
    rw [ite_eq_left ⟨k,hk⟩]
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset κ))
        (f := fun k => if A k ω then μ ω else 0)
        (fun k _ => by split_ifs; exact hμ ω; exact le_rfl) (Finset.mem_univ k)
    simpa only [ite_eq_left hk] using hh
  · simp only [ite_eq_right hA]
    exact Finset.sum_nonneg (fun k _ => by split_ifs; exact hμ ω; exact le_rfl)

lemma probability_or_le {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (A B : Ω → Prop) :
    probability μ (fun ω => A ω ∨ B ω) ≤ probability μ A + probability μ B := by
  classical
  simp only [probability,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA,hB,hμ ω]

lemma markov {μ f : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    probability μ (fun ω => a ≤ f ω) ≤ expectation μ f / a := by
  classical
  apply (le_div_iff₀ ha).mpr
  simp only [probability,Finset.sum_mul,expectation]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : a ≤ f ω
  · simp only [ite_eq_left h]
    exact mul_le_mul_of_nonneg_left h (hμ ω)
  · simp only [ite_eq_right h,zero_mul]
    exact mul_nonneg (hμ ω) (hf ω)

lemma exists_positive_avoiding {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (hs : ∑ ω, μ ω = 1) {A : Ω → Prop} (hA : probability μ A < 1) :
    ∃ ω, 0 < μ ω ∧ ¬A ω := by
  classical
  by_contra hn
  push Not at hn
  have he : probability μ A = 1 := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : 0 < μ ω
    · simp only [ite_eq_left (hn ω h)]
    · have hz : μ ω = 0 := le_antisymm (le_of_not_gt h) (hμ ω)
      simp [hz]
  linarith

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open scoped BigOperators
open Fractional
variable {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V]
  [DecidableEq ι] [DecidableEq V]

lemma expectation_const {μ : Ω → ℝ} (hs : ∑ ω, μ ω = 1) (c : ℝ) :
    expectation μ (fun _ => c) = c := by simp [expectation,← Finset.sum_mul,hs]

lemma collision_nonneg {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V] [DecidableEq ι] [DecidableEq V] (W : Ω → Finset V) {φ : Ω → V → ℝ}
    (hφ : ∀ ω v, 0 ≤ φ ω v) (i : ι) (x : ι → Ω) : 0 ≤ collision W φ i x := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> simp [hφ]

lemma expectation_collision {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hs : ∑ ω, μ ω = 1)
    (W : Ω → Finset V) {φ : Ω → V → ℝ} (hφ : ∀ ω v, 0 ≤ φ ω v)
    (hφsum : ∀ ω, ∑ v, φ ω v ≤ 1) {p : ℝ} (hp : 0 ≤ p)
    (hmarg : ∀ v, probability μ (fun ω => v ∈ W ω) ≤ p) (i : ι) :
    expectation (productMass (fun _ : ι => μ)) (collision W φ i) ≤
      (Fintype.card ι - 1 : ℕ) * p := by
  classical
  unfold collision
  rw [expectation_sum]
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase i, p := by
      apply Finset.sum_le_sum
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
      rw [expectation_sum]
      calc
        _ = ∑ v, expectation μ (fun ω => φ ω v) * probability μ (fun ω => v ∈ W ω) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [expectation_pair (μ := fun _ : ι => μ) (f := fun ω => φ ω v)
            (g := fun ω => if v ∈ W ω then 1 else 0) (fun _ => hs) hij,
            probability_eq_expectation]
        _ ≤ ∑ v, expectation μ (fun ω => φ ω v) * p := by
          apply Finset.sum_le_sum
          intro v _
          exact mul_le_mul_of_nonneg_left (hmarg v) (expectation_nonneg hμ (fun ω => hφ ω v))
        _ = expectation μ (fun ω => ∑ v, φ ω v) * p := by
          rw [← Finset.sum_mul,expectation_sum]
        _ ≤ 1 * p := by
          apply mul_le_mul_of_nonneg_right _ hp
          exact (expectation_mono hμ hφsum).trans_eq (expectation_const hs 1)
        _ = p := one_mul p
    _ = _ := by simp

lemma sum_on_eq (S : Finset V) (f : V → ℝ) :
    (∑ v ∈ S, f v) = ∑ v, if v ∈ S then f v else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

lemma private_weight_loss {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V] [DecidableEq ι] [DecidableEq V] (W : Ω → Finset V) {φ : Ω → V → ℝ}
    (hφ : ∀ ω v, 0 ≤ φ ω v) (i : ι) (x : ι → Ω) :
    (∑ v ∈ W (x i), φ (x i) v) ≤
      (∑ v ∈ privateCopy W i x, φ (x i) v) + collision W φ i x := by
  classical
  rw [sum_on_eq (W (x i)) (φ (x i)),
    sum_on_eq (privateCopy W i x) (φ (x i))]
  unfold collision
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase i,
      φ (x i) v * (if v ∈ W (x j) then 1 else 0) := by
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> simp [hφ]
  by_cases hv : v ∈ W (x i)
  · simp only [ite_eq_left hv]
    by_cases hpr : v ∈ privateCopy W i x
    · simp only [ite_eq_left hpr]
      linarith
    · simp only [ite_eq_right hpr,zero_add]
      have hvO : v ∈ otherCopies W i x := by
        simpa only [privateCopy,Finset.mem_sdiff,hv,true_and,not_not] using hpr
      obtain ⟨j,hj,hvj⟩ := Finset.mem_biUnion.mp hvO
      have hh := Finset.single_le_sum
        (s := Finset.univ.erase i)
        (f := fun j => φ (x i) v * (if v ∈ W (x j) then 1 else 0))
        (fun j _ => by split_ifs <;> simp [hφ]) hj
      simpa only [ite_eq_left hvj,mul_one] using hh
  · simp only [ite_eq_right hv]
    have hc : 0 ≤ (if v ∈ privateCopy W i x then φ (x i) v else 0) := by
      split_ifs; exact hφ _ _; exact le_rfl
    linarith

lemma privateCopies_disjoint {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V] [DecidableEq ι] [DecidableEq V] (W : Ω → Finset V) (x : ι → Ω) {i j : ι} (hij : i ≠ j) :
    Disjoint (privateCopy W i x) (privateCopy W j x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨hi,hni⟩ := Finset.mem_sdiff.mp hvi
  obtain ⟨hj,hnj⟩ := Finset.mem_sdiff.mp hvj
  apply hni
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ _⟩,hj⟩

theorem private_fractional_failure (G : SimpleGraph V) {μ : Ω → ℝ}
    (hμ : ∀ ω, 0 ≤ μ ω) (hs : ∑ ω, μ ω = 1) (W : Ω → Finset V)
    {r p δ : ℝ} (hr : 0 < r) (hp : 0 ≤ p)
    (hmarg : ∀ v, probability μ (fun ω => v ∈ W ω) ≤ p)
    (hhigh : probability μ (fun ω => number (G.induce (W ω : Set V)) ≤ r/5) ≤ δ) :
    probability (productMass (fun _ : ι => μ))
      (fun x => ∃ i, number (G.induce (privateCopy W i x : Set V)) ≤ r/8) ≤
        (Fintype.card ι : ℝ) * δ + 4 * Fintype.card ι * (Fintype.card ι - 1 : ℕ) * p := by
  classical
  choose w hw hz heq using (fun ω => induced_duality G (W ω))
  let a : Ω → ℝ := fun ω => number (G.induce (W ω : Set V))
  let φ : Ω → V → ℝ := fun ω v => if 0 < a ω then w ω v / a ω else 0
  have hφ : ∀ ω v, 0 ≤ φ ω v := by
    intro ω v
    dsimp [φ]
    split_ifs with h
    · exact div_nonneg ((hw ω).1 v) h.le
    · exact le_rfl
  have hwtotal (ω : Ω) : (∑ v, w ω v) = a ω := by
    change (∑ v, w ω v) = number (G.induce (W ω : Set V))
    rw [← heq ω]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    exact hz ω v hv
  have hφsum : ∀ ω, ∑ v, φ ω v ≤ 1 := by
    intro ω
    by_cases ha : 0 < a ω
    · simp only [φ,ite_eq_left ha,← Finset.sum_div,hwtotal,div_self (ne_of_gt ha),le_refl]
    · simp [φ,ha]
  have hφW (ω : Ω) (ha : 0 < a ω) : (∑ v ∈ W ω, φ ω v) = 1 := by
    simp only [φ,ite_eq_left ha,← Finset.sum_div,heq]
    change a ω / a ω = 1
    exact div_self (ne_of_gt ha)
  let bad : ι → (ι → Ω) → Prop := fun i x =>
    a (x i) ≤ r/5 ∨ (1/4 : ℝ) ≤ collision W φ i x
  have hbad_sub (x : ι → Ω) :
      (∃ i, number (G.induce (privateCopy W i x : Set V)) ≤ r/8) → ∃ i, bad i x := by
    rintro ⟨i,hi⟩
    refine ⟨i,?_⟩
    by_contra hn
    have hh : r/5 < a (x i) := lt_of_not_ge (fun h => hn (Or.inl h))
    have hc : collision W φ i x < 1/4 := lt_of_not_ge (fun h => hn (Or.inr h))
    have ha : 0 < a (x i) := by linarith
    have hret := private_weight_loss W hφ i x
    rw [hφW (x i) ha] at hret
    have hweight : (∑ v ∈ privateCopy W i x, w (x i) v) ≤ r/8 :=
      ((hw (x i)).restrict_sum _).trans hi
    have hsum : (∑ v ∈ privateCopy W i x, φ (x i) v) =
        (∑ v ∈ privateCopy W i x, w (x i) v) / a (x i) := by
      simp only [φ,ite_eq_left ha,Finset.sum_div]
    rw [hsum] at hret
    have hpos : (3/4 : ℝ) <
        (∑ v ∈ privateCopy W i x, w (x i) v) / a (x i) := by linarith
    have hprod := (lt_div_iff₀ ha).mp hpos
    nlinarith
  have hbad (i : ι) : probability (productMass (fun _ : ι => μ)) (bad i) ≤
      δ + 4 * (Fintype.card ι - 1 : ℕ) * p := by
    have hor := probability_or_le (productMass_nonneg (fun _ => hμ))
      (fun x : ι → Ω => a (x i) ≤ r/5) (fun x => (1/4 : ℝ) ≤ collision W φ i x)
    have hfirst : probability (productMass (fun _ : ι => μ)) (fun x => a (x i) ≤ r/5) ≤ δ := by
      rw [probability_coordinate (μ := fun _ : ι => μ) (fun _ => hs) i
        (fun ω => a ω ≤ r/5)]
      exact hhigh
    have hmk := markov (productMass_nonneg (fun _ : ι => hμ)) (collision_nonneg W hφ i)
      (a := (1/4 : ℝ)) (by norm_num)
    have hexp := expectation_collision hμ hs W hφ hφsum hp hmarg i
    change probability (productMass (fun _ : ι => μ))
      (fun x => a (x i) ≤ r/5 ∨ (1/4 : ℝ) ≤ collision W φ i x) ≤ _
    linarith
  calc
    _ ≤ probability (productMass (fun _ : ι => μ)) (fun x => ∃ i, bad i x) :=
      probability_mono (productMass_nonneg (fun _ => hμ)) hbad_sub
    _ ≤ ∑ i, probability (productMass (fun _ : ι => μ)) (bad i) :=
      probability_union_le (productMass_nonneg (fun _ => hμ)) _
    _ ≤ ∑ _i : ι, (δ + 4 * (Fintype.card ι - 1 : ℕ) * p) :=
      Finset.sum_le_sum (fun i _ => hbad i)
    _ = _ := by simp; ring

end LinearListHadwiger.Sampling

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.SamplingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open scoped BigOperators
variable {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V]
  [DecidableEq ι] [DecidableEq V]

lemma mem_remainder {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V] [DecidableEq ι] [DecidableEq V] (E : ι → Finset V) (I : Ω → Finset V) (x : ι → Ω) (v : V) :
    v ∈ remainder E I x ↔ ∀ j, v ∈ E j → v ∉ I (x j) := by
  classical
  simp only [remainder,Finset.mem_sdiff,Finset.mem_univ,true_and,
    Finset.mem_biUnion,Finset.mem_inter]
  push Not
  constructor
  · intro h j he hi
    exact h j hi he
  · intro h j hi he
    exact h j he hi

lemma probability_not {μ : Ω → ℝ} (hs : ∑ ω, μ ω = 1) (A : Ω → Prop) :
    probability μ (fun ω => ¬ A ω) = 1 - probability μ A := by
  classical
  have he : probability μ (fun ω => ¬ A ω) + probability μ A = ∑ ω, μ ω := by
    unfold probability
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : A ω <;> simp [h]
  linarith

lemma remainder_survival_eq {μ : ι → Ω → ℝ} (hs : ∀ j, ∑ ω, μ j ω = 1)
    (E : ι → Finset V) (I : Ω → Finset V) (v : V) :
    probability (productMass μ) (fun x => v ∈ remainder E I x) =
      ∏ j, if v ∈ E j then 1 - probability (μ j) (fun ω => v ∈ I ω) else 1 := by
  classical
  let f : ι → Ω → ℝ := fun j ω => if v ∈ E j ∧ v ∈ I ω then 0 else 1
  have hprod (x : ι → Ω) :
      (if v ∈ remainder E I x then (1 : ℝ) else 0) = ∏ j, f j (x j) := by
    by_cases hv : v ∈ remainder E I x
    · rw [ite_eq_left hv]
      symm
      apply Finset.prod_eq_one
      intro j _
      simp only [f]
      exact ite_eq_right (fun hh => (mem_remainder E I x v).mp hv j hh.1 hh.2)
    · rw [ite_eq_right hv]
      have hnot : ¬ ∀ j, v ∈ E j → v ∉ I (x j) := mt (mem_remainder E I x v).mpr hv
      push Not at hnot
      obtain ⟨j,hE,hI⟩ := hnot
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [f,hE,hI]
  rw [probability_eq_expectation]
  simp_rw [hprod]
  rw [expectation_product]
  apply Finset.prod_congr rfl
  intro j _
  by_cases he : v ∈ E j
  · simp only [ite_eq_left he]
    have hf : f j = fun ω => if v ∉ I ω then 1 else 0 := by
      funext ω
      by_cases hi : v ∈ I ω <;> simp [f,he,hi]
    rw [hf,← probability_eq_expectation,probability_not (hs j)]
  · simp only [ite_eq_right he]
    have hf : f j = fun _ => 1 := by funext ω; simp [f,he]
    rw [hf,expectation_const (hs j)]

lemma remainder_survival_power {μ : ι → Ω → ℝ} (hs : ∀ j, ∑ ω, μ j ω = 1)
    (E : ι → Finset V) (I : Ω → Finset V) {p : ℝ}
    (hmarg : ∀ j v, probability (μ j) (fun ω => v ∈ I ω) = p) (v : V) :
    probability (productMass μ) (fun x => v ∈ remainder E I x) =
      (1 - p) ^ (Finset.univ.filter (fun j => v ∈ E j)).card := by
  classical
  rw [remainder_survival_eq hs E I v]
  simp_rw [hmarg]
  rw [← Finset.prod_filter]
  simp

theorem remainder_survival_bound {μ : ι → Ω → ℝ} (hs : ∀ j, ∑ ω, μ j ω = 1)
    (E : ι → Finset V) (I : Ω → Finset V) {r : ℝ} (hr : 1 ≤ r)
    (hmarg : ∀ j v, probability (μ j) (fun ω => v ∈ I ω) = 1 / (2*r))
    (hE : ∀ v, (Fintype.card ι : ℝ)/2 ≤ (Finset.univ.filter (fun j => v ∈ E j)).card)
    (v : V) :
    probability (productMass μ) (fun x => v ∈ remainder E I x) ≤
      Real.exp (-(Fintype.card ι : ℝ)/(4*r)) := by
  classical
  rw [remainder_survival_power hs E I hmarg v]
  have hp : 0 ≤ 1 - 1/(2*r) := by
    have hh : 1/(2*r) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hex : 1 - 1/(2*r) ≤ Real.exp (-(1/(2*r))) := by
    have h := Real.add_one_le_exp (-(1/(2*r)))
    linarith
  calc
    _ ≤ (Real.exp (-(1/(2*r)))) ^ (Finset.univ.filter (fun j => v ∈ E j)).card :=
      pow_le_pow_left₀ hp hex _
    _ = Real.exp (-((Finset.univ.filter (fun j => v ∈ E j)).card : ℝ)/(2*r)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := hE v
      have hpos : 0 < 2*r := by linarith
      apply (div_le_div_iff₀ hpos (by linarith : 0 < 4*r)).mpr
      nlinarith

lemma remainder_sdiff_subset (E : ι → Finset V) (I : Ω → Finset V)
    {i : ι} {x y : ι → Ω} (hxy : ∀ j, j ≠ i → x j = y j) :
    remainder E I x \ remainder E I y ⊆ I (y i) := by
  classical
  intro v hv
  obtain ⟨hx,hy⟩ := Finset.mem_sdiff.mp hv
  by_contra hn
  apply hy
  apply (mem_remainder E I y v).mpr
  intro j he
  by_cases hj : j = i
  · simpa [hj] using hn
  · rw [← hxy j hj]
    exact (mem_remainder E I x v).mp hx j he

lemma inter_sdiff_subset_left {V : Type} [Fintype V] [DecidableEq V] (A S T : Finset V) :
    (A ∩ S) \ (A ∩ T) ⊆ S \ T := by
  intro v hv
  simp only [Finset.mem_sdiff,Finset.mem_inter] at hv ⊢
  tauto

lemma inter_remainder_difference_bound (E : ι → Finset V) (I : Ω → Finset V)
    {M : ℕ} (hI : ∀ ω, (I ω).card ≤ M) (A : Finset V)
    {i : ι} {x y : ι → Ω} (hxy : ∀ j, j ≠ i → x j = y j) :
    (((A ∩ remainder E I x) \ (A ∩ remainder E I y)).card : ℝ) +
      ((A ∩ remainder E I y) \ (A ∩ remainder E I x)).card ≤ 2 * (M : ℝ) := by
  have h₁ := (Finset.card_le_card ((inter_sdiff_subset_left A _ _).trans
    (remainder_sdiff_subset E I hxy))).trans (hI (y i))
  have h₂ := (Finset.card_le_card ((inter_sdiff_subset_left A _ _).trans
    (remainder_sdiff_subset E I (fun j hj => (hxy j hj).symm)))).trans (hI (x i))
  exact_mod_cast (by omega : ((A ∩ remainder E I x) \ (A ∩ remainder E I y)).card +
    ((A ∩ remainder E I y) \ (A ∩ remainder E I x)).card ≤ 2*M)

lemma card_abs_sub_le_differences {V : Type} [Fintype V] [DecidableEq V] (S T : Finset V) :
    |(S.card : ℝ)-T.card| ≤ (S \ T).card + (T \ S).card := by
  have hS := Finset.card_sdiff_add_card_inter S T
  have hT := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at hT
  have hSr : ((S \ T).card : ℝ) + (S ∩ T).card = S.card := by exact_mod_cast hS
  have hTr : ((T \ S).card : ℝ) + (S ∩ T).card = T.card := by exact_mod_cast hT
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (S \ T).card,
    Nat.cast_nonneg (α := ℝ) (T \ S).card]

lemma remainder_card_bounded_changes {N : ℕ} (E : Fin N → Finset V) (I : Ω → Finset V)
    {M : ℕ} (hI : ∀ ω, (I ω).card ≤ M) (A : Finset V) :
    FiniteConcentration.BoundedChanges (fun x => ((A ∩ remainder E I x).card : ℝ)) (2*M) := by
  intro i x y hxy
  exact (card_abs_sub_le_differences _ _).trans (inter_remainder_difference_bound E I hI A hxy)

lemma remainder_fractional_bounded_changes {N : ℕ} (G : SimpleGraph V)
    (E : Fin N → Finset V) (I : Ω → Finset V)
    {M : ℕ} (hI : ∀ ω, (I ω).card ≤ M) (A : Finset V) :
    FiniteConcentration.BoundedChanges
      (fun x => Fractional.number (G.induce (↑(A ∩ remainder E I x) : Set V))) (2*M) := by
  intro i x y hxy
  exact (Fractional.induced_number_abs_sub_le G _ _).trans
    (inter_remainder_difference_bound E I hI A hxy)

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

theorem bounded_differences_general (hn : 1 ≤ Fintype.card ι)
    (μ : ι → Ω → ℝ) (hμ : ∀ i ω, 0 ≤ μ i ω) (hs : ∀ i, ∑ ω, μ i ω = 1)
    (f : (ι → Ω) → ℝ) {b u : ℝ} (hb : 0 < b) (hu : 0 < u)
    (hf : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x-f y| ≤ b) :
    probability (productMass μ) (fun x => u ≤ |f x-expectation (productMass μ) f|) ≤
      2 * Real.exp (-u^2/(2*Fintype.card ι*b^2)) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E : (Fin (Fintype.card ι) → Ω) ≃ (ι → Ω) := Equiv.arrowCongr e (Equiv.refl Ω)
  let μ' : Fin (Fintype.card ι) → Ω → ℝ := fun i => μ (e i)
  have hm (x : Fin (Fintype.card ι) → Ω) :
      productMass μ' x = productMass μ (E x) := by
    apply Fintype.prod_equiv e
    intro i
    simp [μ',E,Equiv.arrowCongr]
  have he : expectation (productMass μ) f =
      expectation (productMass μ') (fun x => f (E x)) := by
    unfold expectation
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro x _
    rw [hm]
  have hc : FiniteConcentration.BoundedChanges (fun x => f (E x)) b := by
    intro i x y hxy
    apply hf (e i)
    intro j hj
    change x (e.symm j) = y (e.symm j)
    apply hxy
    intro heq
    apply hj
    rw [← e.apply_symm_apply j,heq]
  have hh := FiniteConcentration.bounded_differences hn μ' (fun i => hμ (e i))
    (fun i => hs (e i)) (fun x => f (E x)) hb hu hc
  change probability (productMass μ')
    (fun x => u ≤ |f (E x) - expectation (productMass μ') (fun y => f (E y))|) ≤ _ at hh
  rw [← he] at hh
  convert hh using 1
  unfold probability
  rw [← E.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [hm]

variable {κ V : Type} [Fintype κ] [Fintype V] [DecidableEq κ] [DecidableEq V]

lemma unionRemainders_sdiff_subset (E : ι → Finset V) (I : Ω → Finset V)
    {k : κ × ι} {x y : κ × ι → Ω} (hxy : ∀ j, j ≠ k → x j = y j) :
    unionRemainders E I x \ unionRemainders E I y ⊆ I (y k) := by
  classical
  intro v hv
  obtain ⟨hx,hy⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨c,_,hvc⟩ := Finset.mem_biUnion.mp hx
  have hn : v ∉ remainder E I (fun i => y (c,i)) := by
    intro h
    exact hy (Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ _,h⟩)
  have hck : c = k.1 := by
    by_contra hne
    apply hn
    have he : (fun i => y (c,i)) = (fun i => x (c,i)) := by
      funext i
      exact (hxy (c,i) (fun h => hne (congrArg Prod.fst h))).symm
    rw [he]
    exact hvc
  subst c
  have hdiff := remainder_sdiff_subset E I
    (i := k.2) (x := fun i => x (k.1,i)) (y := fun i => y (k.1,i))
    (fun j hj => hxy (k.1,j) (fun h => hj (congrArg Prod.snd h)))
  exact hdiff (Finset.mem_sdiff.mpr ⟨hvc,hn⟩)

lemma unionRemainders_card_bounded_changes (E : ι → Finset V) (I : Ω → Finset V)
    {M : ℕ} (hI : ∀ ω, (I ω).card ≤ M) (A : Finset V)
    {k : κ × ι} {x y : κ × ι → Ω} (hxy : ∀ j, j ≠ k → x j = y j) :
    |((A ∩ unionRemainders E I x).card : ℝ) - (A ∩ unionRemainders E I y).card| ≤ 2*M := by
  have h₁ := (Finset.card_le_card ((inter_sdiff_subset_left A _ _).trans
    (unionRemainders_sdiff_subset E I hxy))).trans (hI (y k))
  have h₂ := (Finset.card_le_card ((inter_sdiff_subset_left A _ _).trans
    (unionRemainders_sdiff_subset E I (fun j hj => (hxy j hj).symm)))).trans (hI (x k))
  apply (card_abs_sub_le_differences _ _).trans
  exact_mod_cast (by omega : ((A ∩ unionRemainders E I x) \ (A ∩ unionRemainders E I y)).card +
    ((A ∩ unionRemainders E I y) \ (A ∩ unionRemainders E I x)).card ≤ 2*M)

end LinearListHadwiger.Sampling

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Separability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

lemma stable_blowup_projection {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {m : ℕ} {S : Finset (V × Fin m)}
    (hS : Stable (cliqueBlowup G m) S) : Stable G (S.image Prod.fst) := by
  classical
  intro v hv w hw hadj
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
  exact hS u hu z hz (Or.inl hadj)

lemma stable_blowup_injOn {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {m : ℕ} {S : Finset (V × Fin m)}
    (hS : Stable (cliqueBlowup G m) S) : Set.InjOn Prod.fst (S : Set (V × Fin m)) := by
  intro u hu v hv huv
  apply Prod.ext huv
  by_contra hn
  exact hS u hu v hv (Or.inr ⟨huv,hn⟩)

lemma Dual.blowup {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w) (m : ℕ) :
    Dual (cliqueBlowup G m) (fun v => w v.1) := by
  classical
  refine ⟨fun v => hw.1 v.1,?_⟩
  intro S hS
  have hh := hw.2 (S.image Prod.fst) (stable_blowup_projection hS)
  rw [Finset.sum_image (stable_blowup_injOn hS)] at hh
  exact hh

lemma dual_sum_le_colors {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w : V → ℝ} (hw : Dual G w)
    {Color : Type} [Fintype Color] (c : G.Coloring Color) :
    (∑ v, w v) ≤ Fintype.card Color := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ c w]
  calc
    _ ≤ ∑ _ : Color, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      apply hw.2
      intro v hv u hu hadj
      exact c.valid hadj ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hu).2.symm)
    _ = _ := by simp

theorem cliqueBlowup_chromatic_lower (G : SimpleGraph V) (m : ℕ) :
    (m : ℝ) * number G ≤ (cliqueBlowup G m).chromaticNumber.toNat := by
  classical
  obtain ⟨w,hw,heq⟩ := duality G
  have hh := dual_sum_le_colors (hw.blowup m)
    (cliqueBlowup G m).colorable_chromaticNumber_of_fintype.some
  rw [← heq]
  simpa only [Fintype.card_fin,Fintype.sum_prod_type,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum] using hh

lemma cliqueBlowup_colorable_rounded {G : SimpleGraph V} {μ : Finset V → ℝ}
    (hμ : Cover G μ) (m : ℕ) :
    (cliqueBlowup G m).Colorable (∑ I, ⌈(m : ℝ)*μ I⌉₊) := by
  classical
  let counts : Finset V → ℕ := fun I => ⌈(m : ℝ)*μ I⌉₊
  let Slots := Σ I : Finset V, Fin (counts I)
  let good (v : V) : Finset Slots := Finset.univ.filter (fun s => v ∈ s.1)
  have hcard (v : V) : (good v).card = ∑ I, if v ∈ I then counts I else 0 := by
    simp only [good,Finset.card_filter]
    change (∑ s : (Σ I : Finset V, Fin (counts I)), if v ∈ s.1 then 1 else 0) = _
    rw [Fintype.sum_sigma]

    apply Finset.sum_congr rfl
    intro I _
    by_cases hv : v ∈ I <;> simp [hv]
  have hlarge (v : V) : m ≤ (good v).card := by
    have hm : (m : ℝ) ≤ ∑ I, if v ∈ I then ((counts I : ℕ) : ℝ) else 0 := by
      calc
        (m : ℝ) ≤ (m : ℝ)*(∑ I, if v ∈ I then μ I else 0) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hμ.2.2 v) (Nat.cast_nonneg m)
        _ = ∑ I, if v ∈ I then (m : ℝ)*μ I else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro I _
          split_ifs <;> simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · exact Nat.le_ceil _
          · exact le_rfl
    rw [hcard]
    exact_mod_cast hm
  have hinj (v : V) : Nonempty (Fin m ↪ good v) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hlarge v)
  let e : (v : V) → Fin m ↪ good v := fun v => (hinj v).some
  let c : V × Fin m → Slots := fun v => (e v.1 v.2).val
  have hc : ∀ {v w : V × Fin m}, (cliqueBlowup G m).Adj v w → c v ≠ c w := by
    intro v w hadj heq
    have hv : v.1 ∈ (c v).1 := (Finset.mem_filter.mp (e v.1 v.2).property).2
    have hw : w.1 ∈ (c v).1 := by
      rw [heq]
      exact (Finset.mem_filter.mp (e w.1 w.2).property).2
    have stable : Stable G (c v).1 := by
      by_contra hn
      have hzero : counts (c v).1 = 0 := by simp [counts,hμ.2.1 _ hn]
      have hslot := (c v).2.isLt
      exact Nat.not_lt_zero _ (by simpa only [hzero] using hslot)
    rcases hadj with hadj | ⟨hfst,hsnd⟩
    · exact stable _ hv _ hw hadj
    · have hwv : w = (v.1,w.2) := Prod.ext hfst.symm rfl
      have he : e v.1 v.2 = e v.1 w.2 := by
        apply Subtype.ext
        change c v = c (v.1,w.2)
        rw [← hwv]
        exact heq
      exact hsnd ((e v.1).injective he)
  have hchoose := (SimpleGraph.Coloring.mk c hc).colorable
  simpa only [Slots,Fintype.card_sigma,Fintype.card_fin,counts] using hchoose

theorem cliqueBlowup_chromatic_upper (G : SimpleGraph V) (m : ℕ) :
    ((cliqueBlowup G m).chromaticNumber.toNat : ℝ) ≤
      (m : ℝ)*number G + Fintype.card (Finset V) := by
  classical
  obtain ⟨μ,hμ,heq⟩ := optimum_exists G
  have hcolor := cliqueBlowup_colorable_rounded hμ m
  have hn := ENat.toNat_le_of_le_natCast hcolor.chromaticNumber_le
  have hnr : ((cliqueBlowup G m).chromaticNumber.toNat : ℝ) ≤
      ∑ I, (⌈(m : ℝ)*μ I⌉₊ : ℝ) := by exact_mod_cast hn
  apply hnr.trans
  calc
    _ ≤ ∑ I, ((m : ℝ)*μ I + 1) := by
      apply Finset.sum_le_sum
      intro I _
      exact (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) (hμ.1 I))).le
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      change (m : ℝ) * cost μ + _ = _
      rw [heq]
      simp

end LinearListHadwiger.Fractional

namespace LinearListHadwiger
namespace FixedDecomposition
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

lemma budget_branch {u a b z : ℕ} (hu : 2*k < u) (hz : z < k)
    (ha : a < u) (hb : b < u) (hsum : a+b = u+z) :
    budget k a + budget k b + 1 ≤ budget k u := by
  unfold budget
  rw [ite_eq_right (by omega : ¬u ≤ 2*k)]
  split_ifs with hka hkb hkb
  · have hp : 2 ≤ u-k := by omega
    nlinarith
  · have hp : 2 ≤ u-k := by omega
    have hbp : b-k < u-k := by omega
    nlinarith
  · have hp : 2 ≤ u-k := by omega
    have hap : a-k < u-k := by omega
    nlinarith
  · have hsum' : (a-k)+(b-k) < u-k := by omega
    have ha0 : 0 < a-k := by omega
    have hb0 : 0 < b-k := by omega
    nlinarith [sq_nonneg ((a-k : ℕ) : ℤ),sq_nonneg ((b-k : ℕ) : ℤ)]

lemma Tree.leaf_subset {S U : Finset V} (d : Tree G k S) (hU : U ∈ d.leaves) :
    U ⊆ S := by
  induction d with
  | leaf _ =>
    have he : U = _ := List.mem_singleton.mp hU
    exact he ▸ Finset.Subset.refl _
  | branch hs hz l r ihl ihr =>
    rcases List.mem_append.mp hU with hl | hr
    · exact (ihl hl).trans hs.left_union_subset
    · exact (ihr hr).trans hs.swap.left_union_subset

lemma Tree.leaf_stop {S U : Finset V} (d : Tree G k S) (hU : U ∈ d.leaves) :
    U.card ≤ 2*k ∨ KConnectedOn G U k := by
  induction d with
  | leaf h =>
    have he : U = _ := List.mem_singleton.mp hU
    exact he ▸ h
  | branch hs hz l r ihl ihr =>
    rcases List.mem_append.mp hU with hl | hr
    · exact ihl hl
    · exact ihr hr

lemma Tree.separator_small {S Z : Finset V} (d : Tree G k S)
    (hZ : Z ∈ d.separators) : Z.card < k := by
  induction d with
  | leaf _ => simp [Tree.separators] at hZ
  | branch hs hz l r ihl ihr =>
    rcases List.mem_cons.mp hZ with rfl | hZ
    · exact hz
    · rcases List.mem_append.mp hZ with hl | hr
      · exact ihl hl
      · exact ihr hr

theorem exists_bounded_tree (S : Finset V) :
    ∃ d : Tree G k S, d.leaves.length + d.separators.length ≤ budget k S.card := by
  classical
  induction S using Finset.strongInductionOn with | _ S ih =>
  by_cases hs : S.card ≤ 2*k
  · refine ⟨Tree.leaf (Or.inl hs),?_⟩
    simp [Tree.leaves,Tree.separators,budget,hs]
  by_cases hc : KConnectedOn G S k
  · refine ⟨Tree.leaf (Or.inr hc),?_⟩
    simp only [Tree.leaves,Tree.separators,List.length_singleton,List.length_nil,Nat.add_zero]
    unfold budget
    rw [ite_eq_right hs]
    have hp : 1 ≤ S.card-k := by omega
    nlinarith
  obtain ⟨A,Z,B,hZ,hsp⟩ := exists_separator G S (by omega : k < S.card) hc
  obtain ⟨l,hl⟩ := ih _ hsp.left_union_ssubset
  obtain ⟨r,hr⟩ := ih _ hsp.swap.left_union_ssubset
  refine ⟨Tree.branch hsp hZ l r,?_⟩
  have hcard : (A ∪ Z).card + (B ∪ Z).card = S.card + Z.card := by
    rw [Finset.card_union_of_disjoint hsp.left_sep,
      Finset.card_union_of_disjoint hsp.sep_right.symm,
      ← hsp.union_eq,Finset.card_union_of_disjoint hsp.left_union_disjoint,
      Finset.card_union_of_disjoint hsp.left_sep]
    omega
  have hb := budget_branch (by omega : 2*k < S.card) hZ
    (Finset.card_lt_card hsp.left_union_ssubset)
    (Finset.card_lt_card hsp.swap.left_union_ssubset) hcard
  simp only [Tree.leaves,Tree.separators,List.length_append,List.length_cons]
  omega

lemma budget_le_square (k u : ℕ) : budget k u ≤ (u+1)^2 := by
  unfold budget
  split_ifs
  · nlinarith
  · have : u-k ≤ u := Nat.sub_le _ _
    nlinarith

lemma reachable_preserves {W : Type} {H : SimpleGraph W} {P : W → Prop}
    (hstep : ∀ u v, H.Adj u v → P u → P v) {u v : W}
    (hr : H.Reachable u v) (hu : P u) : P v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact hu
  | cons h p ih => exact ih (hstep _ _ h hu)

lemma confine_split {W : Type} [DecidableEq W] {H : SimpleGraph W}
    (π : W → V) (hπ : ∀ u v, H.Adj u v → G.Adj (π u) (π v) ∨ π u = π v)
    {S A Z B : Finset V} (hs : SeparatorSplit G S A Z B)
    {T : Finset W} {j : ℕ} (hT : KConnectedOn H T j)
    (hTS : ∀ u ∈ T, π u ∈ S)
    (hZ : (T.filter (fun u => π u ∈ Z)).card < j) :
    (∀ u ∈ T, π u ∈ A ∪ Z) ∨ (∀ u ∈ T, π u ∈ B ∪ Z) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨⟨u,hu,huAZ⟩,v,hv,hvBZ⟩ := hn
  have hmem (w : W) (hw : w ∈ T) : π w ∈ A ∨ π w ∈ Z ∨ π w ∈ B := by
    have hh := hTS w hw
    rw [← hs.union_eq] at hh
    simpa only [Finset.mem_union,or_assoc] using hh
  have huB : π u ∈ B := by have := hmem u hu; simp only [Finset.mem_union] at huAZ; tauto
  have hvA : π v ∈ A := by have := hmem v hv; simp only [Finset.mem_union] at hvBZ; tauto
  let R := T.filter (fun w => π w ∈ Z)
  have huR : u ∈ T \ R := by
    refine Finset.mem_sdiff.mpr ⟨hu,?_⟩
    simpa only [R,Finset.mem_filter,hu,true_and] using
      (show π u ∉ Z from fun hz => huAZ (Finset.mem_union_right _ hz))
  have hvR : v ∈ T \ R := by
    refine Finset.mem_sdiff.mpr ⟨hv,?_⟩
    simpa only [R,Finset.mem_filter,hv,true_and] using
      (show π v ∉ Z from fun hz => hvBZ (Finset.mem_union_right _ hz))
  have hc := hT.2 R (Finset.filter_subset _ _) hZ
  have hstep : ∀ a b : (↑(T \ R) : Set W),
      (H.induce (↑(T \ R) : Set W)).Adj a b → π a.val ∈ A → π b.val ∈ A := by
    intro a b hab ha
    have hbT := (Finset.mem_sdiff.mp b.property).1
    have hbZ : π b.val ∉ Z := by
      intro hz
      exact (Finset.mem_sdiff.mp b.property).2 (Finset.mem_filter.mpr ⟨hbT,hz⟩)
    rcases hmem b hbT with hb | hb | hb
    · exact hb
    · exact (hbZ hb).elim
    · rcases hπ a b hab with hedge | heq
      · exact (hs.anticomplete _ ha _ hb hedge).elim
      · exact heq ▸ ha
  have huA := reachable_preserves hstep (hc.preconnected ⟨v,hvR⟩ ⟨u,huR⟩) hvA
  exact Finset.disjoint_left.mp hs.left_right huA huB

lemma Tree.confine {W : Type} [DecidableEq W] {H : SimpleGraph W}
    {S : Finset V} (d : Tree G k S)
    (π : W → V) (hπ : ∀ u v, H.Adj u v → G.Adj (π u) (π v) ∨ π u = π v)
    {T : Finset W} {j : ℕ} (hT : KConnectedOn H T j)
    (hTS : ∀ u ∈ T, π u ∈ S)
    (hZ : ∀ Z ∈ d.separators, (T.filter (fun u => π u ∈ Z)).card < j) :
    ∃ L ∈ d.leaves, ∀ u ∈ T, π u ∈ L := by
  induction d with
  | leaf _ => exact ⟨_,by simp [Tree.leaves],hTS⟩
  | @branch S A Z B hs hz l r ihl ihr =>
    rcases confine_split π hπ hs hT hTS (hZ Z (by simp [Tree.separators])) with hl | hr
    · obtain ⟨L,hL,hTL⟩ := ihl hl (fun Z hZ' => hZ Z (by simp [Tree.separators,hZ']))
      exact ⟨L,List.mem_append_left _ hL,hTL⟩
    · obtain ⟨L,hL,hTL⟩ := ihr hr (fun Z hZ' => hZ Z (by simp [Tree.separators,hZ']))
      exact ⟨L,List.mem_append_right _ hL,hTL⟩

end FixedDecomposition
end LinearListHadwiger

namespace LinearListHadwiger.FixedDecomposition
open Fractional
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

lemma card_finset_subtype_le {V : Type} [Fintype V] [DecidableEq V] (A : Finset V) :
    Fintype.card (Finset (↑A : Set V)) ≤ Fintype.card (Finset V) := by
  exact Fintype.card_le_of_injective
    (fun s : Finset (↑A : Set V) => s.map (⟨Subtype.val,Subtype.val_injective⟩ : (↑A : Set V) ↪ V))
    (by intro s t h; exact Finset.map_injective _ h)

lemma lifted_separator_card {V : Type} [Fintype V] [DecidableEq V] {A Z : Finset V} {m : ℕ}
    (T : Finset ((↑A : Set V) × Fin m)) :
    (T.filter (fun u => u.1.val ∈ Z)).card ≤ (A ∩ Z).card*m := by
  classical
  let f : (↑A : Set V) × Fin m → V × Fin m := fun u => (u.1.val,u.2)
  have hf : Function.Injective f := by
    intro u v h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact congrArg (fun z : V × Fin m => z.2) h
  calc
    _ ≤ ((A ∩ Z).product (Finset.univ : Finset (Fin m))).card := by
      apply Finset.card_le_card_of_injOn f
      · intro u hu
        exact Finset.mem_product.mpr ⟨Finset.mem_inter.mpr
          ⟨u.1.property,(Finset.mem_filter.mp hu).2⟩,Finset.mem_univ _⟩
      · exact hf.injOn
    _ = _ := by simp

lemma cliqueBlowup_leaf_hom {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A L : Finset V} {m : ℕ}
    (T : Finset ((↑A : Set V) × Fin m))
    (hTL : ∀ u ∈ T, u.1.val ∈ L) :
    Nonempty (((cliqueBlowup (G.induce (↑A : Set V)) m).induce (↑T : Set _)) →g
      cliqueBlowup (G.induce (↑(A ∩ L) : Set V)) m) := by
  let f : (↑T : Set ((↑A : Set V) × Fin m)) → (↑(A ∩ L) : Set V) × Fin m :=
    fun u => (⟨u.val.1.val,Finset.mem_inter.mpr ⟨u.val.1.property,hTL _ u.property⟩⟩,u.val.2)
  refine ⟨⟨f,?_⟩⟩
  intro u v huv
  change G.Adj u.val.1.val v.val.1.val ∨
    (u.val.1 = v.val.1 ∧ u.val.2 ≠ v.val.2) at huv
  change G.Adj u.val.1.val v.val.1.val ∨
    ((f u).1 = (f v).1 ∧ u.val.2 ≠ v.val.2)
  rcases huv with h | ⟨h,h'⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_,h'⟩
    apply Subtype.ext
    exact congrArg (fun x : (↑A : Set V) => x.val) h

theorem fractional_le_leaves_add_separator {S A : Finset V} (d : Tree G k S)
    (hAS : A ⊆ S) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hleaf : ∀ L ∈ d.leaves, number (G.induce (↑(A ∩ L) : Set V)) ≤ a)
    (hsep : ∀ Z ∈ d.separators, ((A ∩ Z).card : ℝ) ≤ b) :
    number (G.induce (↑A : Set V)) ≤ a+6*b := by
  classical
  by_contra hn
  have hgap : 0 < number (G.induce (↑A : Set V))-(a+6*b) := by linarith
  obtain ⟨m,hm⟩ := exists_nat_gt ((12+(Fintype.card (Finset V) : ℝ))/
    (number (G.induce (↑A : Set V))-(a+6*b)))
  have hmbig : 12+(Fintype.card (Finset V) : ℝ) <
      (m : ℝ)*(number (G.induce (↑A : Set V))-(a+6*b)) :=
    (div_lt_iff₀ hgap).mp hm
  let F := cliqueBlowup (G.induce (↑A : Set V)) m
  let j := ⌈(m : ℝ)*b⌉₊ + 1
  have hj : 1 ≤ j := by simp [j]
  have hjlow : (m : ℝ)*b < j := by
    have := Nat.le_ceil ((m : ℝ)*b)
    dsimp [j]
    push_cast
    linarith
  have hjup : (j : ℝ) < (m : ℝ)*b+2 := by
    have := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) hb)
    dsimp [j]
    push_cast
    linarith

  have hlower := cliqueBlowup_chromatic_lower (G.induce (↑A : Set V)) m
  have hlargeR : (6*j : ℕ) < F.chromaticNumber.toNat := by
    have : (6 : ℝ)*j < (F.chromaticNumber.toNat : ℝ) := by
      dsimp [F]
      nlinarith [mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) ha, (show (0:ℝ) ≤ Fintype.card (Finset V) from Nat.cast_nonneg _)]
    exact_mod_cast this
  obtain ⟨T,hT,hχ⟩ := ordinary_connectivity_extraction F hj hlargeR
  let π : (↑A : Set V) × Fin m → V := fun u => u.1.val
  have hπ : ∀ u v, F.Adj u v → G.Adj (π u) (π v) ∨ π u = π v := by
    intro u v h
    rcases h with h | ⟨h,h'⟩
    · exact Or.inl h
    · exact Or.inr (congrArg Subtype.val h)
  have htests : ∀ Z ∈ d.separators, (T.filter (fun u => π u ∈ Z)).card < j := by
    intro Z hZ
    have hc := lifted_separator_card (Z := Z) T
    have hcr : ((T.filter (fun u => π u ∈ Z)).card : ℝ) ≤
      ((A ∩ Z).card : ℝ)*m := by exact_mod_cast hc
    have hrr : ((T.filter (fun u => π u ∈ Z)).card : ℝ) < j := by
      nlinarith [mul_le_mul_of_nonneg_right (hsep Z hZ) (Nat.cast_nonneg m)]
    exact_mod_cast hrr
  obtain ⟨L,hL,hTL⟩ := d.confine π hπ hT (fun u _ => hAS u.1.property) htests
  obtain ⟨hom⟩ := cliqueBlowup_leaf_hom (G := G) T hTL
  have hcolor := (cliqueBlowup (G.induce (↑(A ∩ L) : Set V)) m).colorable_chromaticNumber_of_fintype.of_hom hom
  have hχup := (ordinary_chromatic_le_iff (F.induce (↑T : Set _)) _).mpr hcolor
  have hχupR : ((F.induce (↑T : Set _)).chromaticNumber.toNat : ℝ) ≤
      ((cliqueBlowup (G.induce (↑(A ∩ L) : Set V)) m).chromaticNumber.toNat : ℝ) := by
    exact_mod_cast hχup
  have hu := cliqueBlowup_chromatic_upper (G.induce (↑(A ∩ L) : Set V)) m
  have hcost := card_finset_subtype_le (A ∩ L)
  have hcostR : (Fintype.card (Finset (↑(A ∩ L) : Set V)) : ℝ) ≤
      Fintype.card (Finset V) := by exact_mod_cast hcost
  have hχR : (F.chromaticNumber.toNat : ℝ)-6*j ≤
      ((F.induce (↑T : Set _)).chromaticNumber.toNat : ℝ) := by
    have he : (F.chromaticNumber.toNat-6*j : ℕ) + 6*j = F.chromaticNumber.toNat :=
      Nat.sub_add_cancel hlargeR.le
    have heR : ((F.chromaticNumber.toNat-6*j : ℕ) : ℝ) + 6*j = F.chromaticNumber.toNat := by
      exact_mod_cast he
    have hh : ((F.chromaticNumber.toNat-6*j : ℕ) : ℝ) ≤
      ((F.induce (↑T : Set _)).chromaticNumber.toNat : ℝ) := by exact_mod_cast hχ
    linarith
  have hla := mul_le_mul_of_nonneg_left (hleaf L hL) (Nat.cast_nonneg m)
  dsimp [F] at hχR hχupR
  have hh : (m : ℝ)*number (G.induce (↑A : Set V)) ≤
      (m : ℝ)*a + Fintype.card (Finset V) + 6*j := by
    linarith only [hlower,hχR,hχupR,hu,hcostR,hla]
  nlinarith only [hh,hmbig,hjup]

end LinearListHadwiger.FixedDecomposition

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.PairedSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open Fractional FixedDecomposition
variable {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω]

lemma expectation_inter_card {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω] {μ : Ω → ℝ} (W : Ω → Finset V) (U : Finset V) :
    expectation μ (fun ω => ((W ω ∩ U).card : ℝ)) =
      ∑ v ∈ U, probability μ (fun ω => v ∈ W ω) := by
  classical
  have hc (ω : Ω) : ((W ω ∩ U).card : ℝ) = ∑ v ∈ U, if v ∈ W ω then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp [Finset.filter_mem_eq_inter,Finset.inter_comm]
  simp only [expectation,hc,Finset.mul_sum,probability]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

lemma expectation_inter_card_le {μ : Ω → ℝ} (W : Ω → Finset V) {p : ℝ}
    (hp : ∀ v, probability μ (fun ω => v ∈ W ω) ≤ p) (U : Finset V) :
    expectation μ (fun ω => ((W ω ∩ U).card : ℝ)) ≤ (U.card : ℝ)*p := by
  rw [expectation_inter_card]
  calc
    _ ≤ ∑ _v ∈ U, p := Finset.sum_le_sum (fun v _ => hp v)
    _ = _ := by simp

theorem fixed_region {G : SimpleGraph V} {S : Finset V} {k : ℕ}
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (W : Ω → Finset V) (hWS : ∀ ω, W ω ⊆ S)
    {r p ε : ℝ} (hr : 0 < r) (hp : 0 ≤ p) (hε : 0 ≤ ε)
    (hsurv : ∀ v, probability μ (fun ω => v ∈ W ω) ≤ p)
    (hsparse : (2*k : ℕ)*p ≤ r/1000)
    (htailCard : ∀ U : Finset V, probability μ (fun ω => r/200 ≤
      |((W ω ∩ U).card : ℝ) - expectation μ (fun z => ((W z ∩ U).card : ℝ))|) ≤ ε)
    (htailFrac : ∀ U : Finset V, probability μ (fun ω => r/20 ≤
      |number (G.induce (↑(W ω ∩ U) : Set V)) -
        expectation μ (fun z => number (G.induce (↑(W z ∩ U) : Set V)))|) ≤ ε)
    (hsmall : ((S.card+1 : ℕ)^2 : ℝ)*ε < 1)
    (hfail : ∀ ω, 0 < μ ω → r/2 < number (G.induce (↑(W ω) : Set V))) :
    ∃ H ⊆ S, KConnectedOn G H k ∧
      r/4 < expectation μ (fun ω => number (G.induce (↑(W ω ∩ H) : Set V))) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨d,hd⟩ := exists_bounded_tree (G := G) (k := k) S
  let Idx := Fin d.leaves.length ⊕ Fin d.separators.length
  let cardBad (U : Finset V) (ω : Ω) : Prop := r/200 ≤
    |((W ω ∩ U).card : ℝ)-expectation μ (fun z => ((W z ∩ U).card : ℝ))|
  let fracBad (U : Finset V) (ω : Ω) : Prop := r/20 ≤
    |number (G.induce (↑(W ω ∩ U) : Set V))-
      expectation μ (fun z => number (G.induce (↑(W z ∩ U) : Set V)))|
  let bad : Idx → Ω → Prop := fun i => match i with
    | .inl l => if (d.leaves.get l).card ≤ 2*k then cardBad (d.leaves.get l)
      else fracBad (d.leaves.get l)
    | .inr z => cardBad (d.separators.get z)
  have hbad (i : Idx) : probability μ (bad i) ≤ ε := by
    cases i with
    | inl l =>
      dsimp [bad]
      split_ifs
      · exact htailCard _
      · exact htailFrac _
    | inr z => exact htailCard _
  have hcard : Fintype.card Idx ≤ (S.card+1)^2 := by
    simpa [Idx] using hd.trans (budget_le_square k S.card)
  have hcardR : (Fintype.card Idx : ℝ) ≤ ((S.card+1 : ℕ)^2 : ℝ) := by exact_mod_cast hcard
  have hbadall : probability μ (fun ω => ∃ i, bad i ω) < 1 := by
    calc
      _ ≤ ∑ i, probability μ (bad i) := probability_union_le hμ bad
      _ ≤ ∑ _ : Idx, ε := Finset.sum_le_sum (fun i _ => hbad i)
      _ = (Fintype.card Idx : ℝ)*ε := by simp
      _ ≤ ((S.card+1 : ℕ)^2 : ℝ)*ε := mul_le_mul_of_nonneg_right hcardR hε
      _ < 1 := hsmall
  obtain ⟨ω,hω,havoid⟩ := exists_positive_avoiding hμ hμsum hbadall
  have hsmallset (U : Finset V) (hU : U.card ≤ 2*k) (hgood : ¬cardBad U ω) :
      ((W ω ∩ U).card : ℝ) < r/100 := by
    have he := expectation_inter_card_le W hsurv U
    have hUr : (U.card : ℝ) ≤ (2*k : ℕ) := by exact_mod_cast hU
    have hmean : expectation μ (fun z => ((W z ∩ U).card : ℝ)) ≤ r/1000 :=
      he.trans ((mul_le_mul_of_nonneg_right hUr hp).trans hsparse)
    have hdev := (abs_lt.mp (lt_of_not_ge hgood)).2
    linarith
  have hsep : ∀ Z ∈ d.separators, ((W ω ∩ Z).card : ℝ) ≤ r/100 := by
    intro Z hZ
    obtain ⟨z,hz⟩ := List.mem_iff_get.mp hZ
    apply (hsmallset Z (by have := d.separator_small hZ; omega) ?_).le
    have hh : ¬bad (.inr z) ω := fun h => havoid ⟨.inr z,h⟩
    simpa only [bad,hz] using hh
  have hleaf : ∀ L ∈ d.leaves, number (G.induce (↑(W ω ∩ L) : Set V)) ≤ 3*r/10 := by
    intro L hL
    obtain ⟨l,hl⟩ := List.mem_iff_get.mp hL
    have hh : ¬bad (.inl l) ω := fun h => havoid ⟨.inl l,h⟩
    by_cases hs : L.card ≤ 2*k
    · have hc : ¬cardBad L ω := by simpa only [bad,hl,ite_eq_left hs] using hh
      have hc' := hsmallset L hs hc
      have hn : number (G.induce (↑(W ω ∩ L) : Set V)) ≤ ((W ω ∩ L).card : ℝ) := by
        simpa [Finset.filter_mem_eq_inter, Finset.inter_comm] using
          number_le_card (G.induce (↑(W ω ∩ L) : Set V))
      linarith
    · have hf : ¬fracBad L ω := by simpa only [bad,hl,ite_eq_right hs] using hh
      have hconn := (d.leaf_stop hL).resolve_left hs
      have hmean := hn L (d.leaf_subset hL) hconn
      have hdev := (abs_lt.mp (lt_of_not_ge hf)).2
      linarith
  have hnow := fractional_le_leaves_add_separator d (hWS ω)
    (by positivity : (0 : ℝ) ≤ 3*r/10) (by positivity : (0 : ℝ) ≤ r/100) hleaf hsep
  have hf := hfail ω hω
  linarith

end LinearListHadwiger.Sampling

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Knitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Knitting
open SimpleGraph PathPacking
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma min_degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {k : ℕ} (hc : KConnectedOn G S k) {u : V} (hu : u ∈ S) :
    k ≤ (Density.neighbors G S u).card := by
  classical
  by_contra hn
  have hn : (Density.neighbors G S u).card < k := by omega
  let N := Density.neighbors G S u
  have hNS : N ⊆ S := Finset.filter_subset _ _
  have huN : u ∉ N := by simp [N,Density.neighbors]
  have huR : u ∈ S \ N := Finset.mem_sdiff.mpr ⟨hu,huN⟩
  have hnot : ¬S \ N ⊆ {u} := by
    intro h
    have hh := Finset.card_le_card h
    have he := Finset.card_sdiff_add_card_eq_card hNS
    have hs := hc.1
    simp only [Finset.card_singleton] at hh
    dsimp [N] at he hh
    omega
  simp only [Finset.subset_iff,not_forall,Finset.mem_singleton] at hnot
  obtain ⟨v,hv,hvu⟩ := hnot
  obtain ⟨p⟩ := (hc.2 N hNS hn).preconnected ⟨u,huR⟩ ⟨v,hv⟩
  have hp : ¬p.Nil := p.not_nil_of_ne (fun h => hvu (congrArg Subtype.val h).symm)
  have ha : G.Adj u p.snd.val := p.adj_snd hp
  exact (Finset.mem_sdiff.mp p.snd.property).2
    (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp p.snd.property).1,ha⟩)

lemma induce_connected {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) {k : ℕ}
    (hc : KConnectedOn G S k) :
    KConnectedOn (G.induce (↑S : Set V)) Finset.univ k := by
  classical
  refine ⟨by simpa using hc.1,?_⟩
  intro X _ hx
  let Z := X.image Subtype.val
  have hZ : Z ⊆ S := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  have hZk : Z.card < k := by simpa [Z,Finset.card_image_of_injective _ Subtype.val_injective] using hx
  have hconn := hc.2 Z hZ hZk
  let f : G.induce (↑(S \ Z) : Set V) →g
      (G.induce (↑S : Set V)).induce (↑(Finset.univ \ X) : Set ↥S) :=
    { toFun := fun v => ⟨⟨v.val,(Finset.mem_sdiff.mp v.property).1⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hv =>
          (Finset.mem_sdiff.mp v.property).2 (Finset.mem_image.mpr ⟨_,hv,rfl⟩)⟩⟩
      map_rel' := by intro u v h; exact h }
  apply hconn.map f
  intro w
  have hw : w.val.val ∈ S \ Z := by
    refine Finset.mem_sdiff.mpr ⟨w.val.property,?_⟩
    intro hz
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hz
    have heq : a = w.val := Subtype.ext he
    exact (Finset.mem_sdiff.mp w.property).2 (heq ▸ ha)
  exact ⟨⟨w.val.val,hw⟩,rfl⟩

end LinearListHadwiger.Knitting

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Eligibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open Filter

theorem parameter_range_cutoff : ∀ᶠ t : ℝ in atTop,
    1 < t ∧ 1 ≤ Real.log t ∧ ∀ r : ℝ,
      t/Real.log t ≤ r → r ≤ 4*t →
      400 ≤ r ∧ 1 ≤ max 1 (t/r) ∧ max 1 (t/r) ≤ Real.log t ∧
      t ≤ r*max 1 (t/r) ∧ r*max 1 (t/r) ≤ 4*t := by
  have hl := (Real.isLittleO_log_id_atTop).bound (show (0:ℝ)<1/400 by norm_num)
  have hg := (Real.tendsto_log_atTop).eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hl,hg] with t ht hl hg
  have htpos : 0 < t := by linarith
  have hlog : 0 < Real.log t := by linarith
  have hl' : Real.log t ≤ (1/400:ℝ)*t := by
    simpa only [id_eq,Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos htpos] using hl
  have hr0 : 400 ≤ t/Real.log t := by
    apply (le_div_iff₀ hlog).mpr
    linarith
  refine ⟨ht,hg,?_⟩
  intro r hr hr'
  have hr400 := hr0.trans hr
  have hrpos : 0 < r := by linarith
  have htr : t/r ≤ Real.log t := by
    apply (div_le_iff₀ hrpos).mpr
    have hh := (div_le_iff₀ hlog).mp hr
    nlinarith
  refine ⟨hr400,le_max_left _ _,max_le hg htr,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) (t/r)) hrpos.le
    field_simp at hh
    nlinarith
  · rw [mul_max_of_nonneg _ _ hrpos.le]
    simp only [mul_one,mul_div_cancel₀ _ hrpos.ne']
    exact max_le hr' (by linarith)

lemma floor_parameter {t r y : ℝ} (ht : 0 < t) (hr : 400 ≤ r)
    (hy : 1 ≤ y) (hy' : t/r ≤ y) :
    1 ≤ ⌊r/200⌋₊ ∧ r/400 ≤ (⌊r/200⌋₊ : ℝ) ∧
    (⌈t/(⌊r/200⌋₊ : ℝ)⌉₊ : ℝ) ≤ 401*y := by
  have hrpos : 0 < r := by linarith
  have hfloor := Nat.lt_floor_add_one (r/200)
  have hfloorle := Nat.floor_le (by positivity : 0 ≤ r/200)
  have hx : 1 ≤ ⌊r/200⌋₊ := by
    apply (Nat.one_le_floor_iff _).mpr
    linarith
  have hx' : r/400 ≤ (⌊r/200⌋₊ : ℝ) := by linarith
  have hxpos : (0:ℝ) < ⌊r/200⌋₊ := by exact_mod_cast (by omega : 0 < ⌊r/200⌋₊)
  refine ⟨hx,hx',?_⟩
  have hd : t/(⌊r/200⌋₊ : ℝ) ≤ 400*(t/r) := by
    apply (div_le_iff₀ hxpos).mpr
    apply (le_of_mul_le_mul_right ?_ hrpos)
    field_simp
    nlinarith
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ t/(⌊r/200⌋₊ : ℝ))
  nlinarith

lemma sample_size_parameters {t n r y : ℝ} {B : ℕ}
    (ht : 1 < t) (hn : 1 ≤ n) (hnt : n ≤ t^(11/10:ℝ))
    (hr : 400 ≤ r) (hy : 1 ≤ y) (hry : t ≤ r*y) (hB : 1 ≤ B) :
    1 ≤ ⌈B*r*Real.log (2*y)⌉₊ ∧
    (⌈B*r*Real.log (2*y)⌉₊ : ℝ) ≤ (B+1)*r*Real.log (2*y) ∧
    1 ≤ ⌈n/r⌉₊ ∧ (⌈n/r⌉₊ : ℝ) ≤ 2*t^(1/10:ℝ)*y := by
  have htpos : 0 < t := by linarith
  have hrpos : 0 < r := by linarith
  have hypos : 0 < y := by linarith
  have hB' : (1:ℝ) ≤ B := by exact_mod_cast hB
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hlog : (1/2:ℝ) ≤ Real.log (2*y) := by
    have hh : Real.log 2 ≤ Real.log (2*y) := Real.log_le_log (by norm_num) (by linarith)
    norm_num at htwo
    linarith
  have hlarge : 1 ≤ r*Real.log (2*y) := by nlinarith
  have hsample : 0 < (B:ℝ)*r*Real.log (2*y) := by positivity
  have hN : 1 ≤ ⌈B*r*Real.log (2*y)⌉₊ := by
    have hh := Nat.le_ceil ((B:ℝ)*r*Real.log (2*y))
    by_contra h
    have hh' : ⌈B*r*Real.log (2*y)⌉₊=0 := by omega
    simp only [hh',Nat.cast_zero] at hh
    linarith
  have hM : 1 ≤ ⌈n/r⌉₊ := by
    have hh := Nat.le_ceil (n/r)
    have hnr : 0 < n/r := div_pos (by linarith) hrpos
    by_contra h
    have hh' : ⌈n/r⌉₊=0 := by omega
    simp only [hh',Nat.cast_zero] at hh
    linarith
  refine ⟨hN,?_,hM,?_⟩
  · have hh := Nat.ceil_lt_add_one hsample.le
    nlinarith
  · have hpow : t^(11/10:ℝ)=t^(1/10:ℝ)*t := by
      rw [←Real.rpow_add_one htpos.ne']
      norm_num
    have hp : 1 ≤ t^(1/10:ℝ) := Real.one_le_rpow ht.le (by norm_num)
    have hnratio : n/r ≤ t^(1/10:ℝ)*y := by
      apply (div_le_iff₀ hrpos).mpr
      calc
        n ≤ t^(11/10:ℝ) := hnt
        _ = t^(1/10:ℝ)*t := hpow
        _ ≤ t^(1/10:ℝ)*(r*y) := mul_le_mul_of_nonneg_left hry (by positivity)
        _ = _ := by ring
    have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ n/r)
    have hone : 1 ≤ t^(1/10:ℝ)*y := by nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hy)]
    nlinarith

lemma trial_count_parameters {t r y : ℝ} {B : ℕ}
    (ht : 0 < t) (hr : 400 ≤ r) (hy : 1 ≤ y) (hy' : t/r ≤ y)
    (hry : r*y ≤ 4*t)
    (hN : (⌈B*r*Real.log (2*y)⌉₊ : ℝ) ≤ (B+1)*r*Real.log (2*y)) :
    ((⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2 * ⌈B*r*Real.log (2*y)⌉₊ : ℕ) : ℝ) ≤
      (4*401^2*(B+1):ℝ)*t*y*Real.log (2*y) := by
  have hlog : 0 ≤ Real.log (2*y) := Real.log_nonneg (by linarith)
  have hq := (floor_parameter ht hr hy hy').2.2
  have hq' : (⌈t/(⌊r/200⌋₊ : ℝ)⌉₊ : ℝ)^2 ≤ 401^2*y^2 := by
    calc
      _ ≤ (401*y)^2 := by gcongr
      _ = _ := by ring
  push_cast at hN ⊢
  calc
    _ ≤ (401^2*y^2)*((B+1)*r*Real.log (2*y)) := by gcongr
    _ = (401^2*(B+1)*y*Real.log (2*y))*(r*y) := by ring
    _ ≤ (401^2*(B+1)*y*Real.log (2*y))*(4*t) := by gcongr
    _ = _ := by ring

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter

theorem concentration_numeric_cutoff {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, 1 < t ∧ ∀ y r s M : ℝ,
      1 ≤ y → y ≤ Real.log t → t/y ≤ r →
      0 < s → s ≤ A*t*y*Real.log (2*y) →
      0 < M → M ≤ 2*t^(1/10:ℝ)*y →
      t^(7/10:ℝ) ≤ (δ*r)^2/(2*s*(2*M)^2) := by
  have heps : 0 < δ^2/(64*A) := by positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop (6:ℝ)
    (show (0:ℝ)<1/10 by norm_num)).bound heps
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog] with t ht hlog
  have htpos : 0 < t := by linarith
  have hln : 0 ≤ Real.log t := Real.log_nonneg ht.le
  have hp : 0 < t^(1/10:ℝ) := Real.rpow_pos_of_pos htpos _
  have hu : 0 < t^(7/10:ℝ) := Real.rpow_pos_of_pos htpos _
  have hh : (Real.log t)^6 ≤ δ^2/(64*A)*t^(1/10:ℝ) := by
    rw [←Real.rpow_natCast (Real.log t) 6]
    simpa only [Nat.cast_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hln (6:ℝ)),
      abs_of_nonneg hp.le] using hlog
  refine ⟨ht,?_⟩
  intro y r s M hy hyt hyr hs hs' hM hM'
  have hypos : 0 < y := by linarith
  have hr : 0 < r := lt_of_lt_of_le (div_pos htpos hypos) hyr
  have hly : 0 ≤ Real.log (2*y) := Real.log_nonneg (by linarith)
  have hl : Real.log (2*y) ≤ 2*y := Real.log_le_self (by positivity)
  have hy6 : y^6 ≤ (Real.log t)^6 := by gcongr
  have hnum : 64*A*y^6 ≤ δ^2*t^(1/10:ℝ) := by
    have hh' := hy6.trans hh
    have h64 : 0 < 64*A := by positivity
    have hh'' := (mul_le_mul_of_nonneg_left hh' h64.le)
    field_simp at hh'' ⊢
    nlinarith
  have hry : t ≤ r*y := (div_le_iff₀ hypos).mp hyr
  have hsq : t^2 ≤ r^2*y^2 := by
    calc
      t^2 ≤ (r*y)^2 := by gcongr
      _ = _ := by ring
  have hpow : t*(t^(1/10:ℝ))^3*t^(7/10:ℝ)=t^2 := by
    have hh : (t^(1/10:ℝ))^3=t^(3/10:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul htpos.le]
      norm_num
    rw [hh]
    calc
      _ = t^(1:ℝ)*t^(3/10:ℝ)*t^(7/10:ℝ) := by rw [Real.rpow_one]
      _ = t^(2:ℝ) := by rw [←Real.rpow_add htpos,←Real.rpow_add htpos]; norm_num
      _ = _ := by rw [Real.rpow_two]
  have hb : 2*s*(2*M)^2*t^(7/10:ℝ)*y^2 ≤ δ^2*t^2 := by
    calc
      _ ≤ 2*(A*t*y*Real.log (2*y))*(2*(2*t^(1/10:ℝ)*y))^2*t^(7/10:ℝ)*y^2 := by
        gcongr
      _ ≤ 2*(A*t*y*(2*y))*(2*(2*t^(1/10:ℝ)*y))^2*t^(7/10:ℝ)*y^2 := by gcongr
      _ = (64*A*y^6)*(t*(t^(1/10:ℝ))^2*t^(7/10:ℝ)) := by ring
      _ ≤ (δ^2*t^(1/10:ℝ))*(t*(t^(1/10:ℝ))^2*t^(7/10:ℝ)) := by gcongr
      _ = δ^2*(t*(t^(1/10:ℝ))^3*t^(7/10:ℝ)) := by ring
      _ = δ^2*t^2 := by rw [hpow]
  have hb' : (2*s*(2*M)^2*t^(7/10:ℝ))*y^2 ≤ (δ*r)^2*y^2 := by
    calc
      _ ≤ δ^2*t^2 := hb
      _ ≤ δ^2*(r^2*y^2) := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = _ := by ring
  have hc := (mul_le_mul_iff_left₀ (sq_pos_of_pos hypos)).mp hb'
  apply (le_div_iff₀ (by positivity : 0 < 2*s*(2*M)^2)).mpr
  nlinarith

theorem uniform_bounded_differences {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ y r M : ℝ,
      1 ≤ y → y ≤ Real.log t → t/y ≤ r → 0 < M →
      M ≤ 2*t^(1/10:ℝ)*y →
      ∀ (ι Ω : Type) [Fintype ι] [Fintype Ω] [DecidableEq ι],
      1 ≤ Fintype.card ι → (Fintype.card ι : ℝ) ≤ A*t*y*Real.log (2*y) →
      ∀ (μ : ι → Ω → ℝ), (∀ i ω, 0 ≤ μ i ω) → (∀ i, ∑ ω, μ i ω=1) →
      ∀ f : (ι → Ω) → ℝ,
      (∀ i x x', (∀ j, j ≠ i → x j=x' j) → |f x-f x'| ≤ 2*M) →
      probability (productMass μ) (fun x => δ*r ≤ |f x-expectation (productMass μ) f|)
        ≤ 2*Real.exp (-t^(7/10:ℝ)) := by
  classical
  obtain ⟨T,hT⟩ := eventually_atTop.mp (concentration_numeric_cutoff hA hδ)
  refine ⟨T,?_⟩
  intro t ht y r M hy hyt hyr hM hM' ι Ω _ _ _ hn hs μ hμ hsum f hf
  have htc := hT t ht
  have hr : 0 < r := lt_of_lt_of_le (div_pos (by linarith [htc.1]) (by linarith)) hyr
  have hn' : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card ι)
  have hc := htc.2 y r (Fintype.card ι) M hy hyt hyr hn' hs hM hM'
  have hb := bounded_differences_general hn μ hμ hsum f
    (by positivity : 0 < 2*M) (mul_pos hδ hr) hf
  refine hb.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  exact neg_le_neg hc

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter

theorem source_uniform_concentration {B : ℕ} (hB : 1 ≤ B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈B*r*Real.log (2*y)⌉₊
      let M := ⌈n/r⌉₊
      let q := ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2
      ∀ (ι Ω : Type) [Fintype ι] [Fintype Ω] [DecidableEq ι],
      1 ≤ Fintype.card ι → Fintype.card ι ≤ q*N →
      ∀ (μ : ι → Ω → ℝ), (∀ i ω, 0 ≤ μ i ω) → (∀ i, ∑ ω, μ i ω=1) →
      ∀ f : (ι → Ω) → ℝ,
      (∀ i x x', (∀ j, j ≠ i → x j=x' j) → |f x-f x'| ≤ 2*M) →
      probability (productMass μ) (fun x => δ*r ≤ |f x-expectation (productMass μ) f|)
        ≤ 2*Real.exp (-t^(7/10:ℝ)) := by
  classical
  let A : ℝ := 4*401^2*(B+1)
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₂,hT₂⟩ := uniform_bounded_differences hA hδ
  refine ⟨max T₁ T₂,?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro ι Ω _ _ _ hi hiq μ hμ hsum f hf
  have hp := hT₁ t ((le_max_left _ _).trans ht)
  obtain ⟨hr,hy,hyt,hry,hry'⟩ := hp.2.2 r hrl hru
  obtain ⟨hN,hN',hM,hM'⟩ := sample_size_parameters hp.1 hn hnt hr hy hry hB
  have hs := trial_count_parameters (by linarith [hp.1]) hr hy
    (le_max_right (1:ℝ) (t/r)) hry' hN'
  have hypos : 0 < max 1 (t/r) := by linarith
  have hyr : t/max 1 (t/r) ≤ r := (div_le_iff₀ hypos).mpr (by nlinarith [hry])
  apply hT₂ t ((le_max_right _ _).trans ht) (max 1 (t/r)) r ⌈n/r⌉₊ hy hyt hyr
    (by exact_mod_cast (by omega : 0 < ⌈n/r⌉₊)) hM' ι Ω hi
  · exact (show (Fintype.card ι : ℝ) ≤
      ((⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2*⌈B*r*Real.log (2*max 1 (t/r))⌉₊ : ℕ) : ℝ)
      by exact_mod_cast hiq).trans hs
  · exact hμ
  · exact hsum
  · exact hf

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling

lemma attachment_size_parameters {t r y : ℝ} (ht : 0 < t) (hr : 400 ≤ r)
    (hru : r ≤ 4*t) (hy : 1 ≤ y) (hy' : t/r ≤ y) :
    ((⌊r/200⌋₊ * ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2 : ℕ) : ℝ) ≤ 403*t*y := by
  have hrpos : 0 < r := by linarith
  obtain ⟨hxp,hxlow,hceil⟩ := floor_parameter ht hr hy hy'
  let x : ℝ := ⌊r/200⌋₊
  have hxpos : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < ⌊r/200⌋₊)
  have hxup : x ≤ r/200 := Nat.floor_le (by positivity)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ t/x by positivity)
  have htf : t^2/x ≤ 400*t*(t/r) := by
    apply (div_le_iff₀ hxpos).mpr
    apply le_of_mul_le_mul_right ?_ hrpos
    dsimp [x] at *
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ t^2 by positivity) (show 0 ≤ 400*(⌊r/200⌋₊:ℝ)-r by linarith)]
  have hc' : (⌈t/x⌉₊ : ℝ)^2 ≤ (t/x+1)^2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hc.le
  have he : x*(t/x+1)^2=t^2/x+2*t+x := by field_simp; ring
  push_cast
  change x*(⌈t/x⌉₊ : ℝ)^2 ≤ _
  calc
    _ ≤ x*(t/x+1)^2 := mul_le_mul_of_nonneg_left hc' hxpos.le
    _ = t^2/x+2*t+x := he
    _ ≤ 400*t*(t/r)+2*t+r/200 := by gcongr
    _ ≤ 403*t*y := by nlinarith

lemma attachment_budget {t r y : ℝ} {γ : ℕ} (ht : 0 < t) (hr : 400 ≤ r)
    (hru : r ≤ 4*t) (hy : 1 ≤ y) (hy' : t/r ≤ y) (hγ : 1 ≤ γ) :
    let x := ⌊r/200⌋₊
    let q := ⌈t/(x:ℝ)⌉₊^2
    let k := ⌈(1000000*γ:ℝ)*t*y⌉₊
    r ≤ k ∧ 64*(2*x*q) < k ∧ γ*(2*x*q) ≤ k/32 := by
  dsimp only
  have hxq := attachment_size_parameters ht hr hru hy hy'
  have hypos : 0 < y := by linarith
  have hγ' : (1:ℝ) ≤ γ := by exact_mod_cast hγ
  have hty : 0 < t*y := mul_pos ht hypos
  have hk := Nat.le_ceil ((1000000*γ:ℝ)*t*y)
  have hkR : 64*((2*⌊r/200⌋₊*⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2:ℕ):ℝ) <
      ⌈(1000000*γ:ℝ)*t*y⌉₊ := by
    push_cast at hxq ⊢
    nlinarith [mul_nonneg (show 0 ≤ (γ:ℝ)-1 by linarith) hty.le]
  have hkG : (32*(γ*(2*⌊r/200⌋₊*⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2)):ℕ) ≤
      ⌈(1000000*γ:ℝ)*t*y⌉₊ := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    push_cast at hxq
    have hh := mul_le_mul_of_nonneg_left hxq (show (0:ℝ)≤64*γ by positivity)
    nlinarith
  refine ⟨?_,by exact_mod_cast hkR,?_⟩
  · nlinarith [mul_nonneg (show 0 ≤ (γ:ℝ)-1 by linarith) hty.le]
  · exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simpa [Nat.mul_comm] using hkG)

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Finset ConnectivityTests
variable {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω]

theorem complement_failure (G : SimpleGraph V) [DecidableRel G.Adj]
    {n r ε : ℝ} {k : ℕ} (hk : 64 ≤ k) (hr : 0 < r) (hrk : r ≤ k)
    (hord : (Fintype.card V : ℝ) ≤ n) (hconn : KConnectedOn G univ k)
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (U : Ω → Finset V)
    (hsurv : ∀ v, probability μ (fun ω => v ∈ U ω) ≤ 1/10000)
    (hε : 0 ≤ ε)
    (htail : ∀ A : Finset V, probability μ (fun ω => r/100 ≤
      |((U ω ∩ A).card : ℝ)-expectation μ (fun z => ((U z ∩ A).card : ℝ))|) ≤ ε) :
    probability μ (fun ω => ¬((∀ v, k ≤ 2*((univ \ U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (univ \ U ω) (k/32))) ≤
      (n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε := by
  classical
  obtain ⟨F,hFcard,hF,hFtest⟩ := cut_test G hk hord hconn
  have hD (v : V) : ∃ D ⊆ Density.neighbors G univ v, D.card=k :=
    exists_subset_card_eq (Knitting.min_degree G hconn (mem_univ v))
  choose D hD hDc using hD
  let Idx := V ⊕ ↥F
  let A : Idx → Finset V := fun i => match i with
    | .inl v => D v
    | .inr E => endpoints E.val
  let bad : Idx → Ω → Prop := fun i ω => r/100 ≤
    |((U ω ∩ A i).card : ℝ)-expectation μ (fun z => ((U z ∩ A i).card : ℝ))|
  have hbad (i : Idx) : probability μ (bad i) ≤ ε := htail (A i)
  have hgood (ω : Ω) (havoid : ∀ i, ¬bad i ω) :
      (∀ v, k ≤ 2*((univ \ U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (univ \ U ω) (k/32) := by
    have hsmall (i : Idx) (hAk : (A i).card ≤ k) : 32*(U ω ∩ A i).card < k := by
      have he := expectation_inter_card_le U hsurv (A i)
      have hAc : ((A i).card : ℝ) ≤ k := by exact_mod_cast hAk
      have hm : expectation μ (fun z => ((U z ∩ A i).card : ℝ)) ≤ (k:ℝ)/10000 := by
        nlinarith
      have hdev := (abs_lt.mp (lt_of_not_ge (havoid i))).2
      have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hh : (32:ℝ)*((U ω ∩ A i).card : ℝ) < k := by
        nlinarith
      exact_mod_cast hh
    have hneigh (v : V) : k ≤ 2*((univ \ U ω).filter (G.Adj v)).card := by
      have hc := hsmall (.inl v) (by dsimp [A]; exact (hDc v).le)
      have hd : (D v \ U ω).card+(D v ∩ U ω).card=k := by
        rw [card_sdiff_add_card_inter,hDc]
      have hsub : D v \ U ω ⊆ (univ \ U ω).filter (G.Adj v) := by
        intro w hw
        obtain ⟨hwD,hwU⟩ := mem_sdiff.mp hw
        have hadj := hD v hwD
        simp only [Density.neighbors,mem_filter,mem_univ,true_and] at hadj
        exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hwU⟩,hadj⟩
      have hcard := card_le_card hsub
      dsimp [A] at hc
      rw [inter_comm] at hc
      omega
    refine ⟨hneigh,hFtest (U ω) hneigh ?_⟩
    intro E hE
    have he := (hF E hE).1
    have hcard : (endpoints E).card ≤ k := by
      have hb := endpoints_card_le E
      have hd := Nat.div_mul_le_self k 8
      omega
    have hc := hsmall (.inr ⟨E,hE⟩) hcard
    simpa [A,inter_comm] using hc
  have hprob : probability μ (fun ω => ¬((∀ v, k ≤ 2*((univ \ U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (univ \ U ω) (k/32))) ≤ probability μ (fun ω => ∃ i, bad i ω) := by
    apply probability_mono hμ
    intro ω h
    by_contra hn
    push Not at hn
    exact h (hgood ω hn)
  calc
    _ ≤ probability μ (fun ω => ∃ i, bad i ω) := hprob
    _ ≤ ∑ i, probability μ (bad i) := probability_union_le hμ bad
    _ ≤ ∑ _ : Idx, ε := sum_le_sum (fun i _ => hbad i)
    _ = ((Fintype.card V : ℝ)+F.card)*ε := by simp [Idx]
    _ ≤ _ := by gcongr

end LinearListHadwiger.Sampling

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Thinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open Filter

theorem complement_numeric_cutoff :
    ∀ᶠ t : ℝ in atTop, ∀ n k : ℝ, 1 ≤ n → n ≤ t^(11/10:ℝ) → t ≤ k →
      (n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1)) *
        (2*Real.exp (-t^(7/10:ℝ))) ≤ 1/100 := by
  have hlog := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/10 by norm_num)).bound
    (show (0:ℝ)<1/100 by norm_num)
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<1/10 by norm_num)).eventually
    (eventually_ge_atTop (100:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog,hp] with t ht hlog hp
  intro n k hn hnt htk
  let p : ℝ := t^(1/10:ℝ)
  have htpos : 0 < t := by linarith
  have hkpos : 0 < k := by linarith
  have hp100 : 100 ≤ p := hp
  have hppos : 0 < p := by linarith
  have hlogt : Real.log t ≤ p/100 := by
    have hh : Real.log t ≤ (1/100:ℝ)*p := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg ht.le),
        abs_of_nonneg (Real.rpow_nonneg htpos.le (1/10:ℝ))] using hlog
    linarith
  have hlo2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have horder : 0 < t^(11/10:ℝ) := Real.rpow_pos_of_pos htpos _
  have hlog2n : Real.log (2*n) ≤ p := by
    calc
      _ ≤ Real.log (2*t^(11/10:ℝ)) := Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log 2+(11/10:ℝ)*Real.log t := by
        rw [Real.log_mul (by norm_num) horder.ne',Real.log_rpow htpos]
      _ ≤ p := by linarith
  have hlognp : Real.log (n+1) ≤ p := by
    exact (Real.log_le_log (by positivity) (by linarith : n+1 ≤ 2*n)).trans hlog2n
  have hratio : n/k ≤ p := by
    apply (div_le_iff₀ hkpos).mpr
    have he : t^(11/10:ℝ)=p*t := by
      dsimp [p]
      rw [←Real.rpow_add_one htpos.ne']
      norm_num
    rw [he] at hnt
    nlinarith
  have hceil : (⌈10*(n/k)*Real.log (2*n)⌉₊ : ℝ)+1 ≤ 12*p^2 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 10*(n/k)*Real.log (2*n) by
      have hh : 0 ≤ Real.log (2*n) := Real.log_nonneg (by linarith)
      positivity)
    have hm : 10*(n/k)*Real.log (2*n) ≤ 10*p*p := by
      have hh : 0 ≤ Real.log (2*n) := Real.log_nonneg (by linarith)
      gcongr
    nlinarith [sq_nonneg (p-1)]
  have hpow : (n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1) ≤ Real.exp (12*p^3) := by
    have he : (n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1) =
        Real.exp ((⌈10*(n/k)*Real.log (2*n)⌉₊+1:ℕ)*Real.log (n+1)) := by
      rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
    rw [he]
    apply Real.exp_le_exp.mpr
    have hnlog : 0 ≤ Real.log (n+1) := Real.log_nonneg (by linarith)
    calc
      _ ≤ (12*p^2)*p := by push_cast; gcongr
      _ = _ := by ring
  have hp7 : t^(7/10:ℝ)=p^7 := by
    dsimp [p]
    rw [←Real.rpow_natCast,←Real.rpow_mul htpos.le]
    norm_num
  have hp4 : 24 ≤ p^4 := by
    calc
      _ ≤ (100:ℝ)^4 := by norm_num
      _ ≤ p^4 := by gcongr
  have hhalf : 12*p^3 ≤ t^(7/10:ℝ)/2 := by
    rw [hp7]
    have hh := mul_le_mul_of_nonneg_left hp4 (show 0 ≤ p^3 by positivity)
    nlinarith [show p^3*p^4=p^7 by ring]
  have hnexp : n ≤ Real.exp (t^(7/10:ℝ)/2) := by
    have he : n+1 ≤ Real.exp p := by
      calc
        n+1 = Real.exp (Real.log (n+1)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp p := Real.exp_le_exp.mpr hlognp
    have hple : p ≤ 12*p^3 := by
      have hp2 : 1 ≤ p^2 := by nlinarith [sq_nonneg (p-1)]
      have hh := mul_le_mul_of_nonneg_left hp2 hppos.le
      nlinarith
    exact (by linarith : n ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr (hple.trans hhalf))
  have htests := hpow.trans (Real.exp_le_exp.mpr hhalf)
  have hlarge : 10000 ≤ t^(7/10:ℝ) := by
    rw [hp7]
    calc
      _ ≤ (100:ℝ)^7 := by norm_num
      _ ≤ p^7 := by gcongr
  have hdecay : 4*Real.exp (-(t^(7/10:ℝ)/2)) ≤ 1/100 := by
    have hexp := Real.add_one_le_exp (t^(7/10:ℝ)/2)
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  calc
    _ ≤ (2*Real.exp (t^(7/10:ℝ)/2))*(2*Real.exp (-t^(7/10:ℝ))) := by
      gcongr
      linarith
    _ = 4*Real.exp (-(t^(7/10:ℝ)/2)) := by
      rw [show (2*Real.exp (t^(7/10:ℝ)/2))*(2*Real.exp (-t^(7/10:ℝ))) =
        4*(Real.exp (t^(7/10:ℝ)/2)*Real.exp (-t^(7/10:ℝ))) by ring,
        ←Real.exp_add]
      congr 2
      ring
    _ ≤ _ := hdecay

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling

lemma survival_log_bound {r y : ℝ} (hr : 0 < r) (hy : 1 ≤ y) :
    Real.exp (-((⌈192*r*Real.log (2*y)⌉₊ : ℝ)/(4*r))) * y^4 ≤ 1/(2:ℝ)^48 := by
  have hypos : 0 < y := by linarith
  have hlog : 0 ≤ Real.log (2*y) := Real.log_nonneg (by linarith)
  have hN := Nat.le_ceil (192*r*Real.log (2*y))
  have he : 48*Real.log (2*y) ≤ (⌈192*r*Real.log (2*y)⌉₊ : ℝ)/(4*r) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*r)).mpr
    nlinarith
  have hpexp : Real.exp (-((⌈192*r*Real.log (2*y)⌉₊ : ℝ)/(4*r))) ≤
      1/(2*y)^48 := by
    calc
      _ ≤ Real.exp (-(48*Real.log (2*y))) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [Real.exp_neg,show (48:ℝ)*Real.log (2*y)=(48:ℕ)*Real.log (2*y) by norm_num,
          Real.exp_nat_mul,Real.exp_log (by positivity)]
        simp only [one_div]
  have hpow : y^4 ≤ y^48 := by
    exact pow_le_pow_right₀ hy (by norm_num)
  calc
    _ ≤ (1/(2*y)^48)*y^4 := mul_le_mul_of_nonneg_right hpexp (by positivity)
    _ ≤ (1/(2*y)^48)*y^48 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [mul_pow]; field_simp

theorem source_sparseness {t r : ℝ} (ht : 1 ≤ t) (hr : 400 ≤ r) (hru : r ≤ 4*t) :
    let y := max 1 (t/r)
    let p := Real.exp (-((⌈192*r*Real.log (2*y)⌉₊ : ℝ)/(4*r)))
    let q := ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2
    let k := ⌈(1000000*65536:ℝ)*t*y⌉₊
    2*k*p ≤ r/1000 ∧ (q:ℝ)^2*p ≤ 1/10000 ∧ (q:ℝ)*p ≤ 1/10000 := by
  dsimp only
  let y := max 1 (t/r)
  let p := Real.exp (-((⌈192*r*Real.log (2*y)⌉₊ : ℝ)/(4*r)))
  let q := ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2
  let k := ⌈(1000000*65536:ℝ)*t*y⌉₊
  have htpos : 0 < t := by linarith
  have hrpos : 0 < r := by linarith
  have hy : 1 ≤ y := le_max_left _ _
  have hy' : t/r ≤ y := le_max_right _ _
  have hty : t ≤ r*y := by simpa only [mul_comm] using (div_le_iff₀ hrpos).mp hy'
  have hp : 0 < p := Real.exp_pos _
  have hpy : p*y^4 ≤ 1/(2:ℝ)^48 := survival_log_bound hrpos hy
  have hkc : (k:ℝ) ≤ (1000000*65536+1:ℝ)*t*y := by
    have hh := Nat.ceil_lt_add_one
      (show 0 ≤ (1000000*65536:ℝ)*t*y by positivity)
    have hty1 : 1 ≤ t*y := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hy)]
    dsimp [k]
    nlinarith
  obtain ⟨hx,hxl,hq⟩ := floor_parameter htpos hr hy hy'
  have hqc : (q:ℝ) ≤ 401^2*y^2 := by
    dsimp [q]
    push_cast
    have hh := (sq_le_sq₀ (by positivity : (0:ℝ) ≤ (⌈t/(⌊r/200⌋₊ : ℝ)⌉₊:ℝ))
      (by positivity : (0:ℝ) ≤ 401*y)).mpr hq
    nlinarith
  have hqpos : 1 ≤ q := by
    have hxpos : (0:ℝ) < (⌊r/200⌋₊:ℝ) := by exact_mod_cast (by omega : 0 < ⌊r/200⌋₊)
    have hh := Nat.le_ceil (t/(⌊r/200⌋₊:ℝ))
    have hc : 1 ≤ ⌈t/(⌊r/200⌋₊:ℝ)⌉₊ := by
      by_contra h
      have he : ⌈t/(⌊r/200⌋₊:ℝ)⌉₊=0 := by omega
      rw [he,Nat.cast_zero] at hh
      exact (not_le_of_gt (div_pos htpos hxpos)) hh
    exact one_le_pow₀ hc
  have hpy2 : p*y^2 ≤ 1/(2:ℝ)^48 := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy (by norm_num : 2 ≤ 4)) hp.le).trans hpy
  have hkbound : 2*(k:ℝ)*p ≤ r/1000 := by
    calc
      _ ≤ 2*((1000000*65536+1:ℝ)*t*y)*p := by gcongr
      _ ≤ 2*((1000000*65536+1:ℝ)*(r*y)*y)*p := by gcongr
      _ = (2*(1000000*65536+1:ℝ)*r)*(p*y^2) := by ring
      _ ≤ (2*(1000000*65536+1:ℝ)*r)*(1/(2:ℝ)^48) := by gcongr
      _ ≤ r/1000 := by norm_num; nlinarith
  have hqbound : (q:ℝ)^2*p ≤ 1/10000 := by
    calc
      _ ≤ (401^2*y^2)^2*p := by gcongr
      _ = (401:ℝ)^4*(p*y^4) := by ring
      _ ≤ (401:ℝ)^4*(1/(2:ℝ)^48) := by gcongr
      _ ≤ _ := by norm_num
  refine ⟨hkbound,hqbound,?_⟩
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hqpos
  have hh : (q:ℝ) ≤ (q:ℝ)^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hh hp.le).trans hqbound

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter

theorem polynomial_tail_cutoff (C d : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, C*t^d*(2*Real.exp (-t^(7/10:ℝ))) < η := by
  have ht := tendsto_rpow_atTop (show (0:ℝ)<7/10 by norm_num)
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d/(7/10:ℝ))
    1 (by norm_num)).comp ht
  have hl : Tendsto (fun t : ℝ => t^d*Real.exp (-t^(7/10:ℝ))) atTop (nhds 0) := by
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    dsimp
    rw [←Real.rpow_mul ht.le]
    congr 2 <;> ring
  have hm := hl.const_mul (2*C)
  have he := hm.eventually (eventually_lt_nhds (show (2*C)*0 < η by simpa using hη))
  filter_upwards [he] with t ht
  rw [show C*t^d*(2*Real.exp (-t^(7/10:ℝ))) =
    (2*C)*(t^d*Real.exp (-t^(7/10:ℝ))) by ring]
  exact ht

lemma decomposition_tail_cutoff :
    ∀ᶠ t : ℝ in atTop, ∀ n : ℝ, 1 ≤ n → n ≤ t^(11/10:ℝ) →
      (n+1)^2*(2*Real.exp (-t^(7/10:ℝ))) < 1 := by
  have hh := polynomial_tail_cutoff 4 (22/10) (show (0:ℝ)<1 by norm_num)
  filter_upwards [eventually_gt_atTop (1:ℝ),hh] with t ht hh
  intro n hn hnt
  have hp : (t^(11/10:ℝ))^2=t^(22/10:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : (0:ℝ) ≤ t)]
    norm_num
  calc
    _ ≤ (2*t^(11/10:ℝ))^2*(2*Real.exp (-t^(7/10:ℝ))) := by
      gcongr
      linarith
    _ = 4*t^(22/10:ℝ)*(2*Real.exp (-t^(7/10:ℝ))) := by rw [mul_pow,hp]; ring
    _ < _ := hh

lemma private_tail_cutoff :
    ∀ᶠ t : ℝ in atTop, ∀ r : ℝ, t/Real.log t ≤ r → r ≤ 4*t →
      ((⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2 : ℕ) : ℝ)*(2*Real.exp (-t^(7/10:ℝ))) < 1/100 := by
  have hh := polynomial_tail_cutoff (401^2) 2 (show (0:ℝ)<1/100 by norm_num)
  filter_upwards [parameter_range_cutoff,hh] with t ht hh
  intro r hrl hru
  obtain ⟨hr,hy,hyt,hry,hry'⟩ := ht.2.2 r hrl hru
  have htpos : 0 < t := by linarith [ht.1]
  have hq := (floor_parameter (by linarith [ht.1]) hr hy (le_max_right 1 (t/r))).2.2
  have hlogt : Real.log t ≤ t := Real.log_le_self (by linarith [ht.1])
  have hqc : ((⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2 : ℕ) : ℝ) ≤ 401^2*t^2 := by
    push_cast
    have hh : (⌈t/(⌊r/200⌋₊ : ℝ)⌉₊ : ℝ) ≤ 401*t := by linarith
    have hp := (sq_le_sq₀ (by positivity : (0:ℝ) ≤ (⌈t/(⌊r/200⌋₊ : ℝ)⌉₊ : ℝ))
      (by positivity : (0:ℝ) ≤ 401*t)).mpr hh
    nlinarith
  calc
    _ ≤ 401^2*t^2*(2*Real.exp (-t^(7/10:ℝ))) := by gcongr
    _ < _ := by simpa only [Real.rpow_ofNat] using hh

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Finset Fractional Filter

lemma source_q_pos {t r : ℝ} (ht : 0 < t) (hr : 400 ≤ r) :
    1 ≤ ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2 := by
  have hx : 1 ≤ ⌊r/200⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hxpos : (0:ℝ) < (⌊r/200⌋₊:ℝ) := by exact_mod_cast (by omega : 0 < ⌊r/200⌋₊)
  have hh : 0 < ⌈t/(⌊r/200⌋₊:ℝ)⌉₊ := Nat.ceil_pos.mpr (div_pos ht hxpos)
  exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))

theorem source_fixed_region :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈192*r*Real.log (2*y)⌉₊
      let M := ⌈n/r⌉₊
      let k := ⌈(1000000*65536:ℝ)*t*y⌉₊
      ∀ (V Ω : Type) [Fintype V] [DecidableEq V] [Fintype Ω],
      ∀ G : SimpleGraph V, (Fintype.card V : ℝ) ≤ n →
      ∀ π : Ω → ℝ, (∀ ω, 0 ≤ π ω) → (∑ ω, π ω=1) →
      ∀ (I : Ω → Finset V) (E : Fin N → Finset V),
      (∀ ω, (I ω).card ≤ M) →
      (∀ v, probability π (fun ω => v∈I ω)=1/(2*r)) →
      (∀ v, (N:ℝ)/2 ≤ (univ.filter (fun j => v∈E j)).card) →
      (∀ x, 0 < productMass (fun _ : Fin N => π) x →
        r/2 < number (G.induce (↑(remainder E I x) : Set V))) →
      ∃ H : Finset V, KConnectedOn G H k ∧
        r/4 < expectation (productMass (fun _ : Fin N => π))
          (fun x => number (G.induce (↑(remainder E I x ∩ H) : Set V))) := by
  classical
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₁,hT₁⟩ := source_uniform_concentration (by norm_num : (1:ℕ)≤192)
    (by norm_num : (0:ℝ)<1/200)
  obtain ⟨T₂,hT₂⟩ := source_uniform_concentration (by norm_num : (1:ℕ)≤192)
    (by norm_num : (0:ℝ)<1/20)
  obtain ⟨T₃,hT₃⟩ := eventually_atTop.mp decomposition_tail_cutoff
  refine ⟨max (max T₀ T₁) (max T₂ T₃),?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V Ω _ _ _ G hord π hπ hs I E hI hmarg hE hfail
  have hp := hT₀ t ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
  obtain ⟨hr,hy,hyt,hry,hry'⟩ := hp.2.2 r hrl hru
  have htpos : 0 < t := by linarith [hp.1]
  obtain ⟨hN,hN',hM,hM'⟩ := sample_size_parameters hp.1 hn hnt hr hy hry
    (by norm_num : (1:ℕ)≤192)
  have hq := source_q_pos htpos hr
  let N := ⌈192*r*Real.log (2*max 1 (t/r))⌉₊
  let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
  have hcard : Fintype.card (Fin N) ≤ q*N := by
    rw [Fintype.card_fin]
    simpa only [one_mul] using Nat.mul_le_mul_right N hq
  have hNcard : 1 ≤ Fintype.card (Fin N) := by simpa [N] using hN
  have hc := hT₁ t n r ((le_max_right _ _).trans ((le_max_left _ _).trans ht))
    hn hnt hrl hru (Fin N) Ω hNcard hcard (fun _ => π) (fun _ => hπ) (fun _ => hs)
  have hf := hT₂ t n r ((le_max_left _ _).trans ((le_max_right _ _).trans ht))
    hn hnt hrl hru (Fin N) Ω hNcard hcard (fun _ => π) (fun _ => hπ) (fun _ => hs)
  have hsurv (v : V) := remainder_survival_bound (fun _ : Fin N => hs) E I
    (by linarith : 1 ≤ r) (fun _ => hmarg) (by simpa [N] using hE) v
  have hsparse := (source_sparseness hp.1.le hr hru).1
  have htailCard (A : Finset V) := hc (fun x => ((A ∩ remainder E I x).card : ℝ))
    (remainder_card_bounded_changes E I hI A)
  have htailFrac (A : Finset V) := hf
    (fun x => number (G.induce (↑(A ∩ remainder E I x) : Set V)))
    (remainder_fractional_bounded_changes G E I hI A)
  have hcomm (A : Finset V) (x : Fin N → Ω) :
      number (G.induce (↑(A ∩ remainder E I x) : Set V)) =
      number (G.induce (↑(remainder E I x ∩ A) : Set V)) :=
    congrArg (fun S : Finset V => number (G.induce (↑S : Set V))) (Finset.inter_comm _ _)
  have hsmall := hT₃ t ((le_max_right _ _).trans ((le_max_right _ _).trans ht)) n hn hnt
  obtain ⟨H,hH,hconn,hmean⟩ := fixed_region (G := G) (S := univ)
    (productMass_nonneg (fun _ : Fin N => hπ)) (productMass_sum (fun _ : Fin N => hs))
    (remainder E I) (fun _ => subset_univ _) (by linarith : 0 < r)
    (Real.exp_pos _).le (by positivity : (0:ℝ) ≤ 2*Real.exp (-t^(7/10:ℝ)))
    (by simpa only [Fintype.card_fin,N,neg_div] using hsurv)
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hsparse)
    (by intro A; simpa only [Finset.inter_comm A,show (1/200:ℝ)*r=r/200 by ring] using htailCard A)
    (by intro A; simpa only [hcomm,show (1/20:ℝ)*r=r/20 by ring] using htailFrac A)
    (lt_of_le_of_lt (by push_cast; simp only [card_univ]; gcongr) hsmall)
    hfail
  exact ⟨H,hconn,hmean⟩

end LinearListHadwiger.Sampling

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.SamplingConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open Finset
variable {κ ι Ω V : Type} [Fintype κ] [Fintype ι] [Fintype Ω] [Fintype V]
  [DecidableEq V] [DecidableEq κ] [DecidableEq ι]

lemma probability_product_curry (μ : κ → ι → Ω → ℝ) (P : (κ → ι → Ω) → Prop) :
    probability (productMass (fun k => productMass (μ k))) P =
      probability (productMass (fun j : κ × ι => μ j.1 j.2))
        (fun x => P (fun k i => x (k,i))) := by
  classical
  let e : (κ × ι → Ω) ≃ (κ → ι → Ω) := Equiv.curry κ ι Ω
  have hm (x : κ × ι → Ω) :
      productMass (fun k => productMass (μ k)) (e x) =
        productMass (fun j : κ × ι => μ j.1 j.2) x := by
    simp [productMass,e,Fintype.prod_prod_type]
  unfold probability
  rw [←e.sum_comp]
  apply sum_congr rfl
  intro x _
  change (if P (fun k i => x (k,i)) then _ else 0) = _
  rw [hm]

lemma unionRemainders_survival {π : Ω → ℝ} (hπ : ∀ ω, 0 ≤ π ω)
    (hs : ∑ ω, π ω=1) (E : ι → Finset V) (I : Ω → Finset V) (v : V) :
    probability (productMass (fun _ : κ × ι => π)) (fun x => v∈unionRemainders E I x) ≤
      (Fintype.card κ : ℝ)*probability (productMass (fun _ : ι => π))
        (fun x => v∈remainder E I x) := by
  classical
  let μ := productMass (fun _ : ι => π)
  have hμ : ∀ ω, 0 ≤ μ ω := productMass_nonneg (fun _ => hπ)
  have hsum : ∑ ω, μ ω=1 := productMass_sum (fun _ => hs)
  have he : probability (productMass (fun _ : κ × ι => π))
      (fun x => v∈unionRemainders E I x) =
      probability (productMass (fun _ : κ => μ)) (fun x => ∃ k, v∈remainder E I (x k)) := by
    rw [probability_product_curry (fun _ _ => π)]
    congr 1
    funext x
    simp only [unionRemainders,mem_biUnion,mem_univ,true_and]
  rw [he]
  calc
    _ ≤ ∑ k, probability (productMass (fun _ : κ => μ))
        (fun x => v∈remainder E I (x k)) := probability_union_le (productMass_nonneg (fun _ => hμ)) _
    _ = ∑ _ : κ, probability μ (fun x => v∈remainder E I x) := by
      apply sum_congr rfl
      intro k _
      exact probability_coordinate (fun _ => hsum) k (fun x => v∈remainder E I x)
    _ = _ := by simp [μ]

theorem bounded_sampler (G : SimpleGraph V) {n r : ℝ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (horder : (Fintype.card V : ℝ) ≤ n)
    (hf : Fractional.number G ≤ r) :
    ∃ (π : Finset V → ℝ) (I : Finset V → Finset V),
      (∀ s, 0 ≤ π s) ∧ (∑ s, π s=1) ∧
      (∀ s, Fractional.Stable G (I s) ∧ (I s).card ≤ ⌈n/r⌉₊) ∧
      ∀ v, probability π (fun s => v∈I s)=1/(2*r) := by
  classical
  obtain ⟨π,hπ,hs,hstable,hmarg⟩ := Fractional.bounded_sampling G hn hr horder hf
  let I (s : Finset V) : Finset V :=
    if Fractional.Stable G s ∧ s.card ≤ ⌈n/r⌉₊ then s else ∅
  refine ⟨π,I,hπ,hs,?_,?_⟩
  · intro s
    dsimp [I]
    split_ifs with h
    · exact h
    · exact ⟨Fractional.stable_empty G,by simp⟩
  · intro v
    rw [←hmarg v]
    unfold probability Fractional.marginal
    apply sum_congr rfl
    intro s _
    by_cases hπs : π s=0
    · simp [hπs]
    · simp only [I,ite_eq_left (hstable s hπs)]

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter Finset Fractional

theorem source_private_fractional :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈192*r*Real.log (2*y)⌉₊
      let M := ⌈n/r⌉₊
      let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
      ∀ (V Ω κ : Type) [Fintype V] [DecidableEq V] [Fintype Ω]
        [Fintype κ] [DecidableEq κ], Fintype.card κ=q →
      ∀ G : SimpleGraph V, ∀ π : Ω → ℝ,
      (∀ ω, 0 ≤ π ω) → (∑ ω, π ω=1) →
      ∀ (I : Ω → Finset V) (E : Fin N → Finset V) (H : Finset V),
      (∀ ω, (I ω).card ≤ M) →
      (∀ v, probability π (fun ω => v∈I ω)=1/(2*r)) →
      (∀ v, (N:ℝ)/2 ≤ (univ.filter (fun j => v∈E j)).card) →
      r/4 < expectation (productMass (fun _ : Fin N => π))
        (fun x => number (G.induce (↑(remainder E I x ∩ H) : Set V))) →
      probability (productMass (fun _ : κ => productMass (fun _ : Fin N => π)))
        (fun x => ∃ i, number (G.induce
          (↑(privateCopy (fun z => remainder E I z ∩ H) i x) : Set V)) ≤ r/8) < 1/50 := by
  classical
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₁,hT₁⟩ := source_uniform_concentration (by norm_num : (1:ℕ)≤192)
    (by norm_num : (0:ℝ)<1/20)
  obtain ⟨T₂,hT₂⟩ := eventually_atTop.mp private_tail_cutoff
  refine ⟨max T₀ (max T₁ T₂),?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V Ω κ _ _ _ _ _ hκ G π hπ hs I E H hI hmarg hE hmean
  have hp := hT₀ t ((le_max_left _ _).trans ht)
  obtain ⟨hr,hy,hyt,hry,hry'⟩ := hp.2.2 r hrl hru
  have htpos : 0 < t := by linarith [hp.1]
  obtain ⟨hN,hN',hM,hM'⟩ := sample_size_parameters hp.1 hn hnt hr hy hry
    (by norm_num : (1:ℕ)≤192)
  have hq := source_q_pos htpos hr
  let N := ⌈192*r*Real.log (2*max 1 (t/r))⌉₊
  let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
  let p := Real.exp (-((N:ℝ)/(4*r)))
  let μ := productMass (fun _ : Fin N => π)
  let W := fun z => remainder E I z ∩ H
  have hμ : ∀ x, 0 ≤ μ x := productMass_nonneg (fun _ => hπ)
  have hμs : ∑ x, μ x=1 := productMass_sum (fun _ => hs)
  have hcard : Fintype.card (Fin N) ≤ q*N := by
    rw [Fintype.card_fin]
    simpa only [one_mul] using Nat.mul_le_mul_right N hq
  have hNcard : 1 ≤ Fintype.card (Fin N) := by simpa [N] using hN
  have hc := hT₁ t n r ((le_max_left _ _).trans ((le_max_right _ _).trans ht))
    hn hnt hrl hru (Fin N) Ω hNcard hcard (fun _ => π) (fun _ => hπ) (fun _ => hs)
  have hsurv (v : V) : probability μ (fun x => v∈W x) ≤ p := by
    have hh := remainder_survival_bound (fun _ : Fin N => hs) E I
      (by linarith : 1 ≤ r) (fun _ => hmarg) (by simpa [N] using hE) v
    exact (probability_mono hμ (fun _ h => (mem_inter.mp h).1)).trans
      (by simpa only [μ,p,Fintype.card_fin,N,neg_div] using hh)
  have hcomm (z : Fin N → Ω) :
      number (G.induce (↑(H ∩ remainder E I z) : Set V)) =
      number (G.induce (↑(W z) : Set V)) :=
    congrArg (fun S : Finset V => number (G.induce (↑S : Set V))) (inter_comm _ _)
  have htail := hc (fun z => number (G.induce (↑(H ∩ remainder E I z) : Set V)))
    (remainder_fractional_bounded_changes G E I hI H)
  have hhigh : probability μ (fun z => number (G.induce (↑(W z) : Set V)) ≤ r/5) ≤
      2*Real.exp (-t^(7/10:ℝ)) := by
    have hh := probability_mono hμ (A := fun z => number (G.induce (↑(W z) : Set V)) ≤ r/5)
      (B := fun z => r/20 ≤ |number (G.induce (↑(W z) : Set V)) -
        expectation μ (fun x => number (G.induce (↑(W x) : Set V)))|)
      (by intro z hz; have ha := neg_le_abs (number (G.induce (↑(W z) : Set V)) -
          expectation μ (fun x => number (G.induce (↑(W x) : Set V))));
          change r/4 < expectation μ (fun x => number (G.induce (↑(W x) : Set V))) at hmean
          linarith)
    exact hh.trans (by simpa only [hcomm,show (1/20:ℝ)*r=r/20 by ring] using htail)
  have hfail := private_fractional_failure (ι := κ) G hμ hμs W
    (by linarith : 0 < r) (Real.exp_pos _).le hsurv hhigh
  have hsparse := (source_sparseness hp.1.le hr hru).2.1
  have hqt := hT₂ t ((le_max_right _ _).trans ((le_max_right _ _).trans ht)) r hrl hru
  have hqm : ((q-1:ℕ):ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
  have hcollision : 4*(q:ℝ)*((q-1:ℕ):ℝ)*p ≤ 4/10000 := by
    calc
      _ ≤ 4*(q:ℝ)*(q:ℝ)*p := by gcongr
      _ = 4*((q:ℝ)^2*p) := by ring
      _ ≤ _ := by dsimp [p,N,q]; linarith
  change probability (productMass (fun _ : κ => μ))
    (fun x => ∃ i, number (G.induce (↑(privateCopy W i x) : Set V)) ≤ r/8) < 1/50
  rw [hκ] at hfail
  dsimp only [q] at hcollision
  linarith

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Knitting
open Finset
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

lemma kConnected_image {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (G : SimpleGraph V) (f : W → V) (hf : Function.Injective f)
    {T : Finset W} {k : ℕ} (hc : KConnectedOn (G.comap f) T k) :
    KConnectedOn G (T.image f) k := by
  classical
  refine ⟨by simpa only [card_image_of_injective _ hf] using hc.1,?_⟩
  intro X hX hx
  let Y := T.filter (fun w => f w∈X)
  have hYT : Y ⊆ T := filter_subset _ _
  have hYX : Y.image f=X := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hw).2
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp (hX hv)
      exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hv⟩,rfl⟩
  have hYc : Y.card=X.card := by rw [←hYX,card_image_of_injective _ hf]
  have hcon := hc.2 Y hYT (hYc ▸ hx)
  let g : (G.comap f).induce (↑(T\Y) : Set W) →g
      G.induce (↑(T.image f\X) : Set V) :=
    { toFun := fun w => ⟨f w.val,mem_sdiff.mpr
        ⟨mem_image.mpr ⟨w.val,(mem_sdiff.mp w.property).1,rfl⟩,by
          intro h
          exact (mem_sdiff.mp w.property).2
            (mem_filter.mpr ⟨(mem_sdiff.mp w.property).1,h⟩)⟩⟩
      map_rel' := by intro u v h; exact h }
  apply hcon.map g
  intro v
  obtain ⟨w,hw,he⟩ := mem_image.mp (mem_sdiff.mp v.property).1
  have hwY : w∉Y := by
    intro hh
    exact (mem_sdiff.mp v.property).2 (he ▸ (mem_filter.mp hh).2)
  exact ⟨⟨w,mem_sdiff.mpr ⟨hw,hwY⟩⟩,Subtype.ext he⟩

end LinearListHadwiger.Knitting

namespace LinearListHadwiger.Sampling
open Finset
variable {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω]

theorem complement_failure_on (G : SimpleGraph V) [DecidableRel G.Adj]
    {n r ε : ℝ} {k : ℕ} (hk : 64 ≤ k) (hr : 0 < r) (hrk : r ≤ k)
    (H : Finset V) (hord : (H.card : ℝ) ≤ n) (hconn : KConnectedOn G H k)
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (U : Ω → Finset V)
    (hsurv : ∀ v, probability μ (fun ω => v∈U ω) ≤ 1/10000)
    (hε : 0 ≤ ε)
    (htail : ∀ A : Finset V, probability μ (fun ω => r/100 ≤
      |((U ω ∩ A).card : ℝ)-expectation μ (fun z => ((U z ∩ A).card : ℝ))|) ≤ ε) :
    probability μ (fun ω => ¬((∀ v∈H, k ≤ 2*((H\U ω).filter (G.Adj v)).card) ∧
      KConnectedOn G (H\U ω) (k/32))) ≤
      (n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε := by
  classical
  let U' (ω : Ω) : Finset ↥H := univ.filter (fun v => v.val∈U ω)
  have hsurv' (v : ↥H) : probability μ (fun ω => v∈U' ω) ≤ 1/10000 := by
    simpa only [U',mem_filter,mem_univ,true_and] using hsurv v.val
  have hcard (A : Finset ↥H) (ω : Ω) :
      (U' ω ∩ A).card=(U ω ∩ A.image Subtype.val).card := by
    rw [←card_image_of_injective (U' ω ∩ A) Subtype.val_injective]
    congr 1
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact mem_inter.mpr ⟨(mem_filter.mp (mem_inter.mp hw).1).2,
        mem_image.mpr ⟨w,(mem_inter.mp hw).2,rfl⟩⟩
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp (mem_inter.mp hv).2
      exact mem_image.mpr ⟨w,mem_inter.mpr
        ⟨mem_filter.mpr ⟨mem_univ _,(mem_inter.mp hv).1⟩,hw⟩,rfl⟩
  have ht' (A : Finset ↥H) := htail (A.image Subtype.val)
  have hc := complement_failure (G.induce (↑H : Set V)) hk hr hrk
    (by simpa using hord) (Knitting.induce_connected G H hconn) hμ U' hsurv' hε
    (by intro A; simpa only [hcard] using ht' A)
  have himage (ω : Ω) : (univ\U' ω).image Subtype.val=H\U ω := by
    ext v
    simp only [mem_image,mem_sdiff,mem_univ,true_and,U',mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.property,hw⟩
    · rintro ⟨hv,hu⟩
      exact ⟨⟨v,hv⟩,hu,rfl⟩
  have hncard (ω : Ω) (v : ↥H) :
      (((univ\U' ω).filter ((G.induce (↑H : Set V)).Adj v)).card) =
        ((H\U ω).filter (G.Adj v.val)).card := by
    rw [←card_image_of_injective _ Subtype.val_injective,←himage ω]
    congr 1
    ext w
    simp only [mem_image,mem_filter]
    constructor
    · rintro ⟨z,⟨hz,hzv⟩,rfl⟩
      exact ⟨⟨z,hz,rfl⟩,hzv⟩
    · rintro ⟨⟨z,hz,rfl⟩,hzv⟩
      exact ⟨z,⟨hz,hzv⟩,rfl⟩
  have hg (ω : Ω) (hh :
      (∀ v : ↥H, k ≤ 2*((univ\U' ω).filter ((G.induce (↑H : Set V)).Adj v)).card) ∧
        KConnectedOn (G.induce (↑H : Set V)) (univ\U' ω) (k/32)) :
      (∀ v∈H, k ≤ 2*((H\U ω).filter (G.Adj v)).card) ∧
        KConnectedOn G (H\U ω) (k/32) := by
    constructor
    · intro v hv
      simpa only [hncard] using hh.1 ⟨v,hv⟩
    · have hi := Knitting.kConnected_image G Subtype.val Subtype.val_injective hh.2
      exact (congrArg (fun T : Finset V => KConnectedOn G T (k/32)) (himage ω)).mp hi
  exact (probability_mono hμ (fun ω hbad hgood => hbad (hg ω hgood))).trans hc

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Filter Finset

theorem source_complement_on {B : ℕ} (hB : 1 ≤ B) :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈B*r*Real.log (2*y)⌉₊
      let M := ⌈n/r⌉₊
      let q := ⌈t/(⌊r/200⌋₊ : ℝ)⌉₊^2
      ∀ (V ι Ω : Type) [Fintype V] [DecidableEq V] [Fintype ι] [Fintype Ω]
        [DecidableEq ι],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (H : Finset V),
      64 ≤ k → r ≤ k → t ≤ k → (H.card : ℝ) ≤ n → KConnectedOn G H k →
      1 ≤ Fintype.card ι → Fintype.card ι ≤ q*N →
      ∀ (μ : ι → Ω → ℝ), (∀ i ω, 0 ≤ μ i ω) → (∀ i, ∑ ω, μ i ω=1) →
      ∀ U : (ι → Ω) → Finset V,
      (∀ v, probability (productMass μ) (fun x => v∈U x) ≤ 1/10000) →
      (∀ (A : Finset V) i x x', (∀ j, j ≠ i → x j=x' j) →
        |((A ∩ U x).card : ℝ)-(A ∩ U x').card| ≤ 2*M) →
      probability (productMass μ) (fun x =>
        ¬((∀ v∈H, k ≤ 2*((H \ U x).filter (G.Adj v)).card) ∧
          KConnectedOn G (H \ U x) (k/32))) ≤ 1/100 := by
  classical
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₁,hT₁⟩ := source_uniform_concentration hB (show (0:ℝ)<1/100 by norm_num)
  obtain ⟨T₂,hT₂⟩ := eventually_atTop.mp complement_numeric_cutoff
  refine ⟨max T₀ (max T₁ T₂),?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V ι Ω _ _ _ _ _ G _ k H hk hrk htk hord hconn hi hiq μ hμ hs U hsurv hchange
  have hr := (hT₀ t ((le_max_left _ _).trans ht)).2.2 r hrl hru
  have hconc := hT₁ t n r ((le_max_left _ _).trans ((le_max_right _ _).trans ht))
    hn hnt hrl hru ι Ω hi hiq μ hμ hs
  have htail (A : Finset V) : probability (productMass μ) (fun x => r/100 ≤
      |((U x ∩ A).card : ℝ)-expectation (productMass μ)
        (fun z => ((U z ∩ A).card : ℝ))|) ≤ 2*Real.exp (-t^(7/10:ℝ)) := by
    have hh := hconc (fun z => ((A ∩ U z).card : ℝ)) (hchange A)
    simpa only [inter_comm,show (1/100:ℝ)*r=r/100 by ring] using hh
  have hh := complement_failure_on G hk (by linarith [hr.1]) hrk H hord hconn
    (productMass_nonneg hμ) U hsurv (by positivity) htail
  exact hh.trans (hT₂ t ((le_max_right _ _).trans ((le_max_right _ _).trans ht)) n k hn hnt htk)

end LinearListHadwiger.Sampling

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.StageSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open Filter Finset Fractional
attribute [local instance] Classical.propDecidable

theorem source_thinning_failure_structure_oai :
    ∃ T : ℝ, ∀ t n r : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      t/Real.log t ≤ r → r ≤ 4*t →
      let y := max 1 (t/r)
      let N := ⌈192*r*Real.log (2*y)⌉₊
      let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
      let k := ⌈(1000000*65536:ℝ)*t*y⌉₊
      ∀ (V : Type) [Fintype V] [DecidableEq V], ∀ G : SimpleGraph V,
      (Fintype.card V : ℝ) ≤ n → number G ≤ r →
      ∀ E : Fin N → Finset V,
      (∀ v, (N:ℝ)/2 ≤ (univ.filter (fun j => v∈E j)).card) →
      (∀ J : Fin N → Finset V, (∀ j, Stable G (J j)) →
        r/2 < number (G.induce
          (↑(univ\univ.biUnion (fun j => J j∩E j)) : Set V))) →
      ∃ (H U : Finset V) (S : Fin q → Finset V),
        KConnectedOn G H k ∧
        (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
        (∀ i, S i ⊆ H ∩ U) ∧
        (∀ i, r/8 < number (G.induce (↑(S i) : Set V))) ∧
        (∀ v∈H, k ≤ 2*((H\U).filter (G.Adj v)).card) ∧
        KConnectedOn G (H\U) (k/32) := by
  classical
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp parameter_range_cutoff
  obtain ⟨T₁,hT₁⟩ := source_fixed_region
  obtain ⟨T₂,hT₂⟩ := source_private_fractional
  obtain ⟨T₃,hT₃⟩ := source_complement_on (by norm_num : (1:ℕ) ≤ 192)
  refine ⟨max (max T₀ T₁) (max T₂ T₃),?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V _ _ G hord hf E hE hfail
  have ht₀ := (le_max_left T₀ T₁).trans ((le_max_left _ _).trans ht)
  have ht₁ := (le_max_right T₀ T₁).trans ((le_max_left _ _).trans ht)
  have ht₂ := (le_max_left T₂ T₃).trans ((le_max_right _ _).trans ht)
  have ht₃ := (le_max_right T₂ T₃).trans ((le_max_right _ _).trans ht)
  have hp := hT₀ t ht₀
  obtain ⟨hr,hy,hyt,hry,hry'⟩ := hp.2.2 r hrl hru
  have htpos : 0 < t := by linarith [hp.1]
  let N := ⌈192*r*Real.log (2*max 1 (t/r))⌉₊
  let q := ⌈t/(⌊r/200⌋₊:ℝ)⌉₊^2
  let k := ⌈(1000000*65536:ℝ)*t*max 1 (t/r)⌉₊
  let M := ⌈n/r⌉₊
  obtain ⟨π,I,hπ,hπs,hI,hmarg⟩ := bounded_sampler G hn (by linarith : 1 ≤ r) hord hf
  have hN := (sample_size_parameters hp.1 hn hnt hr hy hry (by norm_num : (1:ℕ)≤192)).1
  have hq : 1 ≤ q := source_q_pos htpos hr
  obtain ⟨H,hH,hmean⟩ := hT₁ t n r ht₁ hn hnt hrl hru V (Finset V) G hord
    π hπ hπs I E (fun ω => (hI ω).2) hmarg hE (by
      intro x _
      exact hfail (fun j => I (x j)) (fun j => (hI (x j)).1))
  let μ := productMass (fun _ : Fin q × Fin N => π)
  let U (x : Fin q × Fin N → Finset V) := unionRemainders E I x
  let S (x : Fin q × Fin N → Finset V) (i : Fin q) :=
    privateCopy (fun z => remainder E I z ∩ H) i (fun j l => x (j,l))
  let privateBad (x : Fin q × Fin N → Finset V) : Prop :=
    ∃ i, number (G.induce (↑(S x i) : Set V)) ≤ r/8
  let complementBad (x : Fin q × Fin N → Finset V) : Prop :=
    ¬((∀ v∈H, k ≤ 2*((H\U x).filter (G.Adj v)).card) ∧
      KConnectedOn G (H\U x) (k/32))
  have hprivate : probability μ privateBad < 1/50 := by
    have hh := hT₂ t n r ht₂ hn hnt hrl hru V (Finset V) (Fin q)
      (by simp [q]) G π hπ hπs I E H (fun ω => (hI ω).2) hmarg hE hmean
    rw [probability_product_curry (fun _ : Fin q => fun _ : Fin N => π)] at hh
    exact hh
  have hb := attachment_budget (γ := 65536) htpos hr hru hy
    (le_max_right 1 (t/r)) (by norm_num)
  have hrk : r ≤ k := hb.1
  have hk64 : 64 ≤ k := by
    have hh : (64:ℝ) ≤ k := by linarith
    exact_mod_cast hh
  have htk : t ≤ k := by
    have hh := Nat.le_ceil ((1000000*65536:ℝ)*t*max 1 (t/r))
    dsimp [k]
    nlinarith [mul_nonneg htpos.le (sub_nonneg.mpr hy)]
  have hHord : (H.card : ℝ) ≤ n :=
    (by exact_mod_cast card_le_univ H : (H.card : ℝ) ≤ Fintype.card V).trans hord
  have hcardpos : 1 ≤ Fintype.card (Fin q × Fin N) := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    dsimp [N] at hN
    simpa only [one_mul] using Nat.mul_le_mul hq hN
  have hcard : Fintype.card (Fin q × Fin N) ≤ q*N := by simp
  have hsurv (v : V) : probability μ (fun x => v∈U x) ≤ 1/10000 := by
    have hh := unionRemainders_survival (κ := Fin q) hπ hπs E I v
    have hd := remainder_survival_bound (fun _ : Fin N => hπs) E I
      (by linarith : 1 ≤ r) (fun _ => hmarg) (by simpa [N] using hE) v
    have hb := (source_sparseness hp.1.le hr hru).2.2
    calc
      _ ≤ (q:ℝ)*probability (productMass (fun _ : Fin N => π))
          (fun x => v∈remainder E I x) := by simpa only [Fintype.card_fin] using hh
      _ ≤ (q:ℝ)*Real.exp (-((N:ℝ)/(4*r))) := by
        gcongr
        simpa only [Fintype.card_fin,neg_div] using hd
      _ ≤ _ := hb
  have hcomplement : probability μ complementBad ≤ 1/100 :=
    hT₃ t n r ht₃ hn hnt hrl hru V (Fin q × Fin N) (Finset V) G k H
      hk64 hrk htk hHord hH hcardpos hcard (fun _ => π) (fun _ => hπ)
      (fun _ => hπs) U hsurv (by
        intro A i x y hxy
        exact unionRemainders_card_bounded_changes E I (fun ω => (hI ω).2) A hxy)
  have hμ : ∀ x, 0 ≤ μ x := productMass_nonneg (fun _ => hπ)
  have hμs : ∑ x, μ x=1 := productMass_sum (fun _ => hπs)
  have hbad : probability μ (fun x => privateBad x ∨ complementBad x) < 1 := by
    have hh := probability_or_le hμ privateBad complementBad
    linarith
  obtain ⟨x,hxp,havoid⟩ := exists_positive_avoiding hμ hμs hbad
  have hpriv : ∀ i, r/8 < number (G.induce (↑(S x i) : Set V)) := by
    intro i
    by_contra hh
    exact havoid (Or.inl ⟨i,le_of_not_gt hh⟩)
  have hcomp : (∀ v∈H, k ≤ 2*((H\U x).filter (G.Adj v)).card) ∧
      KConnectedOn G (H\U x) (k/32) := by
    by_contra hh
    exact havoid (Or.inr hh)
  refine ⟨H,U x,S x,hH,?_,?_,hpriv,hcomp⟩
  · intro i j hij
    exact privateCopies_disjoint _ _ hij
  · intro i v hv
    have hw := (mem_sdiff.mp hv).1
    refine mem_inter.mpr ⟨(mem_inter.mp hw).2,?_⟩
    exact mem_biUnion.mpr ⟨i,mem_univ _,(mem_inter.mp hw).1⟩

end LinearListHadwiger.Sampling

end OAI
end

theorem solution : type_of% @OAI.LinearListHadwiger.Sampling.source_thinning_failure_structure_oai := @OAI.LinearListHadwiger.Sampling.source_thinning_failure_structure_oai
