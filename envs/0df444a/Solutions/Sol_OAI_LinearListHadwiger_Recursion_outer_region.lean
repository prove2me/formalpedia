-- Prove2me | solution 1 for OAI.LinearListHadwiger.Recursion.outer_region
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:50:30.041757+00:00
-- url     : https://prove2.me/submissions/19384db7-7923-4a33-b396-4639ae3e02a2

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000
import Theorems.Thm_OAI_LinearListHadwiger_SmallList_additive_deletion_or_obstruction

section
-- module Solutions.OAIQW_ListHadwiger.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

theorem choosable_mono {V : Type} {G : SimpleGraph V} {k l : ℕ}
    (h : Choosable G k) (hkl : k ≤ l) : Choosable G l := by
  intro Color L hL
  exact h Color L (fun v => hkl.trans (hL v))

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

theorem choosable_listChromaticNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    Choosable G (listChromaticNumber G) := by
  exact Nat.sInf_mem (s := {k : ℕ | Choosable G k})
    ⟨Fintype.card V, choosable_card G⟩

theorem listChromaticNumber_le_iff {V : Type} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) : listChromaticNumber G ≤ k ↔ Choosable G k := by
  constructor
  · exact fun h => choosable_mono (choosable_listChromaticNumber G) h
  · intro h
    exact Nat.sInf_le h

theorem cliqueMinor_order_le_card {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (h : HasCliqueMinor G t) : t ≤ Fintype.card V := by
  classical
  obtain ⟨B, hc, hd, _⟩ := h
  have hb : ∀ i, ∃ v, v ∈ B i := fun i => by
    obtain ⟨v⟩ := (hc i).nonempty
    exact ⟨v.val, v.property⟩
  choose v hv using hb
  have hi : Function.Injective v := by
    intro i j hij
    by_contra hn
    exact Set.disjoint_left.mp (hd i j hn) (hv i) (by
      rw [hij]
      exact hv j)
  simpa using Fintype.card_le_of_injective v hi

theorem cliqueMinor_zero {V : Type} (G : SimpleGraph V) : HasCliqueMinor G 0 := by
  refine ⟨Fin.elim0, ?_, ?_, ?_⟩
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i

theorem hadwiger_bddAbove {V : Type} [Fintype V] (G : SimpleGraph V) :
    BddAbove {t : ℕ | HasCliqueMinor G t} :=
  ⟨Fintype.card V, fun _ h => cliqueMinor_order_le_card h⟩

theorem cliqueMinor_le_hadwigerNumber {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (h : HasCliqueMinor G t) : t ≤ hadwigerNumber G :=
  le_csSup (hadwiger_bddAbove G) h

theorem hasCliqueMinor_hadwigerNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    HasCliqueMinor G (hadwigerNumber G) := by
  exact Nat.sSup_mem ⟨0, cliqueMinor_zero G⟩ (hadwiger_bddAbove G)

theorem cliqueMinor_one {V : Type} [Nonempty V] (G : SimpleGraph V) :
    HasCliqueMinor G 1 := by
  classical
  let v : V := Classical.choice inferInstance
  refine ⟨fun _ => {v}, ?_, ?_, ?_⟩
  · intro i
    exact SimpleGraph.Connected.of_subsingleton
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

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

lemma choosable_induce {V : Type} {G : SimpleGraph V} {k : ℕ}
    (h : Choosable G k) (S : Set V) : Choosable (G.induce S) k := by
  classical
  intro Color L hL
  let ei : Color ↪ Color ⊕ Fin k := ⟨Sum.inl, Sum.inl_injective⟩
  let eo : Fin k ↪ Color ⊕ Fin k := ⟨Sum.inr, Sum.inr_injective⟩
  let L' : V → Finset (Color ⊕ Fin k) := fun v =>
    if hv : v ∈ S then (L ⟨v, hv⟩).map ei else Finset.univ.map eo
  have hL' : ∀ v, k ≤ (L' v).card := by
    intro v
    by_cases hv : v ∈ S
    · simpa [L', hv] using hL ⟨v, hv⟩
    · simp [L', hv]
  obtain ⟨c, hc, hp⟩ := h _ L' hL'
  have hex : ∀ x : S, ∃ a ∈ L x, c x = Sum.inl a := by
    intro x
    have hh := hc x.val
    simp only [L', dite_eq_left x.property, Finset.mem_map] at hh
    obtain ⟨a, ha, heq⟩ := hh
    exact ⟨a, ha, heq.symm⟩
  choose f hf heq using hex
  refine ⟨f, hf, ?_⟩
  intro v w hvw hfw
  apply hp hvw
  change c v.val = c w.val
  rw [heq v, heq w, hfw]

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

lemma choosable_of_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {k : ℕ} (h : Choosable H k) : Choosable G k := by
  intro Color L hL
  obtain ⟨c, hc, hp⟩ := h Color (fun w => L (e.symm w)) (fun w => hL (e.symm w))
  refine ⟨fun v => c (e v), ?_, ?_⟩
  · intro v
    simpa using hc (e v)
  · intro v w hvw
    exact hp (e.map_adj_iff.mpr hvw)

lemma choosable_of_embedding {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ↪g H) {k : ℕ} (h : Choosable H k) : Choosable G k :=
  choosable_of_iso e.isoInduceRange (choosable_induce h _)

lemma choosable_induce_subset {V : Type} {G : SimpleGraph V} {S T : Set V}
    {k : ℕ} (h : Choosable (G.induce S) k) (hTS : T ⊆ S) :
    Choosable (G.induce T) k :=
  choosable_of_embedding (G.induceHomOfLE hTS) h

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

theorem constrained_coloring_on {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) (L B : V → Finset Color) (φ : V → Color)
    {k m : ℕ} (hk : 1 ≤ k) (hAS : A ⊆ S)
    (hconn : ∀ T ⊆ S, KConnectedOn G T k → Choosable (G.induce (↑T : Set V)) m)
    (hL : ∀ v ∈ S, m + 6 * k ≤ (L v).card) (hφ : ValidOn G A L φ)
    (hB : ∀ v ∈ S \ A, (B v).card < k)
    (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    ∃ c, ValidOn G S L c ∧ (∀ v ∈ A, c v = φ v) ∧
      ∀ v ∈ S \ A, c v ∉ B v := by
  classical
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
      have hl := hL v (Finset.mem_sdiff.mp hv).1
      have heq := Finset.card_sdiff_add_card_eq_card hAS
      omega
    by_cases hc : KConnectedOn G S k
    · have hchoose : Choosable (G.induce (↑(S \ A) : Set V)) m :=
        choosable_induce_subset (hconn S Finset.Subset.rfl hc) Finset.sdiff_subset
      apply extend_from_choosable G S A L B φ hφ hchoose
      intro v hv
      have hh := hB v hv
      have hl := hL v (Finset.mem_sdiff.mp hv).1
      omega
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
        (fun v hv => hL v (hS₁ hv)) (hφ.mono Finset.inter_subset_left) hB₁ hbudget₁
    obtain ⟨c₁, hc₁, hc₁ext, hc₁av⟩ :=
      ih (V₁ ∪ Z) hs.left_union_ssubset A₁' B₁ φ₁ hA₁'S₁
        (fun T hT => hconn T (hT.trans hS₁)) (fun v hv => hL v (hS₁ hv))
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
        (fun T hT => hconn T (hT.trans hS₂)) (fun v hv => hL v (hS₂ hv))
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

theorem choosable_of_connected_induced {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k m : ℕ} (hk : 1 ≤ k)
    (hconn : ∀ T : Finset V, KConnectedOn G T k →
      Choosable (G.induce (↑T : Set V)) m) : Choosable G (m + 6 * k) := by
  classical
  intro Color L hL
  have hn : ∀ v, (L v).Nonempty := by
    intro v
    apply Finset.card_pos.mp
    have hh := hL v
    omega
  choose φ hφ using hn
  obtain ⟨c, hc, _, _⟩ := constrained_coloring_on G Finset.univ ∅ L
    (fun _ => ∅) φ hk (Finset.empty_subset _)
    (fun T _ => hconn T) (fun v _ => hL v)
    ⟨by simp, by simp [ProperOn]⟩
    (by intro v hv; simpa using (show 0 < k by omega)) (by simp [constraintCost, vertexCost])
  exact ⟨c, fun v => hc.1 v (Finset.mem_univ _),
    fun _ _ h => hc.2 (Finset.mem_univ _) (Finset.mem_univ _) h⟩

theorem list_connectivity_extraction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hlarge : 6 * k < listChromaticNumber G) :
    ∃ T : Finset V, KConnectedOn G T k ∧
      listChromaticNumber G - 6 * k ≤ listChromaticNumber (G.induce (↑T : Set V)) := by
  classical
  by_contra hn
  push Not at hn
  let m := listChromaticNumber G - 6 * k - 1
  have hconn : ∀ T : Finset V, KConnectedOn G T k →
      Choosable (G.induce (↑T : Set V)) m := by
    intro T hT
    apply (listChromaticNumber_le_iff _ _).mp
    have hh := hn T hT
    dsimp [m]
    omega
  have hchoose := choosable_of_connected_induced G hk hconn
  have hbound := (listChromaticNumber_le_iff G _).mpr hchoose
  dsimp [m] at hbound
  omega

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Connectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

open scoped Classical

theorem choosable_add_deleted_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Z : Finset V) {s : ℕ}
    (hR : Choosable (G.induce (↑(Finset.univ \ Z) : Set V)) s) :
    Choosable G (s + Z.card) := by
  classical
  intro Color L hL
  have hZ : Choosable (G.induce (↑Z : Set V)) Z.card := by
    have hh := choosable_card (G.induce (↑Z : Set V))
    change Choosable _ (Fintype.card ↥Z) at hh
    simpa only [Fintype.card_coe] using hh
  obtain ⟨cZ, hcZ, hpZ⟩ := hZ Color (fun v => L v.val)
    (fun v => (Nat.le_add_left _ _).trans (hL v.val))
  let used : Finset Color := Finset.univ.image cZ
  have hused : used.card ≤ Z.card := by
    calc
      used.card ≤ (Finset.univ : Finset (↑Z : Set V)).card := Finset.card_image_le
      _ = Z.card := by change Fintype.card ↥Z = Z.card; exact Fintype.card_coe Z
  let LR : (↑(Finset.univ \ Z) : Set V) → Finset Color := fun v => L v.val \ used
  have hs : ∀ v, s ≤ (LR v).card := by
    intro v
    have hh := Finset.card_le_card_sdiff_add_card (s := L v.val) (t := used)
    have hl := hL v.val
    dsimp [LR]
    omega
  obtain ⟨cR, hcR, hpR⟩ := hR Color LR hs
  let c : V → Color := fun v =>
    if hv : v ∈ Z then cZ ⟨v, hv⟩ else cR ⟨v, by simp [hv]⟩
  have hcr : ∀ v (hv : v ∉ Z), c v ∈ L v ∧ c v ∉ used := by
    intro v hv
    have hh := hcR ⟨v, by simp [hv]⟩
    simpa only [c, dite_eq_right hv, LR, Finset.mem_sdiff] using hh
  have hcz : ∀ v (hv : v ∈ Z), c v = cZ ⟨v, hv⟩ :=
    fun v hv => dite_eq_left hv
  have hzr : ∀ v (hv : v ∈ Z), c v ∈ used := by
    intro v hv
    rw [hcz v hv]
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩
  refine ⟨c, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ Z
    · rw [hcz v hv]
      exact hcZ ⟨v, hv⟩
    · exact (hcr v hv).1
  · intro v w hadj
    by_cases hv : v ∈ Z <;> by_cases hw : w ∈ Z
    · rw [hcz v hv, hcz w hw]
      exact hpZ hadj
    · intro heq
      exact (hcr w hw).2 (heq ▸ hzr v hv)
    · intro heq
      exact (hcr v hv).2 (heq.symm ▸ hzr w hw)
    · simp only [c, dite_eq_right hv, dite_eq_right hw]
      exact hpR hadj

theorem listChromaticNumber_deleted {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Z : Finset V) :
    listChromaticNumber G - Z.card ≤
      listChromaticNumber (G.induce (↑(Finset.univ \ Z) : Set V)) := by
  have hh := choosable_add_deleted_card G Z
    (choosable_listChromaticNumber (G.induce (↑(Finset.univ \ Z) : Set V)))
  have hb := (listChromaticNumber_le_iff G _).mpr hh
  omega

theorem degenerate_coloring_on {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (L : V → Finset Color) (φ : V → Color)
    {d : ℕ} (hdeg : DegenerateOn G S d) (hL : ∀ v ∈ S, d + 1 ≤ (L v).card) :
    ∃ c, ValidOn G S L c := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain rfl | hS := S.eq_empty_or_nonempty
    · exact ⟨φ, by simp [ValidOn, ProperOn]⟩
    obtain ⟨v, hv, hvd⟩ := hdeg S (Finset.Subset.refl _) hS
    have herase : S.erase v ⊂ S := Finset.erase_ssubset hv
    obtain ⟨c, hc⟩ := ih (S.erase v) herase
      (fun T hT => hdeg T (hT.trans (Finset.erase_subset _ _)))
      (fun w hw => hL w (Finset.mem_of_mem_erase hw))
    let forbidden := (S.filter (G.Adj v)).image c
    have hfc : forbidden.card ≤ d := Finset.card_image_le.trans hvd
    have hpos : (L v \ forbidden).Nonempty := by
      apply Finset.card_pos.mp
      have hh := Finset.card_le_card_sdiff_add_card (s := L v) (t := forbidden)
      have hl := hL v hv
      omega
    obtain ⟨a, ha⟩ := hpos
    obtain ⟨haL, haF⟩ := Finset.mem_sdiff.mp ha
    let c' : V → Color := fun w => if w = v then a else c w
    have hcv : c' v = a := by simp [c']
    have hcw : ∀ w, w ≠ v → c' w = c w := fun w hw => ite_eq_right hw
    refine ⟨c', ?_, ?_⟩
    · intro w hw
      by_cases hwv : w = v
      · subst w
        rwa [hcv]
      · rw [hcw w hwv]
        exact hc.1 w (Finset.mem_erase.mpr ⟨hwv, hw⟩)
    · intro w hw z hz hadj
      by_cases hwv : w = v
      · subst w
        have hzv : z ≠ v := hadj.ne.symm
        rw [hcv, hcw z hzv]
        intro heq
        exact haF (Finset.mem_image.mpr
          ⟨z, Finset.mem_filter.mpr ⟨hz, hadj⟩, heq.symm⟩)
      · by_cases hzv : z = v
        · subst z
          rw [hcw w hwv, hcv]
          intro heq
          exact haF (Finset.mem_image.mpr
            ⟨w, Finset.mem_filter.mpr ⟨hw, hadj.symm⟩, heq⟩)
        · rw [hcw w hwv, hcw z hzv]
          exact hc.2 (Finset.mem_erase.mpr ⟨hwv, hw⟩)
            (Finset.mem_erase.mpr ⟨hzv, hz⟩) hadj

theorem choosable_of_degenerate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d : ℕ} (hdeg : DegenerateOn G Finset.univ d) :
    Choosable G (d + 1) := by
  classical
  intro Color L hL
  have hn : ∀ v, (L v).Nonempty := by
    intro v
    apply Finset.card_pos.mp
    have hh := hL v
    omega
  choose φ hφ using hn
  obtain ⟨c, hc⟩ := degenerate_coloring_on G Finset.univ L φ hdeg (fun v _ => hL v)
  exact ⟨c, fun v => hc.1 v (Finset.mem_univ _),
    fun _ _ h => hc.2 (Finset.mem_univ _) (Finset.mem_univ _) h⟩

theorem listChromaticNumber_le_of_degenerate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d : ℕ} (hdeg : DegenerateOn G Finset.univ d) :
    listChromaticNumber G ≤ d + 1 :=
  (listChromaticNumber_le_iff G _).mpr (choosable_of_degenerate G hdeg)

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.PathPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.PathPacking

open SimpleGraph

theorem successor_of_no_small_separator {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V)
    (hconn : ∀ X : Finset V, X.card < A.card → AvoidingConnection G A B X) :
    ∃ f : {v // v ∉ B} → {v // v ∉ A},
      Function.Injective f ∧ ∀ v, v.val = (f v).val ∨ G.Adj v.val (f v).val := by
  classical
  let L : {v // v ∉ B} → Finset {v // v ∉ A} :=
    fun v => Finset.univ.filter fun w => v.val = w.val ∨ G.Adj v.val w.val
  have hHall : ∀ S : Finset {v // v ∉ B}, S.card ≤ (S.biUnion L).card := by
    intro S
    by_contra hn
    have hbad : (S.biUnion L).card < S.card := by omega
    let T : Finset V := S.image Subtype.val
    let N : Finset V := (S.biUnion L).image Subtype.val
    have hTcard : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hNcard : N.card = (S.biUnion L).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hTB : ∀ v ∈ T, v ∉ B := by
      intro v hv
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
      exact w.property
    have hNA : Disjoint N A := by
      apply Finset.disjoint_left.mpr
      intro v hv ha
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
      exact w.property ha
    have hTN : T ⊆ A ∪ N := by
      intro v hv
      by_cases ha : v ∈ A
      · exact Finset.mem_union_left _ ha
      · apply Finset.mem_union_right
        obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hv
        apply Finset.mem_image.mpr
        refine ⟨⟨v, ha⟩, Finset.mem_biUnion.mpr ⟨w, hw, ?_⟩, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hweq⟩
    let X := (A ∪ N) \ T
    have hcard : X.card < A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card hTN
      have hh' := Finset.card_union_of_disjoint hNA.symm
      change X.card + T.card = (A ∪ N).card at hh
      omega
    have hclosed : ∀ v ∈ T, ∀ w, G.Adj v w → w ∉ X → w ∈ T := by
      intro v hv w hadj hw
      by_contra hwT
      apply hw
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hwT⟩
      by_cases hwA : w ∈ A
      · exact Finset.mem_union_left _ hwA
      · apply Finset.mem_union_right
        obtain ⟨v', hv', heq⟩ := Finset.mem_image.mp hv
        apply Finset.mem_image.mpr
        refine ⟨⟨w, hwA⟩, Finset.mem_biUnion.mpr ⟨v', hv', ?_⟩, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, Or.inr ?_⟩
        simpa only [heq] using hadj
    have hwalk : ∀ {v w : V} (p : G.Walk v w), v ∈ T →
        (∀ z ∈ p.support, z ∉ X) → w ∈ T := by
      intro v w p
      induction p with
      | nil => exact fun hv _ => hv
      | @cons v w u hadj p ih =>
        intro hv hp
        apply ih (hclosed v hv w hadj (hp w (by simp)))
        intro z hz
        exact hp z (by simp [hz])
    obtain ⟨a, ha, b, hb, p, hp⟩ := hconn X hcard
    have haT : a ∈ T := by
      by_contra hn
      exact hp a (by simp) (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ ha, hn⟩)
    exact hTB b (hwalk p haT hp) hb
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective L).mp hHall
  exact ⟨f, hf, fun v => (Finset.mem_filter.mp (hmem v)).2⟩

section Orbits
variable {V : Type} [Fintype V] [DecidableEq V]
variable (A B : Finset V) (f : {v // v ∉ B} → {v // v ∉ A})

lemma next_not_source {V : Type} [Fintype V] [DecidableEq V]
    (A B : Finset V) (f : {v // v ∉ B} → {v // v ∉ A}) {v : V} (hv : v ∉ B) : next A B f v ∉ A := by
  simpa [next, hv] using (f ⟨v, hv⟩).property

lemma next_injective_off_target {V : Type} [Fintype V] [DecidableEq V]
    (A B : Finset V) (f : {v // v ∉ B} → {v // v ∉ A}) (hf : Function.Injective f) {v w : V}
    (hv : v ∉ B) (hw : w ∉ B) (h : next A B f v = next A B f w) : v = w := by
  simp only [next, dite_eq_right hv, dite_eq_right hw] at h
  have hh := hf (Subtype.ext h)
  exact congrArg Subtype.val hh

lemma orbit_collision (hf : Function.Injective f) {a b : V}
    (ha : a ∈ A) (hb : b ∈ A) (n m : ℕ)
    (hn : ∀ i < n, (next A B f)^[i] a ∉ B)
    (hm : ∀ i < m, (next A B f)^[i] b ∉ B)
    (heq : (next A B f)^[n] a = (next A B f)^[m] b) : n = m ∧ a = b := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa using heq
    | succ m =>
      have hh := next_not_source A B f (hm m (Nat.lt_succ_self m))
      rw [Function.iterate_succ_apply'] at heq
      exact (hh (by simpa only [Function.iterate_zero, id_eq] using (heq ▸ ha))).elim
  | succ n ih =>
    cases m with
    | zero =>
      have hh := next_not_source A B f (hn n (Nat.lt_succ_self n))
      rw [Function.iterate_succ_apply'] at heq
      exact (hh (by simpa only [Function.iterate_zero, id_eq] using (heq.symm ▸ hb))).elim
    | succ m =>
      have heq' : (next A B f)^[n] a = (next A B f)^[m] b := by
        apply next_injective_off_target A B f hf (hn n (Nat.lt_succ_self n))
          (hm m (Nat.lt_succ_self m))
        simpa only [Function.iterate_succ_apply'] using heq
      obtain ⟨hnm, hab⟩ := ih m (fun i hi => hn i (by omega))
        (fun i hi => hm i (by omega)) heq'
      exact ⟨congrArg Nat.succ hnm, hab⟩

lemma orbit_hits_target (hf : Function.Injective f) {a : V} (ha : a ∈ A) :
    ∃ n : ℕ, (next A B f)^[n] a ∈ B := by
  by_contra hn
  have havoid : ∀ n : ℕ, (next A B f)^[n] a ∉ B := by simpa using hn
  let g : Fin (Fintype.card V + 1) → V := fun i => (next A B f)^[i.val] a
  have hg : Function.Injective g := by
    intro i j hij
    apply Fin.ext
    exact (orbit_collision A B f hf ha ha i.val j.val
      (fun n _ => havoid n) (fun n _ => havoid n) hij).1
  have hh := Fintype.card_le_of_injective g hg
  simp at hh

lemma orbit_walk (G : SimpleGraph V) (hf : Function.Injective f)
    (hstep : ∀ v, v.val = (f v).val ∨ G.Adj v.val (f v).val)
    {a : V} (ha : a ∈ A) (n : ℕ)
    (hn : ∀ i < n, (next A B f)^[i] a ∉ B) :
    ∃ p : G.Walk a ((next A B f)^[n] a),
      ∀ v ∈ p.support, ∃ i ≤ n, v = (next A B f)^[i] a := by
  induction n with
  | zero =>
    refine ⟨Walk.nil, ?_⟩
    intro v hv
    exact ⟨0, le_rfl, by simpa using hv⟩
  | succ n ih =>
    have hn' : ∀ i < n, (next A B f)^[i] a ∉ B := fun i hi => hn i (by omega)
    obtain ⟨p, hp⟩ := ih hn'
    have hx := hn n (Nat.lt_succ_self n)
    have hne : (next A B f)^[n] a ≠ (next A B f)^[n + 1] a := by
      intro heq
      have hh := (orbit_collision A B f hf ha ha n (n + 1) hn' hn heq).1
      omega
    have hadj : G.Adj ((next A B f)^[n] a) ((next A B f)^[n + 1] a) := by
      rw [Function.iterate_succ_apply', next, dite_eq_right hx]
      rcases hstep ⟨(next A B f)^[n] a, hx⟩ with hh | hh
      · exact (hne (by simpa only [Function.iterate_succ_apply', next, dite_eq_right hx]
          using hh)).elim
      · exact hh
    refine ⟨p.concat hadj, ?_⟩
    intro v hv
    rw [Walk.support_concat] at hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨i, hi, heq⟩ := hp v hv
      exact ⟨i, by omega, heq⟩
    · exact ⟨n + 1, le_rfl, List.mem_singleton.mp hv⟩

end Orbits

theorem fullPacking_of_successor {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V)
    (f : {v // v ∉ B} → {v // v ∉ A}) (hf : Function.Injective f)
    (hstep : ∀ v, v.val = (f v).val ∨ G.Adj v.val (f v).val) :
    Nonempty (FullPacking G A B) := by
  classical
  have hhit : ∀ a : ↥A, ∃ n : ℕ, (next A B f)^[n] a.val ∈ B :=
    fun a => orbit_hits_target A B f hf a.property
  let n : ↥A → ℕ := fun a => Nat.find (hhit a)
  have hn : ∀ a : ↥A, (next A B f)^[n a] a.val ∈ B := fun a => Nat.find_spec (hhit a)
  have hbefore : ∀ a : ↥A, ∀ i < n a, (next A B f)^[i] a.val ∉ B := by
    intro a i hi hb
    have hh := Nat.find_min' (hhit a) hb
    change n a ≤ i at hh
    omega
  have hp : ∀ a : ↥A, ∃ p : G.Walk a.val ((next A B f)^[n a] a.val),
      ∀ v ∈ p.support, ∃ i ≤ n a, v = (next A B f)^[i] a.val :=
    fun a => orbit_walk A B f G hf hstep a.property (n a) (hbefore a)
  choose p hp using hp
  refine ⟨⟨(fun a => ⟨_, hn a⟩), (fun a => (p a).toPath), ?_, ?_, ?_⟩⟩
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro v hva hvb
    obtain ⟨i, hi, hiv⟩ := hp a v ((p a).support_toPath_subset_support hva)
    obtain ⟨j, hj, hjv⟩ := hp b v ((p b).support_toPath_subset_support hvb)
    have heq : (next A B f)^[i] a.val = (next A B f)^[j] b.val := hiv.symm.trans hjv
    have hh := orbit_collision A B f hf a.property b.property i j
      (fun l hl => hbefore a l (by omega)) (fun l hl => hbefore b l (by omega)) heq
    exact hab (Subtype.ext hh.2)
  · intro a v hv hA
    obtain ⟨i, hi, hiv⟩ := hp a v ((p a).support_toPath_subset_support hv)
    have hh := orbit_collision A B f hf a.property hA i 0
      (fun l hl => hbefore a l (by omega)) (by simp) hiv.symm
    exact hh.2.symm
  · intro a v hv hB
    obtain ⟨i, hi, hiv⟩ := hp a v ((p a).support_toPath_subset_support hv)
    have hin : i = n a := by
      by_contra hne
      exact hbefore a i (by omega) (hiv ▸ hB)
    simpa only [hin] using hiv

theorem fullPacking_of_no_small_separator {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V)
    (hconn : ∀ X : Finset V, X.card < A.card → AvoidingConnection G A B X) :
    Nonempty (FullPacking G A B) := by
  obtain ⟨f, hf, hstep⟩ := successor_of_no_small_separator G A B hconn
  exact fullPacking_of_successor G A B f hf hstep

end LinearListHadwiger.PathPacking

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Routing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

open SimpleGraph PathPacking

theorem avoidingConnection_of_kConnectedOn {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S A B X : Finset V) {k : ℕ}
    (hc : KConnectedOn G S k) (haS : A ⊆ S) (hbS : B ⊆ S)
    (ha : X.card < A.card) (hb : X.card < B.card) (hk : X.card < k) :
    AvoidingConnection G A B X := by
  classical
  have hAX : ¬ A ⊆ X := fun hh => (Nat.not_le_of_lt ha) (Finset.card_le_card hh)
  have hBX : ¬ B ⊆ X := fun hh => (Nat.not_le_of_lt hb) (Finset.card_le_card hh)
  simp only [Finset.subset_iff, not_forall] at hAX hBX
  obtain ⟨a, haA, haX⟩ := hAX
  obtain ⟨b, hbB, hbX⟩ := hBX
  let Z := S ∩ X
  have hZ : Z ⊆ S := Finset.inter_subset_left
  have hZk : Z.card < k := (Finset.card_le_card Finset.inter_subset_right).trans_lt hk
  have hc' := (hc.2 Z hZ hZk).preconnected
  have ha' : a ∈ S \ Z := Finset.mem_sdiff.mpr ⟨haS haA, fun hh => haX (Finset.mem_inter.mp hh).2⟩
  have hb' : b ∈ S \ Z := Finset.mem_sdiff.mpr ⟨hbS hbB, fun hh => hbX (Finset.mem_inter.mp hh).2⟩
  obtain ⟨p⟩ := hc' ⟨a, ha'⟩ ⟨b, hb'⟩
  refine ⟨a, haA, b, hbB, p.map (Embedding.induce (↑(S \ Z) : Set V)).toHom, ?_⟩
  intro v hv
  have hv' : v ∈ (p.map (Embedding.induce (↑(S \ Z) : Set V)).toHom).support := hv
  rw [Walk.support_map] at hv'
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv'
  intro hwX
  exact (Finset.mem_sdiff.mp w.property).2
    (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp w.property).1, hwX⟩)

theorem packing_of_kConnectedOn {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S A B : Finset V) {k : ℕ}
    (hc : KConnectedOn G S k) (haS : A ⊆ S) (hbS : B ⊆ S)
    (ha : A.card ≤ k) (hb : A.card ≤ B.card) : Nonempty (FullPacking G A B) := by
  apply fullPacking_of_no_small_separator
  intro X hX
  exact avoidingConnection_of_kConnectedOn G S A B X hc haS hbS hX
    (hX.trans_le hb) (hX.trans_le ha)

lemma deletedFibers_card {V W : Type} [Fintype V] [DecidableEq W]
    (π : W → V) (s : V → W) (hs : ∀ v, π (s v) = v) (X : Finset W) :
    (deletedFibers π X).card ≤ X.card := by
  classical
  have hinj : Function.Injective s := by
    intro v w h
    simpa only [hs] using congrArg π h
  have hh : (deletedFibers π X).image s ⊆ X := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hv).2 (s v) (hs v)
  simpa only [Finset.card_image_of_injective _ hinj] using Finset.card_le_card hh

lemma avoiding_walk_comap {V W : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (π : W → V) (X : Finset W) {a b : W}
    (ha : a ∉ X) (hb : b ∉ X) (hab : π a ≠ π b)
    (hc : (G.induce (↑(Finset.univ \ deletedFibers π X) : Set V)).Connected) :
    ∃ p : (G.comap π).Walk a b, ∀ w ∈ p.support, w ∉ X := by
  classical
  let S := Finset.univ \ deletedFibers π X
  have haS : π a ∈ S := by
    simp only [S, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hh
    exact ha ((Finset.mem_filter.mp hh).2 a rfl)
  have hbS : π b ∈ S := by
    simp only [S, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hh
    exact hb ((Finset.mem_filter.mp hh).2 b rfl)
  have hex : ∀ v : ↥S, ∃ w : W, w ∉ X ∧ π w = v.val := by
    intro v
    have hh := (Finset.mem_sdiff.mp v.property).2
    simp only [deletedFibers, Finset.mem_filter, Finset.mem_univ, true_and,
      not_forall] at hh
    obtain ⟨w, heq, hw⟩ := hh
    exact ⟨w, hw, heq⟩
  choose f hfX hfπ using hex
  let g : ↥S → W := fun v => if v.val = π a then a else if v.val = π b then b else f v
  have hgX : ∀ v, g v ∉ X := by
    intro v
    simp only [g]
    split_ifs
    · exact ha
    · exact hb
    · exact hfX v
  have hgπ : ∀ v, π (g v) = v.val := by
    intro v
    dsimp only [g]
    split_ifs with hh hh
    · exact hh.symm
    · exact hh.symm
    · exact hfπ v
  let φ : G.induce (↑S : Set V) →g G.comap π :=
    { toFun := g
      map_rel' := by
        intro v w hvw
        change G.Adj (π (g v)) (π (g w))
        rw [hgπ, hgπ]
        exact hvw }
  obtain ⟨p⟩ := hc.preconnected (⟨π a, haS⟩ : ↥S) ⟨π b, hbS⟩
  have hga : φ ⟨π a, haS⟩ = a := by simp [φ, g]
  have hgb : φ ⟨π b, hbS⟩ = b := by simp [φ, g, hab.symm]
  refine ⟨(p.map φ).copy hga hgb, ?_⟩
  intro w hw
  have hw' : w ∈ (p.map φ).support := by simpa using hw
  rw [Walk.support_map] at hw'
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw'
  exact hgX v

lemma packing_in_comap {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V)
    (π : W → V) (s : V → W) (hs : ∀ v, π (s v) = v)
    (A B : Finset W) {k : ℕ} (hc : KConnectedOn G Finset.univ k)
    (ha : A.card ≤ k) (hb : A.card ≤ B.card)
    (hdis : ∀ a ∈ A, ∀ b ∈ B, π a ≠ π b) :
    Nonempty (FullPacking (G.comap π) A B) := by
  classical
  apply fullPacking_of_no_small_separator
  intro X hX
  have hAX : ¬ A ⊆ X := fun hh => (Nat.not_le_of_lt hX) (Finset.card_le_card hh)
  have hBX : ¬ B ⊆ X := fun hh => (Nat.not_le_of_lt (hX.trans_le hb)) (Finset.card_le_card hh)
  simp only [Finset.subset_iff, not_forall] at hAX hBX
  obtain ⟨a, haA, haX⟩ := hAX
  obtain ⟨b, hbB, hbX⟩ := hBX
  have hc' := hc.2 (deletedFibers π X) (Finset.subset_univ _) <|
    (deletedFibers_card π s hs X).trans_lt (hX.trans_le ha)
  obtain ⟨p, hp⟩ := avoiding_walk_comap G π X haX hbX (hdis a haA b hbB) hc'
  exact ⟨a, haA, b, hbB, p, hp⟩

theorem double_packing {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (hab : Disjoint A B)
    (hc : KConnectedOn G Finset.univ (2 * A.card)) (hb : 2 * A.card ≤ B.card) :
    Nonempty (DoublePacking G A B) := by
  classical
  let W := {x : V × Bool // x.2 = false ∨ x.1 ∈ A}
  let : Fintype W := Fintype.ofFinite W
  let π : W → V := fun w => w.val.1
  let sec : V → W := fun v => ⟨(v, false), Or.inl rfl⟩
  have hs : ∀ v, π (sec v) = v := fun _ => rfl
  let ι : (↥A × Bool) → W := fun i => ⟨(i.1.val, i.2), Or.inr i.1.property⟩
  have hi : Function.Injective ι := by
    intro i j hij
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun w : W => w.val.1) hij)
    · exact congrArg (fun w : W => w.val.2) hij
  let AC := Finset.univ.image ι
  let BC := (Finset.univ : Finset ↥B).image fun b => sec b.val
  have hAC : AC.card = 2 * A.card := by
    simp only [AC, Finset.card_image_of_injective _ hi, Finset.card_univ,
      Fintype.card_prod, Fintype.card_coe, Fintype.card_bool]
    omega
  have hBS : Function.Injective (fun b : ↥B => sec b.val) := by
    intro b c h
    exact Subtype.ext (congrArg π h)
  have hBC : BC.card = B.card := by
    simp only [BC, Finset.card_image_of_injective _ hBS,
      Finset.card_univ, Fintype.card_coe]
  have hmemAC : ∀ w : W, w ∈ AC ↔ π w ∈ A := by
    intro w
    constructor
    · intro hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact i.1.property
    · intro hw
      exact Finset.mem_image.mpr ⟨(⟨π w, hw⟩, w.val.2), Finset.mem_univ _, rfl⟩
  have hsec : ∀ w : W, π w ∉ A → sec (π w) = w := by
    intro w hw
    apply Subtype.ext
    change (π w, false) = w.val
    exact Prod.ext rfl (w.property.resolve_right hw).symm
  have hmemBC : ∀ w : W, w ∈ BC ↔ π w ∈ B := by
    intro w
    constructor
    · intro hw
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hw
      exact b.property
    · intro hw
      have hwA : π w ∉ A := fun ha => Finset.disjoint_left.mp hab ha hw
      exact Finset.mem_image.mpr ⟨⟨π w, hw⟩, Finset.mem_univ _, hsec w hwA⟩
  obtain ⟨P⟩ := packing_in_comap G π sec hs AC BC hc (by omega) (by omega) (by
    intro a ha b hb heq
    exact Finset.disjoint_left.mp hab ((hmemAC a).mp ha)
      (heq.symm ▸ (hmemBC b).mp hb))
  let src : (↥A × Bool) → ↥AC := fun i =>
    ⟨ι i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hsrc : Function.Injective src := by
    intro i j hij
    exact hi (congrArg Subtype.val hij)
  let tar : (↥A × Bool) → ↥B := fun i =>
    ⟨π (P.target (src i)), (hmemBC _).mp (P.target (src i)).property⟩
  have htar : Function.Injective tar := by
    intro i j hij
    apply hsrc
    apply P.target_injective
    apply Subtype.ext
    have heq : π (P.target (src i)) = π (P.target (src j)) := congrArg Subtype.val hij
    have hiB : π (P.target (src i)) ∈ B := (tar i).property
    have hjB : π (P.target (src j)) ∈ B := (tar j).property
    have hiA : π (P.target (src i)) ∉ A := fun h => Finset.disjoint_left.mp hab h hiB
    have hjA : π (P.target (src j)) ∉ A := fun h => Finset.disjoint_left.mp hab h hjB
    rw [← hsec _ hiA, ← hsec _ hjA, heq]
  let raw : ∀ i : ↥A × Bool, G.Walk i.1.val (tar i).val :=
    fun i => (P.route (src i)).val.map (Hom.comap π G)
  let route : ∀ i : ↥A × Bool, G.Path i.1.val (tar i).val := fun i => (raw i).toPath
  have hsupport : ∀ i, ∀ v ∈ (route i).val.support,
      ∃ w ∈ (P.route (src i)).val.support, π w = v := by
    intro i v hv
    have hv' : v ∈ (raw i).support := (raw i).support_toPath_subset_support hv
    have hv'' : v ∈ ((P.route (src i)).val.map (Hom.comap π G)).support := hv'
    rw [Walk.support_map] at hv''
    obtain ⟨w, hw, heq⟩ := List.mem_map.mp hv''
    exact ⟨w, hw, heq⟩
  have hsource : ∀ i, ∀ v ∈ (route i).val.support, v ∈ A → v = i.1.val := by
    intro i v hv hvA
    obtain ⟨w, hw, heq⟩ := hsupport i v hv
    have hwA : w ∈ AC := (hmemAC w).mpr (heq ▸ hvA)
    have hh := P.source_only (src i) w hw hwA
    exact heq.symm.trans (congrArg π hh)
  have htarget : ∀ i, ∀ v ∈ (route i).val.support, v ∈ B → v = (tar i).val := by
    intro i v hv hvB
    obtain ⟨w, hw, heq⟩ := hsupport i v hv
    have hwB : w ∈ BC := (hmemBC w).mpr (heq ▸ hvB)
    have hh := P.target_only (src i) w hw hwB
    exact heq.symm.trans (congrArg π hh)
  refine ⟨⟨tar, htar, route, hsource, htarget, ?_⟩⟩
  intro i j hij v hvi hvj
  by_cases hvA : v ∈ A
  · exact ⟨hsource i v hvi hvA, hsource j v hvj hvA⟩
  · obtain ⟨w, hw, heq⟩ := hsupport i v hvi
    obtain ⟨w', hw', heq'⟩ := hsupport j v hvj
    have hwA : π w ∉ A := heq ▸ hvA
    have hwA' : π w' ∉ A := heq' ▸ hvA
    have hww : w = w' := by rw [← hsec w hwA, ← hsec w' hwA', heq, heq']
    have hne : src i ≠ src j := fun h => hij (hsrc h)
    exact (Set.disjoint_left.mp (P.disjoint (src i) (src j) hne) hw (hww ▸ hw')).elim

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.MinorModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open SimpleGraph PathPacking

namespace MinorModel
variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}

theorem lift_clique (M : MinorModel G H) {t : ℕ} (h : HasCliqueMinor H t) :
    HasCliqueMinor G t := by
  obtain ⟨B, hc, hd, he⟩ := h
  refine ⟨fun i => M.expand (B i), fun i => M.expand_connected (hc i),
    fun i j hij => M.expand_disjoint (hd i j hij), ?_⟩
  intro i j hij
  obtain ⟨a, ha, b, hb, hab⟩ := he i j hij
  obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hab
  exact ⟨x, ⟨a, ha, hx⟩, y, ⟨b, hb, hy⟩, hxy⟩

theorem hadwiger_le [Fintype V] [Fintype W] (M : MinorModel G H) :
    hadwigerNumber H ≤ hadwigerNumber G :=
  cliqueMinor_le_hadwigerNumber (M.lift_clique (hasCliqueMinor_hadwigerNumber H))

end MinorModel

open scoped Classical

lemma exists_region_avoiding {V I : Type} [Fintype I] [DecidableEq V]
    (C : I → Set V) (X : Finset V) (c r : ℕ) (hc : 0 < c)
    (hI : c * r ≤ Fintype.card I) (hX : X.card < r)
    (hcon : ∀ v ∈ X, (Finset.univ.filter fun i => v ∈ C i).card ≤ c) :
    ∃ i, ∀ v ∈ C i, v ∉ X := by
  classical
  let met : Finset I := X.biUnion fun v => Finset.univ.filter fun i => v ∈ C i
  have hmet : met.card ≤ X.card * c := by
    calc
      met.card ≤ ∑ v ∈ X, (Finset.univ.filter fun i => v ∈ C i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ X, c := Finset.sum_le_sum hcon
      _ = X.card * c := by simp
  have hmI : met.card < Fintype.card I := by
    have hmul := Nat.mul_lt_mul_of_pos_right hX hc
    nlinarith
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show met.card < (Finset.univ : Finset I).card by simpa using hmI)
  refine ⟨i, ?_⟩
  intro v hv hvX
  exact hi (Finset.mem_biUnion.mpr ⟨v, hvX, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩)

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Exchanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open SimpleGraph PathPacking
open scoped Classical

namespace BagRouting
variable {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}

lemma exists_minimal [Fintype I] (h : Nonempty (BagRouting G s B)) :
    ∃ D : BagRouting G s B, D.Minimal := by
  classical
  have hex : ∃ n : ℕ, ∃ D : BagRouting G s B, D.totalLength = n := by
    obtain ⟨D⟩ := h
    exact ⟨D.totalLength, D, rfl⟩
  obtain ⟨D, hd⟩ := Nat.find_spec hex
  refine ⟨D, fun E => ?_⟩
  rw [hd]
  exact Nat.find_min' hex ⟨E, rfl⟩

lemma replace_shorter [Fintype I] [DecidableEq I] (D : BagRouting G s B) (i : I)
    (p : G.Path (s i) (D.paths i).1)
    (hp : ∀ j, i ≠ j → ∀ v ∈ p.val.support,
      v ∈ (D.paths j).2.val.support → v = s i ∧ v = s j)
    (hlt : p.val.length < (D.paths i).2.val.length) :
    (D.replace i p hp).totalLength < D.totalLength := by
  have hi : (D.replace i p hp).paths i = ⟨(D.paths i).1, p⟩ := dite_eq_left rfl
  have ha : ∀ a, a ≠ i → (D.replace i p hp).paths a = D.paths a := fun a h => dite_eq_right h
  apply Finset.sum_lt_sum
  · intro a _
    by_cases h : a = i
    · subst a
      rw [hi]
      exact hlt.le
    · rw [ha a h]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [hi]
    exact hlt

lemma Minimal.walk_length_le [Fintype I] [DecidableEq V] [DecidableEq I]
    {D : BagRouting G s B} (hD : D.Minimal) (i : I)
    (p : G.Walk (s i) (D.paths i).1)
    (hp : ∀ j, i ≠ j → ∀ v ∈ p.support,
      v ∈ (D.paths j).2.val.support → v = s i ∧ v = s j) :
    (D.paths i).2.val.length ≤ p.length := by
  have hp' : ∀ j, i ≠ j → ∀ v ∈ p.toPath.val.support,
      v ∈ (D.paths j).2.val.support → v = s i ∧ v = s j := by
    intro j hij v hv hvj
    exact hp j hij v (p.support_toPath_subset_support hv) hvj
  have hle : (D.paths i).2.val.length ≤ p.toPath.val.length := by
    by_contra hn
    exact (not_lt_of_ge (hD (D.replace i p.toPath hp')))
      (D.replace_shorter i p.toPath hp' (Nat.lt_of_not_ge hn))
  exact hle.trans p.length_bypass_le_length

lemma Minimal.no_long_shortcut [Fintype I] [DecidableEq V] [DecidableEq I]
    {D : BagRouting G s B} (hD : D.Minimal) (i : I) (v : V) (hv : v ∉ D.used)
    (a b : ℕ) (ha : a ≤ (D.paths i).2.val.length) (hb : b ≤ (D.paths i).2.val.length)
    (hva : G.Adj ((D.paths i).2.val.getVert a) v)
    (hvb : G.Adj v ((D.paths i).2.val.getVert b)) : b ≤ a + 2 := by
  let p := (D.paths i).2.val
  let q : G.Walk (s i) (D.paths i).1 := ((p.take a).concat hva).append (Walk.cons hvb (p.drop b))
  change a ≤ p.length at ha
  change b ≤ p.length at hb
  have hq := hD.walk_length_le i q (by
    intro j hij w hw hwj
    have hw' : w ∈ p.support ∨ w = v := by
      simp only [q, Walk.mem_support_append_iff, Walk.support_concat, Walk.support_cons,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (hw | hw) | (hw | hw)
      · left
        rw [Walk.support_take] at hw
        exact List.mem_of_mem_take hw
      · exact Or.inr hw
      · exact Or.inr hw
      · left
        rw [Walk.drop_support_eq_support_drop_min] at hw
        exact List.mem_of_mem_drop hw
    rcases hw' with hw | rfl
    · exact D.overlap i j hij w hw hwj
    · exact (hv ⟨j, hwj⟩).elim)
  have hlen : q.length = a + 2 + (p.length - b) := by
    simp [q, Walk.take_length, Nat.min_eq_left ha, Walk.drop_length]
    omega
  change p.length ≤ q.length at hq
  rw [hlen] at hq
  omega

lemma Minimal.path_neighbors_le_three [Fintype I] [DecidableEq V] [DecidableEq I]
    [DecidableRel G.Adj]
    {D : BagRouting G s B} (hD : D.Minimal) (i : I) (v : V) (hv : v ∉ D.used) :
    ((D.paths i).2.val.support.toFinset.filter fun w => G.Adj v w).card ≤ 3 := by
  classical
  let p := (D.paths i).2.val
  let R := (Finset.range (p.length + 1)).filter fun a => G.Adj v (p.getVert a)
  have hR : R.card ≤ 3 := by
    obtain he | hn := R.eq_empty_or_nonempty
    · simp [he]
    let a := R.min' hn
    have haR : a ∈ R := R.min'_mem hn
    have ha : a ≤ p.length := by
      have hh := (Finset.mem_filter.mp haR).1
      simp only [Finset.mem_range] at hh
      omega
    have hsub : R ⊆ Finset.Icc a (a + 2) := by
      intro b hbR
      have hb : b ≤ p.length := by
        have hh := (Finset.mem_filter.mp hbR).1
        simp only [Finset.mem_range] at hh
        omega
      have hab := hD.no_long_shortcut i v hv a b ha hb
        (Finset.mem_filter.mp haR).2.symm (Finset.mem_filter.mp hbR).2
      exact Finset.mem_Icc.mpr ⟨R.min'_le b hbR, hab⟩
    exact (Finset.card_le_card hsub).trans (by simp; omega)
  have hsub : (p.support.toFinset.filter fun w => G.Adj v w) ⊆ R.image p.getVert := by
    intro w hw
    obtain ⟨hwp, hvw⟩ := Finset.mem_filter.mp hw
    obtain ⟨a, ha, hlen⟩ := Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hwp)
    refine Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨?_, ?_⟩, ha⟩
    · exact Finset.mem_range.mpr (by omega)
    · rwa [ha]
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans hR)

lemma mem_usedFinset [Fintype I] [DecidableEq V] (D : BagRouting G s B) (v : V) :
    v ∈ D.usedFinset ↔ v ∈ D.used := by
  simp [usedFinset, used]

namespace Exchange
variable [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}

lemma length_inequality (E : D.Exchange) (i : I) :
    (E.routing.paths i).2.val.length + (if E.e i ∈ E.active then E.b (E.e i) else 0) ≤
      (D.paths (E.e i)).2.val.length + (if i ∈ E.active then E.a i + 1 else 0) := by
  by_cases hi : i ∈ E.active
  · have he : E.routing.paths i = ⟨(D.paths (E.e i)).1, (E.walk i hi).toPath⟩ := dite_eq_left hi
    rw [he, ite_eq_left hi, ite_eq_left ((E.stable i).mp hi)]
    have hlen : (E.walk i hi).toPath.val.length ≤ (E.walk i hi).length :=
      (E.walk i hi).length_bypass_le_length
    have ha := (E.bounds i hi).1
    have hb := E.bounds (E.e i) ((E.stable i).mp hi)
    have hia := E.bounds i hi
    have hleni : E.a i ≤ (D.paths i).2.val.length := by omega
    have hwlen : (E.walk i hi).length = E.a i + 1 +
        ((D.paths (E.e i)).2.val.length - E.b (E.e i)) := by
      simp only [walk, Walk.length_append, Walk.length_concat, Walk.take_length,
        Nat.min_eq_left hleni, Walk.drop_length]
    rw [hwlen] at hlen
    change (E.walk i hi).toPath.val.length + E.b (E.e i) ≤ _
    omega
  · have he : E.routing.paths i = D.paths i := dite_eq_right hi
    rw [he, E.fixed i hi]
    simp only [ite_eq_right hi, le_refl]

lemma shorter [Fintype I] (E : D.Exchange) (hE : E.active.Nonempty) :
    E.routing.totalLength < D.totalLength := by
  let a : I → ℕ := fun i => if i ∈ E.active then E.a i + 1 else 0
  let b : I → ℕ := fun i => if i ∈ E.active then E.b i else 0
  have hlt : (∑ i, a i) < ∑ i, b i := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i ∈ E.active
      · have := (E.bounds i hi).1
        simp only [a, b, ite_eq_left hi]
        omega
      · simp [a, b, hi]
    · obtain ⟨i, hi⟩ := hE
      refine ⟨i, Finset.mem_univ _, ?_⟩
      have := (E.bounds i hi).1
      simp only [a, b, ite_eq_left hi]
      omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => E.length_inequality i)
  change (∑ i, ((E.routing.paths i).2.val.length + b (E.e i))) ≤
    ∑ i, ((D.paths (E.e i)).2.val.length + a i) at hs
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Equiv.sum_comp E.e b,
    Equiv.sum_comp E.e (fun i => (D.paths i).2.val.length)] at hs
  change E.routing.totalLength + (∑ i, b i) ≤ D.totalLength + (∑ i, a i) at hs
  omega

end Exchange

lemma Minimal.no_exchange [Fintype I] [DecidableEq V] [DecidableEq I]
    {D : BagRouting G s B} (hD : D.Minimal) (E : D.Exchange) : ¬ E.active.Nonempty := by
  intro hE
  exact (not_lt_of_ge (hD E.routing)) (E.shorter hE)

lemma cycle_permutation [Fintype I] [DecidableEq I] (Q : Finset I) (hQ : Q.Nonempty)
    (f : I → I) (hf : ∀ i ∈ Q, f i ∈ Q) :
    ∃ T : Finset I, T ⊆ Q ∧ T.Nonempty ∧ ∃ e : Equiv.Perm I,
      (∀ i, i ∉ T → e i = i) ∧ (∀ i, i ∈ T ↔ e i ∈ T) ∧
      (∀ i ∈ T, e i = f i) := by
  classical
  let C := Q.powerset.filter fun T => T.Nonempty ∧ ∀ i ∈ T, f i ∈ T
  have hQC : Q ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by rfl), hQ, hf⟩
  obtain ⟨T, hTC, hmin⟩ := C.exists_min_image Finset.card ⟨Q, hQC⟩
  obtain ⟨hTQ, hn, hclosed⟩ := Finset.mem_filter.mp hTC
  have hsub : T.image f ⊆ T := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact hclosed j hj
  have hIC : T.image f ∈ C := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hsub.trans (Finset.mem_powerset.mp hTQ)),
      hn.image f, ?_⟩
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hsub hi, rfl⟩
  have heq : T.image f = T := Finset.eq_of_subset_of_card_le hsub (hmin _ hIC)
  let g : ↥T → ↥T := fun i => ⟨f i, hclosed i i.property⟩
  have hsurj : Function.Surjective g := by
    intro i
    have hi : i.val ∈ T.image f := heq.symm ▸ i.property
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
    exact ⟨⟨j, hj⟩, Subtype.ext he⟩
  let e0 : Equiv.Perm ↥T := Equiv.ofBijective g (Finite.surjective_iff_bijective.mp hsurj)
  let e := Equiv.Perm.ofSubtype e0
  refine ⟨T, Finset.mem_powerset.mp hTQ, hn, e, ?_, ?_, ?_⟩
  · intro i hi
    exact Equiv.Perm.ofSubtype_apply_of_not_mem e0 hi
  · intro i
    exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem e0 i).symm
  · intro i hi
    exact Equiv.Perm.ofSubtype_apply_of_mem e0 hi

lemma Minimal.low_degree [Fintype I] [DecidableEq V] [DecidableEq I]
    [DecidableRel G.Adj] {D : BagRouting G s B} (hD : D.Minimal)
    (S : Finset V) (hS : S ⊆ D.usedFinset) (hne : S.Nonempty) :
    ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 2 * Fintype.card I := by
  classical
  by_contra hno
  have hdeg : ∀ v ∈ S, 2 * Fintype.card I < (S.filter (G.Adj v)).card := by
    intro v hv
    exact Nat.lt_of_not_ge (fun hh => hno ⟨v, hv, hh⟩)
  let R : I → Finset ℕ := fun i => (Finset.range ((D.paths i).2.val.length + 1)).filter
    fun a => (D.paths i).2.val.getVert a ∈ S
  let Q : Finset I := Finset.univ.filter fun i => (R i).Nonempty
  let a : I → ℕ := fun i => if hi : (R i).Nonempty then (R i).min' hi else 0
  have hQiff : ∀ i, i ∈ Q ↔ (R i).Nonempty := by simp [Q]
  have hamin : ∀ i ∈ Q, a i ∈ R i := by
    intro i hi
    have hn := (hQiff i).mp hi
    dsimp [a]
    rw [dite_eq_left hn]
    exact Finset.min'_mem _ _
  have haS : ∀ i ∈ Q, (D.paths i).2.val.getVert (a i) ∈ S := by
    intro i hi
    exact (Finset.mem_filter.mp (hamin i hi)).2
  have hfind : ∀ v ∈ S, ∃ i ∈ Q, ∃ b, b ∈ R i ∧ (D.paths i).2.val.getVert b = v := by
    intro v hv
    obtain ⟨i, hi⟩ := (D.mem_usedFinset v).mp (hS hv)
    obtain ⟨b, hb, hblen⟩ := Walk.mem_support_iff_exists_getVert.mp hi
    have hbR : b ∈ R i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb ▸ hv⟩
    exact ⟨i, (hQiff i).mpr ⟨b, hbR⟩, b, hbR, hb⟩
  have hQ : Q.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    obtain ⟨i, hi, _⟩ := hfind v hv
    exact ⟨i, hi⟩
  let M := Finset.univ.biUnion fun i : I =>
    {(D.paths i).2.val.getVert (a i), (D.paths i).2.val.getVert (a i + 1)}
  have hM : M.card ≤ 2 * Fintype.card I := by
    calc
      _ ≤ ∑ i : I, ({(D.paths i).2.val.getVert (a i),
        (D.paths i).2.val.getVert (a i + 1)} : Finset V).card := Finset.card_biUnion_le
      _ ≤ ∑ i : I, 2 := Finset.sum_le_sum fun _ _ => Finset.card_le_two
      _ = _ := by simp [Nat.mul_comm]
  have hm0 : ∀ i, (D.paths i).2.val.getVert (a i) ∈ M := by
    intro i
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
  have hm1 : ∀ i, (D.paths i).2.val.getVert (a i + 1) ∈ M := by
    intro i
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
  have hout : ∀ i, ∃ j b, i ∈ Q → j ∈ Q ∧ a j + 2 ≤ b ∧
      b ≤ (D.paths j).2.val.length ∧
      G.Adj ((D.paths i).2.val.getVert (a i)) ((D.paths j).2.val.getVert b) := by
    intro i
    by_cases hi : i ∈ Q
    · have hlarge := hdeg _ (haS i hi)
      have hex : ∃ v ∈ S.filter (G.Adj ((D.paths i).2.val.getVert (a i))), v ∉ M := by
        by_contra hh
        have hsub : S.filter (G.Adj ((D.paths i).2.val.getVert (a i))) ⊆ M := by
          intro v hv
          by_contra hvm
          exact hh ⟨v, hv, hvm⟩
        have hle := (Finset.card_le_card hsub).trans hM
        omega
      obtain ⟨v, hv, hvm⟩ := hex
      obtain ⟨hvS, hvadj⟩ := Finset.mem_filter.mp hv
      obtain ⟨j, hj, b, hbR, hb⟩ := hfind v hvS
      have hbj : a j ≤ b := by
        have hn := (hQiff j).mp hj
        dsimp [a]
        rw [dite_eq_left hn]
        exact Finset.min'_le _ _ hbR
      have hb0 : b ≠ a j := by
        intro he
        apply hvm
        rw [he] at hb
        exact hb ▸ hm0 j
      have hb1 : b ≠ a j + 1 := by
        intro he
        apply hvm
        rw [he] at hb
        exact hb ▸ hm1 j
      have hblen : b ≤ (D.paths j).2.val.length := by
        have hh := (Finset.mem_filter.mp hbR).1
        simp only [Finset.mem_range] at hh
        omega
      refine ⟨j, b, fun _ => ⟨hj, by omega, hblen, ?_⟩⟩
      rwa [hb]
    · exact ⟨i, 0, fun hh => (hi hh).elim⟩
  choose f c hfc using hout
  obtain ⟨T, hTQ, hT, e, hfix, hstable, heq⟩ :=
    cycle_permutation Q hQ f (fun i hi => (hfc i hi).1)
  let E : D.Exchange := {
    active := T
    e := e
    fixed := hfix
    stable := hstable
    a := a
    b := fun i => c (e.symm i)
    bounds := by
      intro i hi
      have hpre : e.symm i ∈ T := (hstable _).mpr (by simpa using hi)
      have he : f (e.symm i) = i := (heq _ hpre).symm.trans (e.apply_symm_apply i)
      have hc := (hfc _ (hTQ hpre)).2
      rw [he] at hc
      exact ⟨hc.1, hc.2.1⟩
    edge := by
      intro i hi
      have hc := (hfc i (hTQ hi)).2.2.2
      rw [← heq i hi] at hc
      simpa only [Equiv.symm_apply_apply] using hc
  }
  exact hD.no_exchange E hT

end BagRouting

end LinearListHadwiger

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

end ConnectivityTests

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open SimpleGraph

namespace Density
variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma darts_card_le (S : Finset V) : (darts G S).card ≤ S.card * (S.card - 1) := by
  calc
    (darts G S).card ≤ S.offDiag.card := Finset.card_le_card (by
      intro e he
      obtain ⟨hx,hy,ha⟩ := (mem_darts G).mp he
      exact Finset.mem_offDiag.mpr ⟨hx,hy,ha.ne⟩)
    _ = _ := by simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]

lemma darts_separator {S A Z B : Finset V} (h : SeparatorSplit G S A Z B) :
    (darts G S).card ≤ (darts G (A ∪ Z)).card + (darts G (B ∪ Z)).card := by
  apply (Finset.card_le_card (show darts G S ⊆ darts G (A ∪ Z) ∪ darts G (B ∪ Z) from ?_)).trans
    (Finset.card_union_le _ _)
  intro e he
  obtain ⟨hx,hy,ha⟩ := (mem_darts G).mp he
  rw [← h.union_eq] at hx hy
  simp only [Finset.mem_union] at hx hy ⊢
  rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_left _ hy,ha⟩)
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_right _ hy,ha⟩)
  · exact (h.anticomplete _ hx _ hy ha).elim
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_right _ hx,Finset.mem_union_left _ hy,ha⟩)
  · exact Or.inl ((mem_darts G).mpr ⟨Finset.mem_union_right _ hx,Finset.mem_union_right _ hy,ha⟩)
  · exact Or.inr ((mem_darts G).mpr ⟨Finset.mem_union_right _ hx,Finset.mem_union_left _ hy,ha⟩)
  · exact (h.anticomplete _ hy _ hx ha.symm).elim
  · exact Or.inr ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_right _ hy,ha⟩)
  · exact Or.inr ((mem_darts G).mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_left _ hy,ha⟩)

theorem connectivity_of_density (S : Finset V) {k : ℕ} (hk : 1 ≤ k)
    (hedges : 4*k*S.card < (darts G S).card) :
    ∃ T ⊆ S, KConnectedOn G T k := by
  classical
  have hbound := darts_card_le G S
  have hpos : 0 < S.card := by
    by_contra hn
    have hz : S.card = 0 := by omega
    simp only [hz, Nat.zero_mul] at hbound hedges
    omega
  have hlarge : 2*k ≤ S.card := by
    have hh : S.card - 1 ≤ S.card := Nat.sub_le _ _
    nlinarith
  let good := S.powerset.filter (fun T => 2*k ≤ T.card ∧ 4*k*(T.card-k) < (darts G T).card)
  have hSgood : S ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),hlarge,?_⟩
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hedges
  obtain ⟨H,hHg,hmin⟩ := Finset.exists_min_image good Finset.card ⟨S,hSgood⟩
  obtain ⟨hHS,hHsize,hHedges⟩ : H ⊆ S ∧ 2*k ≤ H.card ∧
      4*k*(H.card-k) < (darts G H).card := by
    simpa only [good,Finset.mem_filter,Finset.mem_powerset,and_assoc] using hHg
  have hminimal (T : Finset V) (hTH : T ⊆ H) (hTk : 2*k ≤ T.card)
      (hcard : T.card < H.card) : (darts G T).card ≤ 4*k*(T.card-k) := by
    by_contra hn
    have hgood : T ∈ good := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (hTH.trans hHS),hTk,by omega⟩
    have := hmin T hgood
    omega
  have hHsize' : 2*k < H.card := by
    have hb := darts_card_le G H
    have hsub : H.card - 1 ≤ H.card := Nat.sub_le _ _
    by_contra hn
    have heq : H.card = 2*k := by omega
    have heq' : H.card - k = k := by omega
    rw [heq'] at hHedges
    nlinarith
  have hdegree (v : V) (hv : v ∈ H) : 2*k < (neighbors G H v).card := by
    have heq := Finset.card_erase_add_one hv
    have hd := darts_erase G hv
    have hb := hminimal (H.erase v) (Finset.erase_subset _ _) (by omega) (by omega)
    have hs : H.card-k = (H.erase v).card-k+1 := by omega
    rw [hs] at hHedges
    nlinarith
  refine ⟨H,hHS,?_⟩
  by_contra hn
  obtain ⟨A,Z,B,hZ,hsep⟩ := exists_separator G H (by omega) hn
  have hsub₁ : A ∪ Z ⊆ H := by rw [← hsep.union_eq]; exact Finset.subset_union_left
  have hsub₂ : B ∪ Z ⊆ H := by
    intro v hv
    rw [← hsep.union_eq]
    rcases Finset.mem_union.mp hv with hb | hz
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  have hcard₁ : (A ∪ Z).card < H.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub₁,?_⟩
    intro heq
    obtain ⟨v,hv⟩ := hsep.right_nonempty
    have hvH : v ∈ H := by rw [← hsep.union_eq]; exact Finset.mem_union_right _ hv
    rw [←heq] at hvH
    rcases Finset.mem_union.mp hvH with ha | hz
    · exact Finset.disjoint_left.mp hsep.left_right ha hv
    · exact Finset.disjoint_left.mp hsep.sep_right hz hv
  have hcard₂ : (B ∪ Z).card < H.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub₂,?_⟩
    intro heq
    obtain ⟨v,hv⟩ := hsep.left_nonempty
    have hvH : v ∈ H := hsub₁ (Finset.mem_union_left _ hv)
    rw [←heq] at hvH
    rcases Finset.mem_union.mp hvH with hb | hz
    · exact Finset.disjoint_left.mp hsep.left_right hv hb
    · exact Finset.disjoint_left.mp hsep.left_sep hv hz
  have hsize₁ : 2*k ≤ (A ∪ Z).card := by
    obtain ⟨v,hv⟩ := hsep.left_nonempty
    have hd := hdegree v (hsub₁ (Finset.mem_union_left _ hv))
    have hb : (neighbors G H v).card ≤ (A ∪ Z).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨hwH,ha⟩ := (mem_neighbors G).mp hw
      rw [←hsep.union_eq] at hwH
      rcases Finset.mem_union.mp hwH with hw | hw
      · exact hw
      · exact (hsep.anticomplete _ hv _ hw ha).elim
    omega
  have hsize₂ : 2*k ≤ (B ∪ Z).card := by
    obtain ⟨v,hv⟩ := hsep.right_nonempty
    have hd := hdegree v (hsub₂ (Finset.mem_union_left _ hv))
    have hb : (neighbors G H v).card ≤ (B ∪ Z).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨hwH,ha⟩ := (mem_neighbors G).mp hw
      rw [←hsep.union_eq] at hwH
      rcases Finset.mem_union.mp hwH with hw | hw
      · rcases Finset.mem_union.mp hw with hw | hw
        · exact (hsep.anticomplete _ hw _ hv ha.symm).elim
        · exact Finset.mem_union_right _ hw
      · exact Finset.mem_union_left _ hw
    omega
  have hb₁ := hminimal (A ∪ Z) hsub₁ hsize₁ hcard₁
  have hb₂ := hminimal (B ∪ Z) hsub₂ hsize₂ hcard₂
  have hedge := darts_separator G hsep
  have hcards : (A ∪ Z).card + (B ∪ Z).card = H.card + Z.card := by
    rw [Finset.card_union_of_disjoint hsep.left_sep,
      Finset.card_union_of_disjoint hsep.sep_right.symm, ← hsep.union_eq,
      Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
        ⟨hsep.left_right,hsep.sep_right⟩),Finset.card_union_of_disjoint hsep.left_sep]
    omega
  have h1 : (A ∪ Z).card-k+k = (A ∪ Z).card := Nat.sub_add_cancel (by omega)
  have h2 : (B ∪ Z).card-k+k = (B ∪ Z).card := Nat.sub_add_cancel (by omega)
  have hH : H.card-k+k = H.card := Nat.sub_add_cancel (by omega)
  nlinarith

theorem edge_density_connectivity [Fintype V] {k : ℕ} (hk : 1 ≤ k)
    (he : 2*k*Fintype.card V < G.edgeFinset.card) :
    ∃ T : Finset V, KConnectedOn G T k := by
  obtain ⟨T,_,hT⟩ := connectivity_of_density G Finset.univ hk (by
    rw [darts_univ,Finset.card_univ]
    nlinarith)
  exact ⟨T,hT⟩

end Density

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.PairedSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.PairedSources
open SimpleGraph PathPacking
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

variable {G : SimpleGraph V} {s : I → Bool → V} {U : Set V}

lemma lift_regular {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {G : SimpleGraph V} {s : I → Bool → V} {U : Set V} {x y : I ⊕ V} (q : (graph G s U).Walk x y)
    (h : ∀ i, Sum.inl i ∉ q.support) {u v : V}
    (hx : x = .inr u) (hy : y = .inr v) :
    ∃ p : G.Walk u v, ∀ w ∈ p.support, Sum.inr w ∈ q.support := by
  induction q generalizing u with
  | nil =>
    have huv : u = v := Sum.inr.inj (hx.symm.trans hy)
    subst v
    refine ⟨Walk.nil,?_⟩
    intro w hw
    have : w = u := by simpa using hw
    subst w
    simp [hx]
  | @cons x z y e q ih =>
    have hq : ∀ i, Sum.inl i ∉ q.support := fun i hi => h i (by simp [hi])
    cases z with
    | inl j => exact (hq j q.start_mem_support).elim
    | inr z =>
      obtain ⟨p,hp⟩ := ih hq rfl hy
      have he : G.Adj u z := by
        rw [hx] at e
        exact e.2.2.2.2
      refine ⟨Walk.cons he p,?_⟩
      intro w hw
      simp only [Walk.support_cons,List.mem_cons] at hw ⊢
      rcases hw with rfl | hw
      · exact Or.inl hx.symm
      · exact Or.inr (hp w hw)

lemma mapped_route {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {G : SimpleGraph V} {s : I → Bool → V} {U : Set V} (i : I) (b : Bool) {v : V}
    (p : G.Path (s i b) v)
    (hU : ∀ w ∈ p.val.support, w ∈ U)
    (hsource : ∀ w ∈ p.val.support, ∀ j c, w = s j c → w = s i b)
    (hv : v ≠ s i b) :
    ∃ q : (graph G s U).Walk (.inl i) (.inr v),
      (∀ j, Sum.inl j ∈ q.support → j = i) ∧
      (∀ w, Sum.inr w ∈ q.support → w ∈ p.val.support) := by
  classical
  let f := routeHom i b p hU hsource
  let q0 := (p.val.induce {w | w ∈ p.val.support} (fun _ => id)).map f
  have hs : Sum.inl i = f ⟨s i b,p.val.start_mem_support⟩ := by simp [f,routeHom]
  have ht : Sum.inr v = f ⟨v,p.val.end_mem_support⟩ := by simp [f,routeHom,hv]
  refine ⟨q0.copy hs.symm ht.symm,?_,?_⟩
  · intro j hj
    simp only [Walk.support_copy,q0,Walk.support_map] at hj
    obtain ⟨w,_,hw⟩ := List.mem_map.mp hj
    by_cases h : w.val = s i b
    · have he : Sum.inl i = (Sum.inl j : I ⊕ V) := by
        simpa [f,routeHom,h] using hw
      exact (Sum.inl.inj he).symm
    · have he : Sum.inr w.val = (Sum.inl j : I ⊕ V) := by
        simp [f,routeHom,h] at hw
      cases he
  · intro w hw
    simp only [Walk.support_copy,q0,Walk.support_map] at hw
    obtain ⟨z,_,hz⟩ := List.mem_map.mp hw
    by_cases h : z.val = s i b
    · have he : Sum.inl i = (Sum.inr w : I ⊕ V) := by
        simp [f,routeHom,h] at hz
      cases he
    · have he : Sum.inr z.val = (Sum.inr w : I ⊕ V) := by
        simpa [f,routeHom,h] using hz
      exact (Sum.inr.inj he) ▸ z.property

lemma ordinary_valid_on_walk {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {G : SimpleGraph V} {s : I → Bool → V} {U : Set V} {x y : I ⊕ V} (q : (graph G s U).Walk x y)
    (hx : Valid s U x) :
    ∀ v, Sum.inr v ∈ q.support → v ∈ U ∧ ∀ j b, v ≠ s j b := by
  induction q with
  | @nil x =>
    intro v hv
    have hh : Sum.inr v = x := by simpa using hv
    simpa only [← hh,Valid] using hx
  | @cons x z y e q ih =>
    have hz : Valid s U z := by
      cases z with
      | inl _ => trivial
      | inr z =>
        cases x with
        | inl _ => exact ⟨e.1,e.2.1⟩
        | inr _ => exact ⟨e.2.1,e.2.2.2.1⟩
    intro v hv
    simp only [Walk.support_cons,List.mem_cons] at hv
    rcases hv with hv | hv
    · simpa only [← hv,Valid] using hx
    · exact ih hz v hv

lemma lift_source_path {i : I} {v : V}
    (q : (graph G s U).Path (.inl i) (.inr v))
    (hsource : ∀ j, Sum.inl j ∈ q.val.support → j = i) :
    ∃ b : Bool, ∃ p : G.Path (s i b) v,
      ∀ w ∈ p.val.support, w = s i b ∨
        (Sum.inr w ∈ q.val.support ∧ w ∈ U ∧ ∀ j c, w ≠ s j c) := by
  obtain ⟨q,hq⟩ := q
  cases q with
  | @cons _ z _ e q =>
    cases z with
    | inl j => exact e.elim
    | inr z =>
      obtain ⟨hzU,hzs,b,he⟩ := e
      have havoid : ∀ j, Sum.inl j ∉ q.support := by
        intro j hj
        have hji := hsource j (List.mem_cons_of_mem _ hj)
        subst j
        exact ((Walk.cons_isPath_iff _ _).mp hq).2 hj
      obtain ⟨p,hp⟩ := lift_regular q havoid rfl rfl
      let p0 := Walk.cons he p
      refine ⟨b,p0.toPath,?_⟩
      intro w hw
      have hww := p0.support_toPath_subset_support hw
      simp only [p0,Walk.support_cons,List.mem_cons] at hww
      rcases hww with hww | hww
      · exact Or.inl hww
      · have hqmem : Sum.inr w ∈ (Walk.cons (show (graph G s U).Adj (.inl i) (.inr z) from
            ⟨hzU,hzs,b,he⟩) q).support := by simp [hp w hww]
        exact Or.inr ⟨hqmem,ordinary_valid_on_walk
          (Walk.cons (show (graph G s U).Adj (.inl i) (.inr z) from
            ⟨hzU,hzs,b,he⟩) q) (show Valid s U (.inl i) from trivial) w hqmem⟩

theorem combine {D : Finset V} (target : I → Bool → ↥D)
    (route : ∀ i b, G.Path (s i b) (target i b).val)
    (hgroups : ∀ i b j c, s i b = s j c → i = j)
    (hD : ∀ v ∈ D, ∀ i b, v ≠ s i b)
    (hU : ∀ i b v, v ∈ (route i b).val.support → v ∈ U)
    (hS : ∀ i b v, v ∈ (route i b).val.support →
      ∀ j c, v = s j c → v = s i b)
    (hcon : ∀ v, (Finset.univ.filter (fun ib : I × Bool =>
      v ∈ (route ib.1 ib.2).val.support)).card ≤ 2) :
    Nonempty (Packing G s D U) := by
  classical
  let Q := graph G s U
  let A : Finset (I ⊕ V) := Finset.univ.map ⟨Sum.inl,Sum.inl_injective⟩
  let B : Finset (I ⊕ V) := D.map ⟨Sum.inr,Sum.inr_injective⟩
  have hq (ib : I × Bool) := mapped_route ib.1 ib.2 (route ib.1 ib.2)
    (hU ib.1 ib.2) (hS ib.1 ib.2)
    (hD _ (target ib.1 ib.2).property ib.1 ib.2)
  choose q hqL hqR using hq
  have hconQ (x : I ⊕ V) :
      (Finset.univ.filter (fun ib : I × Bool => x ∈ (q ib).support)).card ≤ 2 := by
    cases x with
    | inl i =>
      have hsub : (Finset.univ.filter (fun ib : I × Bool => Sum.inl i ∈ (q ib).support)) ⊆
          ({i} ×ˢ (Finset.univ : Finset Bool)) := by
        intro ib hib
        have he : ib.1 = i := (hqL ib i (Finset.mem_filter.mp hib).2).symm
        exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr he,Finset.mem_univ _⟩
      simpa using Finset.card_le_card hsub
    | inr v =>
      apply (Finset.card_le_card ?_).trans (hcon v)
      intro ib hib
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqR ib v (Finset.mem_filter.mp hib).2⟩
  have hAC : A.card = Fintype.card I := by simp [A]
  have hPI : 2*A.card ≤ Fintype.card (I × Bool) := by simp [hAC,Fintype.card_prod]; omega
  have hpack : Nonempty (FullPacking Q A B) := by
    apply fullPacking_of_no_small_separator
    intro X hX
    obtain ⟨ib,hi⟩ := exists_region_avoiding (fun ib => {x | x ∈ (q ib).support})
      X 2 A.card (by omega) hPI hX (fun x _ => hconQ x)
    exact ⟨Sum.inl ib.1,by simp [A],Sum.inr (target ib.1 ib.2).val,
      by simp [B,(target ib.1 ib.2).property],q ib,hi⟩
  obtain ⟨P⟩ := hpack
  let a (i : I) : ↥A := ⟨.inl i,by simp [A]⟩
  have ha : Function.Injective a := by
    intro i j hij
    exact Sum.inl.inj (congrArg Subtype.val hij)
  have hd (i : I) : ∃ d : ↥D, (P.target (a i)).val = Sum.inr d.val := by
    obtain ⟨v,hv,hve⟩ := Finset.mem_map.mp (P.target (a i)).property
    exact ⟨⟨v,hv⟩,hve.symm⟩
  choose dest hdest using hd
  let qp (i : I) : Q.Path (.inl i) (.inr (dest i).val) :=
    ⟨(P.route (a i)).val.copy rfl (hdest i),by
      simpa only [Walk.isPath_copy] using (P.route (a i)).property⟩
  have hqps (i j : I) (h : Sum.inl j ∈ (qp i).val.support) : j = i := by
    have hh := P.source_only (a i) (Sum.inl j) (by simpa [qp] using h) (by simp [A])
    exact Sum.inl.inj hh
  have hlift (i : I) := lift_source_path (qp i) (hqps i)
  choose b p hp using hlift
  refine ⟨⟨b,dest,p,?_,?_,?_,?_⟩⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro w hwi hwj
    rcases hp i w hwi with hi | hi <;> rcases hp j w hwj with hj | hj
    · exact hij (hgroups i (b i) j (b j) (hi.symm.trans hj))
    · exact hj.2.2 i (b i) hi
    · exact hi.2.2 j (b j) hj
    · exact Set.disjoint_left.mp (P.disjoint (a i) (a j) (fun h => hij (ha h)))
        (by simpa [qp] using hi.1) (by simpa [qp] using hj.1)
  · intro i v hv ⟨j,c,hvS⟩
    rcases hp i v hv with h | h
    · exact h
    · exact (h.2.2 j c hvS).elim
  · intro i v hv hvD
    rcases hp i v hv with h | h
    · exact (hD v hvD i (b i) h).elim
    · have hh := P.target_only (a i) (Sum.inr v) (by simpa [qp] using h.1)
        (by simp [B,hvD])
      rw [hdest i] at hh
      exact Sum.inr.inj hh
  · intro i v hv
    rcases hp i v hv with h | h
    · simpa only [h] using hU i (b i) _ (route i (b i)).val.start_mem_support
    · exact h.2.1

end LinearListHadwiger.PairedSources

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

lemma connected_induce_congr {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {S T : Finset V} (h : S = T)
    (hc : (G.induce (↑S : Set V)).Connected) :
    (G.induce (↑T : Set V)).Connected := h ▸ hc

lemma delete_connected (G : SimpleGraph V) {S Z : Finset V} {k : ℕ}
    (hc : KConnectedOn G S k) (hZ : Z ⊆ S) (hz : Z.card < k) :
    KConnectedOn G (S \ Z) (k-Z.card) := by
  classical
  refine ⟨?_,?_⟩
  · have hs := Finset.card_sdiff_add_card_eq_card hZ
    have := hc.1
    omega
  · intro X hX hx
    have hXZ : Disjoint X Z := Finset.disjoint_left.mpr (fun v hv hz =>
      (Finset.mem_sdiff.mp (hX hv)).2 hz)
    have huS : Z ∪ X ⊆ S := Finset.union_subset hZ
      (hX.trans Finset.sdiff_subset)
    have huc : (Z ∪ X).card < k := by
      rw [Finset.card_union_of_disjoint hXZ.symm]
      omega
    apply connected_induce_congr G (show S \ (Z ∪ X) = (S \ Z) \ X by
      ext v; simp only [Finset.mem_sdiff,Finset.mem_union]; tauto)
    exact hc.2 _ huS huc

theorem short_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) {k : ℕ} (hk : 0 < k)
    (hdeg : ∀ v, k ≤ (Density.neighbors G Finset.univ v).card) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length < 3 * (Fintype.card V / k + 1) := by
  classical
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
  let n := p.length / 3 + 1
  let N (i : Fin n) := Density.neighbors G Finset.univ (p.getVert (3*i.val))
  have hidx : ∀ i : Fin n, 3*i.val ≤ p.length := by
    intro i
    have := i.isLt
    dsimp [n] at this
    have := Nat.mod_add_div p.length 3
    omega
  have hdist : ∀ i : Fin n, G.dist u (p.getVert (3*i.val)) = 3*i.val := by
    intro i
    have h := length_eq_dist_of_subwalk hp (p.isSubwalk_take (3*i.val))
    simpa [Walk.take_length, Nat.min_eq_left (hidx i)] using h.symm
  have hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (N i) (N j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hi : G.Adj (p.getVert (3*i.val)) w := (Density.mem_neighbors G).mp hwi |>.2
    have hj : G.Adj (p.getVert (3*j.val)) w := (Density.mem_neighbors G).mp hwj |>.2
    have h₁ := hc.dist_triangle (u := u) (v := p.getVert (3*i.val)) (w := w)
    have h₂ := hc.dist_triangle (u := u) (v := w) (w := p.getVert (3*j.val))
    have h₃ := hc.dist_triangle (u := u) (v := p.getVert (3*j.val)) (w := w)
    have h₄ := hc.dist_triangle (u := u) (v := w) (w := p.getVert (3*i.val))
    rw [hdist i, dist_eq_one_iff_adj.mpr hi] at h₁
    rw [hdist j, dist_eq_one_iff_adj.mpr hj.symm] at h₂
    rw [hdist j, dist_eq_one_iff_adj.mpr hj] at h₃
    rw [hdist i, dist_eq_one_iff_adj.mpr hi.symm] at h₄
    have he : i.val = j.val := by omega
    exact hij (Fin.ext he)
  have hsum : (∑ i : Fin n, (N i).card) ≤ Fintype.card V := by
    rw [← Finset.card_biUnion (s := Finset.univ) (t := N)]
    · exact Finset.card_le_univ _
    · intro i _ j _ hij
      exact hdisj i j hij
  have hnk : n*k ≤ Fintype.card V := by
    calc
      n*k = ∑ i : Fin n, k := by simp
      _ ≤ ∑ i : Fin n, (N i).card := Finset.sum_le_sum (fun i _ => hdeg _)
      _ ≤ Fintype.card V := hsum
  have hn : n ≤ Fintype.card V / k := (Nat.le_div_iff_mul_le hk).mpr hnk
  refine ⟨p,p.isPath_of_length_eq_dist hp,?_⟩
  have := Nat.mod_lt p.length (by omega : 0 < 3)
  have := Nat.mod_add_div p.length 3
  dsimp [n] at hn
  omega

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
-- module Solutions.OAIQW_ListHadwiger.TerminalGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Knitting
open SimpleGraph PathPacking
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma model_card_le {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (M : MinorModel G H) : Fintype.card W ≤ Fintype.card V := by
  classical
  let f (w : W) : V := (M.connected w).nonempty.some.val
  have hf : ∀ w, f w ∈ M.branch w := fun w => (M.connected w).nonempty.some.property
  apply Fintype.card_le_of_injective f
  intro a b he
  by_contra hn
  exact Set.disjoint_left.mp (M.disjoint a b hn) (hf a) (he ▸ hf b)

lemma density_iso {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : density G = density H := by
  unfold density
  rw [e.card_edgeFinset_eq, e.card_eq]

theorem maximal_minor_density (G : SimpleGraph V) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)), Nonempty (MinorModel G H) ∧
      ∀ (W : Type) [Fintype W] [DecidableEq W] (J : SimpleGraph W),
        Nonempty (MinorModel G J) → density J ≤ density H := by
  classical
  let Family := Σ n : Fin (Fintype.card V + 1), SimpleGraph (Fin n.val)
  let candidates : Finset Family := Finset.univ.filter fun p => Nonempty (MinorModel G p.2)
  have hnon : candidates.Nonempty := by
    let p : Family := ⟨⟨Fintype.card V,by omega⟩,G.overFin rfl⟩
    refine ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    exact ⟨model_relabel (model_singletons G) (G.overFinIso rfl)⟩
  obtain ⟨p,hp,hmax⟩ := candidates.exists_max_image (fun p => density p.2) hnon
  refine ⟨p.1.val,p.2,(Finset.mem_filter.mp hp).2,?_⟩
  intro W _ _ J hJ
  obtain ⟨M⟩ := hJ
  let q : Family := ⟨⟨Fintype.card W,by have := model_card_le M; omega⟩,J.overFin rfl⟩
  have hq : q ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ⟨model_relabel M (J.overFinIso rfl)⟩⟩
  have hh := hmax q hq
  exact (density_iso (J.overFinIso rfl)).le.trans hh

private lemma proj_collision {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v a b c d : V}
    (huv : u≠v) (ha : edgeGood G u v a b) (hc : edgeGood G u v c d)
    (hac : proj u v huv a = proj u v huv c)
    (hbd : proj u v huv b = proj u v huv d) : a=c := by
  have hcval := congrArg Subtype.val hac
  have hdval := congrArg Subtype.val hbd
  dsimp [proj] at hcval hdval
  by_cases hav : a=v
  · by_cases hcv : c=v
    · exact hav.trans hcv.symm
    · have hcu : c=u := by simpa [hav,hcv] using hcval.symm
      have hp := ha.2.1 hav
      have hb : b≠v := by intro he; exact ha.1.ne (hav.trans he.symm)
      have hd : d≠v := by
        intro he
        exact hp.1 (by simpa [he,hb] using hdval)
      have hbe : b=d := by simpa [hb,hd] using hdval
      exact (hp.2 (hcu ▸ hbe.symm ▸ hc.1)).elim
  · by_cases hcv : c=v
    · have hau : a=u := by simpa [hav,hcv] using hcval
      have hp := hc.2.1 hcv
      have hd : d≠v := by intro he; exact hc.1.ne (hcv.trans he.symm)
      have hb : b≠v := by
        intro he
        exact hp.1 (by simpa [he,hd] using hdval.symm)
      have hbe : b=d := by simpa [hb,hd] using hdval
      exact (hp.2 (hau ▸ hbe ▸ ha.1)).elim
    · simpa [hav,hcv] using hcval

private lemma proj_adj {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v a b : V} (huv : u≠v)
    (ha : edgeGood G u v a b) :
    (contractEdge G u v).Adj (proj u v huv a) (proj u v huv b) := by
  refine ⟨?_,?_⟩
  · intro he
    have hv := congrArg Subtype.val he
    dsimp [proj] at hv
    by_cases hav : a=v <;> by_cases hbv : b=v
    · exact ha.1.ne (hav.trans hbv.symm)
    · exact (ha.2.1 hav).1 (by simpa [hav,hbv] using hv.symm)
    · exact (ha.2.2 hbv).1 (by simpa [hav,hbv] using hv)
    · exact ha.1.ne (by simpa [hav,hbv] using hv)
  · by_cases hav : a=v <;> by_cases hbv : b=v
    · exact (ha.1.ne (hav.trans hbv.symm)).elim
    · right; left
      exact ⟨by simp [proj,hav], by simpa [proj,hbv,hav] using ha.1⟩
    · right; right
      exact ⟨by simp [proj,hbv], by simpa [proj,hbv,hav] using ha.1.symm⟩
    · left
      simpa [proj,hav,hbv] using ha.1

theorem contract_edge_count (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    G.edgeFinset.card ≤ (contractEdge G u v).edgeFinset.card + 1 + (common G u v).card := by
  classical
  let D := Density.darts G Finset.univ
  let good := D.filter fun z => edgeGood G u v z.1 z.2
  let bad := D \ good
  let N := insert u (common G u v)
  have hN : N.card ≤ 1+(common G u v).card := by
    exact (Finset.card_insert_le _ _).trans (by omega)
  have hbad : bad ⊆ N.image (fun w => (v,w)) ∪ N.image (fun w => (w,v)) := by
    intro z hz
    have hzD := (Finset.mem_sdiff.mp hz).1
    have hzG : G.Adj z.1 z.2 := (Finset.mem_filter.mp hzD).2
    have hng : ¬edgeGood G u v z.1 z.2 := by
      intro hg
      exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_filter.mpr ⟨hzD,hg⟩)
    by_cases hfst : z.1=v
    · by_cases hleft : z.2≠u ∧ ¬G.Adj u z.2
      · have hright : z.2=v → z.1≠u ∧ ¬G.Adj u z.1 := by
          intro he; exact (hzG.ne (hfst.trans he.symm)).elim
        exact (hng ⟨hzG,fun _ => hleft,hright⟩).elim
      · have hmem : z.2 ∈ N := by
          dsimp [N]
          by_cases hzu : z.2=u
          · exact Finset.mem_insert.mpr (Or.inl hzu)
          · have had : G.Adj u z.2 := by tauto
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _,had,hfst ▸ hzG⟩))
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z.2,hmem,Prod.ext hfst.symm rfl⟩)
    · have hsnd : z.2=v := by
        by_contra hn
        exact hng ⟨hzG,fun he => (hfst he).elim,fun he => (hn he).elim⟩
      have hright : ¬(z.1≠u ∧ ¬G.Adj u z.1) := by
        intro hr; exact hng ⟨hzG,fun he => (hfst he).elim,fun _ => hr⟩
      have hmem : z.1 ∈ N := by
        dsimp [N]
        by_cases hzu : z.1=u
        · exact Finset.mem_insert.mpr (Or.inl hzu)
        · have had : G.Adj u z.1 := by tauto
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,had,hsnd ▸ hzG.symm⟩))
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z.1,hmem,Prod.ext rfl hsnd.symm⟩)
  have hbadcard : bad.card ≤ 2*(1+(common G u v).card) := by
    have hb := (Finset.card_le_card hbad).trans (Finset.card_union_le _ _)
    have h₁ := Finset.card_image_le (s := N) (f := fun w => (v,w))
    have h₂ := Finset.card_image_le (s := N) (f := fun w => (w,v))
    omega
  let f (z : V×V) := (proj u v huv.ne z.1,proj u v huv.ne z.2)
  have hf : Set.InjOn f (↑good : Set (V×V)) := by
    intro a ha b hb he
    have hag := (Finset.mem_filter.mp ha).2
    have hbg := (Finset.mem_filter.mp hb).2
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    refine Prod.ext (proj_collision huv.ne hag hbg hfst hsnd) ?_
    exact proj_collision huv.ne ⟨hag.1.symm,hag.2.2,hag.2.1⟩
      ⟨hbg.1.symm,hbg.2.2,hbg.2.1⟩ hsnd hfst
  have hfD : good.image f ⊆ Density.darts (contractEdge G u v) Finset.univ := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨by simp,proj_adj huv.ne (Finset.mem_filter.mp ha).2⟩
  have hgcard : good.card ≤ (Density.darts (contractEdge G u v) Finset.univ).card := by
    rw [← Finset.card_image_of_injOn hf]
    exact Finset.card_le_card hfD
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun z => edgeGood G u v z.1 z.2) D)
  change bad.card + good.card = D.card at hsum
  have hD : D.card = 2*G.edgeFinset.card := Density.darts_univ G
  rw [Density.darts_univ] at hgcard
  omega

lemma density_mul_order {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hn : 0 < Fintype.card V) :
    density G * Fintype.card V = (G.edgeFinset.card : ℚ) := by
  unfold density
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

lemma degree_le_twice_density (G : SimpleGraph V) (hn : 0 < Fintype.card V) :
    ∃ u, (G.degree u : ℚ) ≤ 2*density G := by
  classical
  by_contra! h
  have hab := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    (f := fun _ : V => 2*density G) (g := fun v => (G.degree v : ℚ))
    (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn)) (fun v _ => h v)
  have hsum : (∑ v, (G.degree v : ℚ)) = 2*(G.edgeFinset.card : ℚ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hab
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hab
  have he := density_mul_order G hn
  nlinarith

lemma common_of_max_density (G : SimpleGraph V) (hmax : ∀ (W : Type) [Fintype W]
    [DecidableEq W] (J : SimpleGraph W), Nonempty (MinorModel G J) → density J ≤ density G)
    {u v : V} (huv : G.Adj u v) : density G ≤ 1+(common G u v).card := by
  classical
  let H := contractEdge G u v
  have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨u,v,huv.ne⟩
  have hn' : Fintype.card {w : V // w ≠ v} = Fintype.card V - 1 := by
    simp
  have hh : 0 < Fintype.card {w : V // w≠v} := by omega
  have heH := density_mul_order H hh
  have heG := density_mul_order G (by omega)
  have hcount : (G.edgeFinset.card : ℚ) ≤ (H.edgeFinset.card : ℚ)+1+(common G u v).card :=
    by exact_mod_cast contract_edge_count G huv
  have hle := hmax _ H ⟨contract_model G huv⟩
  have hmul := mul_le_mul_of_nonneg_right hle (show (0 : ℚ) ≤ Fintype.card {w : V // w≠v} by positivity)
  rw [heH,hn',Nat.cast_sub (by omega : 1 ≤ Fintype.card V)] at hmul
  norm_num only [Nat.cast_one] at hmul
  nlinarith

lemma neighborhood_degree (G : SimpleGraph V) (u : V) (v : ↥(G.neighborFinset u)) :
    ((G.induce (↑(G.neighborFinset u) : Set V)).degree v) = (common G u v.val).card := by
  classical
  have he : ((G.induce (↑(G.neighborFinset u) : Set V)).neighborFinset v).image Subtype.val =
      common G u v.val := by
    ext w
    simp only [Finset.mem_image,SimpleGraph.mem_neighborFinset,SimpleGraph.induce_adj,
      common,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).mp z.property,hz⟩
    · rintro ⟨hw,hv⟩
      exact ⟨⟨w,(SimpleGraph.mem_neighborFinset _ _ _).mpr hw⟩,hv,rfl⟩
  rw [← he,Finset.card_image_of_injective _ Subtype.val_injective,
    SimpleGraph.card_neighborFinset_eq_degree]

lemma kConnected_iso {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) {k : ℕ}
    (hc : KConnectedOn G Finset.univ k) : KConnectedOn H Finset.univ k := by
  classical
  refine ⟨?_,?_⟩
  · simpa only [Finset.card_univ,← e.card_eq] using hc.1
  · intro X _ hX
    let Z := X.image e.symm
    have hZ : Z.card < k := by simpa [Z,Finset.card_image_of_injective _ e.symm.injective] using hX
    have hconn := hc.2 Z (Finset.subset_univ _) hZ
    let f : (G.induce (↑(Finset.univ \ Z) : Set V)) →g
        (H.induce (↑(Finset.univ \ X) : Set W)) :=
      { toFun := fun v => ⟨e v.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hv =>
          (Finset.mem_sdiff.mp v.property).2
            (Finset.mem_image.mpr ⟨e v.val,hv,e.symm_apply_apply v.val⟩)⟩⟩
        map_rel' := by intro u v h; exact e.map_rel_iff.mpr h }
    apply hconn.map f
    intro w
    have hw : e.symm w.val ∈ Finset.univ \ Z := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      intro hz
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_sdiff.mp w.property).2 (e.symm.injective he ▸ ha)
    exact ⟨⟨e.symm w.val,hw⟩,Subtype.ext (e.apply_symm_apply w.val)⟩

theorem small_minor_core (G : SimpleGraph V) (hlower : (16 : ℚ) ≤ density G) :
    ∃ (n k : ℕ) (H : SimpleGraph (Fin n)), Nonempty (MinorModel G H) ∧
      KConnectedOn H Finset.univ k ∧ n ≤ 32*k ∧
      density G < 8*(k+1) := by
  classical
  obtain ⟨q,J,⟨M⟩,hmax⟩ := maximal_minor_density G
  have hdiag := hmax V G ⟨model_singletons G⟩
  have hd : (16 : ℚ) ≤ density J := hlower.trans hdiag
  have hJmax : ∀ (W : Type) [Fintype W] [DecidableEq W] (L : SimpleGraph W),
      Nonempty (MinorModel J L) → density L ≤ density J := by
    intro W _ _ L hL
    obtain ⟨N⟩ := hL
    exact hmax W L ⟨compose_model M N⟩
  have hJ : 0 < Fintype.card (Fin q) := by
    by_contra hn
    have hh : Fintype.card (Fin q)=0 := by omega
    norm_num [density,hh] at hd
  let k := ⌊density J / 8⌋₊
  have hk : 2 ≤ k := Nat.le_floor (by linarith : (2 : ℚ) ≤ density J/8)
  have hklo : (8*k : ℚ) ≤ density J := by
    have hh := Nat.floor_le (by linarith : (0 : ℚ) ≤ density J/8)
    change (k : ℚ) ≤ density J/8 at hh
    linarith
  have hkhi : density J < 8*((k : ℚ)+1) := by
    have hh := Nat.lt_floor_add_one (density J/8)
    change density J/8 < (k : ℚ)+1 at hh
    linarith
  obtain ⟨u,hu⟩ := degree_le_twice_density J hJ
  let S := J.neighborFinset u
  let : Fintype (↑S : Set (Fin q)) := inferInstanceAs (Fintype ↥S)
  let L := J.induce (↑S : Set (Fin q))
  have hS : (S.card : ℚ) ≤ 2*density J := by simpa [S] using hu
  have hdeg : ∀ v : ↥S, (8*k : ℚ)-1 ≤ L.degree v := by
    intro v
    have hv := common_of_max_density J hJmax ((SimpleGraph.mem_neighborFinset _ _ _).mp v.property)
    rw [← neighborhood_degree J u v] at hv
    linarith
  have hSpos : 0 < S.card := by
    by_contra hn
    have he : S.card=0 := by omega
    have hdu : J.degree u=0 := by simpa [S] using he

    let T : Finset (Fin q) := Finset.univ.erase u
    let : Fintype (↑T : Set (Fin q)) := inferInstanceAs (Fintype ↥T)
    let P := J.induce (↑T : Set (Fin q))
    have hT : T.card+1=q := by
      have := Finset.card_erase_add_one (Finset.mem_univ u)
      simpa [T] using this
    have hed : P.edgeFinset.card = J.edgeFinset.card := by
      have hs : (↑T : Set (Fin q)) = {u}ᶜ := by ext w; simp [T]
      dsimp [P]
      have hh := SimpleGraph.card_edgeFinset_induce_compl_singleton J u
      rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet,hdu,Nat.sub_zero] at hh
      let e : P ≃g (J.induce {u}ᶜ) :=
        { toEquiv := Equiv.setCongr hs
          map_rel_iff' := by intro a b; rfl }
      exact e.card_edgeFinset_eq.trans hh
    have hql : 1 < q := by
      by_contra hn
      have hqpos : 0<q := by simpa using hJ
      have hq : q=1 := by omega
      have hc : J.edgeFinset.card=0 := by
        have hh := SimpleGraph.card_edgeFinset_le_card_choose_two (G := J)
        simp only [Fintype.card_fin,hq] at hh
        norm_num at hh
        simp [hh]
      norm_num [density,hc] at hd
    have htpos : 0 < Fintype.card ↥T := by simpa using (show 0<T.card by omega)
    have hPmax := hJmax _ P ⟨model_induce J T⟩
    have heP := density_mul_order P htpos
    have heJ := density_mul_order J hJ
    erw [hed] at heP
    have htc : (Fintype.card ↥T : ℚ)+1 = Fintype.card (Fin q) := by
      exact_mod_cast (by simpa using hT : Fintype.card ↥T+1=Fintype.card (Fin q))
    have hm := mul_le_mul_of_nonneg_right hPmax (show (0 : ℚ) ≤ Fintype.card ↥T by positivity)
    have heP' : density P * (T.card : ℚ) = (J.edgeFinset.card : ℚ) := by
      have hh : Fintype.card (↑T : Set (Fin q)) = T.card := Fintype.card_coe T
      erw [hh] at heP
      exact heP
    have hm' : density P * (T.card : ℚ) ≤ density J * (T.card : ℚ) := by
      simpa only [Fintype.card_coe] using hm
    have htc' : (T.card : ℚ)+1 = Fintype.card (Fin q) := by simpa only [Fintype.card_coe] using htc
    nlinarith [heP',hm',htc']
  have hedge : 2*k*Fintype.card ↥S < L.edgeFinset.card := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hdeg v)
    have hsum : (∑ v, (L.degree v : ℚ)) = 2*(L.edgeFinset.card : ℚ) := by
      exact_mod_cast L.sum_degrees_eq_twice_card_edges
    erw [hsum] at hs
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
    have hn : (0 : ℚ) < Fintype.card ↥S := by exact_mod_cast (by simpa using hSpos : 0<Fintype.card ↥S)
    have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
    have hh : (2*k*Fintype.card ↥S : ℚ)<L.edgeFinset.card := by nlinarith
    exact_mod_cast hh
  obtain ⟨T,hTc⟩ := Density.edge_density_connectivity L (by omega) hedge
  let : Fintype (↑T : Set ↥S) := inferInstanceAs (Fintype ↥T)
  let H := L.induce (↑T : Set ↥S)
  have hHc := induce_connected L T hTc
  let N := compose_model M (compose_model (model_induce J S) (model_induce L T))
  let e := H.overFinIso rfl
  refine ⟨Fintype.card ↥T,k,H.overFin rfl,⟨model_relabel N e⟩,?_,?_,?_⟩
  ·
    exact kConnected_iso e hHc
  · have ht : T.card ≤ S.card := by simpa using Finset.card_le_univ T
    have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
    have hh : (S.card : ℚ) ≤ 32*k := by nlinarith
    exact (by simpa using ht : Fintype.card ↥T ≤ S.card).trans (by exact_mod_cast hh)
  · exact hdiag.trans_lt hkhi

lemma kConnected_mono {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {S : Finset V} {k l : ℕ}
    (hc : KConnectedOn G S k) (hl : l≤k) : KConnectedOn G S l :=
  ⟨hl.trans_lt hc.1,fun X hX hx => hc.2 X hX (hx.trans_le hl)⟩

end LinearListHadwiger.Knitting

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.CoarseDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.CoarseDensity
open SimpleGraph Finset
open Knitting
variable {V : Type} [Fintype V] [DecidableEq V]

theorem connected_dominating (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) {N k : ℕ} (hk : 0 < k)
    (hn : Fintype.card V ≤ N)
    (hd : ∀ v, k ≤ (Density.neighbors G univ v).card) :
    ∃ D : Finset V, (G.induce (↑D : Set V)).Connected ∧
      (∀ v, ∃ w ∈ D, G.Adj v w) ∧
      D.card ≤ 3*(N/k+1)*⌈10*((N:ℝ)/(3*k))*Real.log (2*N)⌉₊ := by
  classical
  have : Nonempty V := hc.nonempty
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast ((Nat.succ_le_iff.mpr Fintype.card_pos).trans hn)
  obtain ⟨R,_,hR,hcover⟩ := ConnectivityTests.exists_neighborhood_cover G univ hN
    (by positivity : (0:ℝ)<3*k) (by simp)
    (by exact_mod_cast hn) (fun v _ => by
      simpa only [mul_div_cancel_left₀ (k:ℝ) (by norm_num : (3:ℝ)≠0)] using
        (show (k:ℝ) ≤ ((univ.filter (G.Adj v)).card:ℝ) by exact_mod_cast hd v))
  have hRn : R.Nonempty := by
    obtain ⟨w,hw,_⟩ := hcover (Classical.arbitrary V) (mem_univ _)
    exact ⟨w,hw⟩
  obtain ⟨r,hr⟩ := hRn
  have hp : ∀ v : R, ∃ p : G.Walk r v.val, p.IsPath ∧ p.length < 3*(N/k+1) := by
    intro v
    obtain ⟨p,hp,hl⟩ := short_path G hc hk hd r v.val
    exact ⟨p,hp,hl.trans_le (Nat.mul_le_mul_left 3 (Nat.add_le_add_right (Nat.div_le_div_right hn) 1))⟩
  choose p hp hl using hp
  let D : Finset V := univ.biUnion fun v : R => (p v).support.toFinset
  have hsub (v : R) : {w | w ∈ (p v).support} ⊆ (↑D : Set V) := by
    intro w hw
    exact mem_biUnion.mpr ⟨v,mem_univ _,List.mem_toFinset.mpr hw⟩
  have hrD : r ∈ D := hsub ⟨r,hr⟩ (Walk.start_mem_support _)
  refine ⟨D,?_,?_,?_⟩
  · have hre : ∀ v : (↑D : Set V), (G.induce (↑D : Set V)).Reachable ⟨r,hrD⟩ v := by
      rintro ⟨v,hv⟩
      obtain ⟨w,_,hw⟩ := mem_biUnion.mp hv
      have hh := ((p w).connected_induce_support).preconnected
        ⟨r,Walk.start_mem_support _⟩ ⟨v,List.mem_toFinset.mp hw⟩
      exact hh.map (G.induceHomOfLE (hsub w)).toHom
    exact {preconnected := fun v w => (hre v).symm.trans (hre w), nonempty := ⟨⟨r,hrD⟩⟩}
  · intro v
    obtain ⟨w,hw,hvw⟩ := hcover v (mem_univ _)
    exact ⟨w,hsub ⟨w,hw⟩ (Walk.end_mem_support _),hvw⟩
  · calc
      D.card ≤ ∑ v : R, (p v).support.toFinset.card := card_biUnion_le
      _ ≤ ∑ _v : R, 3*(N/k+1) := by
        apply sum_le_sum
        intro v _
        have he := (p v).length_support
        have hh := List.toFinset_card_le (p v).support
        have h := hl v
        omega
      _ = R.card * (3*(N/k+1)) := by simp [Nat.mul_comm]
      _ ≤ _ := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (3*(N/k+1)) hR

lemma neighbors_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Density.neighbors G univ v = G.neighborFinset v := by ext; simp

lemma degree_delete (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (v : (↑(univ \ D) : Set V)) :
    G.degree v.val ≤ (G.induce (↑(univ \ D) : Set V)).degree v + D.card := by
  classical
  have he : ((G.induce (↑(univ \ D) : Set V)).neighborFinset v).image Subtype.val =
      G.neighborFinset v.val ∩ (univ \ D) := by
    ext w
    simp only [mem_image,mem_neighborFinset,induce_adj,mem_inter,mem_sdiff,mem_univ,true_and]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨hz,(mem_sdiff.mp z.property).2⟩
    · rintro ⟨hz,hD⟩
      exact ⟨⟨w,mem_sdiff.mpr ⟨mem_univ _,hD⟩⟩,hz,rfl⟩
  have hec := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective,card_neighborFinset_eq_degree] at hec
  have hu : G.neighborFinset v.val ⊆ G.neighborFinset v.val ∩ (univ \ D) ∪ D := by
    intro w hw
    by_cases hD : w ∈ D
    · exact mem_union_right _ hD
    · exact mem_union_left _ (mem_inter.mpr ⟨hw,mem_sdiff.mpr ⟨mem_univ _,hD⟩⟩)
  have hh := (card_le_card hu).trans (card_union_le _ _)
  rw [card_neighborFinset_eq_degree, ← hec] at hh
  exact hh

lemma clique_successor (G : SimpleGraph V) (D : Finset V)
    (hc : (G.induce (↑D : Set V)).Connected)
    (hd : ∀ v, ∃ w ∈ D, G.Adj v w) {q : ℕ}
    (hm : HasCliqueMinor (G.induce (↑(univ \ D) : Set V)) q) : HasCliqueMinor G (q+1) := by
  classical
  obtain ⟨B,hB,hdis,hE⟩ := hm
  let M := model_induce G (univ \ D)
  let C (i : Fin q) := M.expand (B i)
  have hC (i : Fin q) : (G.induce (C i)).Connected := M.expand_connected (hB i)
  have hCD (i : Fin q) : Disjoint (↑D : Set V) (C i) := by
    apply Set.disjoint_left.mpr
    rintro v hv ⟨w,_,hw⟩
    have he : v=w.val := hw
    exact (mem_sdiff.mp w.property).2 (he ▸ hv)
  have hCC (i j : Fin q) (hne : i≠j) : Disjoint (C i) (C j) := M.expand_disjoint (hdis i j hne)
  have had (i : Fin q) : ∃ v ∈ (↑D : Set V), ∃ w ∈ C i, G.Adj v w := by
    obtain ⟨w⟩ := (hC i).nonempty
    obtain ⟨v,hv,hvw⟩ := hd w.val
    exact ⟨v,hv,w.val,w.property,hvw.symm⟩
  have hCE (i j : Fin q) (hne : i≠j) : ∃ v ∈ C i, ∃ w ∈ C j, G.Adj v w := by
    obtain ⟨v,hv,w,hw,hvw⟩ := hE i j hne
    exact ⟨v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,hvw⟩
  refine ⟨Fin.cases (↑D : Set V) C,?_,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hc
    · exact hC j
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b _ => ?_) j
      · exact fun h => (h rfl).elim
      · exact hCD b
    · refine Fin.cases (fun _ => ?_) (fun b h => ?_) j
      · exact (hCD a).symm
      · exact hCC a b (fun he => h (congrArg Fin.succ he))
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b _ => ?_) j
      · exact fun h => (h rfl).elim
      · exact had b
    · refine Fin.cases (fun _ => ?_) (fun b h => ?_) j
      · obtain ⟨v,hv,w,hw,hvw⟩ := had a
        exact ⟨w,hw,v,hv,hvw.symm⟩
      · exact hCE a b (fun he => h (congrArg Fin.succ he))

lemma component_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (w : (↑(G.connectedComponentMk v).supp.toFinset : Set V)) :
    (G.induce (↑(G.connectedComponentMk v).supp.toFinset : Set V)).degree w = G.degree w.val := by
  classical
  have he : ((G.induce (↑(G.connectedComponentMk v).supp.toFinset : Set V)).neighborFinset w).image
      Subtype.val = G.neighborFinset w.val := by
    ext z
    simp only [mem_image,mem_neighborFinset,induce_adj]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hz
      have hw : w.val ∈ (G.connectedComponentMk v).supp := by simpa using w.property
      have hy : z ∈ (G.connectedComponentMk v).supp.toFinset := by
        simpa using (G.connectedComponentMk v).mem_supp_of_adj_mem_supp hw hz
      exact ⟨⟨z,hy⟩,hz,rfl⟩
  have hh := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  simpa only [card_neighborFinset_eq_degree] using hh

theorem clique_of_min_degree (N k q : ℕ) (hk : 0<k)
    (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V ≤ N)
    (hd : ∀ v, k+q*domBudget N k ≤ G.degree v) : HasCliqueMinor G (q+1) := by
  classical
  induction q generalizing V with
  | zero => exact cliqueMinor_one G
  | succ q ih =>
    let v : V := Classical.arbitrary V
    let C : Finset V := (G.connectedComponentMk v).supp.toFinset
    let H := G.induce (↑C : Set V)
    have hC : H.Connected := by
      change (G.induce (↑(G.connectedComponentMk v).supp.toFinset : Set V)).Connected
      erw [Set.coe_toFinset]
      exact (G.connectedComponentMk v).connected_toSimpleGraph
    have : Nonempty (↑C : Set V) := hC.nonempty
    have hcard : Fintype.card (↑C : Set V) ≤ N := (Fintype.card_subtype_le _).trans hn
    have hdeg : ∀ w : (↑C : Set V), k+(q+1)*domBudget N k ≤ H.degree w := by
      intro w
      have he : H.degree w = G.degree w.val := component_degree G v w
      rw [he]
      exact hd w.val
    obtain ⟨D,hD,hdom,hsize⟩ := connected_dominating H hC hk hcard (fun w => by
      rw [neighbors_univ,card_neighborFinset_eq_degree]
      exact (Nat.le_add_right _ _).trans (hdeg w))
    change D.card ≤ domBudget N k at hsize
    have horder : D.card < Fintype.card (↑C : Set V) := by
      obtain ⟨w⟩ := hC.nonempty
      have hx := H.degree_lt_card_verts w
      have hh := hdeg w
      have hq : domBudget N k ≤ (q+1)*domBudget N k := by nlinarith
      omega
    have hR : (univ \ D).Nonempty := by
      apply card_pos.mp
      rw [card_sdiff_of_subset (subset_univ D),card_univ]
      omega
    have : Nonempty (↑(univ \ D) : Set (↑C : Set V)) := by
      obtain ⟨w,hw⟩ := hR; exact ⟨⟨w,hw⟩⟩
    have hdel : ∀ w : (↑(univ \ D) : Set (↑C : Set V)),
        k+q*domBudget N k ≤ (H.induce (↑(univ \ D) : Set (↑C : Set V))).degree w := by
      intro w
      have hx := degree_delete H D w
      have hh := hdeg w.val
      rw [Nat.add_mul,one_mul] at hh
      omega
    have hm := ih (↑(univ \ D) : Set (↑C : Set V))
      (H.induce (↑(univ \ D) : Set (↑C : Set V)))
      ((Fintype.card_subtype_le _).trans hcard) hdel
    exact (model_induce G C).lift_clique (clique_successor H D hD hdom hm)

lemma log64_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ Real.log (64*x) := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have h64 : (1:ℝ) ≤ Real.log 64 := by
    have he : (64:ℝ)=2^6 := by norm_num
    rw [he,Real.log_pow]
    norm_num at h2 ⊢
    linarith
  exact h64.trans (Real.log_le_log (by norm_num) (by linarith))

lemma domBudget_bound {k : ℕ} (hk : 2≤k) :
    (domBudget (32*k) (k/2) : ℝ) ≤ 100000*Real.log (64*k) := by
  have hk' : 0<k/2 := by omega
  have hratio : 32*k/(k/2) ≤96 := by
    have hh := Nat.mod_lt k (by omega : 0<2)
    have he := Nat.mod_add_div k 2
    have hm : k ≤3*(k/2) := by omega
    exact (Nat.div_le_iff_le_mul hk').mpr (by omega)
  have hr : ((32*k:ℕ):ℝ)/(3*(k/2:ℕ)) ≤32 := by
    have hm : k ≤3*(k/2) := by omega
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num
    exact_mod_cast hm
  have hlog : 1 ≤ Real.log (64*k) := log64_ge_one (by exact_mod_cast (show 1≤k by omega))
  have hval : 0 ≤ 10*(((32*k:ℕ):ℝ)/(3*(k/2:ℕ)))*Real.log (2*(32*k:ℕ)) := by
    have he : (2*(32*k:ℕ):ℝ) = 64*k := by push_cast; ring
    rw [he]; positivity
  have hceil := Nat.ceil_lt_add_one hval
  have he : (2*(32*k:ℕ):ℝ)=64*k := by push_cast; ring
  rw [he] at hceil
  have hv : 10*(((32*k:ℕ):ℝ)/(3*(k/2:ℕ)))*Real.log (64*k) ≤320*Real.log (64*k) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hb : (⌈10*(((32*k:ℕ):ℝ)/(3*(k/2:ℕ)))*Real.log (2*(32*k:ℕ))⌉₊:ℝ) ≤321*Real.log (64*k) := by
    rw [he]
    linarith
  unfold domBudget
  push_cast
  have hrat : (32*k/(k/2):ℕ) + (1:ℝ) ≤97 := by exact_mod_cast (show 32*k/(k/2)+1≤97 by omega)
  calc
    _ ≤ 291*(321*Real.log (64*k)) := by
      apply mul_le_mul
      · linarith
      · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hb
      · positivity
      · norm_num
    _ ≤ _ := by nlinarith

theorem core_size_obstruction (G : SimpleGraph V) {t : ℕ} (ht : 2≤t)
    (hex : hadwigerNumber G < t) (hd : (16:ℚ)≤density G) :
    ∃ k : ℕ, 2≤k ∧ density G <8*(k+1) ∧
      (k:ℝ)<200000*t*Real.log (64*k) := by
  classical
  obtain ⟨n,k,H,⟨M⟩,hc,hn,hden⟩ := small_minor_core G hd
  have hk : 2≤k := by
    by_contra hh
    have hh : k≤1 := by omega
    have hh' : (k:ℚ)≤1 := by exact_mod_cast hh
    linarith
  have hn' : 0<n := by have hh:=hc.1; simpa using (Nat.zero_le k).trans_lt hh
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn'
  have hdeg : ∀ v, k≤H.degree v := by
    intro v
    simpa only [neighbors_univ,card_neighborFinset_eq_degree] using min_degree H hc (mem_univ v)
  have hnot : ¬ k/2+(t-1)*domBudget (32*k) (k/2) ≤ k := by
    intro hh
    have hm := clique_of_min_degree (32*k) (k/2) (t-1) (by omega) (Fin n) H
      (by simpa using hn) (fun v => hh.trans (hdeg v))
    have hle := cliqueMinor_le_hadwigerNumber (M.lift_clique hm)
    omega
  have hnat : k <2*t*domBudget (32*k) (k/2) := by
    have hh := Nat.mod_lt k (by omega : 0<2)
    have he := Nat.mod_add_div k 2
    have htM : (t-1)*domBudget (32*k) (k/2) ≤ t*domBudget (32*k) (k/2) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_assoc]
    omega
  refine ⟨k,hk,hden,?_⟩
  have hr : (k:ℝ)<2*t*(domBudget (32*k) (k/2):ℝ) := by exact_mod_cast hnat
  have hb := domBudget_bound hk
  nlinarith

lemma logarithmic_inversion {x t : ℝ} (hx : 1≤x) (ht : 2≤t)
    (h : x<200000*t*Real.log (64*x)) : x<10400000*t*Real.log (2*t) := by
  have hx0 : 0<x := by linarith
  have ht0 : 0<t := by linarith
  have hs0 : 0<Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs1 : 1≤Real.sqrt x := by
    have hh := Real.sqrt_le_sqrt hx
    simpa using hh
  have hsq : (Real.sqrt x)^2=x := Real.sq_sqrt (by linarith)
  have hlog : Real.log (64*x) ≤8*Real.sqrt x := by
    have h1 := Real.log_le_sub_one_of_pos hs0
    rw [Real.log_sqrt (by linarith : 0≤x)] at h1
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have he : (64:ℝ)=2^6 := by norm_num
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0),he,Real.log_pow]
    norm_num at h2 ⊢
    linarith
  have hsl : Real.sqrt x<1600000*t := by
    have hh := mul_le_mul_of_nonneg_left hlog (show 0≤200000*t by positivity)
    nlinarith
  have hxx : x<(1600000*t)^2 := by nlinarith
  have hpow : 64*x≤(2:ℝ)^50*t^2 := by nlinarith [sq_nonneg t]
  have hll := Real.log_le_log (show 0<64*x by positivity) hpow
  rw [Real.log_mul (show (2:ℝ)^50≠0 by norm_num) (show t^2≠0 by positivity),Real.log_pow,Real.log_pow] at hll
  have h2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have htt : 0≤Real.log t := Real.log_nonneg (by linarith)
  have hl : Real.log (64*x) ≤52*Real.log (2*t) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt ht0)]
    norm_num at hll
    linarith
  have hh := mul_le_mul_of_nonneg_left hl (show 0≤200000*t by positivity)
  nlinarith

theorem density_bound (G : SimpleGraph V) {t : ℕ} (ht : 2≤t)
    (hex : hadwigerNumber G<t) :
    ((density G : ℚ):ℝ) ≤100000000*t*Real.log (2*t) := by
  classical
  have htr : (2:ℝ)≤t := by exact_mod_cast ht
  have hlog : 1≤Real.log (2*t) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    have h4 : (1:ℝ)≤Real.log 4 := by
      have he : (4:ℝ)=2^2 := by norm_num
      rw [he,Real.log_pow]
      norm_num at h2 ⊢
      linarith
    exact h4.trans (Real.log_le_log (by norm_num) (by linarith))
  by_cases hd : (16:ℚ)≤density G
  · obtain ⟨k,hk,hden,hx⟩ := core_size_obstruction G ht hex hd
    have hr := logarithmic_inversion (by exact_mod_cast (show 1≤k by omega)) htr hx
    have hd' : ((density G:ℚ):ℝ)<8*((k:ℝ)+1) := by exact_mod_cast hden
    have hh : (2:ℝ)≤(t:ℝ)*Real.log (2*t) := by nlinarith
    nlinarith
  · have hd' : ((density G:ℚ):ℝ)<16 := by exact_mod_cast (lt_of_not_ge hd)
    nlinarith

lemma degree_induce_finset {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (v : (↑S : Set V)) : (G.induce (↑S : Set V)).degree v = (S.filter (G.Adj v.val)).card := by
  classical
  have he : ((G.induce (↑S : Set V)).neighborFinset v).image Subtype.val = S.filter (G.Adj v.val) := by
    ext w
    simp only [mem_image,mem_neighborFinset,induce_adj,mem_filter]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,hu⟩
    · rintro ⟨hw,hvw⟩
      exact ⟨⟨w,hw⟩,hvw,rfl⟩
  have hh := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective,card_neighborFinset_eq_degree] at hh
  exact hh

end LinearListHadwiger.CoarseDensity

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Incidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Incidence
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V  :  Type} [Fintype V] [DecidableEq V]

lemma hit_pool {V : Type} [Fintype V] [DecidableEq V] {I  :  Type} [Fintype I] (A  :  Finset V) (hA  :  A.Nonempty)
    (R  :  I → V → Prop) [DecidableRel R] (s  :  ℕ) (p  :  ℝ) (hp  :  0 ≤ p)
    (hmiss  :  ∀ i ,  ((A.filter fun v  =>  ¬ R i v).card : ℝ)  ≤  p * A.card)
    (hsmall  :  (Fintype.card I : ℝ) * p ^ s < 1)  :
    ∃ B ⊆ A ,  B.card ≤ s  ∧  ∀ i ,  ∃ v ∈ B ,  R i v  :=  by
  classical
  have hpos : (0 : ℝ) < A.card := by exact_mod_cast card_pos.mpr hA

  let w'  :  A → ℝ  :=  fun _  => (A.card : ℝ)⁻¹
  have hsum'  :  ∑ v  :  A ,  w' v = 1  :=  by
    simp only [w' , sum_const , card_univ , Fintype.card_coe , nsmul_eq_mul]
    exact mul_inv_cancel₀ hpos.ne'
  have hrow (i  :  I)  :  ∑ v  :  A ,  w' v * (if  ¬ R i v.val then 1 else 0)  ≤ p  :=  by
    have he  :  (univ.filter fun v  :  A  =>  ¬ R i v.val).card  =  (A.filter fun v  =>  ¬ R i v).card  :=  by
      apply card_bij (fun v _  => v.val)
      · intro v hv; exact mem_filter.mpr ⟨v.property , (mem_filter.mp hv).2⟩
      · intro v _ u _ he; exact Subtype.ext he
      · intro v hv; exact ⟨⟨v , (mem_filter.mp hv).1⟩ , mem_filter.mpr ⟨mem_univ _ , (mem_filter.mp hv).2⟩ , rfl⟩
    calc
      _  =  ((A.filter fun v  =>  ¬ R i v).card : ℝ) / A.card  :=  by
        simp only [w' , mul_ite , mul_one , mul_zero]
        rw [←sum_filter , sum_const , he]
        simp only [nsmul_eq_mul , div_eq_mul_inv]
      _  ≤  p  :=  (div_le_iff₀ hpos).mpr (hmiss i)
  obtain ⟨f , hf⟩  :=  ConnectivityTests.finite_hitting s w' (fun _  => by dsimp [w']; positivity)
    hsum' (fun i (v : A)  => R i v.val) p hp hrow hsmall
  refine ⟨univ.image (fun i  => (f i).val) , ?_ , ?_ , ?_⟩
  · intro v hv; obtain ⟨i , _ , rfl⟩  :=  mem_image.mp hv; exact (f i).property
  · exact (card_image_le).trans (by simp)
  · intro i
    obtain ⟨j , hj⟩  :=  hf i
    exact ⟨_ , mem_image.mpr ⟨j , mem_univ _ , rfl⟩ , hj⟩

lemma star_connected {V : Type} [Fintype V] [DecidableEq V] (G  :  SimpleGraph V) (c  :  V) (B  :  Finset V)
    (hB  :  ∀ v ∈ B ,  G.Adj c v)  :  (G.induce (↑(insert c B) : Set V)).Connected  :=  by
  classical
  have hc  :  c ∈ insert c B  :=  mem_insert_self _ _
  have hr  :  ∀ v  :  (↑(insert c B) : Set V) ,
      (G.induce (↑(insert c B) : Set V)).Reachable ⟨c , hc⟩ v  :=  by
    intro v
    by_cases he  :  v.val = c
    · have he'  :  v = ⟨c , hc⟩  :=  Subtype.ext he
      subst v; exact Reachable.rfl
    · have hv  :  v.val ∈ B  :=  mem_of_mem_insert_of_ne v.property he
      exact (show (G.induce (↑(insert c B) : Set V)).Adj ⟨c , hc⟩ v from hB v.val hv).reachable
  exact {preconnected  :=  fun v w  => (hr v).symm.trans (hr w) , nonempty  :=  ⟨⟨c , hc⟩⟩}

lemma fresh_star (G  :  SimpleGraph V) [DecidableRel G.Adj]
    (Z  :  Finset V) {q s  :  ℕ} (reps  :  Fin q → V) {d  :  ℝ}
    (hn  :  0 < Fintype.card V)
    (hz  :  2 * Z.card ≤ Fintype.card V)
    (hd  :  0 ≤ d) (hdsmall  :  4 * d ≤ Fintype.card V)
    (hdeg  :  ∀ v ,  ((univ.filter fun w  =>  ¬ G.Adj v w).card : ℝ) ≤ d)
    (hsmall  :  (q : ℝ) * (4 * d/Fintype.card V) ^ s < 1)  :
    ∃ D  :  Finset V ,  Disjoint D Z  ∧  (G.induce (↑D : Set V)).Connected  ∧
      D.card ≤ s + 1  ∧  ∀ i ,  ∃ v ∈ D ,  G.Adj (reps i) v  :=  by
  classical
  have hR  :  (univ\Z).Nonempty  :=  by
    apply card_pos.mp
    rw [card_sdiff_of_subset (subset_univ Z) , card_univ]
    omega
  obtain ⟨c , hc⟩  :=  hR
  let A  :  Finset V  :=  (univ\Z).filter (G.Adj c)
  have hcard  :  (Fintype.card V : ℝ)/4  ≤  A.card  :=  by
    have hbad  :=  hdeg c
    have hcover  :  univ  ⊆  Z ∪ A ∪ univ.filter (fun w  =>  ¬ G.Adj c w)  :=  by
      intro v _
      by_cases hv  :  v ∈ Z
      · exact mem_union_left _ (mem_union_left _ hv)
      · by_cases he  :  G.Adj c v
        · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _ , hv⟩ , he⟩))
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _ , he⟩)
    have hnat  :=  (card_le_card hcover).trans (card_union_le _ _)
    have hun  :=  card_union_le Z A
    have hz'  :  2 * (Z.card : ℝ) ≤ Fintype.card V  :=  by exact_mod_cast hz
    have hnat'  :  (Fintype.card V : ℝ) ≤ (Z∪A).card + (univ.filter fun w  =>  ¬ G.Adj c w).card  :=  by
      exact_mod_cast hnat
    have hun'  :  ((Z∪A).card : ℝ) ≤ Z.card + A.card  :=  by exact_mod_cast hun
    linarith
  have hA  :  A.Nonempty  :=  by
    apply card_pos.mp
    have hn'  :  (0 : ℝ) < Fintype.card V  :=  by exact_mod_cast hn
    have hh  :  (0 : ℝ) < A.card  :=  by linarith
    exact_mod_cast hh
  have hmiss (i  :  Fin q)  :  ((A.filter fun v  =>  ¬ G.Adj (reps i) v).card : ℝ)  ≤
      (4 * d/Fintype.card V) * A.card  :=  by
    have hsub  :  A.filter (fun v  =>  ¬ G.Adj (reps i) v)  ⊆  univ.filter (fun v  =>  ¬ G.Adj (reps i) v)  :=
      filter_subset_filter _ (subset_univ _)
    have hh  :  ((A.filter fun v  =>  ¬ G.Adj (reps i) v).card : ℝ) ≤ d  :=
      by
      have hg : ((A.filter fun v => ¬ G.Adj (reps i) v).card : ℝ) ≤
          (univ.filter fun v => ¬ G.Adj (reps i) v).card := by exact_mod_cast card_le_card hsub
      exact hg.trans (hdeg (reps i))
    have hn'  :  (0 : ℝ) < Fintype.card V  :=  by exact_mod_cast hn
    have hx  :  d  ≤  (4 * d/Fintype.card V) * A.card  :=  by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hn').mpr
      nlinarith
    exact hh.trans hx
  obtain ⟨B , hBA , hBs , hhit⟩  :=  hit_pool A hA (fun i v  => G.Adj (reps i) v) s
    (4 * d/Fintype.card V) (by positivity) hmiss (by simpa using hsmall)
  refine ⟨insert c B , ?_ , star_connected G c B (fun v hv  => (mem_filter.mp (hBA hv)).2) , ?_ , ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hzv
    rcases mem_insert.mp hv with he|hv
    · subst v; exact (mem_sdiff.mp hc).2 hzv
    · exact (mem_sdiff.mp (mem_filter.mp (hBA hv)).1).2 hzv
  · exact (card_insert_le _ _).trans (by omega)
  · intro i; obtain ⟨v , hv , he⟩  :=  hhit i
    exact ⟨v , mem_insert_of_mem hv , he⟩

lemma BoundedBags.minor {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {q b : ℕ} (B : BoundedBags G q b) :
    HasCliqueMinor G q :=
  ⟨fun i => ↑(B.bag i), B.connected,
    fun i j h => Finset.disjoint_coe.mpr (B.disjoint i j h),B.adjacent⟩

lemma BoundedBags.succ {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {q b : ℕ} (B : BoundedBags G q b)
    (D : Finset V) (hc : (G.induce (↑D:Set V)).Connected)
    (hd : ∀ i, Disjoint D (B.bag i)) (hs : D.card ≤ b)
    (ha : ∀ i, ∃ v ∈ D, ∃ w ∈ B.bag i, G.Adj v w) :
    Nonempty (BoundedBags G (q+1) b) := by
  classical
  refine ⟨{bag := Fin.cases D B.bag,connected := ?_, disjoint := ?_,adjacent := ?_,small := ?_}⟩
  · intro i; exact Fin.cases hc B.connected i
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases (fun h => (h rfl).elim) (fun b _ => hd b) j
    · refine Fin.cases (fun _ => (hd a).symm) (fun b h => ?_) j
      exact B.disjoint a b (fun he => h (congrArg Fin.succ he))
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases (fun h => (h rfl).elim) (fun b _ => ha b) j
    · refine Fin.cases (fun _ => ?_) (fun b h => ?_) j
      · obtain ⟨v,hv,w,hw,he⟩ := ha a
        exact ⟨w,hw,v,hv,he.symm⟩
      · exact B.adjacent a b (fun he => h (congrArg Fin.succ he))
  · intro i; exact Fin.cases hs B.small i

theorem near_complete_minor (G : SimpleGraph V) [DecidableRel G.Adj]
    {t s : ℕ} {d : ℝ} (hn : 0<Fintype.card V)
    (hnlarge : 2*t*(s+1)≤Fintype.card V)
    (hd : 0≤d) (hdsmall : 4*d≤Fintype.card V)
    (hdeg : ∀ v, ((univ.filter fun w => ¬G.Adj v w).card:ℝ)≤d)
    (hsmall : (t:ℝ)*(4*d/Fintype.card V)^s<1) : HasCliqueMinor G t := by
  classical
  have all (q : ℕ) (hq : q≤t) : Nonempty (BoundedBags G q (s+1)) := by
    induction q with
    | zero =>
      exact ⟨{ bag := Fin.elim0
               connected := fun i => Fin.elim0 i
               disjoint := fun i => Fin.elim0 i
               adjacent := fun i => Fin.elim0 i
               small := fun i => Fin.elim0 i }⟩
    | succ q ih =>
      obtain ⟨B⟩ := ih (by omega)
      let Z := univ.biUnion B.bag
      have hZ : Z.card ≤ q*(s+1) := by
        calc
          _ ≤ ∑ i, (B.bag i).card := card_biUnion_le
          _ ≤ ∑ _i : Fin q, (s+1) := sum_le_sum (fun i _ => B.small i)
          _ = _ := by simp
      have hz : 2*Z.card ≤ Fintype.card V := by nlinarith
      have hr : ∀ i, ∃ v, v ∈ B.bag i := by
        intro i
        obtain ⟨v⟩ := (B.connected i).nonempty
        exact ⟨v.val,v.property⟩
      choose reps hreps using hr
      have hqsmall : (q:ℝ)*(4*d/Fintype.card V)^s<1 := by
        have hq' : (q:ℝ)≤t := by exact_mod_cast (show q≤t by omega)
        exact (mul_le_mul_of_nonneg_right hq' (by positivity)).trans_lt hsmall
      obtain ⟨D,hDZ,hDc,hDs,hDa⟩ := fresh_star G Z reps hn hz hd hdsmall hdeg hqsmall
      apply B.succ D hDc (fun i => Disjoint.mono_right (subset_biUnion_of_mem B.bag (mem_univ i)) hDZ) hDs
      intro i
      obtain ⟨v,hv,he⟩ := hDa i
      exact ⟨v,hv,reps i,hreps i,he.symm⟩
  obtain ⟨B⟩ := all t le_rfl
  exact B.minor

theorem missing_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    {t s : ℕ} {δ : ℝ} (ht : 1 ≤ t)
    (hex : ¬ HasCliqueMinor G t)
    (hn : 2*t*(s+1) ≤ Fintype.card V)
    (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*Fintype.card V)
    (hprob : (t:ℝ)*(8*δ)^s < 1) :
    ∃ v, δ*Fintype.card V ≤ ((univ.filter fun w => w ≠ v ∧ ¬G.Adj v w).card : ℝ) := by
  classical
  by_contra hc
  push Not at hc
  have hcard : 0<Fintype.card V := by nlinarith
  have hdeg (v : V) : ((univ.filter fun w => ¬G.Adj v w).card : ℝ) ≤ 2*δ*Fintype.card V := by
    have he : univ.filter (fun w => ¬G.Adj v w) =
        insert v (univ.filter fun w => w ≠ v ∧ ¬G.Adj v w) := by
      ext w
      simp only [mem_filter,mem_univ,true_and,mem_insert]
      by_cases hw : w=v
      · subst w; simp
      · simp [hw]
    rw [he,card_insert_of_notMem (by simp)]
    push_cast
    linarith [hc v]
  apply hex
  apply near_complete_minor G hcard hn (d := 2*δ*Fintype.card V) (by positivity)
  · have hn' : (0:ℝ) ≤ Fintype.card V := by positivity
    nlinarith
  · exact hdeg
  · have hn' : (Fintype.card V:ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
    convert hprob using 1; field_simp; ring

lemma addStar_le {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (u : V) (N : Finset V) : H ≤ addStar H u N :=
  fun _ _ h => Or.inl h

lemma addStar_edges (H : SimpleGraph V) (u : V) (N : Finset V) :
    H.edgeFinset.card + (N.filter fun w => w ≠ u ∧ ¬ H.Adj u w).card ≤
      (addStar H u N).edgeFinset.card := by
  classical
  let M := N.filter fun w => w ≠ u ∧ ¬ H.Adj u w
  let E := M.image fun w => s(u,w)
  have hinj : Set.InjOn (fun w : V => s(u,w)) (↑M : Set V) := by
    intro a ha b hb he
    rcases Sym2.eq_iff.mp he with he | he
    · exact he.2
    · exact he.2.trans he.1
  have hcard : E.card = M.card := card_image_of_injOn hinj
  have hdis : Disjoint H.edgeFinset E := by
    apply Finset.disjoint_left.mpr
    intro e he hg
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hg
    exact (mem_filter.mp hw).2.2 (by simpa using he)
  have hsub : H.edgeFinset ∪ E ⊆ (addStar H u N).edgeFinset := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact SimpleGraph.edgeFinset_mono (addStar_le H u N) he
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp he
      have hw' := mem_filter.mp hw
      exact SimpleGraph.mem_edgeFinset.mpr (Or.inr (Or.inl ⟨rfl,hw'.1,hw'.2.1.symm⟩))
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis,hcard] at hc
  exact hc

lemma missing_in_set {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (N : Finset V)
    {t s : ℕ} {δ : ℝ} (ht : 1 ≤ t) (hex : ¬ HasCliqueMinor H t)
    (hn : 2*t*(s+1) ≤ N.card) (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*N.card) (hprob : (t:ℝ)*(8*δ)^s < 1) :
    ∃ u ∈ N, δ*N.card ≤ ((N.filter fun w => w ≠ u ∧ ¬H.Adj u w).card : ℝ) := by
  classical
  let J := H.induce (↑N : Set V)
  have hn' : 2*t*(s+1) ≤ Fintype.card (↑N : Set V) := by simpa using hn
  have hex' : ¬HasCliqueMinor J t := fun hh => hex ((Knitting.model_induce H N).lift_clique hh)
  have hδn' : 1 ≤ δ*Fintype.card (↑N : Set V) := by simpa using hδn
  obtain ⟨u,hu⟩ := missing_vertex J ht hex' hn' hδ hδsmall hδn' hprob
  have he : (univ.filter fun w : (↑N : Set V) => w ≠ u ∧ ¬J.Adj u w).card =
      (N.filter fun w => w ≠ u.val ∧ ¬H.Adj u.val w).card := by
    apply card_bij (fun w _ => w.val)
    · intro w hw
      obtain ⟨hw₁,hw₂⟩ := (mem_filter.mp hw).2
      exact mem_filter.mpr ⟨w.property,(fun he => hw₁ (Subtype.ext he)),hw₂⟩
    · intro a _ b _ he; exact Subtype.ext he
    · intro w hw
      obtain ⟨hwN,hwU,hwE⟩ := mem_filter.mp hw
      refine ⟨⟨w,hwN⟩,mem_filter.mpr ⟨mem_univ _,?_,hwE⟩,rfl⟩
      exact fun hh => hwU (congrArg Subtype.val hh)
  refine ⟨u.val,u.property,?_⟩
  have hcn : Fintype.card (↑N : Set V) = N.card := by simp
  rw [hcn,he] at hu
  exact hu

lemma filter_subtype_card {V : Type} [Fintype V] [DecidableEq V] (A : Finset V) (p : V → Prop) :
    (univ.filter fun a : (↑A : Set V) => p a.val).card = (A.filter p).card := by
  classical
  apply card_bij (fun a _ => a.val)
  · intro a ha; exact mem_filter.mpr ⟨a.property,(mem_filter.mp ha).2⟩
  · intro a _ b _ he; exact Subtype.ext he
  · intro v hv
    exact ⟨⟨v,(mem_filter.mp hv).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩,rfl⟩

theorem incidence_model (P : SimpleGraph V) (A T : Finset V)
    {t s : ℕ} {δ : ℝ} (ht : 1 ≤ t) (hex : ¬ HasCliqueMinor P t)
    (hdis : Disjoint A T)
    (hlarge : ∀ v ∈ T, 2*t*(s+1) ≤ (A.filter (P.Adj v)).card)
    (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*(2*t*(s+1))) (hprob : (t:ℝ)*(8*δ)^s < 1) :
    ∃ (H : SimpleGraph (↑A : Set V)) (M : MinorModel P H),
      (∀ a, a.val ∈ M.branch a) ∧
      (∀ a, M.branch a ⊆ (↑(A∪T) : Set V)) ∧
      δ*(∑ v ∈ T, ((A.filter (P.Adj v)).card : ℝ)) ≤ H.edgeFinset.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    let H : SimpleGraph (↑A : Set V) := ⊥
    let M : MinorModel P H :=
      { branch := fun a => {a.val}
        connected := fun a => by
          have : Nonempty ({a.val} : Set V) := ⟨⟨a.val,rfl⟩⟩
          exact Connected.of_subsingleton
        disjoint := fun a b hn => Set.disjoint_singleton.mpr (fun he => hn (Subtype.ext he))
        adjacent := by intro a b h; exact h.elim }
    refine ⟨H,M,fun a => rfl,?_,?_⟩
    · intro a v hv
      have he : v=a.val := hv
      simp [he,a.property]
    · simp
  | @insert v T hvT ih =>
    have hdisT : Disjoint A T := Finset.disjoint_of_subset_right (subset_insert _ _) hdis
    have hvA : v ∉ A := fun hh => Finset.disjoint_left.mp hdis hh (mem_insert_self _ _)
    obtain ⟨H,M,hroot,hsupp,hcount⟩ := ih hdisT (fun w hw => hlarge w (mem_insert_of_mem hw))
    let N : Finset (↑A:Set V) := univ.filter fun a => P.Adj v a.val
    have hNc : N.card = (A.filter (P.Adj v)).card := filter_subtype_card A (P.Adj v)
    have hNlarge : 2*t*(s+1) ≤ N.card := by rw [hNc]; exact hlarge v (mem_insert_self _ _)
    have hNm : 1 ≤ δ*N.card := by
      have hN' : (2:ℝ)*t*(s+1) ≤ N.card := by exact_mod_cast hNlarge
      exact hδn.trans (mul_le_mul_of_nonneg_left hN' hδ)
    have hexH : ¬ HasCliqueMinor H t := fun h => hex (M.lift_clique h)
    obtain ⟨u,hu,hgain⟩ := missing_in_set H N ht hexH hNlarge hδ hδsmall hNm hprob
    have hvM : ∀ a, v ∉ M.branch a := by
      intro a ha
      rcases mem_union.mp (hsupp a ha) with hh | hh
      · exact hvA hh
      · exact hvT hh
    let M' := extendModel M Subtype.val hroot v hvM N (fun a ha => (mem_filter.mp ha).2) u hu
    have hnew := addStar_edges H u N
    refine ⟨addStar H u N,M',?_,?_,?_⟩
    · intro a
      change a.val ∈ if a=u then insert v (M.branch a) else M.branch a
      split_ifs <;> simp [hroot]
    · intro a w hw
      change w ∈ (if a=u then insert v (M.branch a) else M.branch a) at hw
      split_ifs at hw with ha
      · rcases hw with rfl | hw
        · exact mem_union_right _ (mem_insert_self _ _)
        · rcases mem_union.mp (hsupp a hw) with hw | hw
          · exact mem_union_left _ hw
          · exact mem_union_right _ (mem_insert_of_mem hw)
      · rcases mem_union.mp (hsupp a hw) with hw | hw
        · exact mem_union_left _ hw
        · exact mem_union_right _ (mem_insert_of_mem hw)
    · have hnew' : (H.edgeFinset.card:ℝ) + (N.filter fun w => w ≠ u ∧ ¬H.Adj u w).card ≤
          (addStar H u N).edgeFinset.card := by exact_mod_cast hnew
      rw [sum_insert hvT]
      rw [hNc] at hgain
      nlinarith

theorem incidence_finite (P : SimpleGraph V) (A T : Finset V)
    {t s : ℕ} {δ : ℝ} (ht : 2 ≤ t) (hex : hadwigerNumber P < t)
    (hdis : Disjoint A T)
    (hlarge : ∀ v ∈ T, 2*t*(s+1) ≤ (A.filter (P.Adj v)).card)
    (hδ : 0 ≤ δ) (hδsmall : 8*δ ≤ 1)
    (hδn : 1 ≤ δ*(2*t*(s+1))) (hprob : (t:ℝ)*(8*δ)^s < 1) :
    δ*(∑ v ∈ T, ((A.filter (P.Adj v)).card : ℝ)) ≤
      100000000*t*Real.log (2*t)*A.card := by
  classical
  by_cases hA : A = ∅
  · simp [hA]
  have hn : 0 < Fintype.card (↑A : Set V) := by simpa using card_pos.mpr (nonempty_iff_ne_empty.mpr hA)
  obtain ⟨H,M,_,_,hcount⟩ := incidence_model P A T (by omega) (fun h => (not_lt_of_ge (cliqueMinor_le_hadwigerNumber h)) hex)
    hdis hlarge hδ hδsmall hδn hprob
  have hd := CoarseDensity.density_bound H ht (M.hadwiger_le.trans_lt hex)
  have he : (H.edgeFinset.card : ℝ) = ((Knitting.density H : ℚ):ℝ)*A.card := by
    have hh := Knitting.density_mul_order H hn
    have hh' : ((Knitting.density H : ℚ):ℝ)*Fintype.card (↑A : Set V) = H.edgeFinset.card := by exact_mod_cast hh
    simpa using hh'.symm
  exact hcount.trans (he.le.trans (mul_le_mul_of_nonneg_right hd (by positivity)))

open Filter in
lemma incidence_cutoff : ∀ᶠ z : ℝ in atTop,
    2 ≤ z ∧ 8*z^(-(1/200:ℝ)) ≤ 1 ∧
    1 ≤ z^(-(1/200:ℝ))*(2*z*(1600+1)) ∧
    z*(8*z^(-(1/200:ℝ)))^1600 < 1 ∧
    100000000*Real.log (2*z) ≤ z^(1/200:ℝ) := by
  have hsmall : ∀ᶠ z : ℝ in atTop, 8*z^(-(1/200:ℝ)) ≤ 1 := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/200)).const_mul 8
    apply Tendsto.eventually_le_const (by norm_num : (8:ℝ)*0<1) hh
  have hprob : ∀ᶠ z : ℝ in atTop, (8:ℝ)^1600 * z^(-(7:ℝ)) < 1 := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7)).const_mul ((8:ℝ)^1600)
    apply Tendsto.eventually_lt_const (by simp : (8:ℝ)^1600*0<1) hh
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/200)).bound
    (show (0:ℝ)<1/200000000 by norm_num)
  have hconst : ∀ᶠ z : ℝ in atTop, 200000000*Real.log 2 ≤ z^(1/200:ℝ) :=
    (tendsto_atTop.mp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200))) _
  filter_upwards [eventually_ge_atTop (2:ℝ),hsmall,hprob,hlog,hconst] with z hz hs hp hl hc
  have hzpos : 0<z := by linarith
  have hzone : 1≤z := by linarith
  refine ⟨hz,hs,?_,?_,?_⟩
  · have hpow : z^(-(1/200:ℝ))*z = z^(199/200:ℝ) := by
      rw [←Real.rpow_add_one hzpos.ne']
      norm_num
    have hone := Real.one_le_rpow hzone (show (0:ℝ)≤199/200 by norm_num)
    calc
      _ = 3202*(z^(-(1/200:ℝ))*z) := by ring
      _ = 3202*z^(199/200:ℝ) := by rw [hpow]
      _ ≥ 1 := by linarith
  · have hpw : (z^(-(1/200:ℝ)))^1600 = z^(-(8:ℝ)) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hzpos.le]
      norm_num
    have he : z*z^(-(8:ℝ))=z^(-(7:ℝ)) := by
      calc
        _ = z^(1:ℝ)*z^(-(8:ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hzpos]; norm_num
    calc
      _ = (8:ℝ)^1600 * (z*(z^(-(1/200:ℝ)))^1600) := by rw [mul_pow]; ac_rfl
      _ = (8:ℝ)^1600 * z^(-(7:ℝ)) := by rw [hpw,he]
      _ < 1 := hp
  · have hl' : Real.log z ≤ (1:ℝ)/200000000*z^(1/200:ℝ) := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hzone),
        abs_of_nonneg (Real.rpow_nonneg hzpos.le _)] using hl
    rw [Real.log_mul (by norm_num) hzpos.ne']
    linarith

theorem incidence_bound : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (P : SimpleGraph W),
    hadwigerNumber P < t → ∀ A T : Finset W, Disjoint A T →
    (∑ v ∈ T.filter (fun v => 3202*t ≤ (A.filter (P.Adj v)).card),
      ((A.filter (P.Adj v)).card : ℝ)) ≤ (t:ℝ)^(101/100:ℝ)*A.card := by
  classical
  obtain ⟨t₀,ht₀⟩ := Filter.eventually_atTop.mp incidence_cutoff.natCast_atTop
  refine ⟨t₀,?_⟩
  intro t htt W _ _ P hex A T hdis
  obtain ⟨ht,hs,hn,hp,hl⟩ := ht₀ t htt
  have htn : 2≤t := by exact_mod_cast ht
  have htpos : (0:ℝ)<t := by linarith
  let T' := T.filter (fun v => 3202*t ≤ (A.filter (P.Adj v)).card)
  have hdis' : Disjoint A T' := Finset.disjoint_of_subset_right (filter_subset _ _) hdis
  have hlarge : ∀ v ∈ T', 2*t*(1600+1) ≤ (A.filter (P.Adj v)).card := by
    intro v hv
    have hh := (mem_filter.mp hv).2
    nlinarith
  have hδ : (0:ℝ)<(t:ℝ)^(-(1/200:ℝ)) := Real.rpow_pos_of_pos htpos _
  have hh := incidence_finite P A T' htn hex hdis' hlarge hδ.le hs hn hp
  have he : (t:ℝ)^(-(1/200:ℝ))*(t:ℝ)^(101/100:ℝ) = (t:ℝ)*(t:ℝ)^(1/200:ℝ) := by
    calc
      _ = (t:ℝ)^((-(1/200:ℝ))+(101/100:ℝ)) := (Real.rpow_add htpos _ _).symm
      _ = (t:ℝ)^((1:ℝ)+(1/200:ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add htpos,Real.rpow_one]
  apply (mul_le_mul_iff_right₀ hδ).mp
  calc
    _ ≤ 100000000*t*Real.log (2*t)*A.card := hh
    _ = (t:ℝ)*(100000000*Real.log (2*t))*A.card := by ring
    _ ≤ (t:ℝ)*(t:ℝ)^(1/200:ℝ)*A.card := by gcongr
    _ = (t:ℝ)^(-(1/200:ℝ))*((t:ℝ)^(101/100:ℝ)*A.card) := by rw [←mul_assoc,he]

end LinearListHadwiger.Incidence

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.District
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.District
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

theorem restricted_degree_loss (G : SimpleGraph V) (H S : Finset V) (hHS : H ⊆ S) :
    (∑ v ∈ H, (S.filter (G.Adj v)).card) ≤
      (S ∩ outside G H).card + loss2 G H := by
  rw [degree_sum_split,inter_eq_right.mpr hHS,←darts_sum]
  have hs : ∑ w ∈ S ∩ outside G H, ((H.filter (G.Adj w)).card-1) ≤
      ∑ w ∈ outside G H, ((H.filter (G.Adj w)).card-1) := sum_le_sum_of_subset inter_subset_right
  have hc : ∑ w ∈ S ∩ outside G H, (H.filter (G.Adj w)).card =
      (S ∩ outside G H).card + ∑ w ∈ S ∩ outside G H, ((H.filter (G.Adj w)).card-1) := by
    rw [show (S ∩ outside G H).card = (∑ _w ∈ S ∩ outside G H, (1:ℕ)) by simp,←sum_add_distrib]
    apply sum_congr rfl
    intro w hw
    have hh := outside_pos G H (mem_inter.mp hw).2
    omega
  rw [hc]
  unfold loss2
  omega

lemma outside_insert (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) :
    outside G (insert w H) = (outside G H).erase w ∪ (G.neighborFinset w \ H) := by
  ext z
  simp only [mem_outside,mem_insert,not_or,mem_union,mem_erase,mem_sdiff,SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨hzw,hzH⟩,v,(rfl|hv),h⟩
    · exact Or.inr ⟨h,hzH⟩
    · exact Or.inl ⟨hzw,⟨hzH,v,hv,h⟩⟩
  · rintro (⟨hzw,hzH,v,hv,h⟩|⟨h,hzH⟩)
    · exact ⟨⟨hzw,hzH⟩,v,Or.inr hv,h⟩
    · exact ⟨⟨h.ne.symm,hzH⟩,w,Or.inl rfl,h⟩

lemma neighborhood_increment (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) :
    (outside G (insert w H)).card + ((outside G H).filter (G.Adj w)).card +
      (H.filter (G.Adj w)).card + 1 = (outside G H).card + G.degree w := by
  have hi : (outside G H).erase w ∩ (G.neighborFinset w \ H) =
      (outside G H).filter (G.Adj w) := by
    ext z
    simp only [mem_inter,mem_erase,mem_sdiff,SimpleGraph.mem_neighborFinset,mem_filter]
    constructor
    · rintro ⟨⟨_,hz⟩,h,_⟩; exact ⟨hz,h⟩
    · rintro ⟨hz,h⟩; exact ⟨⟨h.ne.symm,hz⟩,h,((mem_outside _ _ _).mp hz).1⟩
  have hc := card_union_add_card_inter ((outside G H).erase w) (G.neighborFinset w \ H)
  rw [←outside_insert G H hw,hi,card_erase_of_mem hw] at hc
  have he : G.neighborFinset w ∩ H = H.filter (G.Adj w) := by ext z; simp [and_comm]
  have hd := card_sdiff_add_card_inter (G.neighborFinset w) H
  rw [he,SimpleGraph.card_neighborFinset_eq_degree] at hd
  have hp := card_pos.mpr ⟨w,hw⟩
  omega

lemma loss2_insert (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) :
    loss2 G (insert w H) = loss2 G H + 2*(1+((outside G H).filter (G.Adj w)).card) := by
  have hwH := ((mem_outside _ _ _).mp hw).1
  have h1 := loss2_identity G H
  have h2 := loss2_identity G (insert w H)
  have h3 := neighborhood_increment G H hw
  have h4 := Density.darts_erase G (mem_insert_self w H)
  rw [erase_insert hwH] at h4
  have hn : Density.neighbors G (insert w H) w = H.filter (G.Adj w) := by
    ext z
    simp only [Density.mem_neighbors,mem_insert,mem_filter]
    exact ⟨fun ⟨h,ha⟩ => ⟨h.resolve_left ha.ne.symm,ha⟩,fun ⟨h,ha⟩ => ⟨Or.inr h,ha⟩⟩
  rw [hn] at h4
  rw [sum_insert hwH] at h2
  omega

theorem surviving_core (G : SimpleGraph V) (A : Finset V) (d : ℚ)
    (hd : 0 ≤ d)
    (he : (d/4)*Fintype.card V + (1/8:ℚ)*(2*G.edgeFinset.card) <
      ((Density.darts G A).card:ℚ)/2) :
    ∃ S ⊆ A, S.Nonempty ∧ ∀ v ∈ S,
      d/4 ≤ ((S.filter (G.Adj v)).card:ℚ) ∧
      (G.degree v : ℚ)/8 ≤ (S.filter (G.Adj v)).card := by
  classical
  let budget : Finset V → ℚ := fun S =>
    (d/4)*S.card + (1/8:ℚ)*(∑v∈S,(G.degree v:ℚ))
  have hb : 0 ≤ budget A := by dsimp [budget]; positivity
  have hstart : budget A < ((Density.darts G A).card:ℚ)/2 := by
    have hcard : (A.card:ℚ) ≤ Fintype.card V := by exact_mod_cast card_le_univ A
    have hsum : ∑v∈A,(G.degree v:ℚ) ≤ 2*G.edgeFinset.card := by
      calc
        _ ≤ ∑v : V,(G.degree v:ℚ) := sum_le_univ_sum_of_nonneg (fun _ => by positivity)
        _ = _ := by exact_mod_cast G.sum_degrees_eq_twice_card_edges
    dsimp [budget]
    have hc := mul_le_mul_of_nonneg_left hcard (show (0:ℚ)≤d/4 by positivity)
    linarith
  have aux : ∀ n : ℕ, ∀ S ⊆ A, S.card = n → budget S < ((Density.darts G S).card:ℚ)/2 →
      ∃ T ⊆ S, T.Nonempty ∧ ∀ v ∈ T,
        d/4 ≤ ((T.filter (G.Adj v)).card:ℚ) ∧
        (G.degree v : ℚ)/8 ≤ (T.filter (G.Adj v)).card := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hSA hn hs
      by_cases hgood : ∀ v ∈ S, d/4 ≤ ((S.filter (G.Adj v)).card:ℚ) ∧
        (G.degree v : ℚ)/8 ≤ (S.filter (G.Adj v)).card
      · refine ⟨S,Subset.rfl,?_,hgood⟩
        by_contra hne
        have hz : S=∅ := not_nonempty_iff_eq_empty.mp hne
        simp [hz,budget,Density.darts] at hs
      push Not at hgood
      obtain ⟨v,hv,hvbad⟩ := hgood
      have hbdel : budget S = budget (S.erase v) + d/4 + (G.degree v:ℚ)/8 := by
        dsimp [budget]
        rw [←sum_erase_add _ _ hv]
        have hc : (S.card:ℚ) = (S.erase v).card+1 := by exact_mod_cast (card_erase_add_one hv).symm
        rw [hc]
        ring
      have hedel : ((Density.darts G S).card:ℚ)/2 =
          ((Density.darts G (S.erase v)).card:ℚ)/2 + (S.filter (G.Adj v)).card := by
        have hh := Density.darts_erase G hv
        have hh' : ((Density.darts G S).card:ℚ) = (Density.darts G (S.erase v)).card +
          2*(S.filter (G.Adj v)).card := by exact_mod_cast hh
        linarith
      have hvs : ((S.filter (G.Adj v)).card:ℚ) < d/4 + (G.degree v:ℚ)/8 := by
        by_cases hfirst : d/4 ≤ ((S.filter (G.Adj v)).card:ℚ)
        · have hh := hvbad hfirst
          linarith
        · push Not at hfirst
          have : (0:ℚ) ≤ G.degree v := by positivity
          linarith
      have hnew : budget (S.erase v) < ((Density.darts G (S.erase v)).card:ℚ)/2 := by linarith
      obtain ⟨T,hTS,hT,hgoodT⟩ := ih (S.erase v).card (by rw [←hn]; exact card_erase_lt_of_mem hv)
        (S.erase v) (erase_subset _ _ |>.trans hSA) rfl hnew
      exact ⟨T,hTS.trans (erase_subset _ _),hT,hgoodT⟩
  exact aux A.card A Subset.rfl rfl hstart

lemma outside_card_le (G : SimpleGraph V) (H : Finset V) :
    (outside G H).card ≤ ∑ v ∈ H, G.degree v := by
  have hs : outside G H ⊆ H.biUnion (fun v => G.neighborFinset v) := by
    intro w hw
    obtain ⟨_,v,hv,ha⟩ := (mem_outside _ _ _).mp hw
    exact mem_biUnion.mpr ⟨v,hv,by simpa using ha⟩
  exact (card_le_card hs).trans (card_biUnion_le.trans (by simp))

theorem cheap_neighborhood (G : SimpleGraph V) (S X : Finset V) (p : ℕ) (lam M : ℚ)
    (hp : 1 ≤ p) (hlam : 4 ≤ lam) (hM : 0 ≤ M) (hS : S.Nonempty) (hSX : Disjoint S X)
    (hsdeg : ∀ v ∈ S, 25*lam ≤ ((S.filter (G.Adj v)).card:ℚ) ∧
      (G.degree v:ℚ)/8 ≤ (S.filter (G.Adj v)).card)
    (hhigh : ∀ v ∈ S, (G.degree v:ℚ) < M)
    (hXdeg : ∀ v ∈ S, ((X.filter (G.Adj v)).card:ℚ) < lam/4)
    (hnocheap : ∀ H ⊆ S, (G.induce (↑H:Set V)).Connected → H.card=p →
      2*lam*(H.card-1:ℚ) < loss2 G H) :
    ∃ N : Finset V, Disjoint N X ∧ N.Nonempty ∧
      (N.card:ℚ) ≤ p*M ∧ (lam/32)*N.card ≤ (Density.darts G N).card := by
  classical
  let good : Finset (Finset V) := S.powerset.filter fun H => H.Nonempty ∧
    (G.induce (↑H:Set V)).Connected ∧ H.card ≤ p ∧ (loss2 G H:ℚ) ≤ 2*lam*(H.card-1:ℚ)
  obtain ⟨v,hv⟩ := hS
  have hvG : ({v}:Finset V) ∈ good := by
    simp only [good,mem_filter,mem_powerset]
    refine ⟨singleton_subset_iff.mpr hv,by simp,?_,by simpa,by simp⟩
    have he : (↑({v}:Finset V):Set V) = {v} := by ext x; simp
    rw [he]
    exact SimpleGraph.Connected.of_subsingleton
  obtain ⟨H,hHg,hmax⟩ := exists_max_image good card ⟨{v},hvG⟩
  obtain ⟨hHS,hH,hconn,hHp,hcheap⟩ : H ⊆ S ∧ H.Nonempty ∧
      (G.induce (↑H:Set V)).Connected ∧ H.card ≤ p ∧ (loss2 G H:ℚ) ≤ 2*lam*(H.card-1:ℚ) := by
    simpa only [good,mem_filter,mem_powerset,and_assoc] using hHg
  have hplt : H.card < p := lt_of_le_of_ne hHp (fun h => (not_lt_of_ge hcheap) (hnocheap H hHS hconn h))
  let N := outside G H
  have hNS : ∀ w ∈ N ∩ S, lam < 1+((N.filter (G.Adj w)).card:ℚ) := by
    intro w hw
    obtain ⟨hwN,hwS⟩ := mem_inter.mp hw
    by_contra hbad
    push Not at hbad
    have hwH := ((mem_outside _ _ _).mp hwN).1
    obtain ⟨_,u,hu,ha⟩ := (mem_outside _ _ _).mp hwN
    have hnewconn : (G.induce (↑(insert w H):Set V)).Connected := by
      rw [Finset.coe_insert]
      exact Incidence.connected_insert hconn hu ha.symm
    have hnewloss : (loss2 G (insert w H):ℚ) = loss2 G H + 2*(1+(N.filter (G.Adj w)).card) := by
      exact_mod_cast loss2_insert G H hwN
    have hnew : insert w H ∈ good := by
      simp only [good,mem_filter,mem_powerset]
      refine ⟨insert_subset hwS hHS,insert_nonempty _ _,hnewconn,?_,?_⟩
      · rw [card_insert_of_notMem hwH]; omega
      · rw [hnewloss,card_insert_of_notMem hwH]
        push_cast
        nlinarith
    have hh := hmax (insert w H) hnew
    rw [card_insert_of_notMem hwH] at hh
    omega
  let a : ℚ := ∑ v ∈ H, ((S.filter (G.Adj v)).card:ℚ)
  let b : ℚ := ∑ v ∈ H, (G.degree v:ℚ)
  have ha : 25*lam*H.card ≤ a := by
    calc
      _ = ∑ _v ∈ H, 25*lam := by simp [mul_comm]
      _ ≤ a := sum_le_sum (fun v hv => (hsdeg v (hHS hv)).1)
  have hab : b/8 ≤ a := by
    dsimp [a,b]
    rw [sum_div]
    exact sum_le_sum (fun v hv => (hsdeg v (hHS hv)).2)
  have hNb : (N.card:ℚ) ≤ b := by
    dsimp [N,b]
    exact_mod_cast outside_card_le G H
  have haloss : a ≤ (N ∩ S).card + 2*lam*(H.card-1:ℚ) := by
    have hh : a ≤ (S ∩ N).card + (loss2 G H:ℚ) := by
      dsimp [a,N]
      exact_mod_cast restricted_degree_loss G H S hHS
    rw [inter_comm] at hh
    linarith
  have hratio : (N.card:ℚ)/16 ≤ (N ∩ S).card := by nlinarith
  have hNpos : (N ∩ S).Nonempty := by
    have hpH : (0:ℚ) < H.card := by exact_mod_cast card_pos.mpr hH
    have hnpos : (0:ℚ)<(N ∩ S).card := by nlinarith
    exact card_pos.mp (by exact_mod_cast hnpos)
  have hNdeg : ∀ w ∈ N ∩ S, lam/2 ≤ (((N \ X).filter (G.Adj w)).card:ℚ) := by
    intro w hw
    have hh := hNS w hw
    have hx := hXdeg w (mem_inter.mp hw).2
    have hle : (N.filter (G.Adj w)).card ≤ ((N \ X).filter (G.Adj w)).card + (X.filter (G.Adj w)).card := by
      have hsub : N.filter (G.Adj w) ⊆ ((N \ X).filter (G.Adj w)) ∪ X.filter (G.Adj w) := by
        intro z hz
        obtain ⟨hzN,ha⟩ := mem_filter.mp hz
        by_cases hzX : z∈X
        · exact mem_union_right _ (mem_filter.mpr ⟨hzX,ha⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hzN,hzX⟩,ha⟩)
      exact (card_le_card hsub).trans (card_union_le _ _)
    have hle' : ((N.filter (G.Adj w)).card:ℚ) ≤ ((N \ X).filter (G.Adj w)).card + (X.filter (G.Adj w)).card := by exact_mod_cast hle
    linarith
  have hNSsub : N ∩ S ⊆ N \ X := by
    intro w hw
    exact mem_sdiff.mpr ⟨(mem_inter.mp hw).1,fun hh => disjoint_left.mp hSX (mem_inter.mp hw).2 hh⟩
  refine ⟨N \ X,sdiff_disjoint,hNpos.mono hNSsub,?_,?_⟩
  · have hdeg : b ≤ H.card*M := by
      calc
        _ ≤ ∑ _v ∈ H, M := sum_le_sum (fun v hv => (hhigh v (hHS hv)).le)
        _ = _ := by simp [mul_comm]
    have hpn : (H.card:ℚ)≤p := by exact_mod_cast hHp
    have hcN : ((N \ X).card:ℚ)≤N.card := by exact_mod_cast card_le_card sdiff_subset
    have hmul := mul_le_mul_of_nonneg_right hpn hM
    linarith
  · have hdarts : (lam/2)*(N ∩ S).card ≤ (Density.darts G (N \ X)).card := by
      rw [darts_sum]
      push_cast
      calc
        _ = ∑ _w ∈ N ∩ S, lam/2 := by simp [mul_comm]
        _ ≤ ∑ w ∈ N ∩ S, (((N \ X).filter (G.Adj w)).card:ℚ) := sum_le_sum hNdeg
        _ ≤ ∑ w ∈ N \ X, (((N \ X).filter (G.Adj w)).card:ℚ) :=
          sum_le_sum_of_subset_of_nonneg hNSsub (fun _ _ _ => by positivity)
    have hcard : ((N \ X).card:ℚ) ≤ N.card := by exact_mod_cast card_le_card sdiff_subset
    nlinarith

attribute [instance] CheapMinor.fintype

lemma CheapMinor.exists_minimum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (p : ℕ) (lam : ℚ) :
    ∃ M : CheapMinor G p lam, ∀ N : CheapMinor G p lam, Fintype.card M.W ≤ Fintype.card N.W := by
  have hex : ∃ n : ℕ, ∃ M : CheapMinor G p lam, Fintype.card M.W = n :=
    ⟨Fintype.card V,CheapMinor.initial G p lam,rfl⟩
  obtain ⟨M,hm⟩ := Nat.find_spec hex
  exact ⟨M,fun N => hm ▸ Nat.find_min' hex ⟨N,rfl⟩⟩

lemma CheapMinor.big_card {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) : p*M.big.card ≤ Fintype.card V := by
  classical
  have hh := expand_card G M.graph M.model M.big
  have hs : ∑w∈M.big,(M.model.branch w).toFinset.card = p*M.big.card := by
    calc
      _ = ∑ _w∈M.big,p := sum_congr rfl (fun w hw => (mem_filter.mp hw).2)
      _ = _ := by simp [mul_comm]
  rw [hs] at hh
  exact hh ▸ card_le_univ _

theorem CheapMinor.no_cheap {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) (hp : 2 ≤ p)
    (hmin : ∀ N : CheapMinor G p lam, Fintype.card M.W ≤ Fintype.card N.W)
    (H : Finset M.W) (hc : (M.graph.induce (↑H:Set M.W)).Connected)
    (hcard : H.card=p) (hsmall : ∀ w ∈ H, w ∉ M.big) :
    2*lam*(H.card-1:ℚ) < loss2 M.graph H := by
  by_contra hn
  push Not at hn
  let N := M.contract H hc hcard hsmall hn
  have hh := hmin N
  change Fintype.card M.W ≤ Fintype.card (ContractVertex H) at hh
  rw [contract_card] at hh
  have hcW := card_le_univ H
  omega

lemma kConnected_image {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {Q : SimpleGraph W} (f : W → V) (hf : Function.Injective f)
    {S : Finset W} {k : ℕ} (hc : KConnectedOn Q S k)
    (ha : ∀ u ∈ S, ∀ v ∈ S, Q.Adj u v → G.Adj (f u) (f v)) :
    KConnectedOn G (S.image f) k := by
  classical
  refine ⟨by simpa only [card_image_of_injective _ hf] using hc.1,?_⟩
  intro Z hZS hz
  let X := S.filter fun w => f w ∈ Z
  have hXS : X ⊆ S := filter_subset _ _
  have he : X.image f = Z := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hw).2
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp (hZS hv)
      exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hv⟩,rfl⟩
  have hx : X.card < k := by rw [←card_image_of_injective X hf,he]; exact hz
  let g : (Q.induce (↑(S \ X):Set W)) →g (G.induce (↑(S.image f \ Z):Set V)) :=
    { toFun := fun w => ⟨f w.val,mem_sdiff.mpr ⟨mem_image.mpr ⟨w.val,(mem_sdiff.mp w.property).1,rfl⟩,
        fun hz => (mem_sdiff.mp w.property).2 (mem_filter.mpr ⟨(mem_sdiff.mp w.property).1,hz⟩)⟩⟩
      map_rel' := fun {u v} huv => ha u.val (mem_sdiff.mp u.property).1 v.val (mem_sdiff.mp v.property).1 huv }
  apply (hc.2 X hXS hx).map g
  intro v
  obtain ⟨w,hw,heq⟩ := mem_image.mp (mem_sdiff.mp v.property).1
  have hwx : w ∈ S \ X := mem_sdiff.mpr ⟨hw,fun hx =>
    (mem_sdiff.mp v.property).2 (heq ▸ (mem_filter.mp hx).2)⟩
  exact ⟨⟨w,hwx⟩,Subtype.ext heq⟩

lemma CheapMinor.lift_small {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) {S : Finset M.W} {k : ℕ}
    (hc : KConnectedOn M.graph S k) (hsmall : Disjoint S M.big) :
    ∃ T : Finset V, KConnectedOn G T k ∧ T.card = S.card := by
  classical
  let f : M.W → V := fun w => (M.model.connected w).nonempty.some.val
  have hfmem : ∀ w, f w ∈ M.model.branch w := fun w => (M.model.connected w).nonempty.some.property
  have hfi : Function.Injective f := by
    intro a b he
    by_contra hn
    exact Set.disjoint_left.mp (M.model.disjoint a b hn) (hfmem a) (he ▸ hfmem b)
  refine ⟨S.image f,kConnected_image f hfi hc ?_,card_image_of_injective _ hfi⟩
  intro u hu v hv huv
  obtain ⟨a,ha,b,hb,hab⟩ := M.model.adjacent huv
  have he (w : M.W) (hw : w ∈ S) {x : V} (hx : x ∈ M.model.branch w) : x=f w := by
    have hcard := M.small (disjoint_left.mp hsmall hw)
    have hm1 : x ∈ (M.model.branch w).toFinset := Set.mem_toFinset.mpr hx
    have hm2 : f w ∈ (M.model.branch w).toFinset := Set.mem_toFinset.mpr (hfmem w)
    exact (card_le_one.mp hcard.le) x hm1 (f w) hm2
  simpa only [he u hu ha,he v hv hb] using hab

lemma bad_size (R : SimpleGraph V) (X : Finset V) (n q t : ℕ) (d : ℚ)
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hd : 1280800*t < d)
    (hx : q^5*X.card ≤ n) (hupper : (R.edgeFinset.card:ℚ) ≤ d*n)
    (hinc : ∀ A T : Finset V, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    (q:ℚ)^3*(badSet R X d q).card ≤ 7*n := by
  classical
  have hqr : (1:ℚ) ≤ q := by exact_mod_cast hq
  have htr : (1:ℚ) ≤ t := by exact_mod_cast ht
  have hdpos : 0<d := by nlinarith
  let Y := Xᶜ.filter fun v => d/400 ≤ ((X.filter (R.Adj v)).card:ℚ)
  let Z := univ.filter fun v => d*q^4 ≤ (R.degree v:ℚ)
  let B := X ∪ Y ∪ Z
  have hyX : Disjoint X Y := disjoint_of_subset_right (filter_subset _ _) disjoint_compl_right
  have hyinc := hinc X Y hyX
  have heY : Y.filter (fun v => 3202*t ≤ (X.filter (R.Adj v)).card) = Y := by
    apply filter_eq_self.mpr
    intro v hv
    have hh := (mem_filter.mp hv).2
    have : (3202*t:ℚ) ≤ (X.filter (R.Adj v)).card := by linarith
    exact_mod_cast this
  rw [heY] at hyinc
  have hylo : (t:ℚ)*Y.card ≤ ∑v∈Y,((X.filter (R.Adj v)).card:ℚ) := by
    calc
      _ = ∑_v∈Y,(t:ℚ) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => by have hh := (mem_filter.mp hv).2; linarith)
  have hy : (Y.card:ℚ) ≤ 4*q^2*X.card := by nlinarith
  have hzlo : d*q^4*Z.card ≤ ∑v∈Z,(R.degree v:ℚ) := by
    calc
      _ = ∑_v∈Z,d*q^4 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => (mem_filter.mp hv).2)
  have hzup : (∑v∈Z,(R.degree v:ℚ)) ≤ 2*R.edgeFinset.card := by
    calc
      _ ≤ ∑v : V,(R.degree v:ℚ) := sum_le_univ_sum_of_nonneg (fun _ => by positivity)
      _ = _ := by exact_mod_cast R.sum_degrees_eq_twice_card_edges
  have hz : (q:ℚ)^4*Z.card ≤ 2*n := by nlinarith
  have hxn : (q:ℚ)^5*X.card ≤ n := by exact_mod_cast hx
  have hbn : (B.card:ℚ) ≤ X.card+Y.card+Z.card := by
    exact_mod_cast (card_union_le (X ∪ Y) Z).trans (Nat.add_le_add_right (card_union_le X Y) _)
  have hqpow : (q:ℚ)^3 ≤ (q:ℚ)^4 := pow_le_pow_right₀ hqr (by omega)
  have hqpow2 : (q:ℚ)^3 ≤ (q:ℚ)^5 := by
    exact pow_le_pow_right₀ hqr (by omega)
  have hB : (q:ℚ)^3*B.card ≤ 7*n := by
    have h1 := mul_le_mul_of_nonneg_left hbn (show 0≤(q:ℚ)^3 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hy (show 0≤(q:ℚ)^3 by positivity)
    have h3 := mul_le_mul_of_nonneg_right hqpow (show 0≤(Z.card:ℚ) by positivity)
    have h4 := mul_le_mul_of_nonneg_right hqpow2 (show 0≤(X.card:ℚ) by positivity)
    nlinarith
  exact hB

lemma bad_degree_sum (R : SimpleGraph V) (B : Finset V) (n q t : ℕ)
    (hq : 1 ≤ q) (hn : Fintype.card V ≤ n)
    (hB : (q:ℚ)^3*B.card ≤ 7*n)
    (hcoarse : ∀ A : Finset V, ((Density.darts R A).card:ℚ) ≤ 2*t*q*A.card)
    (hinc : ∀ A T : Finset V, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    (∑v∈B,(R.degree v:ℚ)) ≤ 3244*t*n := by
  classical
  have hqr : (1:ℚ)≤q := by exact_mod_cast hq
  have hcross := hinc B Bᶜ disjoint_compl_right
  let U := Bᶜ.filter fun v => 3202*t ≤ (B.filter (R.Adj v)).card
  have hcrossall : (∑v∈Bᶜ,((B.filter (R.Adj v)).card:ℚ)) ≤ 3202*t*n+4*t*q^2*B.card := by
    rw [←sum_filter_add_sum_filter_not Bᶜ (fun v => 3202*t ≤ (B.filter (R.Adj v)).card)]
    have hlo : (∑v∈Bᶜ.filter (fun v => ¬3202*t ≤ (B.filter (R.Adj v)).card),
        ((B.filter (R.Adj v)).card:ℚ)) ≤ 3202*t*n := by
      calc
        _ ≤ ∑_v∈Bᶜ.filter (fun v => ¬3202*t ≤ (B.filter (R.Adj v)).card),(3202*t:ℚ) :=
          sum_le_sum (fun v hv => by exact_mod_cast (le_of_lt (not_le.mp (mem_filter.mp hv).2)))
        _ = (3202*t:ℚ)*(Bᶜ.filter (fun v => ¬3202*t ≤ (B.filter (R.Adj v)).card)).card := by simp [mul_comm]
        _ ≤ 3202*t*n := by gcongr; exact_mod_cast (card_le_univ _).trans hn
    linarith
  have hds : (∑v∈B,(R.degree v:ℚ)) = (Density.darts R B).card +
      ∑v∈Bᶜ,((B.filter (R.Adj v)).card:ℚ) := by
    have he : ∑v∈B,R.degree v = (Density.darts R B).card + ∑v∈Bᶜ,(B.filter (R.Adj v)).card := by
      simp only [degree_partition R B,sum_add_distrib,darts_sum,degree_sum_comm]
    exact_mod_cast he
  have hq1 : (q:ℚ) ≤ (q:ℚ)^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hqr (show 1≤3 by omega))
  have hq2 : (q:ℚ)^2 ≤ (q:ℚ)^3 := pow_le_pow_right₀ hqr (by omega)
  have hdegB : (∑v∈B,(R.degree v:ℚ)) ≤ 3244*t*n := by
    have hc := hcoarse B
    have h1 := mul_le_mul_of_nonneg_right hq1 (show 0≤(B.card:ℚ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hq2 (show 0≤(B.card:ℚ) by positivity)
    have h3 : (q:ℚ)*B.card ≤ 7*n := h1.trans hB
    have h4 : (q:ℚ)^2*B.card ≤ 7*n := h2.trans hB
    have h5 := mul_le_mul_of_nonneg_left h3 (show 0≤2*(t:ℚ) by positivity)
    have h6 := mul_le_mul_of_nonneg_left h4 (show 0≤4*(t:ℚ) by positivity)
    nlinarith
  exact hdegB

theorem bad_set_core (R : SimpleGraph V) (X : Finset V) (n q t : ℕ) (d : ℚ)
    (hq : 1 ≤ q) (ht : 1 ≤ t) (hd : 1280800*t < d)
    (hnposNat : 0 < n) (hn : Fintype.card V ≤ n) (hx : q^5*X.card ≤ n)
    (hupper : (R.edgeFinset.card:ℚ) ≤ d*n)
    (hlower : (99/100:ℚ)*d*n ≤ R.edgeFinset.card)
    (hcoarse : ∀ A : Finset V, ((Density.darts R A).card:ℚ) ≤ 2*t*q*A.card)
    (hinc : ∀ A T : Finset V, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    ∃ S : Finset V, S.Nonempty ∧ Disjoint S X ∧
      (∀ v ∈ S, d/4 ≤ ((S.filter (R.Adj v)).card:ℚ) ∧
        (R.degree v:ℚ)/8 ≤ (S.filter (R.Adj v)).card) ∧
      (∀ v ∈ S, (R.degree v:ℚ) < d*q^4) ∧
      (∀ v ∈ S, ((X.filter (R.Adj v)).card:ℚ) < d/400) := by
  classical
  have hqr : (1:ℚ)≤q := by exact_mod_cast hq
  have htr : (1:ℚ)≤t := by exact_mod_cast ht
  have hdpos : 0<d := by nlinarith
  let B := badSet R X d q
  have hB := bad_size R X n q t d hq ht hd hx hupper hinc
  have hdegB := bad_degree_sum R B n q t hq hn hB hcoarse hinc
  have hnpos : (0:ℚ)<n := by exact_mod_cast hnposNat
  have hremain : (d/4)*Fintype.card V+(1/8:ℚ)*(2*R.edgeFinset.card) <
      ((Density.darts R Bᶜ).card:ℚ)/2 := by
    have hpart : 2*(R.edgeFinset.card:ℚ)+(Density.darts R B).card =
        (Density.darts R Bᶜ).card+2*∑v∈B,(R.degree v:ℚ) := by exact_mod_cast darts_partition R B
    have hnn : (Fintype.card V:ℚ) ≤ n := by exact_mod_cast hn
    have hdnt := mul_lt_mul_of_pos_right hd hnpos
    have hdnn := mul_le_mul_of_nonneg_left hnn hdpos.le
    have hdn := mul_le_mul_of_nonneg_left hupper (by norm_num : (0:ℚ)≤1/4)
    have hnn2 := mul_le_mul_of_nonneg_left hdnn (by norm_num : (0:ℚ)≤1/4)
    have hdarts : (0:ℚ)≤(Density.darts R B).card := by positivity
    linarith
  obtain ⟨S,hS,hSn,hSd⟩ := surviving_core R Bᶜ d hdpos.le hremain
  have hnot (v : V) (hv : v∈S) : v∉B := mem_compl.mp (hS hv)
  refine ⟨S,hSn,?_,hSd,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hx
    exact hnot v hv (mem_union_left _ (mem_union_left _ hx))
  · intro v hv
    by_contra hh
    exact hnot v hv (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,le_of_not_gt hh⟩))
  · intro v hv
    by_contra hh
    have hvX : v∉X := fun hx => hnot v hv (mem_union_left _ (mem_union_left _ hx))
    exact hnot v hv (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_compl.mpr hvX,le_of_not_gt hh⟩)))

theorem district_finite (G : SimpleGraph V) [Nonempty V] (q t k : ℕ)
    (hq : 2 ≤ q) (ht : 1 ≤ t) (hk : 1 ≤ k)
    (hd : max (1280800*t:ℚ) (12800*k) < Knitting.density G)
    (hcoarse : ∀ (W : Type) [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      MinorModel G R → ∀ A : Finset W, ((Density.darts R A).card:ℚ) ≤ 2*t*q*A.card)
    (hinc : ∀ (W : Type) [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      MinorModel G R → ∀ A T : Finset W, Disjoint A T →
      (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℚ)) ≤ 4*t*q^2*A.card) :
    ∃ S : Finset V, KConnectedOn G S k ∧
      (S.card:ℚ) ≤ Knitting.density G*q^9 := by
  classical
  let d := Knitting.density G
  let lam := d/100
  obtain ⟨M,hmin⟩ := CheapMinor.exists_minimum G (q^5) lam
  have hp : 2≤q^5 := by
    have hh : q ≤ q^5 := by simpa only [pow_one] using (Nat.pow_le_pow_right (by omega : 0<q) (show 1≤5 by omega))
    omega
  have hd1 : (1280800*t:ℚ)<d := (le_max_left _ _).trans_lt hd
  have hd2 : (12800*k:ℚ)<d := (le_max_right _ _).trans_lt hd
  have htr : (1:ℚ)≤t := by exact_mod_cast ht
  have hkr : (1:ℚ)≤k := by exact_mod_cast hk
  have hdpos : 0<d := by nlinarith
  have heq : d*Fintype.card V = G.edgeFinset.card := Knitting.density_mul_order G Fintype.card_pos
  have hup : (M.graph.edgeFinset.card:ℚ) ≤ d*Fintype.card V := by
    rw [heq]; exact_mod_cast M.upper
  have hlo : (99/100:ℚ)*d*Fintype.card V ≤ M.graph.edgeFinset.card := by
    have hh := M.budget
    have ho : (0:ℚ)≤Fintype.card M.W := by positivity
    have hh' : lam*Fintype.card M.W ≥ 0 := by dsimp [lam]; positivity
    dsimp [lam] at hh hh'
    rw [←heq] at hh
    linarith
  obtain ⟨S,hSn,hSX,hSd,hhigh,hXdeg⟩ := bad_set_core M.graph M.big
    (Fintype.card V) q t d (by omega) ht hd1 Fintype.card_pos
    (Knitting.model_card_le M.model) M.big_card hup hlo
    (hcoarse _ M.graph M.model) (hinc _ M.graph M.model)
  have hnocheap : ∀ H ⊆ S, (M.graph.induce (↑H:Set M.W)).Connected → H.card=q^5 →
      2*lam*(H.card-1:ℚ) < loss2 M.graph H := by
    intro H hHS hc hcard
    exact M.no_cheap hp hmin H hc hcard (fun w hw => disjoint_left.mp hSX (hHS hw))
  obtain ⟨N,hNX,hNn,hNcard,hNden⟩ := cheap_neighborhood M.graph S M.big (q^5) lam (d*q^4)
    (by omega) (by dsimp [lam]; linarith) (by positivity) hSn hSX
    (fun v hv => by obtain ⟨ha,hb⟩ := hSd v hv; exact ⟨by dsimp [lam]; linarith,hb⟩)
    hhigh (fun v hv => by have hh := hXdeg v hv; dsimp [lam]; linarith) hnocheap
  have hNpos : (0:ℚ)<N.card := by exact_mod_cast card_pos.mpr hNn
  have hNedges : 4*k*N.card < (Density.darts M.graph N).card := by
    have hh := mul_lt_mul_of_pos_right hd2 hNpos
    have hden : (d/3200)*N.card ≤ (Density.darts M.graph N).card := by
      dsimp [lam] at hNden; linarith
    have : (4*(k:ℚ)*N.card) < (Density.darts M.graph N).card := by linarith
    exact_mod_cast this
  obtain ⟨T,hTN,hTc⟩ := Density.connectivity_of_density M.graph N hk hNedges
  obtain ⟨U,hUc,hUcard⟩ := M.lift_small hTc (disjoint_of_subset_left hTN hNX)
  refine ⟨U,hUc,?_⟩
  calc
    (U.card:ℚ) = T.card := by exact_mod_cast hUcard
    _ ≤ N.card := by exact_mod_cast card_le_card hTN
    _ ≤ (q^5:ℕ)*(d*q^4) := hNcard
    _ = d*q^9 := by push_cast; ring

lemma darts_induce (G : SimpleGraph V) (A : Finset V) :
    (Density.darts G A).card = 2*(G.induce (↑A:Set V)).edgeFinset.card := by
  classical
  rw [darts_sum,←SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp only [CoarseDensity.degree_induce_finset]
  exact (Finset.sum_coe_sort A (fun v => (A.filter (G.Adj v)).card)).symm

lemma coarse_darts (G : SimpleGraph V) {q t : ℕ} (ht : 2≤t)
    (hex : hadwigerNumber G<t) (hl : 100000000*Real.log (2*t) ≤ (q:ℝ))
    (A : Finset V) : ((Density.darts G A).card:ℚ) ≤ 2*t*q*A.card := by
  classical
  let H := G.induce (↑A:Set V)
  have hi := (Knitting.model_induce G A).hadwiger_le.trans_lt hex
  have hd := CoarseDensity.density_bound H ht hi
  have hdq : ((Knitting.density H:ℚ):ℝ) ≤ (t:ℝ)*q := by
    calc
      _ ≤ 100000000*t*Real.log (2*t) := hd
      _ = (t:ℝ)*(100000000*Real.log (2*t)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  by_cases hA : A.Nonempty
  · have hn : 0<Fintype.card (↑A:Set V) := by simpa using card_pos.mpr hA
    have he := Knitting.density_mul_order H hn
    have he' : ((Knitting.density H:ℚ):ℝ)*A.card = H.edgeFinset.card := by
      have hr := congrArg (fun x : ℚ => (x:ℝ)) he
      convert hr using 1 <;> simp
      congr 1
    have hh := mul_le_mul_of_nonneg_right hdq (show (0:ℝ)≤A.card by positivity)
    rw [he'] at hh
    rw [darts_induce]
    have : (2*(H.edgeFinset.card:ℝ)) ≤ 2*t*q*A.card := by linarith
    exact_mod_cast this
  · have he : A=∅ := not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [Density.darts]

open Filter Real Asymptotics in
lemma district_cutoff : ∀ᶠ z : ℝ in atTop,
    2 ≤ z ∧ 2 ≤ z^(1/200:ℝ) ∧ 1024 ≤ z^(1/100:ℝ) ∧
      100000000*Real.log (2*z) ≤ z^(1/200:ℝ) := by
  have h1 := (tendsto_atTop.mp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200))) 2
  have h2 := (tendsto_atTop.mp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100))) 1024
  filter_upwards [Incidence.incidence_cutoff,h1,h2] with z hz hz1 hz2
  exact ⟨hz.1,hz1,hz2,hz.2.2.2.2⟩

lemma district_order {t q : ℕ} (ht : (2:ℝ)≤t)
    (hq : (q:ℝ)≤2*(t:ℝ)^(1/200:ℝ))
    (hpow : (1024:ℝ)≤(t:ℝ)^(1/100:ℝ)) :
    (t:ℝ)*q^10 ≤ (t:ℝ)^(53/50:ℝ) := by
  have htpos : (0:ℝ)<t := by linarith
  have he : (t:ℝ)*((t:ℝ)^(1/200:ℝ))^10 = (t:ℝ)^(21/20:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul htpos.le]
    calc
      _ = (t:ℝ)^(1:ℝ)*(t:ℝ)^((1/200:ℝ)*(10:ℝ)) := by norm_num
      _ = _ := by rw [←Real.rpow_add htpos]; norm_num
  have hp := pow_le_pow_left₀ (show (0:ℝ)≤q by positivity) hq 10
  calc
    _ ≤ (t:ℝ)*(2*(t:ℝ)^(1/200:ℝ))^10 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 1024*((t:ℝ)*((t:ℝ)^(1/200:ℝ))^10) := by ring
    _ = 1024*(t:ℝ)^(21/20:ℝ) := by rw [he]
    _ ≤ (t:ℝ)^(1/100:ℝ)*(t:ℝ)^(21/20:ℝ) := by gcongr
    _ = _ := by rw [←Real.rpow_add htpos]; norm_num

theorem district : Statement := by
  classical
  intro K hK
  let D := max 1280800 (12800*K)+1
  refine ⟨D,by dsimp [D]; norm_num,?_⟩
  obtain ⟨t₁,ht₁⟩ := Incidence.incidence_bound
  obtain ⟨t₂,ht₂⟩ := Filter.eventually_atTop.mp district_cutoff.natCast_atTop
  refine ⟨max t₁ t₂,?_⟩
  intro t htt W _ _ _ P hex hedges
  obtain ⟨htr,hpow2,hpow1024,hlog⟩ := ht₂ t (le_trans (le_max_right _ _) htt)
  have ht : 2≤t := by exact_mod_cast htr
  have htpos : (0:ℝ)<t := by linarith
  let q := Nat.ceil ((t:ℝ)^(1/200:ℝ))
  have hqlo : (t:ℝ)^(1/200:ℝ) ≤ q := Nat.le_ceil _
  have hq : 2≤q := by exact_mod_cast hpow2.trans hqlo
  have hqhi : (q:ℝ)≤2*(t:ℝ)^(1/200:ℝ) := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg htpos.le (1/200:ℝ))
    change (q:ℝ)<(t:ℝ)^(1/200:ℝ)+1 at hh
    linarith
  have hlogq : 100000000*Real.log (2*t) ≤ (q:ℝ) := hlog.trans hqlo
  have hdense : (D*t:ℚ) ≤ Knitting.density P := by
    have hn : (0:ℚ)<Fintype.card W := by exact_mod_cast Fintype.card_pos
    apply (le_div_iff₀ hn).mpr
    exact_mod_cast hedges
  have hD1 : (1280800:ℚ)<D := by exact_mod_cast (show 1280800<D by dsimp [D]; omega)
  have hD2 : (12800*K:ℚ)<D := by exact_mod_cast (show 12800*K<D by dsimp [D]; omega)
  have htq : (0:ℚ)<t := by exact_mod_cast (show 0<t by omega)
  have hden : max (1280800*t:ℚ) (12800*(K*t)) < Knitting.density P := by
    apply max_lt
    · exact (mul_lt_mul_of_pos_right hD1 htq).trans_le hdense
    · have hh := mul_lt_mul_of_pos_right hD2 htq
      nlinarith
  have hpowinc : (t:ℝ)^(101/100:ℝ) ≤ 4*t*q^2 := by
    have he : (t:ℝ)^(101/100:ℝ) = (t:ℝ)*((t:ℝ)^(1/200:ℝ))^2 := by
      rw [←Real.rpow_natCast,←Real.rpow_mul htpos.le]
      calc
        _ = (t:ℝ)^((1:ℝ)+(1/200:ℝ)*2) := by norm_num
        _ = _ := by rw [Real.rpow_add htpos,Real.rpow_one]; norm_num
    rw [he]
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg htpos.le _) hqlo 2
    have hx := mul_le_mul_of_nonneg_left hh htpos.le
    nlinarith [sq_nonneg (q:ℝ)]
  obtain ⟨S,hSc,hScard⟩ := district_finite P q t (K*t) hq (by omega) (by nlinarith) (by simpa only [Nat.cast_mul] using hden)
    (fun U _ _ R M A => coarse_darts R ht (M.hadwiger_le.trans_lt hex) hlogq A)
    (by
      intro U _ _ R M A T hdis
      have hh := ht₁ t (le_trans (le_max_left _ _) htt) U R
        (M.hadwiger_le.trans_lt hex) A T hdis
      have hp := mul_le_mul_of_nonneg_right hpowinc (show (0:ℝ)≤A.card by positivity)
      have hbound : (∑v∈T.filter (fun v => 3202*t ≤ (A.filter (R.Adj v)).card),
        ((A.filter (R.Adj v)).card:ℝ)) ≤ 4*t*q^2*A.card := hh.trans hp
      exact_mod_cast hbound)
  refine ⟨S,hSc,?_⟩
  have hd := CoarseDensity.density_bound P ht hex
  have hdq : ((Knitting.density P:ℚ):ℝ) ≤ (t:ℝ)*q := by
    have hh := mul_le_mul_of_nonneg_left hlogq htpos.le
    nlinarith
  have hcard : (S.card:ℝ) ≤ ((Knitting.density P:ℚ):ℝ)*q^9 := by exact_mod_cast hScard
  have hm := mul_le_mul_of_nonneg_right hdq (show (0:ℝ)≤(q:ℝ)^9 by positivity)
  calc
    _ ≤ ((Knitting.density P:ℚ):ℝ)*q^9 := hcard
    _ ≤ (t:ℝ)*q*q^9 := hm
    _ = (t:ℝ)*q^10 := by ring
    _ ≤ _ := district_order htr hqhi hpow1024

end
end LinearListHadwiger.District

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.DistrictAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.District
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma list_dense_core (G : SimpleGraph V) {d : ℕ}
    (hl : d+1 < listChromaticNumber G) :
    ∃ S : Finset V, S.Nonempty ∧
      (d+1)*S.card ≤ 2*(G.induce (↑S:Set V)).edgeFinset.card := by
  classical
  have hnot : ¬DegenerateOn G univ d := by
    intro h
    exact (not_le_of_gt hl) (listChromaticNumber_le_of_degenerate G h)
  have hx : ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, d < (S.filter (G.Adj v)).card := by
    by_contra hn
    apply hnot
    intro S _ hS
    by_contra hh
    apply hn
    refine ⟨S,hS,?_⟩
    intro v hv
    by_contra hn
    exact hh ⟨v,hv,by omega⟩
  obtain ⟨S,hS,hdeg⟩ := hx
  refine ⟨S,hS,?_⟩
  rw [←darts_induce,darts_sum]
  calc
    (d+1)*S.card = ∑ v ∈ S, (d+1) := by simp [mul_comm]
    _ ≤ _ := sum_le_sum fun v hv => by have := hdeg v hv; omega

theorem list_district : ∀ K : ℕ, 0 < K → ∃ D : ℕ,
    max (400*3202) (12800*K) < D ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (P : SimpleGraph W),
    hadwigerNumber P < t → 2*D*t+2 < listChromaticNumber P →
    ∃ S : Finset W, KConnectedOn P S (K*t) ∧
      (S.card : ℝ) ≤ (t:ℝ)^(53/50:ℝ) := by
  intro K hK
  obtain ⟨D,hD,t₀,hd⟩ := district K hK
  refine ⟨D,hD,t₀,?_⟩
  intro t ht W _ _ P hex hl
  obtain ⟨A,hA,hden⟩ := list_dense_core P (d := 2*D*t+1) (by omega)
  let : Nonempty (↑A:Set W) := ⟨⟨hA.choose,hA.choose_spec⟩⟩
  have hh := (Knitting.model_induce P A).hadwiger_le.trans_lt hex
  have he : D*t*Fintype.card (↑A:Set W) ≤ (P.induce (↑A:Set W)).edgeFinset.card := by
    have hAc : Fintype.card (↑A:Set W) = A.card := by simp
    rw [hAc]
    nlinarith
  obtain ⟨S,hSc,hcard⟩ := hd t ht (↑A:Set W) (P.induce (↑A:Set W)) hh he
  refine ⟨S.image Subtype.val,kConnected_image Subtype.val Subtype.val_injective hSc
    (fun _ _ _ _ h => h),?_⟩
  simpa only [card_image_of_injective _ Subtype.val_injective] using hcard

end
end LinearListHadwiger.District

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.SamplingConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

theorem neighbors_in_collection {V J : Type} [DecidableEq V] [Fintype J]
    (G : SimpleGraph V) (B : J → Finset V) (v : V) (b d : ℕ)
    (hpath : ∀ j, ((B j).filter (G.Adj v)).card ≤ d)
    (hcount : (univ.filter (fun j => ∃ w ∈ B j, G.Adj v w)).card ≤ b) :
    ((univ.biUnion B).filter (G.Adj v)).card ≤ d*b := by
  classical
  let Jv := univ.filter (fun j => ∃ w ∈ B j, G.Adj v w)
  have he : (univ.biUnion B).filter (G.Adj v) =
      Jv.biUnion (fun j => (B j).filter (G.Adj v)) := by
    ext w
    simp only [mem_filter,mem_biUnion,mem_univ,true_and,Jv]
    constructor
    · rintro ⟨⟨j,hj⟩,hadj⟩
      exact ⟨j,⟨w,hj,hadj⟩,hj,hadj⟩
    · rintro ⟨j,_,hj,hadj⟩
      exact ⟨⟨j,hj⟩,hadj⟩
  rw [he]
  calc
    _ ≤ ∑ j ∈ Jv, ((B j).filter (G.Adj v)).card := card_biUnion_le
    _ ≤ ∑ _j ∈ Jv, d := sum_le_sum fun j _ => hpath j
    _ = d*Jv.card := by simp [mul_comm]
    _ ≤ d*b := Nat.mul_le_mul_left d hcount

theorem minimum_system_degenerate {V I J : Type} [DecidableEq V] [Fintype I]
    [DecidableEq I] (G : SimpleGraph V) (A : Finset V)
    (s : I → ↥(↑A : Set V)) (B : J → Set ↥(↑A : Set V))
    (D : BagRouting (G.induce (↑A : Set V)) s B) (hD : D.Minimal) :
    DegenerateOn G (D.usedFinset.image Subtype.val) (2*Fintype.card I) := by
  classical
  intro T hT hn
  let T' := D.usedFinset.filter (fun v => v.val ∈ T)
  have he : T'.image Subtype.val = T := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hw).2
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp (hT hv)
      exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,hv⟩,rfl⟩
  have hn' : T'.Nonempty := by
    obtain ⟨v,hv⟩ := hn
    rw [←he] at hv
    obtain ⟨w,hw,_⟩ := mem_image.mp hv
    exact ⟨w,hw⟩
  obtain ⟨v,hv,hd⟩ := hD.low_degree T' (filter_subset _ _) hn'
  refine ⟨v.val,(mem_filter.mp hv).2,?_⟩
  rw [←he,filter_image,card_image_of_injective _ Subtype.val_injective]
  exact hd

theorem minimum_system_path_neighbors {V I J : Type} [DecidableEq V] [Fintype I]
    [DecidableEq I] (G : SimpleGraph V) (A : Finset V)
    (s : I → ↥(↑A : Set V)) (B : J → Set ↥(↑A : Set V))
    (D : BagRouting (G.induce (↑A : Set V)) s B) (hD : D.Minimal)
    (i : I) (v : V) (hv : v ∈ A) (hout : v ∉ D.usedFinset.image Subtype.val) :
    (((D.paths i).2.val.support.toFinset.image Subtype.val).filter (G.Adj v)).card ≤ 3 := by
  classical
  let v' : ↥(↑A : Set V) := ⟨v,hv⟩
  have hv' : v' ∉ D.used := by
    intro hh
    exact hout (mem_image.mpr ⟨v',(D.mem_usedFinset v').mpr hh,rfl⟩)
  have hd := hD.path_neighbors_le_three i v' hv'
  rw [filter_image,card_image_of_injective _ Subtype.val_injective]
  exact hd

end LinearListHadwiger.Footprint

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

namespace System
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

lemma path_subset_domain (S : System G) (i : Fin S.n) : S.path i ⊆ S.domain := by
  intro v hv
  obtain ⟨w,_,rfl⟩ := mem_image.mp hv
  exact w.property

lemma mem_used (S : System G) (v : V) : v ∈ S.used ↔ ∃ i, v ∈ S.path i := by
  simp only [used,path,mem_image,BagRouting.usedFinset,mem_biUnion,mem_univ,true_and]
  aesop

lemma used_eq (S : System G) : S.used = univ.biUnion S.path := by
  ext v
  simp only [S.mem_used,mem_biUnion,mem_univ,true_and]

lemma used_subset_domain (S : System G) : S.used ⊆ S.domain := by
  intro v hv
  obtain ⟨i,hi⟩ := (S.mem_used v).mp hv
  exact S.path_subset_domain i hi

lemma degenerate (S : System G) : DegenerateOn G S.used (2*S.n) := by
  simpa only [used,Fintype.card_fin] using
    minimum_system_degenerate G S.domain S.source _ S.routes S.minimal

lemma path_neighbors (S : System G) (i : Fin S.n) (v : V)
    (hv : v ∈ S.domain) (hout : v ∉ S.used) :
    ((S.path i).filter (G.Adj v)).card ≤ 3 :=
  minimum_system_path_neighbors G S.domain S.source _ S.routes S.minimal i v hv hout

lemma used_neighbors (S : System G) (v : V) (hv : v ∈ S.domain) (hout : v ∉ S.used) :
    (S.used.filter (G.Adj v)).card ≤ 3*S.n := by
  rw [S.used_eq]
  exact neighbors_in_collection G S.path v S.n 3
    (fun i => S.path_neighbors i v hv hout) (by simpa using card_filter_le (univ : Finset (Fin S.n)) _)

end System
end LinearListHadwiger.Footprint

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Stage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
lemma list_iso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    listChromaticNumber G = listChromaticNumber H := by
  apply le_antisymm
  · exact (listChromaticNumber_le_iff _ _).mpr
      (choosable_of_iso e (choosable_listChromaticNumber H))
  · exact (listChromaticNumber_le_iff _ _).mpr
      (choosable_of_iso e.symm (choosable_listChromaticNumber G))

omit [Fintype W] [Fintype V] [DecidableEq W] in
lemma ell_image (G : SimpleGraph V) (f : W → V) (hf : Function.Injective f) (T : Finset W) :
    ell (G.comap f) T = ell G (T.image f) := by
  let e : (G.comap f).induce (↑T : Set W) ≃g G.induce (↑(T.image f) : Set V) :=
    { toEquiv := (Equiv.Set.image f (↑T : Set W) hf).trans
        (Equiv.setCongr (by exact (Finset.coe_image).symm))
      map_rel_iff' := by intro a b; rfl }
  exact list_iso e

omit [DecidableEq V] in
lemma ell_univ (G : SimpleGraph V) : ell G univ = listChromaticNumber G := by
  let e : G.induce (↑(univ : Finset V) : Set V) ≃g G :=
    { toEquiv := { toFun := Subtype.val
                   invFun := fun v => ⟨v,mem_univ v⟩
                   left_inv := fun _ => rfl
                   right_inv := fun _ => rfl }
      map_rel_iff' := by intro a b; rfl }
  exact list_iso e

omit [Fintype V] in
lemma ell_delete (G : SimpleGraph V) (S Z : Finset V) :
    ell G S ≤ ell G (S\Z) + Z.card := by
  let X : Finset (↑S : Set V) := univ.filter (fun v => v.val∈Z)
  have he : (univ\X).image Subtype.val = S\Z := by
    ext v
    simp only [mem_image,mem_sdiff,mem_univ,mem_filter,true_and,X]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact ⟨w.property,hw⟩
    · rintro ⟨hs,hz⟩; exact ⟨⟨v,hs⟩,hz,rfl⟩
  have hX : X.card ≤ Z.card := by
    rw [←card_image_of_injective X Subtype.val_injective]
    apply card_le_card
    rintro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hw).2
  have hh := listChromaticNumber_deleted (G.induce (↑S : Set V)) X
  have ht := ell_image G (Subtype.val : (↑S : Set V) → V) Subtype.val_injective (univ\X)
  rw [he] at ht
  change ell (G.induce (↑S : Set V)) (univ\X) = _ at ht
  change ell G S - X.card ≤ ell (G.induce (↑S : Set V)) (univ\X) at hh
  rw [ht] at hh
  omega

lemma extract_on (G : SimpleGraph V) (S : Finset V) {k : ℕ} (hk : 1≤k)
    (hl : 6*k < ell G S) :
    ∃ T⊆S, KConnectedOn G T k ∧ ell G S ≤ ell G T + 6*k := by
  obtain ⟨T,hTc,hTl⟩ := list_connectivity_extraction (G.induce (↑S:Set V)) hk hl
  refine ⟨T.image Subtype.val,by rintro v hv; obtain ⟨w,hw,rfl⟩ := mem_image.mp hv; exact w.property,
    Knitting.kConnected_image G Subtype.val Subtype.val_injective hTc,?_⟩
  have he := ell_image G (Subtype.val : (↑S : Set V) → V) Subtype.val_injective T
  change ell (G.induce (↑S:Set V)) T = _ at he
  change ell G S - 6*k ≤ ell (G.induce (↑S:Set V)) T at hTl
  rw [he] at hTl
  omega

theorem districts_on : ∀ K : ℕ, 0<K → ∃ D : ℕ,
    max (400*3202) (12800*K)<D ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀≤t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V),
    hadwigerNumber G<t → 2*D*t+2<ell G S →
    ∃ J⊆S, KConnectedOn G J (K*t) ∧ (J.card:ℝ)≤(t:ℝ)^(53/50:ℝ) := by
  intro K hK
  obtain ⟨D,hD,T,hT⟩ := District.list_district K hK
  refine ⟨D,hD,T,?_⟩
  intro t ht V _ _ G S hminor hl
  obtain ⟨J,hJc,hJs⟩ := hT t ht (↑S:Set V) (G.induce (↑S:Set V))
    ((Knitting.model_induce G S).hadwiger_le.trans_lt hminor) hl
  refine ⟨J.image Subtype.val,by rintro v hv; obtain ⟨w,hw,rfl⟩ := mem_image.mp hv; exact w.property,
    Knitting.kConnected_image G Subtype.val Subtype.val_injective hJc,?_⟩
  simpa only [card_image_of_injective _ Subtype.val_injective] using hJs

end LinearListHadwiger.Stage

namespace LinearListHadwiger.DoublePacking
variable {V : Type} {G : SimpleGraph V} {A B : Finset V}

lemma exists_minimal (h : Nonempty (DoublePacking G A B)) :
    ∃ D : BagRouting G (fun i : ↥A × Bool => i.1.val) (fun b : ↥B => {b.val}),
      D.Minimal := by
  obtain ⟨D⟩ := h
  exact BagRouting.exists_minimal ⟨D.routing⟩

end LinearListHadwiger.DoublePacking

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.StageExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

namespace Unpaired
variable {V : Type} {G : SimpleGraph V} {A B : Finset V} {n : ℕ}

lemma exists_minimal (h : Nonempty (Unpaired G A B n)) :
    ∃ D : Unpaired G A B n, D.Minimal := by
  obtain ⟨D⟩ := h
  have hex : ∃ m : ℕ, ∃ E : Unpaired G A B n, E.totalLength=m := ⟨D.totalLength,D,rfl⟩
  obtain ⟨E,hE⟩ := Nat.find_spec hex
  exact ⟨E,fun F => hE ▸ Nat.find_min' hex ⟨F,rfl⟩⟩

lemma replace_shorter (D : Unpaired G A B n) (i : Fin n) (P : Segment G A B)
    (hP : ∀ v, v∈P.walk.2.val.support → v∈(D.segment i).walk.2.val.support)
    (hlen : P.walk.2.val.length < (D.segment i).walk.2.val.length) :
    (D.replace i P hP).totalLength < D.totalLength := by
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j=i
    · subst j
      change (Function.update D.segment i P i).walk.2.val.length ≤ (D.segment i).walk.2.val.length
      rw [Function.update_self]
      exact hlen.le
    · change (Function.update D.segment i P j).walk.2.val.length ≤ (D.segment j).walk.2.val.length
      rw [Function.update_of_ne hj]
  · refine ⟨i,mem_univ _,?_⟩
    change (Function.update D.segment i P i).walk.2.val.length < (D.segment i).walk.2.val.length
    rw [Function.update_self]
    exact hlen

lemma Minimal.source_only [DecidableEq V] {D : Unpaired G A B n} (hD : D.Minimal)
    (i : Fin n) (v : V) (hv : v∈(D.segment i).walk.2.val.support) (ha : v∈A) :
    v=(D.segment i).left.val := by
  by_contra hn
  let P : Segment G A B := ⟨⟨v,ha⟩,⟨(D.segment i).walk.1,
    ⟨(D.segment i).walk.2.val.dropUntil v hv,(D.segment i).walk.2.property.dropUntil hv⟩⟩,
    (D.segment i).right_mem⟩
  have hp (w : V) : w∈P.walk.2.val.support → w∈(D.segment i).walk.2.val.support :=
    fun hw => (D.segment i).walk.2.val.support_dropUntil_subset_support hv hw
  have hs := D.replace_shorter i P hp (Walk.length_dropUntil_lt_length hv hn)
  exact (not_lt_of_ge (hD _)) hs

end Unpaired
end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma under_image {U A : Finset V} (hA : A⊆U) : (under U A).image Subtype.val=A := by
  ext v
  simp only [mem_image,mem_under]
  constructor
  · rintro ⟨w,hw,rfl⟩; exact hw
  · intro hv; exact ⟨⟨v,hA hv⟩,hv,rfl⟩

omit [Fintype V] in
lemma under_card {U A : Finset V} (hA : A⊆U) : (under U A).card=A.card := by
  calc
    _ = ((under U A).image Subtype.val).card := (card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := congrArg Finset.card (under_image hA)

omit [Fintype V] in
lemma under_disjoint {U A B : Finset V} (h : Disjoint A B) :
    Disjoint (under U A) (under U B) := by
  apply disjoint_left.mpr
  intro v hv hw
  exact disjoint_left.mp h (mem_under v |>.mp hv) (mem_under v |>.mp hw)

omit [Fintype V] in
lemma under_connected (G : SimpleGraph V) {U A : Finset V} {k : ℕ}
    (hA : A⊆U) (hc : KConnectedOn G A k) :
    KConnectedOn (G.induce (↑U : Set V)) (under U A) k := by
  classical
  refine ⟨by simpa only [under_card hA] using hc.1,?_⟩
  intro X hX hx
  let Z := X.image Subtype.val
  have hZA : Z⊆A := by
    rintro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_under w).mp (hX hw)
  have hZk : Z.card<k := by
    simpa only [Z,card_image_of_injective _ Subtype.val_injective] using hx
  have hcon := hc.2 Z hZA hZk
  let f : G.induce (↑(A\Z) : Set V) →g
      (G.induce (↑U : Set V)).induce (↑(under U A\X) : Set ↥(↑U : Set V)) := {
    toFun := fun v => ⟨⟨v.val,hA (mem_sdiff.mp v.property).1⟩,
      mem_sdiff.mpr ⟨(mem_under _).mpr (mem_sdiff.mp v.property).1,
        fun hv => (mem_sdiff.mp v.property).2 (mem_image.mpr ⟨_,hv,rfl⟩)⟩⟩
    map_rel' := fun h => h }
  apply hcon.map f
  intro w
  have hw : w.val.val∈A\Z := by
    refine mem_sdiff.mpr ⟨(mem_under _).mp (mem_sdiff.mp w.property).1,?_⟩
    intro hz
    obtain ⟨a,ha,he⟩ := mem_image.mp hz
    have heq : a=w.val := Subtype.ext he
    exact (mem_sdiff.mp w.property).2 (heq ▸ ha)
  exact ⟨⟨w.val.val,hw⟩,rfl⟩

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Footprint.System
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V I : Type} [DecidableEq V] [Fintype I] {G : SimpleGraph V}

lemma mem_route (S : System G) (i : Fin S.n) (v : V) :
    v∈(S.route i).val.support ↔ v∈S.path i := by
  simp only [route,path,SimpleGraph.Walk.support_map,List.mem_map,mem_image,List.mem_toFinset]
  rfl

@[simp] lemma empty_used (U : Finset V) : (empty (G:=G) U).used=∅ := by
  ext v
  simp [mem_used,empty]

end LinearListHadwiger.Footprint.System

namespace LinearListHadwiger.DoublePacking
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}

lemma mem_lift_route {U A B : Finset V} (hA : A⊆U) (hB : B⊆U)
    (P : DoublePacking (G.induce (↑U : Set V)) (Stage.under U A) (Stage.under U B))
    (i : ↥A×Bool) (v : V) :
    v∈((P.lift hA hB).route i).val.support ↔
      ∃ w : ↥(↑U : Set V), w∈(P.route (liftIndex hA i)).val.support ∧ w.val=v := by
  change v∈((P.route (liftIndex hA i)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support ↔ _
  rw [SimpleGraph.Walk.support_map,List.mem_map]
  rfl

theorem in_region [Fintype V] (S A B : Finset V) (hA : A⊆S) (hB : B⊆S)
    (hAB : Disjoint A B) (hc : KConnectedOn G S (2*A.card)) (hb : 2*A.card≤B.card) :
    Nonempty (DoublePacking G A B) := by
  have hconn : KConnectedOn (G.induce (↑S : Set V)) univ (2*(Stage.under S A).card) := by
    have hh := Stage.under_connected G (U:=S) (A:=S) (subset_refl S) hc
    have he : Stage.under S S=univ := by ext v; simp [Stage.under]
    simpa only [he,Stage.under_card hA] using hh
  obtain ⟨P⟩ := double_packing (G.induce (↑S : Set V)) (Stage.under S A) (Stage.under S B)
    (Stage.under_disjoint hAB) hconn (by simpa only [Stage.under_card hA,Stage.under_card hB] using hb)
  exact ⟨P.lift hA hB⟩

end LinearListHadwiger.DoublePacking

namespace LinearListHadwiger.Footprint.System
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V I : Type} [DecidableEq V] [Fintype I] {G : SimpleGraph V}

lemma mem_ofMinimal_used (U : Finset V) (s : I → ↥(↑U : Set V))
    (T : Finset ↥(↑U : Set V))
    (D : BagRouting (G.induce (↑U : Set V)) s (fun b : ↥T => {b.val}))
    (hD : D.Minimal) (v : V) :
    v∈(ofMinimal U s T D hD).used ↔
      ∃ i w, w∈(D.paths i).2.val.support ∧ w.val=v := by
  rw [mem_used]
  simp only [path,ofMinimal,BagRouting.reindex,mem_image]
  constructor
  · rintro ⟨i,w,hw,he⟩; exact ⟨_,w,List.mem_toFinset.mp hw,he⟩
  · rintro ⟨i,w,hw,he⟩
    refine ⟨Fintype.equivFin I i,w,?_,he⟩
    change w∈(D.paths ((Fintype.equivFin I).symm ((Fintype.equivFin I) i))).2.val.support.toFinset
    apply List.mem_toFinset.mpr
    have heq := congrArg (fun j : I => (D.paths j).2.val.support)
      ((Fintype.equivFin I).symm_apply_apply i)
    exact heq.symm ▸ hw

end LinearListHadwiger.Footprint.System

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.StageDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset SimpleGraph Footprint
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
lemma under_mono {U A B : Finset V} (h : A⊆B) : under U A⊆under U B := by
  intro v hv
  exact (mem_under v).mpr (h ((mem_under v).mp hv))

omit [Fintype V] in

theorem first_system (U S Z D : Finset V)
    (hSU : S⊆U) (hZS : Z⊆S) (hDS : D⊆S) (hZD : Disjoint Z D)
    (hc : KConnectedOn G S (2*Z.card)) (hd : 2*Z.card≤D.card) :
    ∃ R : System G, ∃ P : DoublePacking G Z D,
      R.domain=U ∧ R.n=2*Z.card ∧ R.starts=Z ∧ R.ends⊆D ∧
      ∀ i v, v∈(P.route i).val.support → v∈R.used := by
  have hZU := hZS.trans hSU
  have hDU := hDS.trans hSU
  let A := under U Z
  let B := under U D
  have hconn : KConnectedOn (G.induce (↑U : Set V)) (under U S) (2*A.card) := by
    simpa only [A,under_card hZU] using under_connected G hSU hc
  obtain ⟨P₀⟩ := DoublePacking.in_region (under U S) A B (under_mono hZS) (under_mono hDS)
    (under_disjoint hZD) hconn (by simpa only [A,B,under_card hZU,under_card hDU] using hd)
  obtain ⟨Q,hQ⟩ := DoublePacking.exists_minimal ⟨P₀⟩
  let R := System.ofMinimal U (fun i : ↥A×Bool => i.1.val) B Q hQ
  let P₁ := DoublePacking.ofMinimal Q hQ (under_disjoint hZD)
  let P := P₁.lift hZU hDU
  refine ⟨R,P,rfl,?_,?_,?_,?_⟩
  · change Fintype.card (↥A×Bool)=2*Z.card
    simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_coe,A,under_card hZU]
    omega
  · rw [System.ofMinimal_starts]
    ext v
    simp only [mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact (mem_under _).mp i.1.property
    · intro hv
      exact ⟨(⟨⟨v,hZU hv⟩,(mem_under _).mpr hv⟩,false),rfl⟩
  · intro v hv
    have hh := System.ofMinimal_ends U (fun i : ↥A×Bool => i.1.val) B Q hQ hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hh
    exact (mem_under _).mp hw
  · intro i v hv
    obtain ⟨w,hw,he⟩ := (DoublePacking.mem_lift_route hZU hDU P₁ i v).mp hv
    have hw' : w∈(Q.paths (DoublePacking.liftIndex hZU i)).2.val.support := by
      simpa only [P₁,DoublePacking.ofMinimal_support] using hw
    exact (System.mem_ofMinimal_used U _ B Q hQ v).mpr ⟨_,w,hw',he⟩

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset SimpleGraph Footprint
attribute [local instance] Classical.propDecidable

namespace Second
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {U H D : Finset V} {n : ℕ}

lemma mem_route (Q : Second G U H D n) (i : Fin n) (v : V) :
    v∈(Q.route i).val.support ↔
    ∃ w : ↥(↑U : Set V), w∈(Q.sys.segment i).walk.2.val.support ∧ w.val=v := by
  change v∈((Q.sys.segment i).walk.2.val.map
    ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support ↔ _
  rw [Walk.support_map,List.mem_map]
  rfl

lemma route_domain (Q : Second G U H D n) (i : Fin n) {v : V}
    (hv : v∈(Q.route i).val.support) : v∈U := by
  obtain ⟨w,_,rfl⟩ := (Q.mem_route i v).mp hv
  exact w.property

lemma source_only (Q : Second G U H D n) (i : Fin n) (v : V)
    (hv : v∈(Q.route i).val.support) (hH : v∈H) : v=Q.source i := by
  obtain ⟨w,hw,rfl⟩ := (Q.mem_route i v).mp hv
  exact congrArg Subtype.val (Q.minimal.source_only i w hw ((mem_under _).mpr hH))

lemma disjoint (Q : Second G U H D n) (i j : Fin n) (hij : i≠j) :
    Disjoint {v | v∈(Q.route i).val.support} {v | v∈(Q.route j).val.support} := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  obtain ⟨a,ha,rfl⟩ := (Q.mem_route i v).mp hv
  obtain ⟨b,hb,he⟩ := (Q.mem_route j a.val).mp hw
  have heq : b=a := Subtype.ext he
  subst b
  exact Set.disjoint_left.mp (Q.sys.disjoint i j hij) ha hb

lemma mem_record_used (Q : Second G U H D n) (v : V) :
    v∈Q.record.used ↔ ∃ i, v∈(Q.route i).val.support := by
  rw [record,System.mem_ofMinimal_used]
  simp only [Q.mem_route,Unpaired.routing]

theorem exists_in_region (U S H D : Finset V) (n : ℕ)
    (hSU : S⊆U) (hHS : H⊆S) (hDS : D⊆S)
    (hc : KConnectedOn G S n) (hH : n≤H.card) (hD : n≤D.card) :
    Nonempty (Second G U H D n) := by
  have hHU := hHS.trans hSU
  have hDU := hDS.trans hSU
  have hcardH : n≤(under U H).card := by simpa only [under_card hHU] using hH
  obtain ⟨A,hA,hAn⟩ := Finset.exists_subset_card_eq hcardH
  obtain ⟨P⟩ := packing_of_kConnectedOn (G.induce (↑U : Set V)) (under U S)
    A (under U D) (under_connected G hSU hc) (hA.trans (under_mono hHS)) (under_mono hDS)
    (by omega) (by rw [hAn,under_card hDU]; exact hD)
  let e : Fin n ≃ ↥A := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hAn)).symm
  obtain ⟨E,hE⟩ := Unpaired.exists_minimal ⟨Unpaired.ofFullPacking P hA e⟩
  exact ⟨⟨E,hE⟩⟩

end Second
end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma congestion_sum {A B V : Type} [Fintype A] [Fintype B]
    (P : A → Bool → Set V) (Q : B → Bool → Set V) (v : V) :
    (univ.filter (fun ib : (A⊕B)×Bool =>
      v∈Sum.elim (fun a => P a ib.2) (fun b => Q b ib.2) ib.1)).card =
    (univ.filter (fun ib : A×Bool => v∈P ib.1 ib.2)).card +
    (univ.filter (fun ib : B×Bool => v∈Q ib.1 ib.2)).card := by
  classical
  simp only [card_eq_sum_ones,sum_filter,←univ_product_univ,sum_product]
  rw [Fintype.sum_sum_type]
  rfl

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {Z H D : Finset V}

omit [Fintype V] in
lemma double_congestion (P : DoublePacking G Z D) (v : V) :
    (univ.filter (fun ib : ↥Z×Bool => v∈(P.route ib).val.support)).card ≤ 2 := by
  classical
  by_cases hv : v∈Z
  · apply (card_le_card (t:=({⟨v,hv⟩}×ˢuniv)) ?_).trans
      (by simp)
    intro ib hib
    have he := P.source_only ib v (mem_filter.mp hib).2 hv
    exact mem_product.mpr ⟨mem_singleton.mpr (Subtype.ext he.symm),mem_univ _⟩
  · have hc : (univ.filter (fun ib : ↥Z×Bool => v∈(P.route ib).val.support)).card ≤ 1 := by
      apply card_le_one.mpr
      intro i hi j hj
      by_contra hne
      have he := P.overlap i j hne v (mem_filter.mp hi).2 (mem_filter.mp hj).2
      exact hv (he.1 ▸ i.1.property)
    omega

omit [Fintype V] in
lemma double_congestion_off (P : DoublePacking G Z D) (v : V) (hv : v∉Z) :
    (univ.filter (fun ib : ↥Z×Bool => v∈(P.route ib).val.support)).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro i hi j hj
  by_contra hne
  have he := P.overlap i j hne v (mem_filter.mp hi).2 (mem_filter.mp hj).2
  exact hv (he.1 ▸ i.1.property)

theorem combine_double (P : DoublePacking G Z D)
    (s : I×Bool → V) (tar : I×Bool → ↥D)
    (Q : ∀ i, G.Path (s i) (tar i).val)
    (hs : Function.Injective s) (hsH : ∀ i, s i∈H)
    (hZH : Disjoint Z H) (hZD : Disjoint Z D) (hHD : Disjoint H D)
    (hP : ∀ i v, v∈(P.route i).val.support → v∉H)
    (hQZ : ∀ i v, v∈(Q i).val.support → v∉Z)
    (hQH : ∀ i v, v∈(Q i).val.support → v∈H → v=s i)
    (hQQ : ∀ i j, i≠j → Disjoint {v | v∈(Q i).val.support}
      {v | v∈(Q j).val.support}) :
    Nonempty (PairedSources.Packing G
      (fun (i : ↥Z⊕I) b => Sum.elim Subtype.val (fun j => s (j,b)) i) D
      {v | (∃ i, v∈(P.route i).val.support) ∨ ∃ i, v∈(Q i).val.support}) := by
  classical
  let src : (↥Z⊕I) → Bool → V :=
    fun i b => Sum.elim Subtype.val (fun j => s (j,b)) i
  let dest : (↥Z⊕I) → Bool → ↥D := fun i b =>
    Sum.elim (fun z => P.target (z,b)) (fun j => tar (j,b)) i
  let paths : ∀ i b, G.Path (src i b) (dest i b).val := fun i b =>
    match i with
    | .inl z => P.route (z,b)
    | .inr j => Q (j,b)
  apply PairedSources.combine dest paths
  · intro i b j c he
    dsimp only [src] at he
    cases i with
    | inl z =>
      cases j with
      | inl w => exact congrArg Sum.inl (Subtype.ext he)
      | inr j => exact (Finset.disjoint_left.mp hZH z.property ((show z.val = s (j,c) from he).symm ▸ hsH (j,c))).elim
    | inr i =>
      cases j with
      | inl z => exact (Finset.disjoint_left.mp hZH z.property ((show s (i,b) = z.val from he) ▸ hsH (i,b))).elim
      | inr j => exact congrArg Sum.inr (congrArg Prod.fst (hs he))
  · intro v hv i b
    cases i with
    | inl z => exact fun he => Finset.disjoint_left.mp hZD (he ▸ z.property) hv
    | inr i => exact fun he => Finset.disjoint_left.mp hHD (he ▸ hsH (i,b)) hv
  · intro i b v hv
    cases i with
    | inl z => exact Or.inl ⟨(z,b),hv⟩
    | inr i => exact Or.inr ⟨(i,b),hv⟩
  · intro i b v hv j c he
    cases i with
    | inl z =>
      cases j with
      | inl w => exact P.source_only (z,b) v hv (he ▸ w.property)
      | inr j => exact (hP (z,b) v hv (he ▸ hsH (j,c))).elim
    | inr i =>
      cases j with
      | inl w => exact (hQZ (i,b) v hv (he ▸ w.property)).elim
      | inr j => exact hQH (i,b) v hv (he ▸ hsH (j,c))
  · intro v
    have he : (univ.filter (fun ib : (↥Z⊕I)×Bool =>
        v∈(paths ib.1 ib.2).val.support)).card =
        (univ.filter (fun ib : ↥Z×Bool => v∈(P.route ib).val.support)).card +
        (univ.filter (fun ib : I×Bool => v∈(Q ib).val.support)).card := by
      convert congestion_sum (fun a b => {v | v∈(P.route (a,b)).val.support})
        (fun a b => {v | v∈(Q (a,b)).val.support}) v using 2
      · congr 1
        funext ib
        cases ib.1 <;> rfl
      · simp only [Set.mem_ofPred_eq]
      · simp only [Set.mem_ofPred_eq]
    rw [he]
    by_cases hv : v∈Z
    · have hzero : (univ.filter (fun ib : I×Bool => v∈(Q ib).val.support))=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hQZ i v (mem_filter.mp hi).2 hv
      rw [hzero,card_empty,Nat.add_zero]
      exact double_congestion P v
    · have hq : (univ.filter (fun ib : I×Bool => v∈(Q ib).val.support)).card≤1 := by
        apply card_le_one.mpr
        intro i hi j hj
        by_contra hne
        exact Set.disjoint_left.mp (hQQ i j hne) (mem_filter.mp hi).2 (mem_filter.mp hj).2
      have hp := double_congestion_off P v hv
      omega

end LinearListHadwiger.Stage

namespace LinearListHadwiger.PairedSources.Packing
open SimpleGraph Finset
variable {V I : Type} {G : SimpleGraph V} {s : I → Bool → V} {D : Finset V} {U : Set V}

lemma source_injective (P : PairedSources.Packing G s D U) :
    Function.Injective (fun i => s i (P.choose i)) := by
  intro i j he
  by_contra hij
  exact Set.disjoint_left.mp (P.disjoint i j hij) (P.route i).val.start_mem_support
    (Eq.mpr (congrArg (fun v => v∈(P.route j).val.support) he)
      (P.route j).val.start_mem_support)

end LinearListHadwiger.PairedSources.Packing

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.RoleRouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

namespace RoleRouting
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {t a : ℕ}
    {w : Fin t → V} {u : Fin a → V} {F H U : Set V} {D : Finset V}

theorem of_paired (hw : Function.Injective w) (hu : Function.Injective u)
    (hwu : ∀ i j, w i≠u j) (s : Fin t×Bool → V)
    (hs : Function.Injective s) (hsH : ∀ i, s i∈H)
    (hZH : Disjoint (↑(oldSources w u) : Set V) H)
    (P : PairedSources.Packing G
      (fun (i : ↥(oldSources w u)⊕Fin t) b => Sum.elim Subtype.val (fun j => s (j,b)) i) D U)
    (hPF : ∀ p v, v∈(P.route p).val.support → v∈F → ∃ i, w i=v)
    (hPH : ∀ p v, v∈(P.route p).val.support → v∈H → ∃ i b, s (i,b)=v) :
    Nonempty (RoleRouting G w u F H D U) := by
  classical
  let e := roleEquiv w u hw hu hwu
  let w' : Fin t → V := fun i => s (i,P.choose (.inr i))
  let tar : Roles t a → ↥D := fun p => P.target (e p)
  have hstart (p : Roles t a) :
      Sum.elim Subtype.val (fun j => s (j,P.choose (e p))) (e p)=roleStart w u w' p := by
    rcases p with i | (j|i) <;> rfl
  let paths : ∀ p, G.Path (roleStart w u w' p) (tar p).val := fun p =>
    ⟨(P.route (e p)).val.copy (hstart p) rfl,by simp⟩
  have hsup (p : Roles t a) (v : V) : v∈(paths p).val.support ↔ v∈(P.route (e p)).val.support := by
    simp [paths]
  have hsource (p : Roles t a) (v : V) (hv : v∈(paths p).val.support)
      (hi : ∃ i b, v=Sum.elim Subtype.val (fun j => s (j,b)) i) : v=roleStart w u w' p :=
    (P.source_only (e p) v ((hsup p v).mp hv) hi).trans (hstart p)
  have hxinj : Function.Injective (roleStart w u w') := by
    intro p q he
    apply e.injective
    apply P.source_injective
    exact (hstart p).trans (he.trans (hstart q).symm)
  refine ⟨⟨w',?_,fun i => hsH _,tar,paths,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j he
    exact congrArg Prod.fst (hs he)
  · intro p q hpq
    apply Set.disjoint_left.mpr
    intro v hv hw'
    exact Set.disjoint_left.mp (P.disjoint _ _ (fun he => hpq (e.injective he)))
      ((hsup p v).mp hv) ((hsup q v).mp hw')
  · intro p v hv hvF
    obtain ⟨i,hi⟩ := hPF (e p) v ((hsup p v).mp hv) hvF
    have he := hsource p v hv ⟨e (.inl i),false,by simpa [e,roleEquiv,roleTo] using hi.symm⟩
    refine ⟨i,hxinj ?_,hi.symm⟩
    exact he.symm.trans hi.symm
  · intro p v hv hvH
    obtain ⟨i,b,hi⟩ := hPH (e p) v ((hsup p v).mp hv) hvH
    have he := hsource p v hv ⟨Sum.inr i,b,hi.symm⟩
    rcases p with j | (j|j)
    · have he' : v=w j := he
      exact (Set.disjoint_left.mp hZH ((mem_oldSources w u _).mpr (Or.inl ⟨j,rfl⟩))
        (he' ▸ hvH)).elim
    · have he' : v=u j := he
      exact (Set.disjoint_left.mp hZH ((mem_oldSources w u _).mpr (Or.inr ⟨j,rfl⟩))
        (he' ▸ hvH)).elim
    · exact ⟨j,rfl,he⟩
  · intro p j hv
    exact hsource p (u j) hv ⟨e (.inr (.inl j)),false,rfl⟩
  · intro p v hv hvD
    exact P.target_only (e p) v ((hsup p v).mp hv) hvD
  · intro p v hv
    exact P.inside (e p) v ((hsup p v).mp hv)

end RoleRouting
end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset Footprint
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t a : ℕ}

theorem combine_systems (F H D : Finset V) (w : Fin t → V) (u : Fin a → V)
    (hw : Function.Injective w) (hu : Function.Injective u) (hwu : ∀ i j, w i≠u j)
    (hwF : ∀ i, w i∈F) (hZH : Disjoint (oldSources w u) H)
    (hZD : Disjoint (oldSources w u) D) (hHD : Disjoint H D)
    (R : System G) (hRU : R.domain=univ\(F\univ.image w))
    (P : DoublePacking G (oldSources w u) D)
    (hPR : ∀ i v, v∈(P.route i).val.support → v∈R.used)
    (hRH : Disjoint R.used H)
    (Q : Second G (univ\(F∪univ.image u)) H D (2*t)) :
    Nonempty (RoleRouting G w u (↑F : Set V) (↑H : Set V) D
      (↑(R.used∪Q.record.used) : Set V)) := by
  classical
  let e : (Fin t×Bool) ≃ Fin (2*t) := Fintype.equivOfCardEq (by simp; omega)
  let s : Fin t×Bool → V := Q.source ∘ e
  let tar : Fin t×Bool → ↥D := Q.target ∘ e
  let paths : ∀ i, G.Path (s i) (tar i).val := fun i => Q.route (e i)
  have hs : Function.Injective s := Q.source_injective.comp e.injective
  have hsH : ∀ i, s i∈H := fun i => Q.source_mem (e i)
  have hPH : ∀ i v, v∈(P.route i).val.support → v∉H :=
    fun i v hv hH => Finset.disjoint_left.mp hRH (hPR i v hv) hH
  have hQZ : ∀ i v, v∈(paths i).val.support → v∉oldSources w u := by
    intro i v hv hvZ
    have hdom := (mem_sdiff.mp (Q.route_domain (e i) hv)).2
    rcases (mem_oldSources w u v).mp hvZ with ⟨j,rfl⟩|⟨j,rfl⟩
    · exact hdom (mem_union_left _ (hwF j))
    · exact hdom (mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩))
  obtain ⟨K⟩ := combine_double P s tar paths hs hsH hZH hZD hHD hPH hQZ
    (fun i v hv hvH => Q.source_only (e i) v hv hvH)
    (fun i j hij => Q.disjoint _ _ (fun he => hij (e.injective he)))
  have hinside (i) (v) (hv : v∈(K.route i).val.support) : v∈R.used∪Q.record.used := by
    rcases K.inside i v hv with ⟨j,hj⟩|⟨j,hj⟩
    · exact mem_union_left _ (hPR j v hj)
    · exact mem_union_right _ ((Q.mem_record_used v).mpr ⟨e j,hj⟩)
  let K' : PairedSources.Packing G
      (fun (i : ↥(oldSources w u)⊕Fin t) b => Sum.elim Subtype.val (fun j => s (j,b)) i) D
      (↑(R.used∪Q.record.used) : Set V) :=
    { choose := K.choose
      target := K.target
      route := K.route
      disjoint := K.disjoint
      source_only := K.source_only
      target_only := K.target_only
      inside := hinside }
  apply RoleRouting.of_paired hw hu hwu s hs hsH (by exact_mod_cast hZH) K'
  · intro i v hv hvF
    rcases K.inside i v hv with ⟨j,hj⟩|⟨j,hj⟩
    · have hdom := R.used_subset_domain (hPR j v hj)
      rw [hRU] at hdom
      have hvW : v∈univ.image w := by
        by_contra hn
        exact (mem_sdiff.mp hdom).2 (mem_sdiff.mpr ⟨hvF,hn⟩)
      simpa only [mem_image,mem_univ,true_and] using hvW
    · exact False.elim ((mem_sdiff.mp (Q.route_domain (e j) hj)).2 (mem_union_left _ hvF))
  · intro i v hv hvH
    rcases K.inside i v hv with ⟨j,hj⟩|⟨j,hj⟩
    · exact False.elim (hPH j v hj hvH)
    · exact ⟨j.1,j.2,(Q.source_only (e j) v hj hvH).symm⟩

end LinearListHadwiger.Stage

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.RecursiveJunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Recursion
open Finset Stage Footprint SmallList Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma outer_size_cutoff : ∃ T : ℕ, ∀ t : ℕ, T≤t →
    (t:ℝ)^(53/50:ℝ)+(t:ℝ)≤(t:ℝ)^(11/10:ℝ) := by
  have he : ∀ᶠ x : ℝ in atTop, 1≤x ∧ 2≤x^(1/25:ℝ) :=
    (eventually_ge_atTop 1).and ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/25)).eventually (eventually_ge_atTop 2))
  obtain ⟨S,hS⟩ := (eventually_atTop.mp he)
  refine ⟨⌈S⌉₊,fun t ht => ?_⟩
  obtain ⟨h1,h2⟩ := hS t ((Nat.le_ceil S).trans (by exact_mod_cast ht))
  have hle : (t:ℝ)≤(t:ℝ)^(53/50:ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (1:ℝ)≤53/50)
  have heq : (t:ℝ)^(11/10:ℝ)=(t:ℝ)^(53/50:ℝ)*(t:ℝ)^(1/25:ℝ) := by
    rw [←Real.rpow_add (by positivity : (0:ℝ)<t)]
    norm_num
  rw [heq]
  nlinarith [Real.rpow_nonneg (by positivity : (0:ℝ)≤t) (53/50:ℝ)]

theorem outer_region_oai : ∃ A : ℕ, 1≤A ∧ ∃ T : ℕ, 1≤T ∧
    ∀ a : ℕ, 1≤a → T≤64*a → ∀ p : ℕ, p≤3*a →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (r : Fin a → V) (n : Fin (2*p) → V),
    Function.Injective r → Function.Injective n → (∀ i j, r i≠n j) →
    KConnectedOn G univ (30*a) → hadwigerNumber G<64*a →
    A*a<listChromaticNumber G →
    (∃ H D : Finset V, ∃ U : Set V,
      Nonempty (RoleRouting G r n (↑(univ.image r):Set V) (↑H:Set V) D U) ∧
      Disjoint H D ∧ KConnectedOn G H (K₀*(64*a)) ∧
      KConnectedOn G D (K₀*(64*a)) ∧
      listChromaticNumber G≤ell G H+(4*32768+42+5+6*K₀)*(64*a)) ∨
      FractionalObstruction G := by
  obtain ⟨D,hD,Td,hTd⟩ := districts_on K₀ (by norm_num [K₀])
  obtain ⟨Tx,hTx⟩ := outer_size_cutoff
  obtain ⟨Ta,hTa⟩ := additive_deletion_or_obstruction
  let c : ℕ := 4*32768+42+5
  let A := 128*D+10+64*(c+6*K₀)
  refine ⟨A,by dsimp [A]; omega,max 1 (max Td (max Tx Ta)),by omega,?_⟩
  intro a ha ht p hp V _ _ G r n hr hn hrn hc hm hl
  classical
  have htd : Td≤64*a := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htx : Tx≤64*a := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have hta : Ta≤64*a := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  let Z := oldSources r n
  have hz : Z.card≤7*a := by
    have h := card_union_le (univ.image r) (univ.image n)
    have h1 := card_image_le (s:=univ) (f:=r)
    have h2 := card_image_le (s:=univ) (f:=n)
    simp only [card_univ,Fintype.card_fin] at h1 h2
    change ((univ.image r)∪(univ.image n)).card≤7*a
    omega
  have hdel := ell_delete G univ Z
  rw [ell_univ] at hdel
  obtain ⟨J,hJS,hJc,hJs⟩ := hTd (64*a) htd V G (univ\Z) hm (by dsimp [A] at hl; nlinarith)
  have hZJ : Disjoint Z J := disjoint_sdiff_self_right.mono_right hJS
  have hk : 2*Z.card≤30*a := by omega
  have hJcard : 2*Z.card≤J.card := by have := hJc.1; dsimp [K₀] at this; omega
  obtain ⟨R,P,hRU,hRn,hRZ,hRJ,hPR⟩ := first_system univ univ Z J (Subset.refl _) (subset_univ _) (subset_univ _) hZJ
    (Knitting.kConnected_mono hc hk) hJcard
  let X := Z∪J
  let Y := R.used\X
  have hX : (X.card:ℝ)≤((64*a:ℕ):ℝ)^(11/10:ℝ) := by
    have hcard := card_union_le Z J
    have hle : (X.card:ℝ)≤(J.card:ℝ)+(64*a:ℕ) := by exact_mod_cast (by dsimp [X]; omega : X.card≤J.card+64*a)
    have hcut := hTx (64*a) htx
    linarith
  have hY : DegenerateOn G Y (42*(64*a)) := by
    intro B hBY hB
    obtain ⟨v,hv,hdeg⟩ := R.degenerate B (hBY.trans sdiff_subset) hB
    exact ⟨v,hv,hdeg.trans (by rw [hRn]; omega)⟩
  have hnY (v) (hv : v∉X∪Y) : (Y.filter (G.Adj v)).card≤42*(64*a) := by
    have hnot : v∉R.used := by
      intro hw
      by_cases hx : v∈X
      · exact hv (mem_union_left _ hx)
      · exact hv (mem_union_right _ (mem_sdiff.mpr ⟨hw,hx⟩))
    have hd : v∈R.domain := by rw [hRU]; exact mem_univ v
    exact (card_le_card (filter_subset_filter _ sdiff_subset)).trans
      ((R.used_neighbors v hd hnot).trans (by rw [hRn]; omega))
  rcases hTa (64*a) hta V G X Y 42 hm hX disjoint_sdiff_self_right hY hnY with hloss|hb
  swap
  · exact Or.inr hb
  have hlarge : 6*(K₀*(64*a))<ell G (univ\(X∪Y)) := by
    change listChromaticNumber G≤ell G (univ\(X∪Y))+c*(64*a) at hloss
    dsimp [A] at hl
    nlinarith
  obtain ⟨H,hHS,hHc,hHl⟩ := extract_on G (univ\(X∪Y)) (by dsimp [K₀]; omega) hlarge
  have hXH : Disjoint X H := by
    apply disjoint_left.mpr
    intro v hv hw
    exact (mem_sdiff.mp (hHS hw)).2 (mem_union_left _ hv)
  have hRH : Disjoint R.used H := by
    apply disjoint_left.mpr
    intro v hv hw
    have hout := (mem_sdiff.mp (hHS hw)).2
    by_cases hx : v∈X
    · exact hout (mem_union_left _ hx)
    · exact hout (mem_union_right _ (mem_sdiff.mpr ⟨hv,hx⟩))
  have hZH : Disjoint Z H := hXH.mono_left (subset_union_left)
  have hJH : Disjoint J H := hXH.mono_left (subset_union_right)
  have hHsub : H⊆univ\Z := fun v hv => mem_sdiff.mpr ⟨mem_univ _,fun hz => disjoint_left.mp hZH hz hv⟩
  have hcc : KConnectedOn G (univ\Z) (2*a) := by
    exact Knitting.kConnected_mono (Knitting.delete_connected G hc (subset_univ Z) (by omega)) (by omega)
  obtain ⟨Q⟩ := Second.exists_in_region (univ\Z) (univ\Z) H J (2*a) (Subset.refl _) hHsub hJS hcc
    (by have := hHc.1; dsimp [K₀] at this; omega) (by have := hJc.1; dsimp [K₀] at this; omega)
  have hF : univ\(univ.image r\univ.image r)=(univ:Finset V) := by simp
  have hRu : R.domain=univ\(univ.image r\univ.image r) := by rwa [hF]
  obtain ⟨routing⟩ := combine_systems (univ.image r) H J r n hr hn hrn
    (fun i => mem_image.mpr ⟨i,mem_univ _,rfl⟩) hZH hZJ hJH.symm R hRu P hPR hRH Q
  refine Or.inl ⟨H,J,_,⟨routing⟩,hJH.symm,hHc,hJc,?_⟩
  change listChromaticNumber G≤ell G (univ\(X∪Y))+c*(64*a) at hloss
  dsimp [c] at hloss
  nlinarith

end LinearListHadwiger.Recursion

end OAI
end

theorem solution : type_of% @OAI.LinearListHadwiger.Recursion.outer_region_oai := @OAI.LinearListHadwiger.Recursion.outer_region_oai
