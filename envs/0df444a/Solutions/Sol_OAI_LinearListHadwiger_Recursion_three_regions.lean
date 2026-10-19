-- Prove2me | solution 1 for OAI.LinearListHadwiger.Recursion.three_regions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:55:27.739212+00:00
-- url     : https://prove2.me/submissions/587fda9b-5603-48ab-8e3c-9700c6b5bfbc

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000
import Theorems.Thm_OAI_LinearListHadwiger_Footprint_History_list_loss_or_obstruction
import Theorems.Thm_OAI_LinearListHadwiger_Stage_districts_woven
import Theorems.Thm_OAI_LinearListHadwiger_Stage_two_districts

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

namespace BagRouting
variable {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}

theorem exists_avoiding_unused [Fintype I] [DecidableEq V] [DecidableEq I]
    (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (h : Nonempty (BagRouting G s B)) :
    ∃ D : BagRouting G s B, ∀ j, j ∉ Set.range D.bag →
      ∀ i v, v ∈ (D.paths i).2.val.support → v ∉ B j := by
  classical
  have hex : ∃ n : ℕ, ∃ D : BagRouting G s B, D.totalLength = n := by
    obtain ⟨D⟩ := h
    exact ⟨D.totalLength, D, rfl⟩
  obtain ⟨D, hd⟩ := Nat.find_spec hex
  refine ⟨D, ?_⟩
  intro j hj i v hv hB
  have hmin := Nat.find_min' hex ⟨D.truncate i j hj v hv hB, rfl⟩
  rw [← hd] at hmin
  exact (not_le_of_gt (D.truncate_length_lt hdis i j hj v hv hB)) hmin

end BagRouting

theorem bagRouting_of_double_packing {V J : Type} [Fintype V] [Fintype J]
    [DecidableEq V] (G : SimpleGraph V) (A : Finset V) (B : J → Set V)
    (hc : KConnectedOn G Finset.univ (2 * A.card))
    (hcB : ∀ j, (G.induce (B j)).Connected)
    (hdB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (haB : ∀ j, Disjoint (↑A : Set V) (B j))
    (hcard : 2 * A.card ≤ Fintype.card J) :
    Nonempty (BagRouting G (fun i : ↥A × Bool => i.1.val) B) := by
  classical
  have hex : ∀ j, ∃ v, v ∈ B j := fun j => by
    obtain ⟨v⟩ := (hcB j).nonempty
    exact ⟨v.val, v.property⟩
  choose rep hrep using hex
  have hinj : Function.Injective rep := by
    intro i j heq
    by_contra hij
    exact Set.disjoint_left.mp (hdB i j hij) (hrep i) (heq ▸ hrep j)
  let T : Finset V := Finset.univ.image rep
  have hAT : Disjoint A T := by
    apply Finset.disjoint_left.mpr
    intro a ha ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    exact Set.disjoint_left.mp (haB j) ha (hrep j)
  have hT : T.card = Fintype.card J := by
    simp [T, Finset.card_image_of_injective _ hinj]
  obtain ⟨D⟩ := double_packing G A T hAT hc (hT ▸ hcard)
  have htar : ∀ i : ↥A × Bool, ∃ j, rep j = (D.target i).val := by
    intro i
    obtain ⟨j, _, heq⟩ := Finset.mem_image.mp (D.target i).property
    exact ⟨j, heq⟩
  choose idx hidx using htar
  refine ⟨⟨fun i => ⟨(D.target i).val, D.route i⟩, idx, ?_, ?_, D.overlap⟩⟩
  · intro i j hij
    apply D.target_injective
    apply Subtype.ext
    rw [← hidx i, ← hidx j, hij]
  · intro i
    change (D.target i).val ∈ B (idx i)
    rw [← hidx]
    exact hrep (idx i)

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
-- module Solutions.OAIQW_ListHadwiger.BagContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open SimpleGraph PathPacking
open scoped Classical

namespace BagContraction
variable {V J : Type} (G : SimpleGraph V) (B : J → Set V)

lemma liftSet_connected {C : Set V} (hC : C ⊆ Remnant B)
    (hc : (G.induce C).Connected) : ((graph G B).induce (liftSet B C)).Connected := by
  let f : G.induce C →g (graph G B).induce (liftSet B C) :=
    { toFun := fun v => ⟨Sum.inl ⟨v.val, hC v.property⟩, v.property⟩
      map_rel' := by
        intro u v huv
        refine ⟨?_, u.val, rfl, v.val, rfl, huv⟩
        intro heq
        apply huv.ne
        apply Subtype.ext
        exact congrArg (fun w : Vertex B => match w with
          | .inl z => z.val
          | .inr _ => u.val) heq }
  apply hc.map f
  intro w
  rcases w with ⟨w, hw⟩
  cases w with
  | inl v => exact ⟨⟨v.val, hw⟩, rfl⟩
  | inr j => exact hw.elim

lemma liftSet_adj_target {C : Set V} (hC : C ⊆ Remnant B) {j : J}
    (h : ∃ x ∈ C, ∃ y ∈ B j, G.Adj x y) :
    ∃ w ∈ liftSet B C, (graph G B).Adj w (.inr j) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨.inl ⟨x, hC hx⟩, hx, Sum.inl_ne_inr, x, rfl, y, hy, hxy⟩

end BagContraction

namespace BagRouting
variable {V J : Type} {G : SimpleGraph V} {A : Finset V} {B : J → Set V}

lemma region_connected (D : BagRouting G (fun i : ↥A × Bool => i.1.val) B)
    (hc : ∀ j, (G.induce (B j)).Connected) (i : ↥A × Bool) :
    (G.induce (D.region i)).Connected := by
  exact SimpleGraph.induce_union_connected
    (D.paths i).2.val.connected_induce_support.preconnected (hc (D.bag i)).preconnected
    ⟨(D.paths i).1, (D.paths i).2.val.end_mem_support, D.endpoint_mem i⟩

lemma root_mem_region (D : BagRouting G (fun i : ↥A × Bool => i.1.val) B)
    (i : ↥A × Bool) : i.1.val ∈ D.region i :=
  Or.inl (D.paths i).2.val.start_mem_support

lemma region_congestion (D : BagRouting G (fun i : ↥A × Bool => i.1.val) B)
    (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hA : ∀ j, Disjoint (↑A : Set V) (B j)) (v : V) :
    (Finset.univ.filter fun i => v ∈ D.region i).card ≤ 2 := by
  classical
  let R : Finset (↥A × Bool) := Finset.univ.filter fun i => v ∈ (D.paths i).2.val.support
  let T : Finset (↥A × Bool) := Finset.univ.filter fun i => v ∈ B (D.bag i)
  have hRT : (Finset.univ.filter fun i => v ∈ D.region i) = R ∪ T := by
    ext i
    simp [R, T, region]
  have hR : R.card ≤ 2 := by
    have hle : R.card ≤ (Finset.univ : Finset Bool).card :=
      Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _) (by
        intro i hi j hj hij
        by_cases heq : i = j
        · exact heq
        have hh := D.overlap i j heq v (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hj).2
        exact Prod.ext (Subtype.ext (hh.1.symm.trans hh.2)) hij)
    simpa using hle
  by_cases hvA : v ∈ A
  · have hT : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact Set.disjoint_left.mp (hA (D.bag i)) hvA (Finset.mem_filter.mp hi).2
    simpa [hRT, hT] using hR
  · have hR1 : R.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hh := D.overlap i j hij v (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2
      exact hvA (hh.1 ▸ i.1.property)
    have hT1 : T.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hne : D.bag i ≠ D.bag j := fun hh => hij (D.bag_injective hh)
      exact Set.disjoint_left.mp (hd _ _ hne) (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2
    rw [hRT]
    exact (Finset.card_union_le R T).trans (by omega)

lemma region_avoids_unused (D : BagRouting G (fun i : ↥A × Bool => i.1.val) B)
    (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (havoid : ∀ j, j ∉ Set.range D.bag → ∀ i v,
      v ∈ (D.paths i).2.val.support → v ∉ B j)
    (j : J) (hj : j ∉ Set.range D.bag) (i : ↥A × Bool) :
    Disjoint (D.region i) (B j) := by
  apply Set.disjoint_left.mpr
  intro v hv hvj
  rcases hv with hvp | hvb
  · exact havoid j hj i v hvp hvj
  · have hne : D.bag i ≠ j := fun hh => hj ⟨i, hh⟩
    exact Set.disjoint_left.mp (hd _ _ hne) hvb hvj

end BagRouting

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

end BagRouting

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

open SimpleGraph

lemma first_district_visit {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (J : Set V) (h : ∃ z ∈ p.support, z ∈ J) :
    ∃ x ∈ J, ∃ q : G.Walk u x, ∃ r : G.Walk x v,
      p = q.append r ∧ ∀ z, z ∈ q.support → z ∈ J → z = x := by
  classical
  induction p with
  | @nil u =>
    obtain ⟨z,hz,hzJ⟩ := h
    have heq : z = u := by simpa using hz
    subst z
    exact ⟨u,hzJ,.nil,.nil,rfl,by intro z hz _; simpa using hz⟩
  | @cons u v w huv p ih =>
    by_cases hu : u ∈ J
    · exact ⟨u,hu,.nil,.cons huv p,rfl,by intro z hz _; simpa using hz⟩
    · have ht : ∃ z ∈ p.support, z ∈ J := by
        obtain ⟨z,hz,hzJ⟩ := h
        rcases (show z = u ∨ z ∈ p.support by simpa using hz) with rfl | hz
        · exact (hu hzJ).elim
        · exact ⟨z,hz,hzJ⟩
      obtain ⟨x,hx,q,r,hp,hfirst⟩ := ih ht
      refine ⟨x,hx,.cons huv q,r,?_,?_⟩
      · simp only [Walk.cons_append, hp]
      · intro z hz hzJ
        rcases (show z = u ∨ z ∈ q.support by simpa using hz) with rfl | hz
        · exact (hu hzJ).elim
        · exact hfirst z hz hzJ

lemma district_visits_exist {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (J : Set V) (h : ∃ z ∈ p.support, z ∈ J) :
    Nonempty (DistrictVisits p J) := by
  obtain ⟨x,hx,q,r,hp,hfirst⟩ := first_district_visit p J h
  have hr : ∃ z ∈ p.reverse.support, z ∈ J := by simpa using h
  obtain ⟨y,hy,q',r',hp',hfirst'⟩ := first_district_visit p.reverse J hr
  refine ⟨⟨x,y,hx,hy,q,q'.reverse,⟨r,hp⟩,?_,hfirst,?_⟩⟩
  · refine ⟨r'.reverse, ?_⟩
    have hh := congrArg Walk.reverse hp'
    simpa only [Walk.reverse_reverse, Walk.reverse_append] using hh
  · intro z hz hzJ
    exact hfirst' z (by simpa using hz) hzJ

namespace DistrictVisits
variable {V : Type} {G : SimpleGraph V} {u v : V} {p : G.Walk u v} {J : Set V}
lemma initial_subset (D : DistrictVisits p J) : D.initial.support ⊆ p.support := by
  obtain ⟨q,hq⟩ := D.initial_part
  simpa only [← hq] using (Walk.support_subset_support_append_left D.initial q)
lemma terminal_subset (D : DistrictVisits p J) : D.terminal.support ⊆ p.support := by
  obtain ⟨q,hq⟩ := D.terminal_part
  simpa only [← hq] using (Walk.support_subset_support_append_right q D.terminal)
lemma entry_on (D : DistrictVisits p J) : D.entry ∈ p.support :=
  D.initial_subset (Walk.end_mem_support _)
lemma exit_on (D : DistrictVisits p J) : D.exit ∈ p.support :=
  D.terminal_subset (Walk.start_mem_support _)
end DistrictVisits

theorem reroute_woven_district {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (J : Set V) {a b q : ℕ} (hJ : WovenOn G J a b)
    (roots : Fin a → V) (hinj : Function.Injective roots) (hr : ∀ i, roots i ∈ J)
    (x y : Fin q → V) (P : ∀ i, G.Path (x i) (y i)) (hq : q ≤ b)
    (hdisj : ∀ i j, i ≠ j → Disjoint
      {v | v ∈ (P i).val.support} {v | v ∈ (P j).val.support}) :
    ∃ M : RootedCliqueModel G roots, (∀ j, M.branch j ⊆ J) ∧
    ∃ P' : ∀ i, G.Path (x i) (y i),
      (∀ i j, i ≠ j → Disjoint
        {v | v ∈ (P' i).val.support} {v | v ∈ (P' j).val.support}) ∧
      (∀ i, (¬∃ z ∈ (P i).val.support, z ∈ J) → P' i = P i) ∧
      (∀ i v, v ∈ (P' i).val.support → v ∉ J → v ∈ (P i).val.support) ∧
      (∀ i j v, v ∈ (P' i).val.support → v ∈ M.branch j →
        v ∈ Set.range roots ∧ ∃ D : DistrictVisits (P i).val J,
          v = D.entry ∨ v = D.exit) := by
  classical
  let I : Type := {i : Fin q // ∃ z ∈ (P i).val.support, z ∈ J}
  have : Fintype I := Fintype.ofFinite _
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let D : ∀ i : I, DistrictVisits (P i.val).val J := fun i =>
    Classical.choice (district_visits_exist (P i.val).val J i.property)
  let s : Fin (Fintype.card I) → V := fun i => (D (e i)).entry
  let t : Fin (Fintype.card I) → V := fun i => (D (e i)).exit
  have hcard : Fintype.card I ≤ b := by
    calc
      Fintype.card I ≤ Fintype.card (Fin q) := Fintype.card_subtype_le _
      _ = q := Fintype.card_fin _
      _ ≤ b := hq
  have hst : ∀ i j, i ≠ j → Disjoint ({s i,t i} : Set V) {s j,t j} := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    have hi : v ∈ (P (e i).val).val.support := by
      rcases hvi with rfl | hv
      · exact (D (e i)).entry_on
      · have heq : v = t i := hv
        rw [heq]
        exact (D (e i)).exit_on
    have hj : v ∈ (P (e j).val).val.support := by
      rcases hvj with rfl | hv
      · exact (D (e j)).entry_on
      · have heq : v = t j := hv
        rw [heq]
        exact (D (e j)).exit_on
    exact Set.disjoint_left.mp (hdisj _ _ (fun h => hij (e.injective (Subtype.ext h)))) hi hj
  obtain ⟨W⟩ := hJ roots hinj hr (Fintype.card I) hcard s t
    (fun i => ⟨(D (e i)).entry_mem,(D (e i)).exit_mem⟩) hst
  have hs (i : I) : s (e.symm i) = (D i).entry :=
    congrArg (fun j : I => (D j).entry) (e.apply_symm_apply i)
  have ht (i : I) : t (e.symm i) = (D i).exit :=
    congrArg (fun j : I => (D j).exit) (e.apply_symm_apply i)
  let Q : ∀ i : I, G.Path (D i).entry (D i).exit := fun i =>
    ⟨(W.paths (e.symm i)).val.copy (hs i) (ht i), by
      simp⟩
  have hQsup (i : I) (v : V) :
      v ∈ (Q i).val.support ↔ v ∈ (W.paths (e.symm i)).val.support := by
    simp [Q]
  let P' : ∀ i, G.Path (x i) (y i) := fun i =>
    if hi : ∃ z ∈ (P i).val.support, z ∈ J then
      (((D ⟨i,hi⟩).initial.append (Q ⟨i,hi⟩).val).append (D ⟨i,hi⟩).terminal).toPath
    else P i
  have hparts (i : Fin q) (hi : ∃ z ∈ (P i).val.support, z ∈ J) (v : V)
      (hv : v ∈ (P' i).val.support) :
      v ∈ (D ⟨i,hi⟩).initial.support ∨ v ∈ (Q ⟨i,hi⟩).val.support ∨
        v ∈ (D ⟨i,hi⟩).terminal.support := by
    simp only [P',dite_eq_left hi] at hv
    have hh := Walk.support_toPath_subset_support _ hv
    simpa only [Walk.mem_support_append_iff, or_assoc] using hh
  have houtside (i : Fin q) (v : V) (hv : v ∈ (P' i).val.support) (hn : v ∉ J) :
      v ∈ (P i).val.support := by
    by_cases hi : ∃ z ∈ (P i).val.support, z ∈ J
    · rcases hparts i hi v hv with hpre | hrep | hsuf
      · exact (D ⟨i,hi⟩).initial_subset hpre
      · exact (hn (W.path_subset _ v ((hQsup _ _).mp hrep))).elim
      · exact (D ⟨i,hi⟩).terminal_subset hsuf
    · simpa only [P',dite_eq_right hi] using hv
  have hinside (i : Fin q) (v : V) (hv : v ∈ (P' i).val.support) (hvJ : v ∈ J) :
      ∃ hi : ∃ z ∈ (P i).val.support, z ∈ J, v ∈ (Q ⟨i,hi⟩).val.support := by
    by_cases hi : ∃ z ∈ (P i).val.support, z ∈ J
    · refine ⟨hi,?_⟩
      rcases hparts i hi v hv with hpre | hrep | hsuf
      · rw [(D ⟨i,hi⟩).first v hpre hvJ]
        exact Walk.start_mem_support _
      · exact hrep
      · rw [(D ⟨i,hi⟩).last v hsuf hvJ]
        exact Walk.end_mem_support _
    · exact (hi ⟨v,by simpa only [P',dite_eq_right hi] using hv,hvJ⟩).elim
  refine ⟨W.model,W.branch_subset,P',?_,?_,houtside,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    by_cases hvJ : v ∈ J
    · obtain ⟨hi,hQi⟩ := hinside i v hvi hvJ
      obtain ⟨hj,hQj⟩ := hinside j v hvj hvJ
      have hne : e.symm ⟨i,hi⟩ ≠ e.symm ⟨j,hj⟩ := by
        intro h
        exact hij (congrArg Subtype.val (e.symm.injective h))
      exact Set.disjoint_left.mp (W.disjoint _ _ hne) ((hQsup _ _).mp hQi) ((hQsup _ _).mp hQj)
    · exact Set.disjoint_left.mp (hdisj i j hij) (houtside i v hvi hvJ) (houtside j v hvj hvJ)
  · intro i hi
    simp only [P',dite_eq_right hi]
  · intro i j v hv hm
    obtain ⟨hi,hQi⟩ := hinside i v hv (W.branch_subset j hm)
    have hc := W.clean (e.symm ⟨i,hi⟩) j v ((hQsup _ _).mp hQi) hm
    refine ⟨hc.1,D ⟨i,hi⟩,?_⟩
    simpa only [hs,ht] using hc.2

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
-- module Solutions.OAIQW_ListHadwiger.Fractional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

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

lemma cover_comap {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {μ : Finset V → ℝ} (hμ : Cover G μ) (f : W → V) :
    ∃ ν, Cover (G.comap f) ν ∧ cost ν = cost μ := by
  classical
  let pull : Finset V → Finset W := fun I => Finset.univ.filter (fun w => f w ∈ I)
  let ν := transport μ pull
  have hstable (I : Finset V) (hI : Stable G I) : Stable (G.comap f) (pull I) := by
    intro u hu v hv hadj
    exact hI (f u) (Finset.mem_filter.mp hu).2 (f v) (Finset.mem_filter.mp hv).2 hadj
  refine ⟨ν,⟨transport_nonneg hμ.1 pull,?_,?_⟩,transport_sum μ pull⟩
  · intro J hn
    apply Finset.sum_eq_zero
    intro I _
    split_ifs with he
    · apply hμ.2.1 I
      intro hI
      apply hn
      rw [← he]
      exact hstable I hI
    · rfl
  · intro w
    change 1 ≤ marginal ν w
    rw [marginal_eq_expect,transport_expect]
    have he (I : Finset V) : indicator (pull I) w = indicator I (f w) := by
      simp [indicator,pull]
    simp only [he,← marginal_eq_expect]
    exact hμ.2.2 (f w)

lemma number_comap {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (f : W → V) : number (G.comap f) ≤ number G := by
  obtain ⟨μ,hμ,heq⟩ := optimum_exists G
  obtain ⟨ν,hν,hcost⟩ := cover_comap hμ f
  exact (number_le_cost hν).trans_eq (hcost.trans heq)

end LinearListHadwiger.Fractional

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

theorem packing_from_many_neighbors {I : Type} [Fintype I]
    (G : SimpleGraph V) (A B : Finset V) (C : I → Set V) (s : I → V)
    (N : I → Finset V) (c : ℕ) (hc : 0 < c)
    (hs : ∀ i, s i ∈ A) (hsC : ∀ i, s i ∈ C i)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hN : ∀ i, N i ⊆ B) (hcard : ∀ i, A.card ≤ (N i).card)
    (hadj : ∀ i b, b ∈ N i → ∃ w ∈ C i, G.Adj w b)
    (hcon : ∀ v, (Finset.univ.filter fun i => v ∈ C i).card ≤ c)
    (hI : c * A.card ≤ Fintype.card I) : Nonempty (FullPacking G A B) := by
  classical
  apply fullPacking_of_no_small_separator
  intro X hX
  obtain ⟨i,hi⟩ := exists_region_avoiding C X c A.card hc hI hX (fun v _ => hcon v)
  have hn : ¬N i ⊆ X := fun h => (Nat.not_le_of_lt (hX.trans_le (hcard i)))
    (Finset.card_le_card h)
  simp only [Finset.subset_iff,not_forall] at hn
  obtain ⟨b,hb,hbX⟩ := hn
  obtain ⟨w,hw,hwb⟩ := hadj i b hb
  obtain ⟨p⟩ := (hC i).preconnected ⟨s i,hsC i⟩ ⟨w,hw⟩
  let q : G.Walk (s i) w := p.map (Embedding.induce (C i)).toHom
  refine ⟨s i,hs i,b,hN i hb,q.append hwb.toWalk,?_⟩
  intro v hv
  rw [Walk.mem_support_append_iff] at hv
  rcases hv with hv | hv
  · have hv' : v ∈ (p.map (Embedding.induce (C i)).toHom).support := hv
    rw [Walk.support_map] at hv'
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hv'
    exact hi z.val z.property
  · have hv' : v = w ∨ v = b := by simpa using hv
    rcases hv' with rfl | rfl
    · exact hi _ hw
    · exact hbX

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

lemma connected_of_kConnected (G : SimpleGraph V) {S : Finset V} {k : ℕ}
    (hc : KConnectedOn G S k) (hk : 0 < k) : (G.induce (↑S : Set V)).Connected := by
  exact connected_induce_congr G (Finset.sdiff_empty (s := S))
    (hc.2 ∅ (Finset.empty_subset _) (by simpa using hk))

theorem short_avoiding_path (G : SimpleGraph V) (S X : Finset V) {k : ℕ}
    (hc : KConnectedOn G S k) (hXS : X ⊆ S) (hX : X.card < k)
    {u v : V} (hu : u ∈ S \ X) (hv : v ∈ S \ X) :
    ∃ p : G.Walk u v, p.IsPath ∧
      p.length < 3 * (S.card / (k-X.card) + 1) ∧
      ∀ w ∈ p.support, w ∈ S \ X := by
  classical
  let R := S \ X
  let H := G.induce (↑R : Set V)
  have hr := delete_connected G hc hXS hX
  have hr' := induce_connected G R hr
  have hhk : 0 < k-X.card := by omega
  have hconn : H.Connected := by
    have hhh := connected_of_kConnected G hr hhk
    exact hhh
  obtain ⟨p,hp,hl⟩ := short_path H hconn hhk (fun w => min_degree H hr' (Finset.mem_univ w))
    (⟨u,hu⟩ : R) (⟨v,hv⟩ : R)
  let q : G.Walk u v := p.map (Embedding.induce (↑R : Set V)).toHom
  refine ⟨q,hp.map (f := (Embedding.induce (G := G) (↑R : Set V)).toHom) Subtype.val_injective,?_,?_⟩
  · have hcard : Fintype.card ↥R ≤ S.card := by
      simpa using Finset.card_le_card (Finset.sdiff_subset : R ⊆ S)
    have hdiv : Fintype.card ↥R / (k-X.card) ≤ S.card / (k-X.card) := Nat.div_le_div_right hcard
    change (p.map (Embedding.induce (G := G) (↑R : Set V)).toHom).length < _
    rw [Walk.length_map]
    exact hl.trans_le (by omega :
      3*(Fintype.card ↥R / (k-X.card)+1) ≤ 3*(S.card/(k-X.card)+1))
  · intro w hw
    change w ∈ (p.map (Embedding.induce (G := G) (↑R : Set V)).toHom).support at hw
    rw [Walk.support_map] at hw
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hw
    exact z.property

lemma packedBranch_source {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) (a : ↥A) : a.val ∈ packedBranch P (P.target a) :=
  Or.inr ⟨a,rfl,(P.route a).val.start_mem_support⟩

theorem root_minor_core {J : Type} [Fintype J] [DecidableEq J]
    (G : SimpleGraph V) (H : SimpleGraph J) [DecidableRel H.Adj]
    (A : Finset V) (M : MinorModel G H)
    (hc : KConnectedOn G Finset.univ (2*A.card))
    (haB : ∀ j, Disjoint (↑A : Set V) (M.branch j))
    (hdeg : ∀ j, 3*A.card ≤ (Density.neighbors H Finset.univ j).card)
    (hsize : 3*A.card ≤ Fintype.card J) :
    ∃ T : Finset J, Fintype.card J ≤ T.card + 2*A.card ∧
      ∃ N : MinorModel G (H.induce (↑T : Set J)),
      ∃ f : ↥A → ↥T, Function.Injective f ∧ ∀ a, a.val ∈ N.branch (f a) := by
  classical
  let B := M.branch
  obtain ⟨D,hD⟩ := BagRouting.exists_avoiding_unused M.disjoint
    (bagRouting_of_double_packing G A B hc M.connected M.disjoint haB (by omega))
  let Used := Finset.univ.image D.bag
  let T : Finset J := Finset.univ \ Used
  have hUsed : Used.card = 2*A.card := by
    simp [Used,Finset.card_image_of_injective _ D.bag_injective,Nat.mul_comm]
  have hTcard : Fintype.card J = T.card+2*A.card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Used)
    simpa only [Finset.card_univ,hUsed] using h.symm
  have hunused : ∀ j : ↥T, j.val ∉ Set.range D.bag := by
    intro j ⟨i,hi⟩
    exact (Finset.mem_sdiff.mp j.property).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)
  let BT : ↥T → Set V := fun j => B j.val
  let W := BagContraction.Vertex BT
  let Q := BagContraction.graph G BT
  have hreg : ∀ i : ↥A × Bool, D.region i ⊆ BagContraction.Remnant BT := by
    intro i v hv j hvj
    exact Set.disjoint_left.mp (D.region_avoids_unused M.disjoint hD j.val (hunused j) i) hv hvj
  have harem : ∀ a : ↥A, a.val ∈ BagContraction.Remnant BT := by
    intro a j hj
    exact Set.disjoint_left.mp (haB j.val) a.property hj
  let src : ↥A → W := fun a => .inl ⟨a.val,harem a⟩
  have hsrc : Function.Injective src := by
    intro a b hab
    have hh : (⟨a.val,harem a⟩ : ↥(BagContraction.Remnant BT)) = ⟨b.val,harem b⟩ := Sum.inl.inj hab
    exact Subtype.ext (congrArg (fun z : ↥(BagContraction.Remnant BT) => z.val) hh)
  let AS : Finset W := Finset.univ.image src
  let TS : Finset W := Finset.univ.image (Sum.inr : ↥T → W)
  have hAS : AS.card = A.card := by simp [AS,Finset.card_image_of_injective _ hsrc]
  let C := fun i : ↥A × Bool => BagContraction.liftSet BT (D.region i)
  have hcon : ∀ w : W, (Finset.univ.filter fun i => w ∈ C i).card ≤ 2 := by
    intro w
    cases w with
    | inl v => exact D.region_congestion M.disjoint haB v.val
    | inr j =>
      have he : (Finset.univ.filter fun i => (Sum.inr j : W) ∈ C i) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      rw [he]
      simp
  let Nbr (i : ↥A × Bool) : Finset ↥T := Finset.univ.filter fun j => H.Adj (D.bag i) j.val
  let NT (i : ↥A × Bool) : Finset W := (Nbr i).image Sum.inr
  have hNT : ∀ i, AS.card ≤ (NT i).card := by
    intro i
    have hcount : (Nbr i).card = ((Density.neighbors H Finset.univ (D.bag i)) \ Used).card := by
      have he : (Nbr i).image Subtype.val = (Density.neighbors H Finset.univ (D.bag i)) \ Used := by
        ext j
        simp only [Nbr,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
          Density.mem_neighbors,Finset.mem_sdiff]
        constructor
        · rintro ⟨w,hw,rfl⟩
          exact ⟨hw,(Finset.mem_sdiff.mp w.property).2⟩
        · rintro ⟨hj,hju⟩
          exact ⟨⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hju⟩⟩,hj,rfl⟩
      rw [← he,Finset.card_image_of_injective _ Subtype.val_injective]
    have hsplit := Finset.card_sdiff_add_card_inter (Density.neighbors H Finset.univ (D.bag i)) Used
    have hInt := Finset.card_le_card (Finset.inter_subset_right :
      Density.neighbors H Finset.univ (D.bag i) ∩ Used ⊆ Used)
    have hd := hdeg (D.bag i)
    rw [hUsed] at hInt
    rw [← hcount] at hsplit
    rw [hAS]
    dsimp [NT]
    rw [Finset.card_image_of_injective _ Sum.inr_injective]
    omega
  have hadj : ∀ i b, b ∈ NT i → ∃ w ∈ C i, Q.Adj w b := by
    intro i b hb
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    apply BagContraction.liftSet_adj_target G BT (hreg i)
    obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent (Finset.mem_filter.mp hj).2
    exact ⟨x,Or.inr hx,y,hy,hxy⟩
  obtain ⟨P⟩ := packing_from_many_neighbors Q AS TS C (fun i => src i.1) NT 2 (by omega)
    (fun i => Finset.mem_image.mpr ⟨i.1,Finset.mem_univ _,rfl⟩)
    (fun i => D.root_mem_region i)
    (fun i => BagContraction.liftSet_connected G BT (hreg i) (D.region_connected M.connected i))
    (fun i => Finset.image_subset_image (Finset.subset_univ _)) hNT hadj hcon
    (by simp [hAS,Fintype.card_prod,Nat.mul_comm])
  let MQ := BagContraction.model G BT (fun j => M.connected j.val)
    (fun i j hij => M.disjoint i.val j.val (fun h => hij (Subtype.ext h)))
  let MP := compose_model MQ (absorb_packing P)
  let fT : ↥T → ↥TS := fun j => ⟨.inr j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  have hfT : Function.Bijective fT := by
    constructor
    · intro i j hij
      exact Sum.inr_injective (congrArg Subtype.val hij)
    · intro j
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp j.property
      exact ⟨i,Subtype.ext hi⟩
  let e := Equiv.ofBijective fT hfT
  let N : MinorModel G (H.induce (↑T : Set J)) :=
    { branch := fun j => MP.branch (e j)
      connected := fun j => MP.connected (e j)
      disjoint := fun i j hij => MP.disjoint (e i) (e j) (fun h => hij (e.injective h))
      adjacent := by
        intro i j hij
        apply MP.adjacent
        change Q.Adj (.inr i) (.inr j)
        refine ⟨?_,?_⟩
        · intro h
          exact hij.ne (Sum.inr.inj h)
        · exact M.adjacent hij }
  let sA : ↥A → ↥AS := fun a => ⟨src a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩
  let f : ↥A → ↥T := fun a => e.symm (P.target (sA a))
  refine ⟨T,hTcard.le,N,f,?_,?_⟩
  · intro a b hab
    have he : P.target (sA a) = P.target (sA b) := e.symm.injective hab
    exact hsrc (congrArg Subtype.val (P.target_injective he))
  · intro a
    change a.val ∈ MP.branch (e (e.symm (P.target (sA a))))
    rw [e.apply_symm_apply]
    exact ⟨src a,packedBranch_source P (sA a),rfl⟩

theorem group_small_core {I : Type} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (A : Finset V) (label : ↥A → I)
    (hsurj : Function.Surjective label) (hA : 1 ≤ A.card)
    (r k : ℕ) (hc : KConnectedOn G Finset.univ k)
    (horder : Fintype.card V ≤ r*k) (hk : (12*r+18)*A.card ≤ k) :
    ∃ B : I → Finset V,
      (∀ i, (G.induce (↑(B i) : Set V)).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ a : ↥A, a.val ∈ B (label a)) := by
  classical
  have hI : Fintype.card I ≤ A.card := by
    simpa using Fintype.card_le_of_surjective label hsurj
  choose rep hrep using hsurj
  let d := 6*r+6
  have hex : ∀ S : Finset ↥A, ∃ B : I → Finset V,
      (∀ i, (G.induce (↑(B i) : Set V)).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i (a : ↥A), a.val ∈ B i → label a = i) ∧
      (∀ i, (rep i).val ∈ B i) ∧
      (∀ a ∈ S, a.val ∈ B (label a)) ∧
      (∑ i, (B i).card) ≤ Fintype.card I + d*S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨fun i => {(rep i).val},?_,?_,?_,?_,?_,?_⟩
      · intro i
        have : Nonempty (↑({(rep i).val} : Finset V) : Set V) := ⟨⟨(rep i).val,by simp⟩⟩
        have : Subsingleton (↑({(rep i).val} : Finset V) : Set V) := ⟨by
          intro a b
          apply Subtype.ext
          exact (Finset.mem_singleton.mp a.property).trans (Finset.mem_singleton.mp b.property).symm⟩
        exact SimpleGraph.Connected.of_subsingleton
      · intro i j hij
        apply Finset.disjoint_left.mpr
        intro v hi hj
        have he : rep i = rep j := Subtype.ext ((Finset.mem_singleton.mp hi).symm.trans (Finset.mem_singleton.mp hj))
        exact hij ((hrep i).symm.trans ((congrArg label he).trans (hrep j)))
      · intro i a ha
        have he : a = rep i := Subtype.ext (Finset.mem_singleton.mp ha)
        simpa only [he] using hrep i
      · intro i
        exact Finset.mem_singleton_self _
      · simp
      · simp
    | @insert a S ha ih =>
      obtain ⟨B,hBc,hBd,hBpure,hBr,hBS,hBcard⟩ := ih
      let i := label a
      let u := (rep i).val
      let v := a.val
      let Z := ((Finset.univ.filter (· ≠ i)).biUnion B) ∪ (A \ {u,v})
      have hS : S.card ≤ A.card := by simpa using Finset.card_le_univ S
      have hsum : (∑ j, (B j).card) ≤ (d+1)*A.card := by
        have hm := Nat.mul_le_mul_left d hS
        nlinarith
      have hZc : Z.card ≤ (d+2)*A.card := by
        have hz₁ : ((Finset.univ.filter (· ≠ i)).biUnion B).card ≤ ∑ j, (B j).card :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (by intros; omega))
        have hz₂ : (A \ {u,v}).card ≤ A.card := Finset.card_le_card Finset.sdiff_subset
        have hz := Finset.card_union_le ((Finset.univ.filter (· ≠ i)).biUnion B) (A \ {u,v})
        dsimp [Z]
        nlinarith
      have hZk : 2*Z.card < k := by dsimp [d] at hZc; nlinarith
      have huZ : u ∉ Z := by
        intro hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨j,hj,huj⟩ := Finset.mem_biUnion.mp hz
          have hp := hBpure j (rep i) huj
          exact (Finset.mem_filter.mp hj).2 (hp.symm.trans (hrep i))
        · exact (Finset.mem_sdiff.mp hz).2 (by simp [u])
      have hvZ : v ∉ Z := by
        intro hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨j,hj,hvj⟩ := Finset.mem_biUnion.mp hz
          have hp := hBpure j a hvj
          exact (Finset.mem_filter.mp hj).2 hp.symm
        · exact (Finset.mem_sdiff.mp hz).2 (by simp [v])
      obtain ⟨p,hpath,hlen,hps⟩ := short_avoiding_path G Finset.univ Z hc
        (Finset.subset_univ _) (by omega : Z.card < k)
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u,huZ⟩)
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,hvZ⟩)
      have hden : 0 < k-Z.card := by omega
      have hkden : k ≤ 2*(k-Z.card) := by omega
      have hn : Fintype.card V < (2*r+1)*(k-Z.card) := by
        have hh := Nat.mul_le_mul_left r hkden
        nlinarith
      have hdiv : Fintype.card V / (k-Z.card) < 2*r+1 :=
        (Nat.div_lt_iff_lt_mul hden).mpr (by nlinarith)
      have hlen' : p.length < d := by
        rw [Finset.card_univ] at hlen
        dsimp [d]
        omega
      let P := p.support.toFinset
      have hPc : P.card ≤ d := by
        have hh := List.toFinset_card_le p.support
        rw [Walk.length_support] at hh
        dsimp [P]
        omega
      have hpZ : ∀ w ∈ P, w ∉ Z := by
        intro w hw
        exact (Finset.mem_sdiff.mp (hps w (List.mem_toFinset.mp hw))).2
      have huP : u ∈ P := List.mem_toFinset.mpr p.start_mem_support
      have hvP : v ∈ P := List.mem_toFinset.mpr p.end_mem_support
      let B' : I → Finset V := fun j => if j = i then B j ∪ P else B j
      have hBB : ∀ j, B j ⊆ B' j := by
        intro j
        by_cases hj : j=i
        · simp only [B',ite_eq_left hj]
          exact Finset.subset_union_left
        · simp only [B',ite_eq_right hj]
          exact Finset.Subset.refl _
      have hPother : ∀ j, j ≠ i → Disjoint P (B j) := by
        intro j hj
        apply Finset.disjoint_left.mpr
        intro w hw hwj
        exact hpZ w hw (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,hwj⟩))
      refine ⟨B',?_,?_,?_,?_,?_,?_⟩
      · intro j
        by_cases hj : j=i
        · subst j
          change (G.induce (↑(if i=i then B i ∪ P else B i) : Set V)).Connected
          rw [ite_eq_left rfl,Finset.coe_union]
          have hpcon : (G.induce (↑P : Set V)).Connected := by
            have he : (↑P : Set V) = {w | w ∈ p.support} := by ext w; simp [P]
            rw [he]
            exact p.connected_induce_support
          exact SimpleGraph.induce_union_connected (hBc i).preconnected hpcon.preconnected
            ⟨u,hBr i,huP⟩
        · change (G.induce (↑(if j=i then B j ∪ P else B j) : Set V)).Connected
          rw [ite_eq_right hj]
          exact hBc j
      · intro j l hjl
        by_cases hj : j=i <;> by_cases hl : l=i
        · exact (hjl (hj.trans hl.symm)).elim
        · simp only [B',ite_eq_left hj,ite_eq_right hl]
          exact Finset.disjoint_union_left.mpr ⟨hBd j l hjl,hPother l hl⟩
        · simp only [B',ite_eq_right hj,ite_eq_left hl]
          exact Finset.disjoint_union_right.mpr ⟨hBd j l hjl,(hPother j hj).symm⟩
        · simpa only [B',ite_eq_right hj,ite_eq_right hl] using hBd j l hjl
      · intro j b hb
        by_cases hj : j=i
        · change b.val ∈ if j=i then B j ∪ P else B j at hb
          rw [ite_eq_left hj] at hb
          rcases Finset.mem_union.mp hb with hb | hb
          · exact hBpure j b hb
          · have hbuv : b.val ∈ ({u,v} : Finset V) := by
              by_contra hn
              exact hpZ b.val hb (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨b.property,hn⟩))
            rcases Finset.mem_insert.mp hbuv with hbu | hbv
            · have he : b = rep i := Subtype.ext hbu
              exact (congrArg label he).trans ((hrep i).trans hj.symm)
            · have he : b = a := Subtype.ext (Finset.mem_singleton.mp hbv)
              exact (congrArg label he).trans hj.symm
        · exact hBpure j b (by simpa only [B',ite_eq_right hj] using hb)
      · intro j
        exact hBB j (hBr j)
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · change v ∈ if i=i then B i ∪ P else B i
          rw [ite_eq_left rfl]
          exact Finset.mem_union_right _ hvP
        · exact hBB _ (hBS b hb)
      · have hstep : (∑ j, (B' j).card) ≤ (∑ j, (B j).card) + d := by
          calc
            (∑ j, (B' j).card) ≤ ∑ j, ((B j).card + if j=i then d else 0) := by
              apply Finset.sum_le_sum
              intro j _
              by_cases hj : j=i
              · simp only [B',ite_eq_left hj]
                exact (Finset.card_union_le _ _).trans (by omega)
              · simp [B',hj]
            _ = (∑ j, (B j).card)+d := by simp [Finset.sum_add_distrib]
        rw [Finset.card_insert_of_notMem ha]
        nlinarith
  obtain ⟨B,hcB,hdB,_,_,hAll,_⟩ := hex Finset.univ
  exact ⟨B,hcB,hdB,fun a => hAll a (Finset.mem_univ _)⟩

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

lemma kConnected_restrict {G : SimpleGraph V} {k z : ℕ}
    (hc : KConnectedOn G Finset.univ k) (T : Finset V)
    (hloss : Fintype.card V ≤ T.card+z) (hz : z<k) : KConnectedOn G T (k-z) := by
  classical
  let X := Finset.univ \ T
  have hsum : X.card+T.card=Fintype.card V := by
    simpa [X] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hX : X.card<k := by omega
  have hc' := delete_connected G hc (Finset.subset_univ X) hX
  have he : Finset.univ \ X=T := by ext v; simp [X]
  rw [he] at hc'
  exact kConnected_mono hc' (by omega)

lemma density_of_connectivity (G : SimpleGraph V) {k : ℕ}
    (hc : KConnectedOn G Finset.univ k) : (k : ℚ) ≤ 2*density G := by
  classical
  have hn : 0<Fintype.card V := by have := hc.1; simpa only [Finset.card_univ] using (Nat.zero_le k).trans_lt this
  have hd : ∀ v, k ≤ G.degree v := by
    intro v
    have hh := min_degree G hc (Finset.mem_univ v)
    have he : Density.neighbors G Finset.univ v=G.neighborFinset v := by ext w; simp [Density.neighbors]
    rwa [he,SimpleGraph.card_neighborFinset_eq_degree] at hh
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hd v)
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  have hsq : (Fintype.card V : ℚ)*k ≤ 2*G.edgeFinset.card := by exact_mod_cast hs
  have he := density_mul_order G hn
  have hnq : (0 : ℚ)<Fintype.card V := by exact_mod_cast hn
  nlinarith

lemma bags_meeting_bound {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (M : MinorModel G H) (A : Finset V) :
    (Finset.univ.filter fun j => ∃ a∈A, a∈M.branch j).card ≤ A.card := by
  classical
  let X := Finset.univ.filter fun j => ∃ a∈A, a∈M.branch j
  have hx : ∀ j : ↥X, ∃ a : ↥A, a.val ∈ M.branch j.val := by
    intro j
    obtain ⟨a,ha,hab⟩ := (Finset.mem_filter.mp j.property).2
    exact ⟨⟨a,ha⟩,hab⟩
  choose f hf using hx
  have hinj : Function.Injective f := by
    intro j l he
    by_contra hn
    exact Set.disjoint_left.mp (M.disjoint j.val l.val (fun h => hn (Subtype.ext h)))
      (hf j) (he ▸ hf l)
  have hh := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe,Fintype.card_coe] at hh
  exact hh

theorem group_terminals {I : Type} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (A : Finset V) (label : ↥A → I)
    (hsurj : Function.Surjective label) (hA : 1≤A.card)
    (hc : KConnectedOn G Finset.univ (65536*A.card)) :
    ∃ B : I → Set V,
      (∀ i, (G.induce (B i)).Connected) ∧
      (∀ i j, i≠j → Disjoint (B i) (B j)) ∧
      (∀ a : ↥A, a.val ∈ B (label a)) := by
  classical
  have hd := density_of_connectivity G hc
  have hm : (1 : ℚ)≤A.card := by exact_mod_cast hA
  have hdlow : (32768 : ℚ)*A.card ≤ density G := by push_cast at hd; linarith
  obtain ⟨n,k,H,⟨M⟩,hH,hsize,hdbound⟩ := small_minor_core G (by linarith)
  have hk : 4096*A.card ≤ k := by
    have hh : (4096*A.card : ℚ)<k+1 := by linarith
    have hh' : 4096*A.card<k+1 := by exact_mod_cast hh
    omega
  let X : Finset (Fin n) := Finset.univ.filter fun j => ∃ a∈A, a∈M.branch j
  have hX : X.card≤A.card := bags_meeting_bound M A
  let S : Finset (Fin n) := Finset.univ \ X
  have hSc : KConnectedOn H S (k-X.card) := delete_connected H hH (Finset.subset_univ X) (by omega)
  let L := H.induce (↑S : Set (Fin n))
  have hLc : KConnectedOn L Finset.univ (k-X.card) := induce_connected H S hSc
  let N := compose_model M (model_induce H S)
  have hbranch : ∀ j : ↥S, N.branch j = M.branch j.val := by
    intro j
    ext v
    simp only [N,compose_model,MinorModel.expand,model_induce,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    constructor
    · rintro ⟨w,hw,hv⟩
      simpa only [hw] using hv
    · exact fun hv => ⟨j.val,rfl,hv⟩
  have haB : ∀ j, Disjoint (↑A : Set V) (N.branch j) := by
    intro j
    apply Set.disjoint_left.mpr
    intro a ha hab
    exact (Finset.mem_sdiff.mp j.property).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,ha,(hbranch j) ▸ hab⟩)
  have hendegree : ∀ j, 3*A.card≤(Density.neighbors L Finset.univ j).card := by
    intro j
    exact (by omega : 3*A.card≤k-X.card).trans (min_degree L hLc (Finset.mem_univ j))
  have hlorder : 3*A.card ≤ Fintype.card ↥S := by
    have ho := hLc.1
    simp only [Finset.card_univ] at ho
    have he : Fintype.card (↑S : Set (Fin n))=S.card := Fintype.card_coe S
    erw [he] at ho
    rw [Fintype.card_coe]
    omega
  obtain ⟨T,hTcard,P,f,hf,hroot⟩ := root_minor_core G L A N
    (kConnected_mono hc (by omega)) haB hendegree hlorder
  have hloss : k-X.card-(2*A.card) ≥ k-3*A.card := by omega
  have hTc : KConnectedOn L T (k-3*A.card) := kConnected_mono
    (kConnected_restrict hLc T hTcard (by omega)) hloss
  let Q := L.induce (↑T : Set ↥S)
  have hQc : KConnectedOn Q Finset.univ (k-3*A.card) := induce_connected L T hTc
  have hQorder : Fintype.card ↥T ≤ 64*(k-3*A.card) := by
    have ht : T.card≤Fintype.card ↥S := Finset.card_le_univ T
    have hs : S.card≤n := by simpa using Finset.card_le_univ S
    have hts : T.card≤n := (by simpa using ht : T.card≤S.card).trans hs
    have hnum : n≤64*(k-3*A.card) := by omega
    simpa using hts.trans hnum
  let A' : Finset ↥T := Finset.univ.image f
  have hAcard : A'.card=A.card := by simp [A',Finset.card_image_of_injective _ hf]
  let ff : ↥A → ↥A' := fun a => ⟨f a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩
  have hff : Function.Bijective ff := by
    constructor
    · intro a b he
      exact hf (congrArg Subtype.val he)
    · intro b
      obtain ⟨a,_,ha⟩ := Finset.mem_image.mp b.property
      exact ⟨a,Subtype.ext ha⟩
  let e := Equiv.ofBijective ff hff
  let label' : ↥A' → I := fun b => label (e.symm b)
  have hsurj' : Function.Surjective label' := hsurj.comp e.symm.surjective
  obtain ⟨B,hBc,hBd,hBroot⟩ := group_small_core Q A' label' hsurj'
    (by simpa only [hAcard] using hA) 64 (k-3*A.card) hQc hQorder (by rw [hAcard]; omega)
  refine ⟨fun i => P.expand (↑(B i) : Set ↥T),?_,?_,?_⟩
  · intro i
    exact P.expand_connected (hBc i)
  · intro i j hij
    exact P.expand_disjoint (by exact_mod_cast hBd i j hij)
  · intro a
    refine ⟨f a,?_,hroot a⟩
    have hh := hBroot (e a)
    change f a ∈ B (label (e.symm (e a))) at hh
    rw [e.symm_apply_apply] at hh
    exact hh

end LinearListHadwiger.Knitting

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
-- module Solutions.OAIQW_ListHadwiger.SmallList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.SmallList
open Finset Filter

theorem schedule_cutoff : ∀ᶠ t : ℝ in atTop,
    1 < t ∧ 1 ≤ Real.log t ∧ 4*Real.log t ≤ t ∧
    t^(7/10:ℝ) ≤ t/Real.log t := by
  have hl := (Real.isLittleO_log_id_atTop).bound (show (0:ℝ)<1/4 by norm_num)
  have hp := (isLittleO_log_rpow_rpow_atTop (1:ℝ)
    (show (0:ℝ)<3/10 by norm_num)).bound (show (0:ℝ)<1 by norm_num)
  have hg := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hl,hp,hg] with t ht hl hp hg
  have ht0 : 0<t := by linarith
  have hg0 : 0<Real.log t := by linarith
  have hl' : Real.log t ≤ (1/4:ℝ)*t := by
    simpa only [id_eq,Real.norm_eq_abs,abs_of_pos hg0,abs_of_pos ht0] using hl
  have hp' : Real.log t ≤ t^(3/10:ℝ) := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hg0,
      abs_of_nonneg (Real.rpow_nonneg ht0.le (3/10:ℝ)),one_mul] using hp
  refine ⟨ht,hg,by linarith,?_⟩
  apply (le_div_iff₀ hg0).mpr
  calc
    _ ≤ t^(7/10:ℝ)*t^(3/10:ℝ) := mul_le_mul_of_nonneg_left hp' (by positivity)
    _ = t := by rw [←Real.rpow_add ht0]; norm_num

end LinearListHadwiger.SmallList

namespace LinearListHadwiger.SmallList
open Finset Fractional
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma number_iso {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : number G=number H := by
  apply le_antisymm
  · have he : G=H.comap e := by ext u v; exact e.map_adj_iff.symm
    rw [he]
    exact number_comap H e
  · have he : H=G.comap e.symm := by ext u v; exact e.symm.map_adj_iff.symm
    rw [he]
    exact number_comap G e.symm

omit [Fintype V] in
lemma obstruction_induce (G : SimpleGraph V) (R : Finset V)
    (h : FractionalObstruction (G.induce (↑R:Set V))) : FractionalObstruction G := by
  obtain ⟨A,hA⟩ := h
  let e := induceImageIso G R A
  have hm := (singletonModel _ _ e.symm e.symm.injective
    (fun {_ _} ha => e.symm.map_adj_iff.mpr ha)).hadwiger_le
  refine ⟨A.image Subtype.val,?_⟩
  rw [number_iso e] at hA
  have hm' : (hadwigerNumber (G.induce (↑(A.image Subtype.val):Set V)):ℝ) ≤
      hadwigerNumber ((G.induce (↑R:Set V)).induce (↑A:Set (↑R:Set V))) := by
    exact_mod_cast hm
  linarith

end LinearListHadwiger.SmallList

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

namespace System
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

lemma path_subset_domain (S : System G) (i : Fin S.n) : S.path i ⊆ S.domain := by
  intro v hv
  obtain ⟨w,_,rfl⟩ := mem_image.mp hv
  exact w.property

lemma mem_used (S : System G) (v : V) : v ∈ S.used ↔ ∃ i, v ∈ S.path i := by
  simp only [used,path,mem_image,BagRouting.usedFinset,mem_biUnion,mem_univ,true_and]
  aesop

lemma used_subset_domain (S : System G) : S.used ⊆ S.domain := by
  intro v hv
  obtain ⟨i,hi⟩ := (S.mem_used v).mp hv
  exact S.path_subset_domain i hi

lemma starts_card (S : System G) : S.starts.card ≤ S.n := by
  exact (card_image_le).trans (by simp)

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

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

namespace History

lemma append_final (H : History G t) (R : Round G t (H.footprint H.q)) :
    (H.append R).footprint (H.append R).q = R.final := by simp [append]

end History
end LinearListHadwiger.Footprint

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

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

variable {V I : Type} [DecidableEq V] [Fintype I] {G : SimpleGraph V}

theorem reroute_sources (J : Set V) {a b : ℕ} (hJ : WovenOn G J a b)
    (u : Fin a → V) (hu : Function.Injective u) (huJ : ∀ j, u j∈J)
    (x y : I → V) (P : ∀ i, G.Path (x i) (y i))
    (hcard : Fintype.card I ≤ b)
    (hPP : ∀ i j, i≠j → Disjoint {v | v∈(P i).val.support} {v | v∈(P j).val.support})
    (hroot : ∀ i j, u j∈(P i).val.support → u j=x i) :
    ∃ M : RootedCliqueModel G u, (∀ j, M.branch j⊆J) ∧
    ∃ Q : ∀ i, G.Path (x i) (y i),
      (∀ i j, i≠j → Disjoint {v | v∈(Q i).val.support} {v | v∈(Q j).val.support}) ∧
      (∀ i v, v∈(Q i).val.support → v∉J → v∈(P i).val.support) ∧
      (∀ i j v, v∈(Q i).val.support → v∈M.branch j → v=x i ∧ v=u j) := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  obtain ⟨M,hMJ,Q,hQQ,_,hQP,hQM⟩ := reroute_woven_district G J hJ u hu huJ
    (x ∘ e) (y ∘ e) (fun i => P (e i)) hcard
    (fun i j hij => hPP _ _ (fun h => hij (e.injective h)))
  let Q' : ∀ i, G.Path (x i) (y i) := fun i =>
    ⟨(Q (e.symm i)).val.copy (congrArg x (e.apply_symm_apply i))
      (congrArg y (e.apply_symm_apply i)),by simp⟩
  have hsup (i : I) (v : V) : v∈(Q' i).val.support ↔ v∈(Q (e.symm i)).val.support := by
    simp [Q']
  refine ⟨M,hMJ,Q',?_,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hv hw
    exact Set.disjoint_left.mp (hQQ _ _ (fun h => hij (e.symm.injective h)))
      ((hsup i v).mp hv) ((hsup j v).mp hw)
  · intro i v hv hvJ
    have he := congrArg (fun j => (P j).val.support) (e.apply_symm_apply i)
    exact he ▸ hQP _ v ((hsup i v).mp hv) hvJ
  · intro i j v hv hvm
    obtain ⟨⟨j',rfl⟩,D,hD⟩ := hQM _ j v ((hsup i v).mp hv) hvm
    have horig : u j'∈(P i).val.support := by
      have he := congrArg (fun j => (P j).val.support) (e.apply_symm_apply i)
      rw [←he]
      rcases hD with hd | hd
      · exact hd.symm ▸ D.entry_on
      · exact hd.symm ▸ D.exit_on
    have he := hroot i j' horig
    have hj : j'=j := by
      by_contra hne
      exact Set.disjoint_left.mp (M.disjoint j' j hne) (M.root_mem j') hvm
    exact ⟨he,congrArg u hj⟩

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

omit [DecidableEq V] in
lemma start_injective (R : RoleRouting G w u F H D U) :
    Function.Injective (roleStart w u R.fresh) := by
  intro p q he
  by_contra hpq
  exact Set.disjoint_left.mp (R.disjoint p q hpq) (R.route p).val.start_mem_support
    (Eq.mpr (congrArg (fun v => v∈(R.route q).val.support) he) (R.route q).val.start_mem_support)

omit [DecidableEq V] in
lemma target_injective (R : RoleRouting G w u F H D U) : Function.Injective R.target := by
  intro p q he
  by_contra hpq
  exact Set.disjoint_left.mp (R.disjoint p q hpq) (R.route p).val.end_mem_support
    (Eq.mpr (congrArg (fun v => v∈(R.route q).val.support) (congrArg Subtype.val he))
      (R.route q).val.end_mem_support)

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

theorem weave (R : RoleRouting G w u F H D U) (J : Set V) {b : ℕ}
    (hJ : WovenOn G J a b) (hu : Function.Injective u) (huJ : ∀ j, u j∈J)
    (hc : 2*t+a≤b) (hJF : Disjoint J F) (hJH : Disjoint J H)
    (hJD : Disjoint J (↑D : Set V)) :
    ∃ M : RootedCliqueModel G u, (∀ j, M.branch j⊆J) ∧
    ∃ R' : RoleRouting G w u F H D (U∪J), R'.fresh=R.fresh ∧
      ∀ p j v, v∈(R'.route p).val.support → v∈M.branch j → p=Sum.inr (Sum.inl j) := by
  have hcard : Fintype.card (Roles t a)≤b := by simpa [Roles,show t+(a+t)=2*t+a by omega] using hc
  obtain ⟨M,hMJ,Q,hQQ,hQP,hQM⟩ := reroute_sources J hJ u hu huJ
    (roleStart w u R.fresh) (fun p => (R.target p).val) R.route hcard R.disjoint R.root_only
  let R' : RoleRouting G w u F H D (U∪J) :=
    { fresh := R.fresh
      fresh_injective := R.fresh_injective
      fresh_mem := R.fresh_mem
      target := R.target
      route := Q
      disjoint := hQQ
      old_only := fun p v hv hvF => R.old_only p v
        (hQP p v hv (fun hvJ => Set.disjoint_left.mp hJF hvJ hvF)) hvF
      new_only := fun p v hv hvH => R.new_only p v
        (hQP p v hv (fun hvJ => Set.disjoint_left.mp hJH hvJ hvH)) hvH
      root_only := fun p j hv => (hQM p j (u j) hv (M.root_mem j)).1
      target_only := fun p v hv hvD => R.target_only p v
        (hQP p v hv (fun hvJ => Set.disjoint_left.mp hJD hvJ hvD)) hvD
      inside := fun p v hv => by
        by_cases hvJ : v∈J
        · exact Or.inr hvJ
        · exact Or.inl (R.inside p v (hQP p v hv hvJ)) }
  refine ⟨M,hMJ,R',rfl,?_⟩
  intro p j v hv hvm
  obtain ⟨he,he'⟩ := hQM p j v hv hvm
  exact R.start_injective (he.symm.trans he')

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

omit [Fintype V] in
lemma Second.used_inter_region (F H D : Finset V) {n : ℕ}
    (Q : Second G F H D n) : Q.record.used∩H=Q.record.starts := by
  rw [Q.record_starts]
  ext v
  simp only [mem_inter,Q.mem_record_used,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨⟨i,hi⟩,hvH⟩
    exact ⟨i,(Q.source_only i v hi hvH).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨⟨i,(Q.route i).val.start_mem_support⟩,Q.source_mem i⟩

omit [Fintype V] in
lemma Second.starts_card (F H D : Finset V) {n : ℕ}
    (Q : Second G F H D n) : Q.record.starts.card=n := by
  rw [Q.record_starts,card_image_of_injective _ Q.source_injective,card_univ,Fintype.card_fin]

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma union_connected {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {A B : Finset V} {k : ℕ}
    (hA : KConnectedOn G A k) (hB : KConnectedOn G B k)
    (hAB : k ≤ (A∩B).card) : KConnectedOn G (A∪B) k := by
  classical
  refine ⟨hA.1.trans_le (card_le_card subset_union_left),?_⟩
  intro Z _ hZ
  have hZA : (Z∩A).card < k := (card_le_card inter_subset_left).trans_lt hZ
  have hZB : (Z∩B).card < k := (card_le_card inter_subset_left).trans_lt hZ
  have hAc := hA.2 (Z∩A) inter_subset_right hZA
  have hBc := hB.2 (Z∩B) inter_subset_right hZB
  have hn : ((A∩B)\Z).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    have hs : A∩B ⊆ Z := sdiff_eq_empty_iff_subset.mp he
    have hh := card_le_card hs
    omega
  obtain ⟨v,hv⟩ := hn
  have hvA : v∈A\(Z∩A) := by simpa using (show v∈A ∧ v∉Z from
    ⟨(mem_inter.mp (mem_sdiff.mp hv).1).1,(mem_sdiff.mp hv).2⟩)
  have hvB : v∈B\(Z∩B) := by simpa using (show v∈B ∧ v∉Z from
    ⟨(mem_inter.mp (mem_sdiff.mp hv).1).2,(mem_sdiff.mp hv).2⟩)
  have he : (↑((A∪B)\Z):Set V) = (↑(A\(Z∩A)):Set V) ∪ (↑(B\(Z∩B)):Set V) := by
    ext w
    simp only [mem_coe,mem_sdiff,mem_union,mem_inter,Set.mem_union]
    tauto
  rw [he]
  exact SimpleGraph.induce_union_connected hAc.preconnected hBc.preconnected ⟨v,hvA,hvB⟩

lemma attached_connected {V P : Type} {G : SimpleGraph V} (C : P → Set V)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p))
    (hC : ∀ p, (G.induce (C p)).Connected) (hx : ∀ p, x p∈C p) (p : P) :
    (G.induce (attached C x y paths p)).Connected :=
  SimpleGraph.induce_union_connected (hC p).preconnected
    (paths p).val.connected_induce_support.preconnected ⟨x p,hx p,(paths p).val.start_mem_support⟩

lemma extended_connected {V P I : Type} {G : SimpleGraph V}
    (E : I → Set V) (C : P → Set V) (owner : P → I)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p))
    (hE : ∀ i, (G.induce (E i)).Connected)
    (hC : ∀ p, (G.induce (C p)).Connected)
    (hx : ∀ p, x p∈C p) (hy : ∀ p, y p∈E (owner p)) (i : I) :
    (G.induce (extended E C owner x y paths i)).Connected := by
  obtain ⟨u,hu⟩ := (hE i).nonempty
  apply G.induce_connected_of_patches u (Or.inl hu)
  intro v hv
  rcases hv with hv | ⟨p,hpi,hvp⟩
  · exact ⟨E i,Set.subset_union_left,hu,hv,(hE i).preconnected _ _⟩
  · have hc := SimpleGraph.induce_union_connected (hE i).preconnected
      (attached_connected C x y paths hC hx p).preconnected
      ⟨y p,hpi ▸ hy p,Or.inr (paths p).val.end_mem_support⟩
    refine ⟨E i ∪ attached C x y paths p,?_,Or.inl hu,Or.inr hvp,hc.preconnected _ _⟩
    intro w hw
    rcases hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr ⟨p,hpi,hw⟩

lemma extended_disjoint {V P I : Type} {G : SimpleGraph V}
    (E : I → Set V) (C : P → Set V) (owner : P → I)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p))
    (hE : ∀ i j, i≠j → Disjoint (E i) (E j))
    (hC : ∀ p q, owner p≠owner q → Disjoint (C p) (C q))
    (hEC : ∀ i p, i≠owner p → Disjoint (E i) (C p))
    (hEP : ∀ i p, i≠owner p → Disjoint (E i) {v | v∈(paths p).val.support})
    (hCP : ∀ p q, owner p≠owner q → Disjoint (C p) {v | v∈(paths q).val.support})
    (hP : ∀ p q, owner p≠owner q → Disjoint {v | v∈(paths p).val.support}
      {v | v∈(paths q).val.support}) :
    ∀ i j, i≠j → Disjoint (extended E C owner x y paths i) (extended E C owner x y paths j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hv hw
  rcases hv with hv | ⟨p,hpi,hvp|hvp⟩ <;> rcases hw with hw | ⟨q,hqj,hvq|hvq⟩
  · exact Set.disjoint_left.mp (hE i j hij) hv hw
  · exact Set.disjoint_left.mp (hEC i q (hqj ▸ hij)) hv hvq
  · exact Set.disjoint_left.mp (hEP i q (hqj ▸ hij)) hv hvq
  · exact Set.disjoint_left.mp (hEC j p (hpi ▸ Ne.symm hij)) hw hvp
  · exact Set.disjoint_left.mp (hC p q (by simpa only [hpi,hqj] using hij)) hvp hvq
  · exact Set.disjoint_left.mp (hCP p q (by simpa only [hpi,hqj] using hij)) hvp hvq
  · exact Set.disjoint_left.mp (hEP j p (hpi ▸ Ne.symm hij)) hw hvp
  · exact Set.disjoint_left.mp (hCP q p (by simpa only [hpi,hqj] using Ne.symm hij)) hvq hvp
  · exact Set.disjoint_left.mp (hP p q (by simpa only [hpi,hqj] using hij)) hvp hvq

lemma satellite_subset {V P I : Type} {G : SimpleGraph V}
    (E : I → Set V) (C : P → Set V) (owner : P → I)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p)) (p : P) :
    C p ⊆ extended E C owner x y paths (owner p) :=
  fun _ hv => Or.inr ⟨p,rfl,Or.inl hv⟩

lemma extended_subset {V P I : Type} {G : SimpleGraph V}
    (E : I → Set V) (C : P → Set V) (owner : P → I)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p)) {F : Set V}
    (hE : ∀ i, E i ⊆ F) (hC : ∀ p, C p ⊆ F)
    (hP : ∀ p v, v∈(paths p).val.support → v∈F) (i : I) :
    extended E C owner x y paths i ⊆ F := by
  rintro v (hv|⟨p,_,hv|hv⟩)
  · exact hE i hv
  · exact hC p hv
  · exact hP p v hv

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem grouped_ends {V P I : Type} [Fintype V] [DecidableEq V]
    [Fintype P] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (D : Finset V) (y : P → V)
    (hy : Function.Injective y) (hyD : ∀ p, y p∈D)
    (owner : P → I) (hs : Function.Surjective owner)
    (hp : 1≤Fintype.card P) (hc : KConnectedOn G D (65536*Fintype.card P)) :
    ∃ E : I → Set V,
      (∀ i, (G.induce (E i)).Connected) ∧
      (∀ i j, i≠j → Disjoint (E i) (E j)) ∧
      (∀ i, E i⊆(↑D : Set V)) ∧ ∀ p, y p∈E (owner p) := by
  classical
  let yr : P → ↥D := fun p => ⟨y p,hyD p⟩
  have hyr : Function.Injective yr := fun _ _ he => hy (congrArg Subtype.val he)
  let A : Finset ↥D := univ.image yr
  have hAc : A.card=Fintype.card P := by rw [card_image_of_injective _ hyr,card_univ]
  have ha (p : P) : yr p∈A := mem_image.mpr ⟨p,mem_univ _,rfl⟩
  have hpre : ∀ a : ↥A, ∃ p, yr p=a.val := by
    intro a
    obtain ⟨p,_,he⟩ := mem_image.mp a.property
    exact ⟨p,he⟩
  choose idx hidx using hpre
  have hi (p : P) : idx ⟨yr p,ha p⟩=p := hyr (hidx ⟨yr p,ha p⟩)
  let lab : ↥A → I := fun a => owner (idx a)
  have hls : Function.Surjective lab := by
    intro i
    obtain ⟨p,rfl⟩ := hs i
    exact ⟨⟨yr p,ha p⟩,congrArg owner (hi p)⟩
  have hc' : KConnectedOn (G.induce (↑D : Set V)) univ (65536*A.card) := by
    rw [hAc]
    exact Knitting.induce_connected G D hc
  obtain ⟨E,hE,hEE,hterm⟩ := Knitting.group_terminals (G.induce (↑D : Set V)) A lab hls
    (by omega) hc'
  let M := Knitting.model_induce G D
  refine ⟨fun i => M.expand (E i),fun i => M.expand_connected (hE i),
    fun i j hij => M.expand_disjoint (hEE i j hij),?_,?_⟩
  · intro i v hv
    obtain ⟨w,_,hw⟩ := hv
    have he : v=w.val := hw
    exact he ▸ w.property
  · intro p
    refine ⟨yr p,?_,rfl⟩
    simpa only [lab,hi] using hterm ⟨yr p,ha p⟩

end LinearListHadwiger.Stage

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.StagePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem extend_bags {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {t a : ℕ} (ht : 0<t)
    (F J H : Set V) (D : Finset V)
    (hFJ : Disjoint F J) (hFH : Disjoint F H) (hFD : Disjoint F (↑D : Set V))
    (hJH : Disjoint J H) (hJD : Disjoint J (↑D : Set V)) (hHD : Disjoint H (↑D : Set V))
    (B : Fin t → Set V) (w : Fin t → V)
    (hB : ∀ i, (G.induce (B i)).Connected)
    (hBB : ∀ i j, i≠j → Disjoint (B i) (B j))
    (hBF : ∀ i, B i⊆F) (hwB : ∀ i, w i∈B i)
    (u : Fin a → V) (M : RootedCliqueModel G u) (hMJ : ∀ j, M.branch j⊆J)
    (label : Fin a → Fin t) (w' : Fin t → V)
    (hw' : Function.Injective w') (hw'H : ∀ i, w' i∈H)
    (y : Roles t a → V) (hy : Function.Injective y) (hyD : ∀ p, y p∈D)
    (P : ∀ p, G.Path (roleStart w u w' p) (y p))
    (hPP : ∀ p q, p≠q → Disjoint {v | v∈(P p).val.support} {v | v∈(P q).val.support})
    (hPF : ∀ p v, v∈(P p).val.support → v∈F →
      ∃ i, p=Sum.inl i ∧ v=w i)
    (hPM : ∀ p j v, v∈(P p).val.support → v∈M.branch j → p=Sum.inr (Sum.inl j))
    (hPH : ∀ p v, v∈(P p).val.support → v∈H →
      ∃ i, p=Sum.inr (Sum.inr i) ∧ v=w' i)
    (hPD : ∀ p v, v∈(P p).val.support → v∈D → v=y p)
    (hDc : KConnectedOn G D (65536*(2*t+a)))
    (F' : Set V) (hFF' : F⊆F') (hJF' : J⊆F') (hDF' : (↑D : Set V)⊆F')
    (hPF' : ∀ p v, v∈(P p).val.support → v∈F') :
    ∃ B' : Fin t → Set V,
      (∀ i, (G.induce (B' i)).Connected) ∧
      (∀ i j, i≠j → Disjoint (B' i) (B' j)) ∧
      (∀ i, B i⊆B' i) ∧ (∀ i, w' i∈B' i) ∧
      (∀ j, M.branch j⊆B' (label j)) ∧ (∀ i, B' i⊆F') := by
  classical
  let owner := roleOwner label
  have hos : Function.Surjective owner := fun i => ⟨Sum.inl i,rfl⟩
  have hrc : Fintype.card (Roles t a)=2*t+a := by simp [Roles]; omega
  obtain ⟨E,hE,hEE,hED,hyE⟩ := grouped_ends G D y hy hyD owner hos
    (by rw [hrc]; omega) (by rw [hrc]; exact hDc)
  let C : Roles t a → Set V := Sum.elim B (Sum.elim M.branch (fun i => {w' i}))
  have hC : ∀ p, (G.induce (C p)).Connected := by
    rintro (i|j|i)
    · exact hB i
    · exact M.connected j
    · change (G.induce ({w' i} : Set V)).Connected
      exact SimpleGraph.Connected.of_subsingleton
  have hx : ∀ p, roleStart w u w' p∈C p := by
    rintro (i|j|i)
    · exact hwB i
    · exact M.root_mem j
    · exact Set.mem_singleton _
  have hCC : ∀ p q, p≠q → Disjoint (C p) (C q) := by
    rintro (i|j|i) (i'|j'|i') hne
    · exact hBB i i' (fun he => hne (congrArg Sum.inl he))
    · exact hFJ.mono (hBF i) (hMJ j')
    · exact hFH.mono (hBF i) (Set.singleton_subset_iff.mpr (hw'H i'))
    · exact hFJ.symm.mono (hMJ j) (hBF i')
    · exact M.disjoint j j' (fun he => hne (congrArg (Sum.inr ∘ Sum.inl) he))
    · exact hJH.mono (hMJ j) (Set.singleton_subset_iff.mpr (hw'H i'))
    · exact hFH.symm.mono (Set.singleton_subset_iff.mpr (hw'H i)) (hBF i')
    · exact hJH.symm.mono (Set.singleton_subset_iff.mpr (hw'H i)) (hMJ j')
    · apply Set.disjoint_singleton.mpr
      intro he
      exact hne (congrArg (Sum.inr ∘ Sum.inr) (hw' he))
  have hEC : ∀ i p, Disjoint (E i) (C p) := by
    intro i
    rintro (j|j|j)
    · exact hFD.symm.mono (hED i) (hBF j)
    · exact hJD.symm.mono (hED i) (hMJ j)
    · exact hHD.symm.mono (hED i) (Set.singleton_subset_iff.mpr (hw'H j))
  have hCP : ∀ p q, p≠q → Disjoint (C p) {v | v∈(P q).val.support} := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro v hv hvq
    rcases p with i | (j|i)
    · obtain ⟨j,hq,hv'⟩ := hPF q v hvq (hBF i hv)
      have hj : i=j := by
        by_contra hne
        exact Set.disjoint_left.mp (hBB i j hne) hv (hv'.symm ▸ hwB j)
      exact hpq (hj ▸ hq.symm)
    · exact hpq (hPM q j v hvq hv).symm
    · obtain ⟨j,hq,hv'⟩ := hPH q v hvq (by
        have he : v=w' i := hv
        exact he.symm ▸ hw'H i)
      have he : v=w' i := hv
      exact hpq (congrArg (Sum.inr ∘ Sum.inr) (hw' (he.symm.trans hv')) |>.trans hq.symm)
  have hEP : ∀ i p, i≠owner p → Disjoint (E i) {v | v∈(P p).val.support} := by
    intro i p hip
    apply Set.disjoint_left.mpr
    intro v hv hvp
    have he := hPD p v hvp (hED i hv)
    exact Set.disjoint_left.mp (hEE i (owner p) hip) hv (he.symm ▸ hyE p)
  let B' := extended E C owner (roleStart w u w') y P
  refine ⟨B',extended_connected E C owner _ _ P hE hC hx hyE,
    extended_disjoint E C owner _ _ P hEE
      (fun p q hpq => hCC p q (fun he => hpq (congrArg owner he)))
      (fun i p _ => hEC i p) hEP
      (fun p q hpq => hCP p q (fun he => hpq (congrArg owner he)))
      (fun p q hpq => hPP p q (fun he => hpq (congrArg owner he))),?_,?_,?_,?_⟩
  · intro i
    exact satellite_subset E C owner _ _ P (Sum.inl i)
  · intro i
    exact satellite_subset E C owner _ _ P (Sum.inr (Sum.inr i)) rfl
  · intro j
    exact satellite_subset E C owner _ _ P (Sum.inr (Sum.inl j))
  · apply extended_subset E C owner _ _ P (fun i => (hED i).trans hDF') _ hPF'
    rintro (i|j|i) v hv
    · exact hFF' (hBF i hv)
    · exact hJF' (hMJ j hv)
    · have he : v=w' i := hv
      exact he.symm ▸ hPF' (Sum.inr (Sum.inr i)) (w' i) (P _).val.start_mem_support

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset Footprint
attribute [local instance] Classical.propDecidable

theorem extend_with_systems {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {t a : ℕ} (ht : 0<t) (F J H D : Finset V)
    (B : Fin t → Set V) (w : Fin t → V)
    (hB : ∀ i, (G.induce (B i)).Connected)
    (hBB : ∀ i j, i≠j → Disjoint (B i) (B j))
    (hBF : ∀ i, B i⊆(↑F : Set V)) (hwB : ∀ i, w i∈B i)
    (hw : Function.Injective w)
    (u : Fin a → V) (hu : Function.Injective u) (huJ : ∀ j, u j∈J)
    (label : Fin a → Fin t)
    (hJF : Disjoint J F) (hDFJ : Disjoint D (F∪J))
    (R : System G) (hRU : R.domain=univ\(F\univ.image w))
    (P : DoublePacking G (oldSources w u) D)
    (hPR : ∀ i v, v∈(P.route i).val.support → v∈R.used)
    (hH : Disjoint H (F∪J∪D∪R.used))
    (Q : Second G (univ\(F∪univ.image u)) H D (2*t))
    (hJ : WovenOn G (↑J : Set V) a (3*t)) (ha : a≤t)
    (hDc : KConnectedOn G D (65536*(2*t+a))) :
    ∃ B' : Fin t → Set V, ∃ w' : Fin t → V,
      (∀ i, (G.induce (B' i)).Connected) ∧
      (∀ i j, i≠j → Disjoint (B' i) (B' j)) ∧
      (∀ i, B i⊆B' i) ∧ (∀ i, w' i∈B' i) ∧
      (∀ j j', j≠j' → ∃ v∈B' (label j), ∃ v'∈B' (label j'), G.Adj v v') ∧
      (∀ i, B' i⊆(↑(F∪J∪D∪R.used∪Q.record.used) : Set V)) ∧
      Function.Injective w' ∧ (∀ i, w' i∈Q.record.starts) := by
  classical
  have hHF : Disjoint H F := hH.mono_right (fun v hv => by simp [hv])
  have hHJ : Disjoint H J := hH.mono_right (fun v hv => by simp [hv])
  have hHD : Disjoint H D := hH.mono_right (fun v hv => by simp [hv])
  have hHR : Disjoint H R.used := hH.mono_right subset_union_right
  have hDF : Disjoint D F := hDFJ.mono_right subset_union_left
  have hDJ : Disjoint D J := hDFJ.mono_right subset_union_right
  have hwF (i) : w i∈F := hBF i (hwB i)
  have hwu : ∀ i j, w i≠u j := fun i j he =>
    Finset.disjoint_left.mp hJF (huJ j) (he ▸ hwF i)
  have hZH : Disjoint (oldSources w u) H := by
    apply Finset.disjoint_left.mpr
    intro v hv hvH
    rcases (mem_oldSources w u v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact Finset.disjoint_left.mp hHF hvH (hwF i)
    · exact Finset.disjoint_left.mp hHJ hvH (huJ j)
  have hZD : Disjoint (oldSources w u) D := by
    apply Finset.disjoint_left.mpr
    intro v hv hvD
    rcases (mem_oldSources w u v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact Finset.disjoint_left.mp hDF hvD (hwF i)
    · exact Finset.disjoint_left.mp hDJ hvD (huJ j)
  obtain ⟨L⟩ := combine_systems F H D w u hw hu hwu hwF hZH hZD hHD R hRU P hPR hHR.symm Q
  obtain ⟨M,hMJ,L',hLf,hML⟩ := L.weave (↑J : Set V) hJ hu huJ (by omega)
    (by exact_mod_cast hJF) (by exact_mod_cast hHJ.symm) (by exact_mod_cast hDJ.symm)
  have hFsubset : (↑F : Set V)⊆(↑(F∪J∪D∪R.used∪Q.record.used) : Set V) := by
    intro v hv; simp only [mem_coe,mem_union]; tauto
  have hJsubset : (↑J : Set V)⊆(↑(F∪J∪D∪R.used∪Q.record.used) : Set V) := by
    intro v hv; simp only [mem_coe,mem_union]; tauto
  have hDsubset : (↑D : Set V)⊆(↑(F∪J∪D∪R.used∪Q.record.used) : Set V) := by
    intro v hv; simp only [mem_coe,mem_union]; tauto
  have hLsubset : ∀ p v, v∈(L'.route p).val.support → v∈F∪J∪D∪R.used∪Q.record.used := by
    intro p v hv
    have hh := L'.inside p v hv
    simp only [Set.mem_union,mem_coe,mem_union] at hh ⊢
    tauto
  have htar : Function.Injective (fun p => (L'.target p).val) :=
    fun _ _ he => L'.target_injective (Subtype.ext he)
  obtain ⟨B',hB',hBB',hOld,hTips,hModels,hFin⟩ := extend_bags G ht
    (↑F : Set V) (↑J : Set V) (↑H : Set V) D
    (by exact_mod_cast hJF.symm) (by exact_mod_cast hHF.symm) (by exact_mod_cast hDF.symm)
    (by exact_mod_cast hHJ.symm) (by exact_mod_cast hDJ.symm) (by exact_mod_cast hHD)
    B w hB hBB hBF hwB u M hMJ label L'.fresh L'.fresh_injective L'.fresh_mem
    (fun p => (L'.target p).val) htar (fun p => (L'.target p).property)
    L'.route L'.disjoint L'.old_only hML L'.new_only L'.target_only hDc
    (↑(F∪J∪D∪R.used∪Q.record.used) : Set V) hFsubset hJsubset hDsubset hLsubset
  refine ⟨B',L'.fresh,hB',hBB',hOld,hTips,?_,hFin,L'.fresh_injective,?_⟩
  · intro j j' hj
    obtain ⟨v,hv,v',hv',hvv'⟩ := M.adjacent j j' hj
    exact ⟨v,hModels j hv,v',hModels j' hv',hvv'⟩
  · intro i
    rw [hLf]
    have hvH := L.fresh_mem i
    have hused := L.inside (Sum.inr (Sum.inr i)) (L.fresh i)
      (L.route (Sum.inr (Sum.inr i))).val.start_mem_support
    have hvQ : L.fresh i∈Q.record.used := by
      rcases mem_union.mp hused with hr|hq
      · exact False.elim (Finset.disjoint_left.mp hHR hvH hr)
      · exact hq
    rw [←Q.used_inter_region]
    exact mem_inter.mpr ⟨hvQ,hvH⟩

end LinearListHadwiger.Stage

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.StageAdvance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
lemma choose_vertices {S : Finset V} {n : ℕ} (h : n≤S.card) :
    ∃ w : Fin n → V, Function.Injective w ∧ ∀ i, w i∈S := by
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq h
  let e : Fin n ≃ ↥T := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hT)).symm
  exact ⟨fun i => (e i).val,Subtype.val_injective.comp e.injective,fun i => hTS (e i).property⟩

omit [Fintype V] in
lemma overlap_of_inseparable {r b a c k : ℕ} {H H' : Finset V}
    (hn : Inseparable G r b) (hH : r≤ell G H+a) (hH' : r≤ell G H'+c)
    (ha : a≤b) (hc : c+k≤b) : k≤(H∩H').card := by
  by_contra hh
  have hcard : (H'∩H).card<k := by simpa only [inter_comm] using Nat.lt_of_not_ge hh
  have hl := ell_delete G H' (H'∩H)
  apply hn H (H'\(H'∩H)) (Finset.disjoint_left.mpr (by
    intro v hv hw
    exact (mem_sdiff.mp hw).2 (mem_inter.mpr ⟨(mem_sdiff.mp hw).1,hv⟩)))
  · omega
  · omega

lemma restore_region {t r : ℕ} (ht : 0<t) (H' F T : Finset V)
    (hc : KConnectedOn G H' ((K₀+1)*t))
    (hl : r≤ell G H'+(cf+6*(K₀+1))*t)
    (hHF : H'∩F=T) (hT : T.card=2*t)
    (w : Fin t → V) (hw : Function.Injective w) (hwT : ∀ i, w i∈T) :
    let W := univ.image w
    let H := H'\(T\W)
    KConnectedOn G H (K₀*t) ∧ r≤ell G H+ch*t ∧ H∩F=W := by
  let W := univ.image w
  have hW : W.card=t := by simp only [W,card_image_of_injective _ hw,card_univ,Fintype.card_fin]
  have hWT : W⊆T := by rintro v hv; obtain ⟨i,hi,rfl⟩ := mem_image.mp hv; exact hwT i
  have hTH : T⊆H' := by rw [←hHF]; exact inter_subset_left
  have hdel : (T\W).card=t := by have hh := card_sdiff_add_card_eq_card hWT; omega
  have hdt : (T\W).card<(K₀+1)*t := by rw [hdel]; dsimp [K₀]; omega
  have hconn := Knitting.delete_connected G hc (sdiff_subset.trans hTH) hdt
  have hlev : (K₀+1)*t-(T\W).card=K₀*t := by rw [hdel,Nat.add_mul,one_mul,Nat.add_sub_cancel]
  rw [hlev] at hconn
  refine ⟨hconn,?_,?_⟩
  · have hh := ell_delete G H' (T\W)
    rw [hdel] at hh
    change r≤ell G (H'\(T\W))+ch*t
    dsimp [ch,cf,K₀] at hl ⊢
    omega
  · ext v
    simp only [mem_inter,mem_sdiff]
    constructor
    · rintro ⟨⟨hv,hnot⟩,hf⟩
      have hvT : v∈T := hHF ▸ mem_inter.mpr ⟨hv,hf⟩
      by_contra hw
      exact hnot ⟨hvT,hw⟩
    · intro hw
      have hvT := hWT hw
      have hvHF : v∈H'∩F := hHF.symm ▸ hvT
      exact ⟨⟨(mem_inter.mp hvHF).1,fun hh => hh.2 hw⟩,(mem_inter.mp hvHF).2⟩

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t r : ℕ}

namespace State
lemma tip_region (A : State G t r) (i : Fin t) : A.tip i∈A.region := by
  have hh : A.tip i∈A.region∩A.history.footprint A.history.q := by rw [A.intersection]; simp
  exact (mem_inter.mp hh).1

lemma live_disjoint (A : State G t r) :
    Disjoint (A.region\univ.image A.tip) (A.history.footprint A.history.q) := by
  apply Finset.disjoint_left.mpr
  intro v hv hf
  exact (mem_sdiff.mp hv).2 (A.intersection ▸ mem_inter.mpr ⟨(mem_sdiff.mp hv).1,hf⟩)

theorem initial (ht : 0<t) (hr : 6*(K₀*t)<listChromaticNumber G) :
    ∃ A : State G t (listChromaticNumber G), A.history.q=0 := by
  obtain ⟨H,hHU,hHc,hHl⟩ := extract_on G univ (by dsimp [K₀]; omega : 1≤K₀*t)
    (by simpa only [ell_univ] using hr)
  obtain ⟨w,hw,hwH⟩ := choose_vertices (show t≤H.card from by have hh := hHc.1; dsimp [K₀] at hh; omega)
  let W := univ.image w
  have hW : W.card≤t := by simp only [W,card_image_of_injective _ hw,card_univ,Fintype.card_fin,le_refl]
  let A : State G t (listChromaticNumber G) := {
    history := History.initial W hW
    bag := fun i => {w i}
    tip := w
    connected := fun i => SimpleGraph.Connected.of_subsingleton
    disjoint := fun i j hij => Set.disjoint_singleton.mpr (fun he => hij (hw he))
    inside := by intro i v hv; have he : v=w i := hv; simp [History.initial,W,he]
    tip_mem := fun _ => rfl
    tip_injective := hw
    region := H
    region_conn := hHc
    region_list := by
      rw [ell_univ] at hHl
      dsimp [ch,cf,K₀] at hHl ⊢
      omega
    intersection := by
      change H∩W=W
      exact inter_eq_right.mpr (by rintro v hv; obtain ⟨i,hi,rfl⟩ := mem_image.mp hv; exact hwH i) }
  exact ⟨A,rfl⟩
end State

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t r : ℕ}

theorem second_system (A : State G t r) (ht : 0<t) (J D H' : Finset V)
    (hJH : J⊆A.region) (hDS : D⊆A.region\univ.image A.tip)
    (hJD : Disjoint J D) (hDc : KConnectedOn G D (K₀*t))
    {a : ℕ} (u : Fin a → V) (hua : a≤t) (huJ : ∀ j, u j∈J)
    (hHp : KConnectedOn G H' ((K₀+1)*t))
    (hHpFJ : Disjoint H' (A.history.footprint A.history.q∪J))
    (hover : K₀*t≤(A.region∩H').card) :
    Nonempty (Second G (univ\(A.history.footprint A.history.q∪univ.image u)) H' D (2*t)) := by
  let Z := oldSources A.tip u
  have hZ : Z.card≤2*t := by
    have h1 : (univ.image A.tip).card≤t := by simpa using card_image_le (s:=univ) (f:=A.tip)
    have h2 : (univ.image u).card≤a := by simpa using card_image_le (s:=univ) (f:=u)
    have hh := card_union_le (univ.image A.tip) (univ.image u)
    dsimp [Z,oldSources]
    omega
  have hZH : Z⊆A.region := by
    intro v hv
    rcases (mem_oldSources _ _ v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact A.tip_region i
    · exact hJH (huJ j)
  have hZH' : Disjoint Z H' := by
    apply Finset.disjoint_left.mpr
    intro v hv hvP
    rcases (mem_oldSources _ _ v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact Finset.disjoint_left.mp hHpFJ hvP (mem_union_left _ (A.tip_footprint i))
    · exact Finset.disjoint_left.mp hHpFJ hvP (mem_union_right _ (huJ j))
  have hZD : Disjoint Z D := by
    apply Finset.disjoint_left.mpr
    intro v hv hvD
    rcases (mem_oldSources _ _ v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact (mem_sdiff.mp (hDS hvD)).2 (by simp)
    · exact Finset.disjoint_left.mp hJD (huJ j) hvD
  have hconn := union_connected G A.region_conn
    (Knitting.kConnected_mono hHp (by dsimp [K₀]; omega)) hover
  have hz : Z.card<K₀*t := by dsimp [K₀]; omega
  have hconn' := Knitting.delete_connected G hconn (hZH.trans subset_union_left) hz
  have hlevel : 2*t≤K₀*t-Z.card := by dsimp [K₀]; omega
  apply Second.exists_in_region _ ((A.region∪H')\Z) _ _ _ ?_ ?_ ?_
    (Knitting.kConnected_mono hconn' hlevel)
    (by have hh := hHp.1; dsimp [K₀] at hh; omega)
    (by have hh := hDc.1; dsimp [K₀] at hh; omega)
  · intro v hv
    obtain ⟨hv,hz⟩ := mem_sdiff.mp hv
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hf
    rcases mem_union.mp hf with hf|hu
    · rcases mem_union.mp hv with hvH|hvP
      · have hw : v∈univ.image A.tip := A.intersection ▸ mem_inter.mpr ⟨hvH,hf⟩
        exact hz (mem_union_left _ hw)
      · exact Finset.disjoint_left.mp hHpFJ hvP (mem_union_left _ hf)
    · exact hz (mem_union_right _ hu)
  · intro v hv
    exact mem_sdiff.mpr ⟨mem_union_right _ hv,fun hz => Finset.disjoint_left.mp hZH' hz hv⟩
  · intro v hv
    exact mem_sdiff.mpr ⟨mem_union_left _ (mem_sdiff.mp (hDS hv)).1,
      fun hz => Finset.disjoint_left.mp hZD hz hv⟩

lemma completeRound_intersection {F H : Finset V} (R : Round G t F)
    (Q : Second G (univ\(F∪R.roots)) H R.junction (2*t))
    (hH : Disjoint H (F∪R.district∪R.junction∪R.first.used)) :
    H∩(completeRound R Q hH).final=Q.record.starts := by
  rw [←Q.used_inter_region]
  ext v
  simp only [completeRound,Round.final,mem_inter,mem_union]
  constructor
  · rintro ⟨hv,hf|hq⟩
    · exact False.elim (Finset.disjoint_left.mp hH hv (by simpa only [mem_union] using hf))
    · exact ⟨hq,hv⟩
  · rintro ⟨hq,hv⟩; exact ⟨hv,Or.inr hq⟩

end LinearListHadwiger.Stage

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.StageSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable

lemma round_connectivity_level {t a : ℕ} (h : a≤t) : 65536*(2*t+a)≤K₀*t := by
  dsimp [K₀]
  omega

theorem advance_or_obstruction : ∃ S : ℕ, ch<S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ t : ℕ, T≤t → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    hadwigerNumber G<t → 2*S*t≤listChromaticNumber G →
    Inseparable G (listChromaticNumber G) (S*t) →
    ∀ A : State G t (listChromaticNumber G), A.history.q<rounds t →
    ∀ a : ℕ, 1≤a → a≤t → a≤2*⌈(t:ℝ)/(Real.log t)^2⌉₊ →
    ∀ label : Fin a → Fin t,
    (∃ A' : State G t (listChromaticNumber G),
      A'.history.q=A.history.q+1 ∧ (∀ i, A.bag i⊆A'.bag i) ∧
      ∀ i j, i≠j → ∃ v∈A'.bag (label i), ∃ w∈A'.bag (label j), G.Adj v w) ∨
      FractionalObstruction G := by
  obtain ⟨D₀,hD₀,Td,hTd⟩ := two_districts K₀ (by decide)
  obtain ⟨Tl,hTl⟩ := History.list_loss_or_obstruction
  obtain ⟨Tw,hTw⟩ := districts_woven
  let S := ch+K₀+2*D₀+(4*32768+5)+10
  refine ⟨S,by dsimp [S]; omega,max 1 (max Td (max Tl Tw)),le_max_left _ _,?_⟩
  intro t ht V _ _ G hminor hlist hn A hq a ha hat haq label
  have ht1 : 1≤t := (le_max_left _ _).trans ht
  have htd : Td≤t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htl : Tl≤t := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have htw : Tw≤t := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  let F := A.history.footprint A.history.q
  let W := univ.image A.tip
  have hW : W.card=t := by simp only [W,card_image_of_injective _ A.tip_injective,card_univ,Fintype.card_fin]
  have hregion := A.region_list
  have hdelete := ell_delete G A.region W
  rw [hW] at hdelete
  have hdistrict : (2*D₀+4*32768+5)*t+2<ell G (A.region\W) := by
    dsimp [S,ch,cf,K₀] at hlist hregion
    nlinarith
  rcases hTd t htd V G (A.region\W) hminor hdistrict with
    ⟨J,hJS,D,hDS,hJD,hJc,hDc,hJsize,hDsize⟩|hbad
  swap
  · exact Or.inr hbad
  have hJF : Disjoint J F := A.live_disjoint.mono_left hJS
  have hDF : Disjoint D F := A.live_disjoint.mono_left hDS
  have hDFJ : Disjoint D (F∪J) := Finset.disjoint_union_right.mpr ⟨hDF,hJD.symm⟩
  have hJH : J⊆A.region := hJS.trans sdiff_subset
  have hDH : D⊆A.region := hDS.trans sdiff_subset
  obtain ⟨u,hu,huJ⟩ := choose_vertices (show a≤J.card from by
    have hh := hJc.1
    dsimp [K₀] at hh
    omega)
  let Z := oldSources A.tip u
  have hZcard : Z.card≤2*t := by
    have hh := card_union_le W (univ.image u)
    have hh' : (univ.image u).card≤a := by simpa using card_image_le (s:=univ) (f:=u)
    dsimp [Z,oldSources]
    dsimp [W] at hW hh
    omega
  have hZF : A.region⊆univ\(F\W) := by
    intro v hv
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    rintro hf
    have hw : v∈univ.image A.tip := A.intersection ▸ mem_inter.mpr ⟨hv,(mem_sdiff.mp hf).1⟩
    exact (mem_sdiff.mp hf).2 hw
  have hZH : Z⊆A.region := by
    intro v hv
    rcases (mem_oldSources _ _ v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact A.tip_region i
    · exact hJH (huJ j)
  have hZD : Disjoint Z D := by
    apply Finset.disjoint_left.mpr
    intro v hv hvD
    rcases (mem_oldSources _ _ v).mp hv with ⟨i,rfl⟩|⟨j,rfl⟩
    · exact Finset.disjoint_left.mp hDF hvD (A.tip_footprint i)
    · exact Finset.disjoint_left.mp hJD (huJ j) hvD
  obtain ⟨R,P,hRU,hRn,hRS,hRE,hPR⟩ := first_system (univ\(F\W)) A.region Z D
    hZF hZH hDH hZD (Knitting.kConnected_mono A.region_conn (by dsimp [K₀]; omega))
    (by have hh := hDc.1; dsimp [K₀] at hh; omega)
  let C := firstRound A J D hJsize hDsize hJF hDFJ u huJ R hRU hRS hRE (by omega)
  have hCfinal : C.final=F∪J∪D∪R.used := by
    simp only [C,F,Round.final,firstRound,System.empty_used,union_empty]
  have hbound : (A.history.append C).q≤rounds t := by change A.history.q+1≤rounds t; omega
  rcases hTl t htl V G (A.history.append C) hminor hbound with hfoot|hbad
  swap
  · exact Or.inr hbad
  rw [History.append_final,hCfinal] at hfoot
  have hlarge : 6*((K₀+1)*t)<ell G (univ\(F∪J∪D∪R.used)) := by
    change listChromaticNumber G≤ell G (univ\(F∪J∪D∪R.used))+cf*t at hfoot
    dsimp [S,ch,cf,K₀] at hlist hfoot ⊢
    nlinarith
  obtain ⟨H',hH's,hH'c,hH'l⟩ := extract_on G (univ\(F∪J∪D∪R.used))
    (by dsimp [K₀]; omega : 1≤(K₀+1)*t) hlarge
  have hH'list : listChromaticNumber G≤ell G H'+(cf+6*(K₀+1))*t := by
    change listChromaticNumber G≤ell G (univ\(F∪J∪D∪R.used))+cf*t at hfoot
    dsimp [cf,K₀] at hfoot hH'l ⊢
    omega
  have hH'dis : Disjoint H' (F∪J∪D∪R.used) := Finset.disjoint_left.mpr
    (fun v hv hf => (mem_sdiff.mp (hH's hv)).2 hf)
  have hover : K₀*t≤(A.region∩H').card := overlap_of_inseparable hn A.region_list hH'list
    (by dsimp [S,ch,cf,K₀]; nlinarith)
    (by dsimp [S,ch,cf,K₀]; nlinarith)
  obtain ⟨Q⟩ := second_system A (by omega) J D H' hJH hDS hJD hDc u hat huJ hH'c
    (hH'dis.mono_right (fun v hv => by simp only [mem_union] at *; tauto)) hover
  let C' := completeRound C Q hH'dis
  have hC'final : C'.final=F∪J∪D∪R.used∪Q.record.used := rfl
  have hWoven := hTw t htw a ha haq V G J hJsize hJc
  obtain ⟨B',w',hB',hBB',hOld,hwB',hAdj,hInside,hw',hwQ⟩ := extend_with_systems G (t:=t) (a:=a)
    (by omega) F J H' D A.bag A.tip A.connected A.disjoint A.inside A.tip_mem A.tip_injective
    u hu huJ label hJF hDFJ R hRU P hPR hH'dis Q hWoven hat
    (Knitting.kConnected_mono hDc (round_connectivity_level hat))
  obtain ⟨hNewC,hNewL,hNewI⟩ := restore_region (by omega) H' C'.final Q.record.starts hH'c hH'list
    (completeRound_intersection C Q hH'dis) (Q.starts_card _ _ _) w' hw' hwQ
  let A' : State G t (listChromaticNumber G) := {
    history := A.history.append C'
    bag := B'
    tip := w'
    connected := hB'
    disjoint := hBB'
    inside := by intro i; rw [History.append_final,hC'final]; exact hInside i
    tip_mem := hwB'
    tip_injective := hw'
    region := H'\(Q.record.starts\univ.image w')
    region_conn := hNewC
    region_list := hNewL
    intersection := by rw [History.append_final]; exact hNewI }
  exact Or.inl ⟨A',rfl,hOld,hAdj⟩

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Filter
attribute [local instance] Classical.propDecidable

lemma block_nonempty {t m : ℕ} (hmt : m≤t) (b : Fin m) : (block t m b).Nonempty := by
  refine ⟨⟨b.val,b.isLt.trans_le hmt⟩,?_⟩
  simp only [block,mem_filter,mem_univ,true_and]
  exact Nat.mod_eq_of_lt b.isLt

lemma block_card_le {t m q : ℕ} (hm : 0 < m) (ht : t≤q*m) (b : Fin m) :
    (block t m b).card≤q := by
  let f : ↥(block t m b) → Fin q := fun i => ⟨i.val.val/m,
    (Nat.div_lt_iff_lt_mul hm).mpr (i.val.isLt.trans_le ht)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hv := congrArg Fin.val hij
    change i.val.val/m=j.val.val/m at hv
    have hi : i.val.val%m=b.val := (mem_filter.mp i.property).2
    have hj : j.val.val%m=b.val := (mem_filter.mp j.property).2
    have hmod := Nat.mod_add_div i.val.val m
    have hmod' := Nat.mod_add_div j.val.val m
    rw [hi,hv] at hmod
    rw [hj] at hmod'
    apply Subtype.ext
    apply Fin.ext
    omega
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hinj

lemma roundSet_nonempty {t m : ℕ} (hmt : m≤t) (r : Sym2 (Fin m)) :
    (roundSet t m r).Nonempty := by
  rcases Sym2.mk_surjective r with ⟨⟨b,c⟩,rfl⟩
  exact (block_nonempty hmt b).mono subset_union_left

lemma roundSet_card_le {t m q : ℕ} (hm : 0 < m) (ht : t≤q*m) (r : Sym2 (Fin m)) :
    (roundSet t m r).card≤2*q := by
  rcases Sym2.mk_surjective r with ⟨⟨b,c⟩,rfl⟩
  change (block t m b∪block t m c).card≤2*q
  have h := card_union_le (block t m b) (block t m c)
  have hb := block_card_le hm ht b
  have hc := block_card_le hm ht c
  omega

lemma roundSet_cover {t m : ℕ} (hm : 0 < m) (i j : Fin t) :
    ∃ r, i∈roundSet t m r ∧ j∈roundSet t m r := by
  refine ⟨s(⟨i.val%m,Nat.mod_lt _ hm⟩,⟨j.val%m,Nat.mod_lt _ hm⟩),?_,?_⟩
  · exact mem_union_left _ (by simp [block])
  · exact mem_union_right _ (by simp [block])

lemma sym2_fin_card (m : ℕ) : Fintype.card (Sym2 (Fin m))=m*(m+1)/2 := by
  rw [Sym2.card,Fintype.card_fin,Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm]

lemma schedule_parameter_cutoff : ∀ᶠ t : ℝ in atTop,
    1≤⌈(Real.log t)^2⌉₊ ∧ ⌈(Real.log t)^2⌉₊≤⌊t⌋₊ ∧
    t≤(⌈t/(Real.log t)^2⌉₊:ℝ)*⌈(Real.log t)^2⌉₊ := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (2:ℝ)
    (show (0:ℝ)<1 by norm_num)).bound (show (0:ℝ)<1/2 by norm_num)
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),hlog] with t ht hl ho
  have ht0 : 0<t := by linarith
  have hl0 : 0<Real.log t := by linarith
  have hs : (Real.log t)^2≤t/2 := by
    have hh : (Real.log t)^2≤(1/2:ℝ)*t := by
      rw [←Real.rpow_natCast (Real.log t) 2]
      simpa only [Nat.cast_ofNat,Real.norm_eq_abs,Real.rpow_one,
        abs_of_nonneg (Real.rpow_nonneg hl0.le (2:ℝ)),abs_of_pos ht0] using ho
    linarith
  have hm := Nat.le_ceil ((Real.log t)^2)
  have hm1 : 1≤⌈(Real.log t)^2⌉₊ := by
    have hh : (1:ℝ)≤⌈(Real.log t)^2⌉₊ := by nlinarith
    exact_mod_cast hh
  have hfloor := Nat.lt_floor_add_one t
  have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log t))
  have hmf : (⌈(Real.log t)^2⌉₊:ℝ)≤⌊t⌋₊ := by linarith
  have hq := Nat.le_ceil (t/(Real.log t)^2)
  have hmul := mul_le_mul_of_nonneg_right hq (sq_nonneg (Real.log t))
  rw [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hl0))] at hmul
  have hmul' := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg ⌈t/(Real.log t)^2⌉₊)
  exact ⟨hm1,by exact_mod_cast hmf,hmul.trans hmul'⟩

theorem schedule_cutoff : ∃ T : ℕ, ∀ t : ℕ, T≤t →
    ∃ A : Fin (Footprint.rounds t) → Finset (Fin t),
      (∀ r, (A r).Nonempty) ∧
      (∀ r, (A r).card≤2*⌈(t:ℝ)/(Real.log t)^2⌉₊) ∧
      (∀ i j, ∃ r, i∈A r ∧ j∈A r) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp schedule_parameter_cutoff
  refine ⟨⌈T⌉₊,?_⟩
  intro t ht
  have htr : T≤(t:ℝ) := (Nat.le_ceil T).trans (by exact_mod_cast ht)
  obtain ⟨hm,hm',hq⟩ := hT t htr
  rw [Nat.floor_natCast] at hm'
  let m := ⌈(Real.log t)^2⌉₊
  let q := ⌈(t:ℝ)/(Real.log t)^2⌉₊
  have hqm : t≤q*m := by exact_mod_cast hq
  let e : Fin (Footprint.rounds t) ≃ Sym2 (Fin m) :=
    (Fintype.equivFinOfCardEq (show Fintype.card (Sym2 (Fin m))=Footprint.rounds t from
      sym2_fin_card m)).symm
  refine ⟨fun r => roundSet t m (e r),?_,?_,?_⟩
  · intro r; exact roundSet_nonempty hm' _
  · intro r; exact roundSet_card_le (by omega) hqm _
  · intro i j
    obtain ⟨r,hi,hj⟩ := roundSet_cover (m:=m) (by omega) i j
    exact ⟨e.symm r,by simpa using hi,by simpa using hj⟩

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable

theorem separability_or_obstruction : ∃ S : ℕ, 1≤S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ t : ℕ, T≤t → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    hadwigerNumber G<t → 2*S*t≤listChromaticNumber G →
    (∃ X Y : Finset V, Disjoint X Y ∧
      listChromaticNumber G≤ell G X+S*t ∧ listChromaticNumber G≤ell G Y+S*t) ∨
      FractionalObstruction G := by
  obtain ⟨S,hS,Ta,hTa,hAdvance⟩ := advance_or_obstruction
  obtain ⟨Ts,hTs⟩ := schedule_cutoff
  refine ⟨S,by omega,max Ta Ts,hTa.trans (le_max_left _ _),?_⟩
  intro t ht V _ _ G hminor hlist
  have hta : Ta≤t := (le_max_left _ _).trans ht
  have hts : Ts≤t := (le_max_right _ _).trans ht
  have ht1 : 1≤t := hTa.trans hta
  by_cases hbad : FractionalObstruction G
  · exact Or.inr hbad
  by_cases hsep : ∃ X Y : Finset V, Disjoint X Y ∧
      listChromaticNumber G≤ell G X+S*t ∧ listChromaticNumber G≤ell G Y+S*t
  · exact Or.inl hsep
  have hn : Inseparable G (listChromaticNumber G) (S*t) := by
    intro X Y hd hx hy
    exact hsep ⟨X,Y,hd,hx,hy⟩
  have hinit : 6*(K₀*t)<listChromaticNumber G := by
    dsimp [ch,cf,K₀] at hS ⊢
    nlinarith
  obtain ⟨A₀,hA₀⟩ := State.initial (by omega) hinit
  obtain ⟨A,hA,hAs,hcover⟩ := hTs t hts
  have build : ∀ n : ℕ, n≤rounds t →
      ∃ X : State G t (listChromaticNumber G), X.history.q=n ∧
        ∀ r : Fin (rounds t), r.val<n → ∀ x∈A r, ∀ y∈A r, x≠y →
          ∃ v∈X.bag x, ∃ w∈X.bag y, G.Adj v w := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨A₀,hA₀,by intro r hr; omega⟩
    | succ n ih =>
      intro hnR
      obtain ⟨X,hX,hXadj⟩ := ih (by omega)
      let r : Fin (rounds t) := ⟨n,by omega⟩
      let a := (A r).card
      let e : Fin a ≃ ↥(A r) := (Fintype.equivFinOfCardEq (by simp [a])).symm
      let label : Fin a → Fin t := fun i => (e i).val
      have ha : 1≤a := card_pos.mpr (hA r)
      have hat : a≤t := by simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ (A r))
      rcases hAdvance t hta V G hminor hlist hn X (by rw [hX]; omega)
        a ha hat (hAs r) label with ⟨Y,hY,hretain,hnew⟩|hbad'
      swap
      · exact False.elim (hbad hbad')
      refine ⟨Y,by omega,?_⟩
      intro r' hr' x hx y hy hxy
      by_cases he : r'.val=n
      · have her : r'=r := Fin.ext he
        subst r'
        let ix := e.symm ⟨x,hx⟩
        let iy := e.symm ⟨y,hy⟩
        have hix : label ix=x := by simp [label,ix]
        have hiy : label iy=y := by simp [label,iy]
        have hne : ix≠iy := by intro he'; exact hxy (hix.symm.trans ((congrArg label he').trans hiy))
        simpa only [hix,hiy] using hnew ix iy hne
      · obtain ⟨v,hv,w,hw,hvw⟩ := hXadj r' (by omega) x hx y hy hxy
        exact ⟨v,hretain x hv,w,hretain y hw,hvw⟩
  obtain ⟨X,hX,hXadj⟩ := build (rounds t) le_rfl
  have hmodel : HasCliqueMinor G t := by
    refine ⟨X.bag,X.connected,X.disjoint,?_⟩
    intro i j hij
    obtain ⟨r,hi,hj⟩ := hcover i j
    exact hXadj r r.isLt i hi j hj hij
  exact False.elim (Nat.not_le_of_lt hminor (cliqueMinor_le_hadwigerNumber hmodel))

end LinearListHadwiger.Stage

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.RecursiveDistricts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Recursion
open Finset Stage SmallList
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem separability_on : ∃ S : ℕ, 1≤S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ t : ℕ, T≤t → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (H : Finset V), hadwigerNumber G<t → 2*S*t≤ell G H →
    (∃ X⊆H, ∃ Y⊆H, Disjoint X Y ∧ ell G H≤ell G X+S*t ∧ ell G H≤ell G Y+S*t) ∨
      FractionalObstruction G := by
  obtain ⟨S,hS,T,hT,hs⟩ := separability_or_obstruction
  refine ⟨S,hS,T,hT,?_⟩
  intro t ht V _ _ G H hm hl
  rcases hs t ht (↑H:Set V) (G.induce (↑H:Set V))
    ((Knitting.model_induce G H).hadwiger_le.trans_lt hm) hl with ⟨X,Y,hd,hX,hY⟩|hb
  · left
    have himg (A : Finset (↑H:Set V)) : A.image Subtype.val⊆H := by
      rintro v hv
      obtain ⟨w,_,rfl⟩ := mem_image.mp hv
      exact w.property
    refine ⟨X.image Subtype.val,himg X,Y.image Subtype.val,himg Y,?_,?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hv hw
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
      obtain ⟨y,hy,he⟩ := mem_image.mp hw
      exact Finset.disjoint_left.mp hd hx (Subtype.val_injective he ▸ hy)
    · have he := ell_image G (Subtype.val : (↑H:Set V)→V) Subtype.val_injective X
      change ell (G.induce (↑H:Set V)) X=ell G (X.image Subtype.val) at he
      change ell G H≤ell (G.induce (↑H:Set V)) X+S*t at hX
      rwa [he] at hX
    · have he := ell_image G (Subtype.val : (↑H:Set V)→V) Subtype.val_injective Y
      change ell (G.induce (↑H:Set V)) Y=ell G (Y.image Subtype.val) at he
      change ell G H≤ell (G.induce (↑H:Set V)) Y+S*t at hY
      rwa [he] at hY
  · exact Or.inr (obstruction_induce G H hb)

theorem three_regions_oai : ∃ S : ℕ, 1≤S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ t : ℕ, T≤t → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (H : Finset V) (k R : ℕ), 1≤k → hadwigerNumber G<t →
    3*S*t≤ell G H → R+6*k+2*S*t<ell G H →
    (∃ J : Fin 3 → Finset V,
      (∀ d, J d⊆H) ∧ (∀ d e, d≠e → Disjoint (J d) (J e)) ∧
      (∀ d, KConnectedOn G (J d) k) ∧ (∀ d, R<ell G (J d))) ∨ FractionalObstruction G := by
  obtain ⟨S,hS,T,hT,hs⟩ := separability_on
  refine ⟨S,hS,T,hT,?_⟩
  intro t ht V _ _ G H k R hk hm hsep hlarge
  rcases hs t ht V G H hm (by nlinarith) with ⟨X,hXH,Y,hYH,hXY,hX,hY⟩|hb
  swap
  · exact Or.inr hb
  rcases hs t ht V G X hm (by nlinarith) with ⟨A,hAX,B,hBX,hAB,hA,hB⟩|hb
  swap
  · exact Or.inr hb
  obtain ⟨A',hA'A,hA'c,hA'l⟩ := extract_on G A hk (by nlinarith)
  obtain ⟨B',hB'B,hB'c,hB'l⟩ := extract_on G B hk (by nlinarith)
  obtain ⟨Y',hY'Y,hY'c,hY'l⟩ := extract_on G Y hk (by nlinarith)
  let J : Fin 3 → Finset V := ![A',B',Y']
  have hj (d : Fin 3) : J d⊆H ∧ KConnectedOn G (J d) k ∧ R<ell G (J d) := by
    fin_cases d
    · exact ⟨hA'A.trans (hAX.trans hXH),hA'c,by dsimp [J]; nlinarith⟩
    · exact ⟨hB'B.trans (hBX.trans hXH),hB'c,by dsimp [J]; nlinarith⟩
    · exact ⟨hY'Y.trans hYH,hY'c,by dsimp [J]; nlinarith⟩
  have hab : Disjoint A' B' := hAB.mono hA'A hB'B
  have hay : Disjoint A' Y' := hXY.mono (hA'A.trans hAX) hY'Y
  have hby : Disjoint B' Y' := hXY.mono (hB'B.trans hBX) hY'Y
  refine Or.inl ⟨J,fun d => (hj d).1,?_,fun d => (hj d).2.1,fun d => (hj d).2.2⟩
  intro d e hde
  fin_cases d <;> fin_cases e
  · exact (hde rfl).elim
  · exact hab
  · exact hay
  · exact hab.symm
  · exact (hde rfl).elim
  · exact hby
  · exact hay.symm
  · exact hby.symm
  · exact (hde rfl).elim

end LinearListHadwiger.Recursion

end OAI
end

theorem solution : type_of% @OAI.LinearListHadwiger.Recursion.three_regions_oai := @OAI.LinearListHadwiger.Recursion.three_regions_oai
