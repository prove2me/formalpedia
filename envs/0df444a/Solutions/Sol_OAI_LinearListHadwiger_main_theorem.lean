-- Prove2me | solution 1 for OAI.LinearListHadwiger.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:49:23.765954+00:00
-- url     : https://prove2.me/submissions/af693b9b-23cb-4204-b5d5-5564a56b13cd

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000
import Theorems.Thm_OAI_LinearListHadwiger_Fractional_fractional_chromatic_le_two_hadwiger
import Theorems.Thm_OAI_LinearListHadwiger_Recursion_outer_region
import Theorems.Thm_OAI_LinearListHadwiger_Recursion_three_regions

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

theorem one_le_hadwigerNumber {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : 1 ≤ hadwigerNumber G :=
  cliqueMinor_le_hadwigerNumber (cliqueMinor_one G)

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

theorem rootedModel_of_packing {V W : Type} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (M : MinorModel G H)
    {A B : Finset W} (D : FullPacking H A B)
    (hcl : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → H.Adj x y)
    (roots : ↥A → V) (hr : ∀ a, roots a ∈ M.branch a.val) :
    Nonempty (RootedCliqueModel G roots) := by
  let S : ↥A → Set W := fun a => {w | w ∈ (D.route a).val.support}
  refine ⟨⟨fun a => M.expand (S a), ?_, ?_, ?_, ?_⟩⟩
  · intro a
    exact M.expand_connected (D.route a).val.connected_induce_support
  · intro a b hab
    exact M.expand_disjoint (D.disjoint a b hab)
  · intro a b hab
    have hne : (D.target a).val ≠ (D.target b).val := by
      intro h
      exact hab (D.target_injective (Subtype.ext h))
    obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent
      (hcl _ (D.target a).property _ (D.target b).property hne)
    exact ⟨x, ⟨_, (D.route a).val.end_mem_support, hx⟩,
      y, ⟨_, (D.route b).val.end_mem_support, hy⟩, hxy⟩
  · intro a
    exact ⟨a.val, (D.route a).val.start_mem_support, hr a⟩

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

theorem packing_from_regions {V I : Type} [Fintype V] [Fintype I]
    [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    (C : I → Set V) (s : I → V) (c : ℕ) (hc : 0 < c)
    (hs : ∀ i, s i ∈ A) (hsC : ∀ i, s i ∈ C i)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hadj : ∀ i b, b ∈ B → ∃ w ∈ C i, G.Adj w b)
    (hcon : ∀ v, (Finset.univ.filter fun i => v ∈ C i).card ≤ c)
    (hI : c * A.card ≤ Fintype.card I) (hB : A.card ≤ B.card) :
    Nonempty (FullPacking G A B) := by
  classical
  apply fullPacking_of_no_small_separator
  intro X hX
  obtain ⟨i, hi⟩ := exists_region_avoiding C X c A.card hc hI hX (fun v _ => hcon v)
  have hn : ¬B ⊆ X := fun h => (Nat.not_le_of_lt (hX.trans_le hB)) (Finset.card_le_card h)
  simp only [Finset.subset_iff, not_forall] at hn
  obtain ⟨b, hb, hbX⟩ := hn
  obtain ⟨w, hw, hwb⟩ := hadj i b hb
  obtain ⟨p⟩ := (hC i).preconnected ⟨s i, hsC i⟩ ⟨w, hw⟩
  let q : G.Walk (s i) w := p.map (Embedding.induce (C i)).toHom
  refine ⟨s i, hs i, b, hb, q.append hwb.toWalk, ?_⟩
  intro v hv
  rw [Walk.mem_support_append_iff] at hv
  rcases hv with hv | hv
  · have hv' : v ∈ (p.map (Embedding.induce (C i)).toHom).support := hv
    rw [Walk.support_map] at hv'
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hv'
    exact hi z.val z.property
  · have hv' : v = w ∨ v = b := by simpa using hv
    rcases hv' with rfl | rfl
    · exact hi _ hw
    · exact hbX

theorem rooting_from_eligible {V J : Type} [Fintype V] [Fintype J]
    [DecidableEq V] (G : SimpleGraph V) (A : Finset V) (B : J → Set V)
    (hc : KConnectedOn G Finset.univ (2 * A.card))
    (hcB : ∀ j, (G.induce (B j)).Connected)
    (hdB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (haB : ∀ j, Disjoint (↑A : Set V) (B j))
    (heB : ∀ i j, i ≠ j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y)
    (hcard : 3 * A.card ≤ Fintype.card J) :
    Nonempty (RootedCliqueModel G (fun a : ↥A => a.val)) := by
  classical
  obtain ⟨D, hD⟩ := BagRouting.exists_avoiding_unused hdB
    (bagRouting_of_double_packing G A B hc hcB hdB haB (by omega))
  let T : Finset J := Finset.univ \ Finset.univ.image D.bag
  have hT : A.card ≤ T.card := by
    have hi : (Finset.univ.image D.bag).card = 2 * A.card := by
      simp [Finset.card_image_of_injective _ D.bag_injective, Nat.mul_comm]
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Finset.univ.image D.bag))
    simp only [Finset.card_univ] at hh
    dsimp [T]
    omega
  have hunused : ∀ j : ↥T, j.val ∉ Set.range D.bag := by
    intro j ⟨i, hi⟩
    exact (Finset.mem_sdiff.mp j.property).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  let BT : ↥T → Set V := fun j => B j.val
  let W := BagContraction.Vertex BT
  let H := BagContraction.graph G BT
  have hreg : ∀ i : ↥A × Bool, D.region i ⊆ BagContraction.Remnant BT := by
    intro i v hv j hvj
    exact Set.disjoint_left.mp (D.region_avoids_unused hdB hD j.val (hunused j) i) hv hvj
  have harem : ∀ a : ↥A, a.val ∈ BagContraction.Remnant BT := by
    intro a j hj
    exact Set.disjoint_left.mp (haB j.val) a.property hj
  let src : ↥A → W := fun a => .inl ⟨a.val, harem a⟩
  have hsrc : Function.Injective src := by
    intro a b hab
    have hh : (⟨a.val, harem a⟩ : ↥(BagContraction.Remnant BT)) = ⟨b.val, harem b⟩ := Sum.inl.inj hab
    apply Subtype.ext
    exact congrArg (fun z : ↥(BagContraction.Remnant BT) => z.val) hh
  let AS : Finset W := Finset.univ.image src
  let TS : Finset W := Finset.univ.image (Sum.inr : ↥T → W)
  have hAS : AS.card = A.card := by simp [AS, Finset.card_image_of_injective _ hsrc]
  have hTS : TS.card = T.card := by
    simp [TS, Finset.card_image_of_injective _ Sum.inr_injective]
  let C := fun i : ↥A × Bool => BagContraction.liftSet BT (D.region i)
  have hcon : ∀ w : W, (Finset.univ.filter fun i => w ∈ C i).card ≤ 2 := by
    intro w
    cases w with
    | inl v => exact D.region_congestion hdB haB v.val
    | inr j =>
      have he : (Finset.univ.filter fun i => (Sum.inr j : W) ∈ C i) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hh : False := (Finset.mem_filter.mp hi).2
        exact hh
      rw [he]
      simp
  have hadj : ∀ i b, b ∈ TS → ∃ w ∈ C i, H.Adj w b := by
    intro i b hb
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    apply BagContraction.liftSet_adj_target G BT (hreg i)
    have hne : D.bag i ≠ j.val := fun hh => hunused j ⟨i, hh⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := heB _ _ hne
    exact ⟨x, Or.inr hx, y, hy, hxy⟩
  obtain ⟨P⟩ := packing_from_regions H AS TS C (fun i => src i.1) 2 (by omega)
    (fun i => Finset.mem_image.mpr ⟨i.1, Finset.mem_univ _, rfl⟩)
    (fun i => D.root_mem_region i)
    (fun i => BagContraction.liftSet_connected G BT (hreg i) (D.region_connected hcB i))
    hadj hcon (by simp [hAS, Fintype.card_prod, Nat.mul_comm]) (by omega)
  let M := BagContraction.model G BT (fun j => hcB j.val)
    (fun i j hij => hdB i.val j.val (fun h => hij (Subtype.ext h)))
  have hcl : ∀ x ∈ TS, ∀ y ∈ TS, x ≠ y → H.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨hxy, ?_⟩
    exact heB i.val j.val (fun h => hxy (congrArg Sum.inr (Subtype.ext h)))
  have hroot : ∀ a : ↥AS, ∃ v : V, v ∈ M.branch a.val := by
    intro a
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp a.property
    exact ⟨i.val, by rw [← hi]; exact rfl⟩
  choose r hr using hroot
  obtain ⟨N⟩ := rootedModel_of_packing M P hcl r hr
  let f : ↥A → ↥AS := fun a => ⟨src a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Injective f := fun _ _ h => hsrc (congrArg Subtype.val h)
  have heq : r ∘ f = fun a : ↥A => a.val := by
    funext a
    exact hr (f a)
  rw [← heq]
  exact ⟨N.reindex f hf⟩

lemma eligible_bags_card {V J : Type} [Fintype J] [DecidableEq V]
    (A : Finset V) (B : J → Set V)
    (hdB : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    Fintype.card J ≤ (Finset.univ.filter fun j => Disjoint (↑A : Set V) (B j)).card + A.card := by
  classical
  let E : Finset J := Finset.univ.filter fun j => Disjoint (↑A : Set V) (B j)
  let Q := Finset.univ \ E
  have hex : ∀ j : ↥Q, ∃ v : ↥A, v.val ∈ B j.val := by
    intro j
    have hn : ¬Disjoint (↑A : Set V) (B j.val) := by
      intro h
      exact (Finset.mem_sdiff.mp j.property).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    by_contra hh
    apply hn
    apply Set.disjoint_left.mpr
    intro v hv hvB
    exact hh ⟨⟨v, hv⟩, hvB⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hn
    exact Set.disjoint_left.mp (hdB i.val j.val (fun h => hn (Subtype.ext h)))
      (hf i) (hij ▸ hf j)
  have hQ : Q.card ≤ A.card := by simpa using Fintype.card_le_of_injective f hinj
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
  simp only [Finset.card_univ] at hsum
  change Fintype.card J ≤ E.card + A.card
  dsimp [Q] at hQ
  omega

theorem rooting {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V)
    (hc : KConnectedOn G Finset.univ (2 * A.card))
    (hh : 4 * A.card ≤ hadwigerNumber G) :
    Nonempty (RootedCliqueModel G (fun a : ↥A => a.val)) := by
  classical
  obtain ⟨B, hcB, hdB, heB⟩ := hasCliqueMinor_hadwigerNumber G
  let E : Finset (Fin (hadwigerNumber G)) :=
    Finset.univ.filter fun j => Disjoint (↑A : Set V) (B j)
  apply rooting_from_eligible G A (fun j : ↥E => B j.val) hc
  · exact fun j => hcB j.val
  · exact fun i j hij => hdB i.val j.val (fun h => hij (Subtype.ext h))
  · exact fun j => (Finset.mem_filter.mp j.property).2
  · exact fun i j hij => heB i.val j.val (fun h => hij (Subtype.ext h))
  · have hE := eligible_bags_card A B hdB
    simp only [Fintype.card_fin] at hE
    simp only [Fintype.card_coe]
    change hadwigerNumber G ≤ E.card + A.card at hE
    omega

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
-- module Solutions.OAIQW_ListHadwiger.Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Assembly
open SimpleGraph
variable {V I O : Type} (G : SimpleGraph V)

lemma connected_glue (C : Set V) (B : O → Set V)
    (hC : (G.induce C).Connected)
    (hB : ∀ o, (G.induce (B o)).Connected)
    (hE : ∀ o, ∃ x ∈ B o, ∃ y ∈ C, G.Adj x y) :
    (G.induce (C ∪ {v | ∃ o, v ∈ B o})).Connected := by
  let S := C ∪ {v | ∃ o, v ∈ B o}
  have hCS : C ⊆ S := Set.subset_union_left
  obtain ⟨root⟩ := hC.nonempty
  have hreach : ∀ v : S, (G.induce S).Reachable v ⟨root.val,hCS root.property⟩ := by
    rintro ⟨v,hv⟩
    rcases hv with hv | ⟨o,hv⟩
    · exact (hC.preconnected ⟨v,hv⟩ root).map (G.induceHomOfLE hCS).toHom
    · obtain ⟨x,hx,y,hy,hxy⟩ := hE o
      have hBS : B o ⊆ S := fun _ hw => Or.inr ⟨o,hw⟩
      have h₁ := ((hB o).preconnected ⟨v,hv⟩ ⟨x,hx⟩).map
        (G.induceHomOfLE hBS).toHom
      have h₂ : (G.induce S).Adj ⟨x,hBS hx⟩ ⟨y,hCS hy⟩ := hxy
      have h₃ := (hC.preconnected ⟨y,hy⟩ root).map (G.induceHomOfLE hCS).toHom
      exact h₁.trans (h₂.reachable.trans h₃)
  refine { preconnected := ?_, nonempty := ⟨⟨root.val,hCS root.property⟩⟩ }
  intro v w
  exact (hreach v).trans (hreach w).symm

lemma attach_ports [Fintype V] [Fintype O] [DecidableEq V] [DecidableRel G.Adj]
    (port : O → V) (U : Finset V)
    (hN : ∀ o, Fintype.card O ≤ (U.filter (fun v => G.Adj (port o) v)).card) :
    ∃ nbr : O → V, Function.Injective nbr ∧ ∀ o, nbr o ∈ U ∧ G.Adj (port o) (nbr o) := by
  classical
  let N (o : O) := U.filter (fun v => G.Adj (port o) v)
  have hall : ∀ S : Finset O, S.card ≤ (S.biUnion N).card := by
    intro S
    obtain rfl | hS := S.eq_empty_or_nonempty
    · simp
    obtain ⟨o,ho⟩ := hS
    exact (Finset.card_le_univ S).trans ((hN o).trans
      (Finset.card_le_card (Finset.subset_biUnion_of_mem N ho)))
  obtain ⟨nbr,hi,hn⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hall
  exact ⟨nbr,hi,fun o => Finset.mem_filter.mp (hn o)⟩

end LinearListHadwiger.Assembly

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

theorem coarse_list_bound (G : SimpleGraph V) {t : ℕ} (ht : 2≤t)
    (hex : hadwigerNumber G<t) :
    listChromaticNumber G ≤ ⌊200000000*t*Real.log (2*t)⌋₊+1 := by
  classical
  apply listChromaticNumber_le_of_degenerate
  intro S _ hS
  have : Nonempty (↑S : Set V) := by obtain ⟨v,hv⟩ := hS; exact ⟨⟨v,hv⟩⟩
  let H := G.induce (↑S : Set V)
  have hm : hadwigerNumber H ≤ hadwigerNumber G :=
    cliqueMinor_le_hadwigerNumber ((model_induce G S).lift_clique (hasCliqueMinor_hadwigerNumber H))
  have hd := density_bound H ht (hm.trans_lt hex)
  obtain ⟨v,hv⟩ := degree_le_twice_density H Fintype.card_pos
  have hv' : (H.degree v : ℝ) ≤2*((density H:ℚ):ℝ) := by exact_mod_cast hv
  have hdeg : (H.degree v : ℝ) ≤200000000*t*Real.log (2*t) := by nlinarith
  refine ⟨v.val,v.property,?_⟩
  rw [←degree_induce_finset G S v]
  exact Nat.le_floor hdeg

end LinearListHadwiger.CoarseDensity

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

end LinearListHadwiger.Stage

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
lemma target_injective (R : RoleRouting G w u F H D U) : Function.Injective R.target := by
  intro p q he
  by_contra hpq
  exact Set.disjoint_left.mp (R.disjoint p q hpq) (R.route p).val.end_mem_support
    (Eq.mpr (congrArg (fun v => v∈(R.route q).val.support) (congrArg Subtype.val he))
      (R.route q).val.end_mem_support)

end RoleRouting
end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

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
-- module Solutions.OAIQW_ListHadwiger.BagAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Assembly
open SimpleGraph Finset
variable {V O I : Type} [Fintype V] [DecidableEq V]
  [Fintype O] [Fintype I] [DecidableEq I]

omit [Fintype V] in

lemma path_in_connected {G : SimpleGraph V} {S : Set V}
    (hS : (G.induce S).Connected) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    ∃ Q : G.Path x y, ∀ v ∈ Q.val.support, v ∈ S := by
  classical
  obtain ⟨w⟩ := hS.preconnected ⟨x,hx⟩ ⟨y,hy⟩
  let f : G.induce S →g G := ⟨Subtype.val,fun he => he⟩
  let q := w.map f
  refine ⟨q.toPath,?_⟩
  intro v hv
  have hv' := q.support_toPath_subset_support hv
  dsimp [q] at hv'
  rw [Walk.support_map] at hv'
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv'
  exact u.property

end LinearListHadwiger.Assembly

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
open Finset SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma woven_induce (G : SimpleGraph V) (J : Finset V) {a b : ℕ}
    (hw : Woven (G.induce (↑J : Set V)) a b) : WovenOn G (↑J : Set V) a b := by
  classical
  intro roots hr hJ p hp x y hxy he
  let r' (i : Fin a) : (↑J : Set V) := ⟨roots i,hJ i⟩
  let x' (i : Fin p) : (↑J : Set V) := ⟨x i,(hxy i).1⟩
  let y' (i : Fin p) : (↑J : Set V) := ⟨y i,(hxy i).2⟩
  have he' : ∀ i j, i≠j → Disjoint ({x' i,y' i} : Set (↑J:Set V)) {x' j,y' j} := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hv hw
    apply Set.disjoint_left.mp (he i j hij) (show v.val∈({x i,y i}:Set V) from ?_)
      (show v.val∈({x j,y j}:Set V) from ?_)
    · simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Subtype.ext_iff,x',y'] using hv
    · simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Subtype.ext_iff,x',y'] using hw
  obtain ⟨A⟩ := hw r' (fun i j hij => hr (congrArg Subtype.val hij)) (by simp)
    p hp x' y' (by simp) he'
  let N := Knitting.model_induce G J
  let M : RootedCliqueModel G roots := {
    branch := fun i => N.expand (A.model.branch i)
    connected := fun i => N.expand_connected (A.model.connected i)
    disjoint := fun i j hij => N.expand_disjoint (A.model.disjoint i j hij)
    adjacent := by
      intro i j hij
      obtain ⟨v,hv,w,hw,hvw⟩ := A.model.adjacent i j hij
      exact ⟨v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,hvw⟩
    root_mem := fun i => ⟨r' i,A.model.root_mem i,rfl⟩ }
  let f : (G.induce (↑J:Set V)) →g G := ⟨Subtype.val,fun h => h⟩
  let paths : ∀ i, G.Path (x i) (y i) := fun i =>
    ⟨(A.paths i).val.map f,(A.paths i).property.map Subtype.val_injective⟩
  have hpath (i : Fin p) (v : V) : v∈(paths i).val.support ↔
      ∃ w : (↑J:Set V), w∈(A.paths i).val.support ∧ w.val=v := by
    simp only [paths,Walk.support_map,List.mem_map]
    rfl
  have hbranch (i : Fin a) (v : V) : v∈M.branch i ↔
      ∃ w : (↑J:Set V), w∈A.model.branch i ∧ w.val=v := by
    simp only [M,N,MinorModel.expand,Knitting.model_induce,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    constructor
    · rintro ⟨w,hw,h⟩; exact ⟨w,hw,h.symm⟩
    · rintro ⟨w,hw,h⟩; exact ⟨w,hw,h.symm⟩
  refine ⟨⟨M,?_,paths,?_,?_,?_⟩⟩
  · intro i v hv
    obtain ⟨w,hw,rfl⟩ := (hbranch i v).mp hv
    exact w.property
  · intro i v hv
    obtain ⟨w,hw,rfl⟩ := (hpath i v).mp hv
    exact w.property
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hv hw
    obtain ⟨w,hw',rfl⟩ := (hpath i v).mp hv
    obtain ⟨z,hz,heq⟩ := (hpath j w.val).mp hw
    exact Set.disjoint_left.mp (A.disjoint i j hij) hw'
      (show w∈(A.paths j).val.support from (Subtype.ext heq : z=w) ▸ hz)
  · intro i j v hv hb
    obtain ⟨w,hw,rfl⟩ := (hpath i v).mp hv
    obtain ⟨z,hz,heq⟩ := (hbranch j w.val).mp hb
    have hz' : w∈A.model.branch j := (Subtype.ext heq : z=w) ▸ hz
    obtain ⟨⟨k,hk⟩,hend⟩ := A.clean i j w hw hz'
    refine ⟨⟨k,congrArg Subtype.val hk⟩,?_⟩
    exact hend.imp (congrArg Subtype.val) (congrArg Subtype.val)

end LinearListHadwiger.Stage

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
open Finset Filter
attribute [local instance] Classical.propDecidable

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

end LinearListHadwiger.Stage

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Recursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Recursion
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem weaving_from_proxy_groups (G : SimpleGraph V) {a p : ℕ}
    (roots : Fin a → V) (x y : Fin p → V) (hr : Function.Injective roots)
    (he : ∀ i j, i ≠ j → Disjoint ({x i,y i} : Set V) {x j,y j})
    (C : (Fin a ⊕ Fin p) → Set V)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hCC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hroot : ∀ i j, roots j ∉ C i)
    (hx : ∀ i j, x j ∉ C i) (hy : ∀ i j, y j ∉ C i)
    (hclique : ∀ i j, i ≠ j → ∃ v ∈ C (.inl i), ∃ w ∈ C (.inl j), G.Adj v w)
    (hattachRoot : ∀ j, ∃ w ∈ C (.inl j), G.Adj (roots j) w)
    (hattachX : ∀ i, ∃ w ∈ C (.inr i), G.Adj (x i) w)
    (hattachY : ∀ i, ∃ w ∈ C (.inr i), G.Adj (y i) w) :
    Nonempty (WeavingWithin G Set.univ roots x y) := by
  classical
  let bag (j : Fin a) := insert (roots j) (C (.inl j))
  have hb (j : Fin a) : (G.induce (bag j)).Connected := by
    obtain ⟨w,hw,hew⟩ := hattachRoot j
    exact Incidence.connected_insert (hC (.inl j)) hw hew
  have hbd (i j : Fin a) (hij : i ≠ j) : Disjoint (bag i) (bag j) := by
    apply Set.disjoint_left.mpr
    intro v hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact hij (hr (hi.symm.trans hj))
    · exact hroot (.inl j) i (hi ▸ hj)
    · exact hroot (.inl i) j (hj ▸ hi)
    · exact Set.disjoint_left.mp (hCC (.inl i) (.inl j) (by simpa using hij)) hi hj
  let M : RootedCliqueModel G roots :=
    { branch := bag
      connected := hb
      disjoint := hbd
      adjacent := fun i j hij => by
        obtain ⟨v,hv,w,hw,hvw⟩ := hclique i j hij
        exact ⟨v,Or.inr hv,w,Or.inr hw,hvw⟩
      root_mem := fun _ => Or.inl rfl }
  let S (i : Fin p) := insert (x i) (insert (y i) (C (.inr i)))
  have hS (i : Fin p) : (G.induce (S i)).Connected := by
    obtain ⟨w,hw,hew⟩ := hattachY i
    have hh := Incidence.connected_insert (hC (.inr i)) hw hew
    obtain ⟨w,hw,hew⟩ := hattachX i
    exact Incidence.connected_insert hh (Or.inr hw) hew
  have hpaths : ∀ i, ∃ Q : G.Path (x i) (y i), ∀ v ∈ Q.val.support, v ∈ S i :=
    fun i => Assembly.path_in_connected (hS i) (Or.inl rfl) (Or.inr (Or.inl rfl))
  choose Q hQ using hpaths
  refine ⟨⟨M,fun _ _ _ => Set.mem_univ _,Q,fun _ _ _ => Set.mem_univ _,?_,?_⟩⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hi hj
    have hi' := hQ i v hi
    have hj' := hQ j v hj
    have hterm : ∀ i k, ∀ v ∈ ({x i,y i} : Set V), v ∉ C k := by
      intro i k v hv
      rcases hv with rfl | hv
      · exact hx k i
      · exact hv ▸ hy k i
    have hsplit : ∀ i v, v ∈ S i → v ∈ ({x i,y i} : Set V) ∨ v ∈ C (.inr i) := by
      intro i v hv
      rcases hv with hv | hv | hv
      · exact Or.inl (Or.inl hv)
      · exact Or.inl (Or.inr hv)
      · exact Or.inr hv
    rcases hsplit i v hi' with hi' | hi' <;> rcases hsplit j v hj' with hj' | hj'
    · exact Set.disjoint_left.mp (he i j hij) hi' hj'
    · exact hterm i (.inr j) v hi' hj'
    · exact hterm j (.inr i) v hj' hi'
    · exact Set.disjoint_left.mp (hCC (.inr i) (.inr j) (by simpa using hij)) hi' hj'
  · intro i j v hv hbag
    have hs := hQ i v hv
    change v ∈ insert (roots j) (C (.inl j)) at hbag
    rcases hs with hs | hs | hs
    · subst v
      rcases hbag with hb | hb
      · exact ⟨⟨j,hb.symm⟩,Or.inl rfl⟩
      · exact (hx (.inl j) i hb).elim
    · subst v
      rcases hbag with hb | hb
      · exact ⟨⟨j,hb.symm⟩,Or.inr rfl⟩
      · exact (hy (.inl j) i hb).elim
    · rcases hbag with hb | hb
      · exact (hroot (.inr i) j (hb ▸ hs)).elim
      · exact (Set.disjoint_left.mp (hCC (.inr i) (.inl j) (by simp)) hs hb).elim

lemma distinct_proxies {O : Type} [Fintype O]
    (G : SimpleGraph V) [DecidableRel G.Adj] (port : O → V) (Z : Finset V)
    {k : ℕ} (hc : KConnectedOn G univ k) (hk : Fintype.card O+Z.card≤k) :
    ∃ nbr : O → V, Function.Injective nbr ∧ ∀ o, nbr o ∉ Z ∧ G.Adj (port o) (nbr o) := by
  classical
  have hn (o : O) : Fintype.card O ≤ ((univ\Z).filter (G.Adj (port o))).card := by
    have hdeg := Knitting.min_degree G hc (mem_univ (port o))
    have he : Density.neighbors G univ (port o) \ Z = (univ\Z).filter (G.Adj (port o)) := by
      ext v
      simp only [Density.neighbors,mem_sdiff,mem_filter,mem_univ,true_and]
      tauto
    have hh := card_le_card (show Density.neighbors G univ (port o) ⊆
      Density.neighbors G univ (port o) \ Z ∪ Z from fun v hv => by
        by_cases hZ : v∈Z
        · exact mem_union_right _ hZ
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hv,hZ⟩))
    have hu := card_union_le (Density.neighbors G univ (port o) \ Z) Z
    rw [he] at hh hu
    omega
  obtain ⟨nbr,hi,hn'⟩ := Assembly.attach_ports (G:=G) port (univ\Z) hn
  exact ⟨nbr,hi,fun o => ⟨(mem_sdiff.mp (hn' o).1).2,(hn' o).2⟩⟩

omit [Fintype V] [DecidableEq V] in

lemma proxy_groups_of_model (G : SimpleGraph V) {a p : ℕ}
    (proxy : Fin a ⊕ (Fin p × Bool) → V)
    (M : RootedCliqueModel G proxy) :
    ∃ C : (Fin a ⊕ Fin p) → Set V,
      (∀ i, (G.induce (C i)).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (∀ j, C (.inl j)=M.branch (.inl j)) ∧
      (∀ i, proxy (.inr (i,false))∈C (.inr i) ∧ proxy (.inr (i,true))∈C (.inr i)) ∧
      (∀ i v, v∈C i → ∃ o, v∈M.branch o) := by
  classical
  let C : (Fin a ⊕ Fin p) → Set V := Sum.elim (fun j => M.branch (.inl j))
    (fun i => M.branch (.inr (i,false)) ∪ M.branch (.inr (i,true)))
  have hs (i) (v) (hv : v∈C i) : ∃ o, v∈M.branch o ∧
      (Sum.map id (fun z : Fin p × Bool => z.1) o : Fin a ⊕ Fin p) = i := by
    cases i with
    | inl j => exact ⟨.inl j,hv,rfl⟩
    | inr j =>
      rcases hv with hv|hv
      · exact ⟨.inr (j,false),hv,rfl⟩
      · exact ⟨.inr (j,true),hv,rfl⟩
  refine ⟨C,?_,?_,fun _ => rfl,fun i => ⟨Or.inl (M.root_mem _),Or.inr (M.root_mem _)⟩,?_⟩
  · intro i
    cases i with
    | inl j => exact M.connected (.inl j)
    | inr j =>
      obtain ⟨v,hv,w,hw,he⟩ := M.adjacent (.inr (j,false)) (.inr (j,true)) (by simp)
      exact SimpleGraph.connected_induce_union (M.connected _).preconnected
        (M.connected _).preconnected hv hw he
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hi hj
    obtain ⟨o,ho,hoi⟩ := hs i v hi
    obtain ⟨o',ho',hoj⟩ := hs j v hj
    exact Set.disjoint_left.mp (M.disjoint o o' (fun h => hij (hoi.symm.trans (h ▸ hoj)))) ho ho'
  · intro i v hv
    obtain ⟨o,ho,_⟩ := hs i v hv
    exact ⟨o,ho⟩

omit [Fintype V] [DecidableEq V] in
lemma connected_pullback (G : SimpleGraph V) (S B : Set V) (hBS : B⊆S)
    (hc : (G.induce B).Connected) :
    ((G.induce S).induce {v | v.val∈B}).Connected := by
  let f : G.induce B →g (G.induce S).induce {v | v.val∈B} :=
    ⟨fun v => ⟨⟨v.val,hBS v.property⟩,v.property⟩,fun h => h⟩
  refine { preconnected := ?_, nonempty := ?_ }
  · intro u v
    exact (hc.preconnected ⟨u.val.val,u.property⟩ ⟨v.val.val,v.property⟩).map f
  · obtain ⟨v⟩ := hc.nonempty
    exact ⟨f v⟩

lemma hadwiger_delete (G : SimpleGraph V) (Z : Finset V) :
    hadwigerNumber G ≤ hadwigerNumber (G.induce (↑(univ\Z):Set V))+Z.card := by
  classical
  obtain ⟨B,hB,hBB,hE⟩ := hasCliqueMinor_hadwigerNumber G
  let E := univ.filter (fun i => Disjoint (↑Z:Set V) (B i))
  have hn := eligible_bags_card Z B hBB
  change Fintype.card (Fin (hadwigerNumber G))≤E.card+Z.card at hn
  rw [Fintype.card_fin] at hn
  let e : Fin E.card ≃ E := by simpa only [Fintype.card_coe] using (Fintype.equivFin E).symm
  have hBS (i : E) : B i.val ⊆ (↑(univ\Z):Set V) := by
    intro v hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun hz => Set.disjoint_left.mp (mem_filter.mp i.property).2 hz hv⟩
  have hm : HasCliqueMinor (G.induce (↑(univ\Z):Set V)) E.card := by
    refine ⟨fun i => {v | v.val∈B (e i).val},?_,?_,?_⟩
    · intro i
      exact connected_pullback G _ _ (hBS (e i)) (hB (e i).val)
    · intro i j hij
      apply Set.disjoint_left.mpr
      intro v hi hj
      exact Set.disjoint_left.mp (hBB _ _ (fun h => hij (e.injective (Subtype.ext h)))) hi hj
    · intro i j hij
      obtain ⟨v,hv,w,hw,he⟩ := hE _ _ (fun h => hij (e.injective (Subtype.ext h)))
      exact ⟨⟨v,hBS (e i) hv⟩,hv,⟨w,hBS (e j) hw⟩,hw,he⟩
  exact hn.trans (Nat.add_le_add_right (cliqueMinor_le_hadwigerNumber hm) _)

lemma rooting_on {I : Type} [Fintype I] (G : SimpleGraph V) (S : Finset V)
    (r : I → V) (hi : Function.Injective r) (hr : ∀ i, r i∈S)
    (hc : KConnectedOn G S (2*Fintype.card I))
    (hh : 4*Fintype.card I≤hadwigerNumber (G.induce (↑S:Set V))) :
    ∃ M : RootedCliqueModel G r, ∀ i, M.branch i⊆(↑S:Set V) := by
  classical
  let rr : I → (↑S:Set V) := fun i => ⟨r i,hr i⟩
  have hir : Function.Injective rr := fun i j he => hi (congrArg Subtype.val he)
  let A := univ.image rr
  have hac : A.card=Fintype.card I := by simp [A,card_image_of_injective _ hir]
  have har (i) : rr i∈A := mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have hci : KConnectedOn (G.induce (↑S:Set V)) univ (2*A.card) := by
    rw [hac]
    exact Knitting.induce_connected G S hc
  have hhi : 4*A.card≤hadwigerNumber (G.induce (↑S:Set V)) := by simpa only [hac] using hh
  obtain ⟨M⟩ := rooting (G.induce (↑S:Set V)) A hci hhi
  let f : I → A := fun i => ⟨rr i,har i⟩
  have hif : Function.Injective f := fun _ _ he => hir (congrArg Subtype.val he)
  let N := M.reindex f hif
  let D := Knitting.model_induce G S
  let B (i : I) := D.expand (N.branch i)
  have hB (i) : B i⊆(↑S:Set V) := by
    rintro v ⟨w,_,hw⟩
    have he : v=w.val := hw
    exact he ▸ w.property
  refine ⟨⟨B,fun i => D.expand_connected (N.connected i),
    fun i j hij => D.expand_disjoint (N.disjoint i j hij),?_,?_⟩,hB⟩
  · intro i j hij
    obtain ⟨v,hv,w,hw,he⟩ := N.adjacent i j hij
    exact ⟨v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,he⟩
  · intro i
    exact ⟨rr i,N.root_mem i,rfl⟩

theorem large_minor_woven (G : SimpleGraph V) [DecidableRel G.Adj]
    {a : ℕ} (ha : 1≤a) (hc : KConnectedOn G univ (100*a))
    (hh : 64*a≤hadwigerNumber G) : Woven G a (3*a) := by
  classical
  intro roots hr _ p hp x y _ hxy
  let O := Fin a ⊕ (Fin p × Bool)
  let port : O → V := Sum.elim roots (fun z => if z.2 then y z.1 else x z.1)
  let Z := univ.image port
  have hO : Fintype.card O=a+2*p := by simp [O]; omega
  have hZ : Z.card≤a+2*p := by
    calc Z.card≤Fintype.card O := (card_image_le).trans (by simp)
         _ = a+2*p := hO
  obtain ⟨proxy,hproxy,hadj⟩ := distinct_proxies G port Z hc
    (show Fintype.card O+Z.card≤100*a by rw [hO]; omega)
  let R := univ\Z
  have hrp (o) : proxy o∈R := mem_sdiff.mpr ⟨mem_univ _,(hadj o).1⟩
  have hcR : KConnectedOn G R (2*Fintype.card O) := by
    have hd := Knitting.delete_connected G hc (subset_univ Z)
      (show Z.card<100*a by omega)
    exact Knitting.kConnected_mono hd (by rw [hO]; omega)
  have hhR : 4*Fintype.card O≤hadwigerNumber (G.induce (↑R:Set V)) := by
    have hd := hadwiger_delete G Z
    change hadwigerNumber G≤hadwigerNumber (G.induce (↑R:Set V))+Z.card at hd
    rw [hO]
    omega
  obtain ⟨M,hMR⟩ := rooting_on G R proxy hproxy hrp hcR hhR
  obtain ⟨C,hC,hCC,hCr,hCp,hCM⟩ := proxy_groups_of_model G proxy M
  have hCZ (i v) (hv : v∈C i) : v∉Z := by
    obtain ⟨o,ho⟩ := hCM i v hv
    exact (mem_sdiff.mp (hMR o ho)).2
  have hpZ (o : O) : port o∈Z := mem_image.mpr ⟨o,mem_univ _,rfl⟩
  have hrZ (j) : roots j∈Z := hpZ (.inl j)
  have hxZ (i) : x i∈Z := hpZ (.inr (i,false))
  have hyZ (i) : y i∈Z := hpZ (.inr (i,true))
  apply weaving_from_proxy_groups G roots x y hr hxy C hC hCC
    (fun i j hv => hCZ i _ hv (hrZ j))
    (fun i j hv => hCZ i _ hv (hxZ j))
    (fun i j hv => hCZ i _ hv (hyZ j))
  · intro i j hij
    rw [hCr i,hCr j]
    exact M.adjacent (.inl i) (.inl j) (fun he => hij (Sum.inl.inj he))
  · intro j
    refine ⟨proxy (.inl j),?_,(hadj (.inl j)).2⟩
    rw [hCr j]
    exact M.root_mem (.inl j)
  · intro i
    exact ⟨proxy (.inr (i,false)),(hCp i).1,(hadj (.inr (i,false))).2⟩
  · intro i
    exact ⟨proxy (.inr (i,true)),(hCp i).2,(hadj (.inr (i,true))).2⟩

end LinearListHadwiger.Recursion

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.RecursiveGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Recursion
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V I : Type} [DecidableEq V] [Fintype I] {G : SimpleGraph V}

theorem reroute_selected (J : Set V) {a b : ℕ} (hJ : WovenOn G J a b)
    (u : Fin a → V) (hu : Function.Injective u) (huJ : ∀ j, u j∈J)
    (keep : Fin a → Prop)
    (x y : I → V) (P : ∀ i, G.Path (x i) (y i))
    (hcard : Fintype.card I ≤ b)
    (hPP : ∀ i j, i≠j → Disjoint {v | v∈(P i).val.support} {v | v∈(P j).val.support})
    (hroot : ∀ i j, keep j → u j∈(P i).val.support → u j=x i) :
    ∃ M : RootedCliqueModel G u, (∀ j, M.branch j⊆J) ∧
    ∃ Q : ∀ i, G.Path (x i) (y i),
      (∀ i j, i≠j → Disjoint {v | v∈(Q i).val.support} {v | v∈(Q j).val.support}) ∧
      (∀ i v, v∈(Q i).val.support → v∉J → v∈(P i).val.support) ∧
      (∀ i j v, keep j → v∈(Q i).val.support → v∈M.branch j → v=x i ∧ v=u j) := by
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
  · intro i j v hjkeep hv hvm
    obtain ⟨⟨j',rfl⟩,D,hD⟩ := hQM _ j v ((hsup i v).mp hv) hvm
    have hj : j'=j := by
      by_contra hne
      exact Set.disjoint_left.mp (M.disjoint j' j hne) (M.root_mem j') hvm
    have horig : u j'∈(P i).val.support := by
      have he := congrArg (fun j => (P j).val.support) (e.apply_symm_apply i)
      rw [←he]
      rcases hD with hd | hd
      · exact hd.symm ▸ D.entry_on
      · exact hd.symm ▸ D.exit_on
    exact ⟨hroot i j' (hj ▸ hjkeep) horig,congrArg u hj⟩

omit [DecidableEq V] [Fintype I] in
lemma source_only (x y : I → V) (P : ∀ i, G.Path (x i) (y i))
    (hPP : ∀ i j, i≠j → Disjoint {v | v∈(P i).val.support} {v | v∈(P j).val.support})
    (i j : I) (h : x j∈(P i).val.support) : x j=x i := by
  by_cases he : i=j
  · exact he ▸ rfl
  · exact (Set.disjoint_left.mp (hPP i j he) h (P j).val.start_mem_support).elim

omit [DecidableEq V] [Fintype I] in

lemma rooted_of_occurrences {O : Type} (G : SimpleGraph V) (r : I → V)
    (hr : Function.Injective r) (label : O → I) (B : O → Set V)
    (hB : ∀ o, (G.induce (B o)).Connected)
    (hBB : ∀ o p, label o≠label p → Disjoint (B o) (B p))
    (hroot : ∀ o i, r i∉B o)
    (hattach : ∀ o, ∃ v∈B o, G.Adj v (r (label o)))
    (hpairs : ∀ i j, i≠j → ∃ o p, label o=i ∧ label p=j ∧
      ∃ v∈B o, ∃ w∈B p, G.Adj v w) :
    ∃ M : RootedCliqueModel G r,
      ∀ i, M.branch i={r i}∪{v | ∃ o, label o=i ∧ v∈B o} := by
  let C (i : I) := {r i}∪{v | ∃ o, label o=i ∧ v∈B o}
  have hc (i) : (G.induce (C i)).Connected := by
    have hsingleton : (G.induce ({r i}:Set V)).Connected := by
      have : Nonempty ({r i}:Set V) := ⟨⟨r i,rfl⟩⟩
      exact Connected.of_subsingleton
    have h := Assembly.connected_glue G {r i}
      (fun o : {o // label o=i} => B o.val) hsingleton (fun o => hB o.val) (fun o => by
        obtain ⟨v,hv,he⟩ := hattach o.val
        exact ⟨v,hv,r i,rfl,by simpa only [o.property] using he⟩)
    have he : C i={r i}∪{v | ∃ o : {o // label o=i},v∈B o.val} := by
      ext v
      simp only [C,Set.mem_union,Set.mem_ofPred_eq,Subtype.exists,exists_prop]
    exact he ▸ h
  refine ⟨⟨C,hc,?_,?_,fun _ => Or.inl rfl⟩,fun _ => rfl⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hi hj
    rcases hi with hi | ⟨o,ho,hi⟩ <;> rcases hj with hj | ⟨p,hp,hj⟩
    · exact hij (hr (hi.symm.trans hj))
    · exact hroot p i (hi ▸ hj)
    · exact hroot o j (hj ▸ hi)
    · exact Set.disjoint_left.mp (hBB o p (by simpa only [ho,hp] using hij)) hi hj
  · intro i j hij
    obtain ⟨o,p,ho,hp,v,hv,w,hw,he⟩ := hpairs i j hij
    exact ⟨v,Or.inr ⟨o,ho,hv⟩,w,Or.inr ⟨p,hp,hw⟩,he⟩

theorem reroute_disjoint_districts {D : Type} [Fintype D]
    (J : D → Set V) {a b : ℕ} (hJ : ∀ d, WovenOn G (J d) a b)
    (hJJ : ∀ d e, d≠e → Disjoint (J d) (J e))
    (u : D → Fin a → V) (hu : ∀ d, Function.Injective (u d)) (huJ : ∀ d j, u d j∈J d)
    (x y : I → V) (P : ∀ i, G.Path (x i) (y i))
    (hcard : Fintype.card I≤b)
    (hPP : ∀ i j, i≠j → Disjoint {v | v∈(P i).val.support} {v | v∈(P j).val.support}) :
    ∃ M : ∀ d, RootedCliqueModel G (u d), (∀ d j, (M d).branch j⊆J d) ∧
    ∃ Q : ∀ i, G.Path (x i) (y i),
      (∀ i j, i≠j → Disjoint {v | v∈(Q i).val.support} {v | v∈(Q j).val.support}) ∧
      (∀ i v, v∈(Q i).val.support → (∀ d, v∉J d) → v∈(P i).val.support) ∧
      (∀ d i j v, (∃ k, x k=u d j) → v∈(Q i).val.support →
        v∈(M d).branch j → v=x i ∧ v=u d j) := by
  classical
  have step (S : Finset D) :
      ∃ M : ∀ d∈S, RootedCliqueModel G (u d), (∀ d hd j, (M d hd).branch j⊆J d) ∧
      ∃ Q : ∀ i, G.Path (x i) (y i),
        (∀ i j, i≠j → Disjoint {v | v∈(Q i).val.support} {v | v∈(Q j).val.support}) ∧
        (∀ i v, v∈(Q i).val.support → (∀ d, v∉J d) → v∈(P i).val.support) ∧
        (∀ d hd i j v, (∃ k, x k=u d j) → v∈(Q i).val.support →
          v∈(M d hd).branch j → v=x i ∧ v=u d j) := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨fun d hd => (notMem_empty d hd).elim,fun d hd => (notMem_empty d hd).elim,
        P,hPP,fun _ _ hv _ => hv,fun d hd => (notMem_empty d hd).elim⟩
    | @insert d S hd ih =>
      obtain ⟨M,hMJ,Q,hQQ,hQP,hQM⟩ := ih
      obtain ⟨N,hNJ,R,hRR,hRQ,hRN⟩ := reroute_selected (J d) (hJ d) (u d) (hu d) (huJ d)
        (fun j => ∃ i, x i=u d j) x y Q hcard hQQ (by
          intro i j hj hv
          obtain ⟨k,hk⟩ := hj
          rw [←hk] at hv
          exact hk.symm.trans (source_only x y Q hQQ i k hv))
      let M' : ∀ e∈insert d S, RootedCliqueModel G (u e) := fun e he =>
        if h : e=d then h.symm ▸ N else M e ((mem_insert.mp he).resolve_left h)
      have hnew (he : d∈insert d S) : M' d he=N := by simp [M']
      have hold (e : D) (he : e∈insert d S) (hne : e≠d) :
          M' e he=M e ((mem_insert.mp he).resolve_left hne) := by simp [M',hne]
      refine ⟨M',?_,R,hRR,?_,?_⟩
      · intro e he j
        by_cases h : e=d
        · subst e
          rw [hnew he]
          exact hNJ j
        · rw [hold e he h]
          exact hMJ e _ j
      · intro i v hv hvJ
        exact hQP i v (hRQ i v hv (hvJ d)) hvJ
      · intro e he i j v hj hv hvm
        by_cases h : e=d
        · subst e
          rw [hnew he] at hvm
          exact hRN i j v hj hv hvm
        · rw [hold e he h] at hvm
          have hvJ : v∉J d := fun hvd =>
            Set.disjoint_left.mp (hJJ e d h) (hMJ e _ j hvm) hvd
          exact hQM e _ i j v hj (hRQ i v hv hvJ) hvm
  obtain ⟨M,hMJ,Q,hQQ,hQP,hQM⟩ := step univ
  exact ⟨fun d => M d (mem_univ d),fun d j => hMJ d _ j,Q,hQQ,hQP,
    fun d => hQM d (mem_univ d)⟩

lemma paired_paths_on [Fintype V] [DecidableEq I]
    (G : SimpleGraph V) (S : Finset V) (z : I × Bool → V)
    (hz : Function.Injective z) (hzS : ∀ o, z o∈S)
    (hI : 1≤Fintype.card I)
    (hc : KConnectedOn G S (65536*(2*Fintype.card I))) :
    ∃ P : ∀ i, G.Path (z (i,false)) (z (i,true)),
      (∀ i v, v∈(P i).val.support → v∈S) ∧
      ∀ i j, i≠j → Disjoint {v | v∈(P i).val.support} {v | v∈(P j).val.support} := by
  have hp : 1≤Fintype.card (I × Bool) := by simp only [Fintype.card_prod,Fintype.card_bool]; omega
  have hc' : KConnectedOn G S (65536*Fintype.card (I×Bool)) := by
    simpa only [Fintype.card_prod,Fintype.card_bool,Nat.mul_comm (Fintype.card I) 2] using hc
  obtain ⟨C,hC,hCC,hCS,hzC⟩ := Stage.grouped_ends G S z hz hzS Prod.fst
    (fun i => ⟨(i,false),rfl⟩) hp hc'
  have hex (i : I) : ∃ P : G.Path (z (i,false)) (z (i,true)), ∀ v∈P.val.support, v∈C i :=
    Assembly.path_in_connected (hC i) (hzC (i,false)) (hzC (i,true))
  choose P hP using hex
  refine ⟨P,fun i v hv => hCS i (hP i v hv),?_⟩
  intro i j hij
  exact Set.disjoint_left.mpr (fun v hi hj => Set.disjoint_left.mp (hCC i j hij) (hP i v hi) (hP j v hj))

omit [DecidableEq V] [Fintype I] in

lemma rooted_from_bag_routes {O : Type} (G : SimpleGraph V)
    (r : I → V) (hr : Function.Injective r) (label : O → I)
    (x y : O → V) (hx : Function.Injective x)
    (C : O → Set V) (P : ∀ o, G.Path (x o) (y o))
    (hC : ∀ o, (G.induce (C o)).Connected) (hCx : ∀ o, x o∈C o)
    (hCC : ∀ o p, o≠p → Disjoint (C o) (C p))
    (hPP : ∀ o p, o≠p → Disjoint {v | v∈(P o).val.support} {v | v∈(P p).val.support})
    (hPC : ∀ o p v, v∈(P o).val.support → v∈C p → v=x o ∧ v=x p)
    (hRC : ∀ o i, r i∉C o)
    (hRP : ∀ o i, r i∉(P o).val.support)
    (hadj : ∀ o, G.Adj (y o) (r (label o)))
    (hpairs : ∀ i j, i≠j → ∃ o p, label o=i ∧ label p=j ∧
      ∃ v∈C o, ∃ w∈C p, G.Adj v w) :
    ∃ M : RootedCliqueModel G r, ∀ i,
      M.branch i={r i}∪{v | ∃ o, label o=i ∧ (v∈C o ∨ v∈(P o).val.support)} := by
  let B (o : O) := C o∪{v | v∈(P o).val.support}
  have hB (o) : (G.induce (B o)).Connected :=
    Stage.attached_connected C x y P hC hCx o
  have hBB (o p) (hop : label o≠label p) : Disjoint (B o) (B p) := by
    have hne : o≠p := fun h => hop (congrArg label h)
    apply Set.disjoint_left.mpr
    intro v ho hp
    rcases ho with ho|ho <;> rcases hp with hp|hp
    · exact Set.disjoint_left.mp (hCC o p hne) ho hp
    · have he := hPC p o v hp ho
      exact hne (hx (he.2.symm.trans he.1))
    · have he := hPC o p v ho hp
      exact hne (hx (he.1.symm.trans he.2))
    · exact Set.disjoint_left.mp (hPP o p hne) ho hp
  apply rooted_of_occurrences G r hr label B hB hBB
  · intro o i hi
    exact hi.elim (hRC o i) (hRP o i)
  · intro o
    exact ⟨y o,Or.inr (P o).val.end_mem_support,hadj o⟩
  · intro i j hij
    obtain ⟨o,p,ho,hp,v,hv,w,hw,he⟩ := hpairs i j hij
    exact ⟨o,p,ho,hp,v,Or.inl hv,w,Or.inl hw,he⟩

end LinearListHadwiger.Recursion

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
open Finset
attribute [local instance] Classical.propDecidable

lemma district_labels_card (a : ℕ) (d : Fin 3) : (districtLabels a d).card≤child a := by
  have he : districtLabels a d=(univ.erase d).biUnion (Stage.block a 3) := by
    ext i
    simp only [districtLabels,mem_filter,mem_univ,true_and,mem_biUnion,mem_erase]
    constructor
    · intro hi
      refine ⟨triBlock i,⟨hi,trivial⟩,?_⟩
      exact mem_filter.mpr ⟨mem_univ _,rfl⟩
    · rintro ⟨b,⟨hbd,_⟩,hib⟩
      have hi : triBlock i=b := by
        apply Fin.ext
        exact (mem_filter.mp hib).2
      exact hi ▸ hbd
  rw [he]
  have hb (b : Fin 3) : (Stage.block a 3 b).card≤(a+2)/3 :=
    Stage.block_card_le (by decide) (by omega) b
  calc
    #((univ.erase d).biUnion (Stage.block a 3))≤∑b∈univ.erase d,(Stage.block a 3 b).card := card_biUnion_le
    _ ≤ ∑_b∈univ.erase d,(a+2)/3 := sum_le_sum (fun b _ => hb b)
    _ = child a := by simp [child]

lemma district_mem_labels {a : ℕ} (o : Fin a × Fin 2) :
    o.1∈districtLabels a (district o) := by
  exact mem_filter.mpr ⟨mem_univ _,Ne.symm (Fin.succAbove_ne _ _)⟩

lemma district_pair_coverage {a : ℕ} (i j : Fin a) :
    ∃ k l : Fin 2, district (i,k)=district (j,l) := by
  have third : ∀ i j : Fin 3, ∃ d, d≠i ∧ d≠j := by decide
  obtain ⟨d,hdi,hdj⟩ := third (triBlock i) (triBlock j)
  obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hdi
  obtain ⟨l,hl⟩ := Fin.exists_succAbove_eq hdj
  exact ⟨k,l,hk.trans hl.symm⟩

lemma district_same_injective {a : ℕ} (o p : Fin a × Fin 2)
    (hl : o.1=p.1) (hd : district o=district p) : o=p := by
  apply Prod.ext hl
  have he : (triBlock o.1).succAbove o.2=(triBlock o.1).succAbove p.2 := by
    simpa only [district,hl] using hd
  exact Fin.succAbove_right_injective he

lemma child_shrink {a : ℕ} (ha : 24<a) : 1≤child a ∧ child a<a ∧ 4*child a≤3*a := by
  dsimp [child]
  omega

lemma path_capacity (a : ℕ) : 2*a≤3*child a := by
  dsimp [child]
  omega

lemma district_indices (a : ℕ) :
    ∃ index : (Fin a × Fin 2) → Fin (child a),
      ∀ o p, district o=district p → index o=index p → o=p := by
  classical
  let f (d : Fin 3) : ↥(districtLabels a d) ↪ Fin (child a) :=
    (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (by simpa only [Fintype.card_coe] using district_labels_card a d))
  let index (o : Fin a × Fin 2) := f (district o) ⟨o.1,district_mem_labels o⟩
  refine ⟨index,?_⟩
  intro o p hd hi
  have key (d e : Fin 3) (i : ↥(districtLabels a d)) (j : ↥(districtLabels a e))
      (hde : d=e) (hij : f d i=f e j) : i.val=j.val := by
    subst e
    exact congrArg Subtype.val ((f d).injective hij)
  have hlabel : o.1=p.1 := key _ _ _ _ hd hi
  exact district_same_injective o p hlabel hd

end LinearListHadwiger.Recursion

namespace LinearListHadwiger.Recursion
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem three_district_model (G : SimpleGraph V) {a : ℕ} (ha : 1≤a)
    (S : Finset V) (r : Fin a → V) (hr : Function.Injective r) (hrS : ∀ i, r i∈S)
    (n : Fin a × Fin 2 → V) (hn : Function.Injective n)
    (hnS : ∀ o, n o∈S) (hnr : ∀ o i, n o≠r i)
    (hnadj : ∀ o, G.Adj (n o) (r o.1))
    (J : Fin 3 → Set V) (hJS : ∀ d, J d⊆(↑S:Set V))
    (hJr : ∀ d i, r i∉J d) (hJn : ∀ d o, n o∉J d)
    (hJJ : ∀ d e, d≠e → Disjoint (J d) (J e))
    (hJ : ∀ d, WovenOn G (J d) (child a) (3*child a))
    (u : Fin 3 → Fin (child a) → V) (hu : ∀ d, Function.Injective (u d))
    (huJ : ∀ d j, u d j∈J d)
    (hc : KConnectedOn G (S\univ.image r) (65536*(4*a))) :
    ∃ M : RootedCliqueModel G r, ∀ i, M.branch i⊆(↑S:Set V) := by
  classical
  obtain ⟨index,hindex⟩ := district_indices a
  let x (o : Fin a × Fin 2) := u (district o) (index o)
  have hx (o) : x o∈J (district o) := huJ _ _
  have hxi : Function.Injective x := by
    intro o p h
    have hd : district o=district p := by
      by_contra hne
      exact Set.disjoint_left.mp (hJJ _ _ hne) (hx o) (h ▸ hx p)
    have hi : index o=index p := (hu (district o)) (by simpa only [x,←hd] using h)
    exact hindex o p hd hi
  let z : (Fin a × Fin 2) × Bool → V := fun q => if q.2 then n q.1 else x q.1
  have hzi : Function.Injective z := by
    rintro ⟨o,b⟩ ⟨p,c⟩ h
    cases b <;> cases c
    · exact Prod.ext (hxi h) rfl
    · change x o=n p at h
      exact (hJn (district o) p (h ▸ hx o)).elim
    · change n o=x p at h
      exact (hJn (district p) o (h.symm ▸ hx p)).elim
    · exact Prod.ext (hn h) rfl
  have hzS (q) : z q∈S\univ.image r := by
    rcases q with ⟨o,b⟩
    cases b
    · refine mem_sdiff.mpr ⟨hJS _ (hx o),?_⟩
      rintro h
      obtain ⟨i,_,hi⟩ := mem_image.mp h
      exact hJr (district o) i (hi ▸ hx o)
    · refine mem_sdiff.mpr ⟨hnS o,?_⟩
      rintro h
      obtain ⟨i,_,hi⟩ := mem_image.mp h
      exact hnr o i hi.symm
  have hcard : Fintype.card (Fin a × Fin 2)=2*a := by simp [Nat.mul_comm]
  have hc' : KConnectedOn G (S\univ.image r) (65536*(2*Fintype.card (Fin a × Fin 2))) := by
    rw [hcard]; convert hc using 1; omega
  obtain ⟨P,hPS,hPP⟩ := paired_paths_on G (S\univ.image r) z hzi hzS (by rw [hcard]; omega) hc'
  change ∀ o, G.Path (x o) (n o) at P
  obtain ⟨M,hMJ,Q,hQQ,hQP,hQM⟩ := reroute_disjoint_districts J hJ hJJ u hu huJ x n P
    (by rw [hcard]; exact path_capacity a) hPP
  have hQS (o) (v) (hv : v∈(Q o).val.support) : v∈S\univ.image r := by
    by_cases hj : ∃ d, v∈J d
    · obtain ⟨d,hd⟩ := hj
      refine mem_sdiff.mpr ⟨hJS d hd,?_⟩
      rintro hm
      obtain ⟨i,_,hi⟩ := mem_image.mp hm
      exact hJr d i (hi ▸ hd)
    · exact hPS o v (hQP o v hv (by simpa only [not_exists] using hj))
  let C (o : Fin a × Fin 2) := (M (district o)).branch (index o)
  have hC (o) : (G.induce (C o)).Connected := (M _).connected _
  have hCx (o) : x o∈C o := (M _).root_mem _
  have hCJ (o) : C o⊆J (district o) := hMJ _ _
  have hCC (o p) (hne : o≠p) : Disjoint (C o) (C p) := by
    by_cases hd : district o=district p
    · have hi : index o≠index p := fun h => hne (hindex o p hd h)
      change Disjoint ((M (district o)).branch (index o)) ((M (district p)).branch (index p))
      rw [←hd]
      exact (M _).disjoint _ _ hi
    · exact (hJJ _ _ hd).mono (hCJ o) (hCJ p)
  have hPC (o p v) (hv : v∈(Q o).val.support) (hw : v∈C p) : v=x o ∧ v=x p :=
    hQM (district p) o (index p) v ⟨p,rfl⟩ hv hw
  have hRC (o i) : r i∉C o := fun hv => hJr _ i (hCJ o hv)
  have hRP (o i) : r i∉(Q o).val.support := fun hv =>
    (mem_sdiff.mp (hQS o (r i) hv)).2 (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
  have hpairs (i j : Fin a) (hij : i≠j) : ∃ o p : Fin a × Fin 2,
      o.1=i ∧ p.1=j ∧ ∃ v∈C o, ∃ w∈C p, G.Adj v w := by
    obtain ⟨k,l,hd⟩ := district_pair_coverage i j
    have hne : index (i,k)≠index (j,l) := fun h => hij (congrArg Prod.fst (hindex _ _ hd h))
    obtain ⟨v,hv,w,hw,he⟩ := (M (district (i,k))).adjacent _ _ hne
    refine ⟨(i,k),(j,l),rfl,rfl,v,hv,w,?_,he⟩
    change w∈(M (district (j,l))).branch (index (j,l))
    rw [←hd]
    exact hw
  obtain ⟨R,hR⟩ := rooted_from_bag_routes G r hr Prod.fst x n hxi C Q hC hCx hCC hQQ
    hPC hRC hRP hnadj hpairs
  refine ⟨R,?_⟩
  intro i v hv
  rw [hR] at hv
  rcases hv with hv | ⟨o,_,hv|hv⟩
  · exact hv ▸ hrS i
  · exact hJS _ (hCJ o hv)
  · exact (mem_sdiff.mp (hQS o v hv)).1

end LinearListHadwiger.Recursion

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
open SimpleGraph Finset Stage
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem junction_groups (G : SimpleGraph V) {a p : ℕ} (ha : 1≤a)
    (r : Fin a → V) (n : Fin (2*p) → V) (e : (Fin p × Bool) ≃ Fin (2*p)) (H D : Finset V) (F U : Set V)
    (hHD : Disjoint H D)
    (R : RoleRouting G r n F (↑H:Set V) D U)
    (M : RootedCliqueModel G R.fresh) (hMH : ∀ i, M.branch i⊆(↑H:Set V))
    (hc : KConnectedOn G D (65536*Fintype.card (Roles a (2*p)))) :
    ∃ C : (Fin a ⊕ Fin p) → Set V,
      (∀ i, (G.induce (C i)).Connected) ∧
      (∀ i j, i≠j → Disjoint (C i) (C j)) ∧
      (∀ i j, i≠j → ∃ v∈C (.inl i), ∃ w∈C (.inl j), G.Adj v w) ∧
      (∀ i, r i∈C (.inl i)) ∧
      (∀ q, n (e q)∈C (.inr q.1)) := by
  classical
  let owner : Roles a (2*p) → Fin a ⊕ Fin p :=
    Sum.elim Sum.inl (Sum.elim (fun j => Sum.inr (e.symm j).1) Sum.inl)
  let start := roleStart r n R.fresh
  let target (o : Roles a (2*p)) := (R.target o).val
  have htar : Function.Injective target := Subtype.val_injective.comp R.target_injective
  have hs : Function.Surjective owner := by
    intro i
    cases i with
    | inl i => exact ⟨.inl i,rfl⟩
    | inr i => exact ⟨.inr (.inl (e (i,false))),by simp [owner]⟩
  have hcpos : 1≤Fintype.card (Roles a (2*p)) := by simp only [Roles,Fintype.card_sum,Fintype.card_fin]; omega
  obtain ⟨E,hE,hEE,hED,htE⟩ := grouped_ends G D target htar (fun o => (R.target o).property)
    owner hs hcpos hc
  let B : Roles a (2*p) → Set V := Sum.elim (fun i => {r i}) (Sum.elim (fun j => {n j}) M.branch)
  have hB (o) : (G.induce (B o)).Connected := by
    rcases o with i|(j|i)
    · change (G.induce ({r i}:Set V)).Connected
      have : Nonempty ({r i}:Set V) := ⟨⟨r i,rfl⟩⟩
      exact Connected.of_subsingleton
    · change (G.induce ({n j}:Set V)).Connected
      have : Nonempty ({n j}:Set V) := ⟨⟨n j,rfl⟩⟩
      exact Connected.of_subsingleton
    · exact M.connected i
  have hxB (o) : start o∈B o := by
    rcases o with i|(j|i)
    · rfl
    · rfl
    · exact M.root_mem i
  have hBP (o q) (hne : owner o≠owner q) :
      Disjoint (B o) {v | v∈(R.route q).val.support} := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    rcases o with i|(j|i)
    · have he : v=r i := hv
      subst v
      have hneq : Sum.inl i≠q := fun h => hne (congrArg owner h)
      exact Set.disjoint_left.mp (R.disjoint _ _ hneq) (R.route (.inl i)).val.start_mem_support hw
    · have he : v=n j := hv
      subst v
      have hneq : Sum.inr (Sum.inl j)≠q := fun h => hne (congrArg owner h)
      exact Set.disjoint_left.mp (R.disjoint _ _ hneq) (R.route (.inr (.inl j))).val.start_mem_support hw
    · obtain ⟨j,rfl,hv'⟩ := R.new_only q v hw (hMH i hv)
      have hij : i≠j := by intro h; subst j; exact hne rfl
      exact Set.disjoint_left.mp (M.disjoint i j hij) hv (hv'.symm ▸ M.root_mem j)
  have hBB (o q) (hne : owner o≠owner q) : Disjoint (B o) (B q) := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    rcases q with j|(j|j)
    · have he : v=r j := hw
      exact Set.disjoint_left.mp (hBP o (.inl j) hne) hv (he.symm ▸ (R.route (.inl j)).val.start_mem_support)
    · have he : v=n j := hw
      exact Set.disjoint_left.mp (hBP o (.inr (.inl j)) hne) hv (he.symm ▸ (R.route (.inr (.inl j))).val.start_mem_support)
    · rcases o with i|(i|i)
      · have he : v=r i := hv
        exact Set.disjoint_left.mp (hBP (.inr (.inr j)) (.inl i) (Ne.symm hne)) hw
          (he.symm ▸ (R.route (.inl i)).val.start_mem_support)
      · have he : v=n i := hv
        exact Set.disjoint_left.mp (hBP (.inr (.inr j)) (.inr (.inl i)) (Ne.symm hne)) hw
          (he.symm ▸ (R.route (.inr (.inl i))).val.start_mem_support)
      · exact Set.disjoint_left.mp (M.disjoint i j (fun h => hne (congrArg Sum.inl h))) hv hw
  have hEP (i o) (hne : i≠owner o) : Disjoint (E i) {v | v∈(R.route o).val.support} := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    have he := R.target_only o v hw (hED i hv)
    exact Set.disjoint_left.mp (hEE i (owner o) hne) hv (he.symm ▸ htE o)
  have hEB (i o) (hne : i≠owner o) : Disjoint (E i) (B o) := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    rcases o with j|(j|j)
    · have he : v=r j := hw
      exact Set.disjoint_left.mp (hEP i (.inl j) hne) hv (he.symm ▸ (R.route (.inl j)).val.start_mem_support)
    · have he : v=n j := hw
      exact Set.disjoint_left.mp (hEP i (.inr (.inl j)) hne) hv (he.symm ▸ (R.route (.inr (.inl j))).val.start_mem_support)
    · exact Finset.disjoint_left.mp hHD (hMH j hw) (hED i hv)
  let C := extended E B owner start target R.route
  have hC (i) : (G.induce (C i)).Connected := extended_connected E B owner start target R.route
    hE hB hxB htE i
  have hCC : ∀ i j, i≠j → Disjoint (C i) (C j) :=
    extended_disjoint E B owner start target R.route hEE hBB hEB hEP hBP
      (fun o q hne => R.disjoint o q (fun h => hne (congrArg owner h)))
  have hBC (o) : B o⊆C (owner o) := fun _ hv => Or.inr ⟨o,rfl,Or.inl hv⟩
  refine ⟨C,hC,hCC,?_,fun i => hBC (.inl i) rfl,?_⟩
  · intro i j hij
    obtain ⟨v,hv,w,hw,he⟩ := M.adjacent i j hij
    exact ⟨v,hBC (.inr (.inr i)) hv,w,hBC (.inr (.inr j)) hw,he⟩
  · intro q
    have hmem := hBC (.inr (.inl (e q))) rfl
    simpa only [owner,Sum.elim_inr,Sum.elim_inl,e.symm_apply_apply] using hmem

end LinearListHadwiger.Recursion

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.RecursiveInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Recursion
open Finset Stage SmallList SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma neighbors_on {O : Type} [Fintype O] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S Z : Finset V) (port : O → V) (hp : ∀ o, port o∈S) {k : ℕ}
    (hc : KConnectedOn G S k) (hk : Fintype.card O+Z.card≤k) :
    ∃ n : O → V, Function.Injective n ∧ ∀ o, n o∈S\Z ∧ G.Adj (port o) (n o) := by
  classical
  apply Assembly.attach_ports G port (S\Z)
  intro o
  have hdeg := Knitting.min_degree G hc (hp o)
  have he : Density.neighbors G S (port o) \ Z=(S\Z).filter (G.Adj (port o)) := by
    ext v
    simp only [Density.neighbors,mem_sdiff,mem_filter]
    tauto
  have hh := card_le_card (show Density.neighbors G S (port o)⊆
    Density.neighbors G S (port o)\Z∪Z from fun v hv => by
      by_cases hz : v∈Z
      · exact mem_union_right _ hz
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hv,hz⟩))
  have hu := card_union_le (Density.neighbors G S (port o)\Z) Z
  rw [he] at hh hu
  have hbound : Fintype.card O≤((S\Z).filter (G.Adj (port o))).card := by omega
  exact hbound

omit [Fintype V] in
lemma connected_induce_univ (G : SimpleGraph V) (J : Finset V) {k : ℕ}
    (hc : KConnectedOn G J k) : KConnectedOn (G.induce (↑J:Set V)) univ k := by
  have hh := under_connected G (U:=J) (A:=J) (subset_refl J) hc
  have he : under J J=univ := by ext v; simp [under]
  rwa [he] at hh

theorem fresh_model : ∃ S : ℕ, 1≤S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ a K Q : ℕ, 1≤a → 1≤K → T≤64*a →
    (∀ (W : Type) [Fintype W] [DecidableEq W] (P : SimpleGraph W),
      KConnectedOn P univ (K*child a) → Q*child a≤listChromaticNumber P →
      Woven P (child a) (3*child a) ∨ FractionalObstruction P) →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (H : Finset V) (r : Fin a → V), Function.Injective r → (∀ i, r i∈H) →
      hadwigerNumber G<64*a → KConnectedOn G H (K₀*(64*a)) →
      3*S*(64*a)+3*a≤ell G H →
      Q*child a+6*(K*child a)+2*S*(64*a)+3*a<ell G H →
      (∃ M : RootedCliqueModel G r, ∀ i, M.branch i⊆(↑H:Set V)) ∨ FractionalObstruction G := by
  obtain ⟨S,hS,T,hT,hs⟩ := three_regions
  refine ⟨S,hS,T,hT,?_⟩
  intro a K Q ha hK ht ih V _ _ G H r hr hrH hm hc hsep hl
  classical
  let R := univ.image r
  have hR : R.card=a := by simp only [R,card_image_of_injective _ hr,card_univ,Fintype.card_fin]
  have hRH : R⊆H := by rintro v hv; obtain ⟨i,_,rfl⟩ := mem_image.mp hv; exact hrH i
  obtain ⟨n,hn,hnH⟩ := neighbors_on G H R (fun o : Fin a × Fin 2 => r o.1)
    (fun _ => hrH _) hc (by simp only [Fintype.card_prod,Fintype.card_fin,hR]; dsimp [K₀]; omega)
  let N := univ.image n
  have hN : N.card=2*a := by simp only [N,card_image_of_injective _ hn,card_univ,Fintype.card_prod,Fintype.card_fin]; omega
  let B := R∪N
  have hB : B.card≤3*a := by have := card_union_le R N; dsimp [B]; omega
  have hdel := ell_delete G H B
  have ha' : 1≤child a := by unfold child; omega
  rcases hs (64*a) ht V G (H\B) (K*child a) (Q*child a) (by nlinarith) hm
    (by omega) (by omega) with ⟨J,hJH,hJJ,hJc,hJl⟩|hb
  swap
  · exact Or.inr hb
  have hchild (d : Fin 3) : WovenOn G (↑(J d):Set V) (child a) (3*child a) ∨ FractionalObstruction G := by
    rcases ih (↑(J d):Set V) (G.induce (↑(J d):Set V))
      (connected_induce_univ G (J d) (hJc d)) (Nat.le_of_lt (hJl d)) with hw|hb
    · exact Or.inl (woven_induce G (J d) hw)
    · exact Or.inr (obstruction_induce G (J d) hb)
  by_cases hb : FractionalObstruction G
  · exact Or.inr hb
  have hw (d) : WovenOn G (↑(J d):Set V) (child a) (3*child a) := (hchild d).resolve_right hb
  have hroots (d : Fin 3) : ∃ u : Fin (child a) → V,
      Function.Injective u ∧ ∀ i, u i∈J d := by
    apply choose_vertices
    have hh := (hJc d).1
    nlinarith
  choose u hu huJ using hroots
  have hconn : KConnectedOn G (H\univ.image r) (65536*(4*a)) := by
    apply Knitting.kConnected_mono (Knitting.delete_connected G hc hRH (by rw [hR]; dsimp [K₀]; omega))
    rw [hR]
    dsimp [K₀]
    omega
  apply Or.inl
  apply three_district_model G ha H r hr hrH n hn
    (fun o => (mem_sdiff.mp (hnH o).1).1)
    (fun o i he => (mem_sdiff.mp (hnH o).1).2 (he ▸ mem_image.mpr ⟨i,mem_univ _,rfl⟩))
    (fun o => (hnH o).2.symm) (fun d => (↑(J d):Set V))
    (fun d => (hJH d).trans sdiff_subset) ?_ ?_ (fun d e hne => by exact_mod_cast hJJ d e hne)
    hw u hu huJ hconn
  · intro d i hi
    exact (mem_sdiff.mp (hJH d hi)).2 (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩))
  · intro d o ho
    exact (mem_sdiff.mp (hJH d ho)).2 (mem_union_right _ (mem_image.mpr ⟨o,mem_univ _,rfl⟩))

end LinearListHadwiger.Recursion

namespace LinearListHadwiger.Recursion
open Finset Stage SmallList SimpleGraph
attribute [local instance] Classical.propDecidable

theorem recursive_woven_or_obstruction : ∃ K Q : ℕ, 100≤K ∧ 1≤Q ∧
    ∀ a : ℕ, 1≤a → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      KConnectedOn G univ (K*a) → Q*a≤listChromaticNumber G →
      Woven G a (3*a) ∨ FractionalObstruction G := by
  obtain ⟨A,hA,T₁,hT₁,houter⟩ := outer_region
  obtain ⟨S,hS,T₂,hT₂,hfresh⟩ := fresh_model
  let K := A+100
  let a₀ := max 24 (max T₁ T₂)
  let B := ⌊(200000000:ℝ)*(64*a₀:ℕ)*Real.log (2*(64*a₀:ℕ))⌋₊+1
  let c : ℕ := 4*32768+42+5+6*K₀
  let Q := B+A+18*K+512*S+40+256*c+1
  have hK : 100≤K := by dsimp [K]; omega
  have hQ : 1≤Q := by dsimp [Q]; omega
  have hQA : A+7<Q := by dsimp [Q]; omega
  have hQbig : 18*K+512*S+40+256*c<Q := by dsimp [Q]; omega
  have hQB : B<Q := by dsimp [Q]; omega
  refine ⟨K,Q,hK,hQ,?_⟩
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro ha V _ _ G hc hl
    classical
    have hka : 100*a≤K*a := Nat.mul_le_mul_right a hK
    by_cases hminor : 64*a≤hadwigerNumber G
    · exact Or.inl (large_minor_woven G ha (Knitting.kConnected_mono hc hka) hminor)
    have hm : hadwigerNumber G<64*a := by omega
    have ha₀ : a₀<a := by
      by_contra hn
      have hma : hadwigerNumber G<64*a₀ := hm.trans_le (by omega)
      have hb := CoarseDensity.coarse_list_bound G (show 2≤64*a₀ by dsimp [a₀]; omega) hma
      change listChromaticNumber G≤B at hb
      nlinarith only [ha,hl,hQB,hb]
    have hac : 24<a := (le_max_left _ _).trans_lt ha₀
    obtain ⟨hcpos,hclt,hcshrink⟩ := child_shrink hac
    have ht₁ : T₁≤64*a := by have := (le_max_left T₁ T₂).trans (le_max_right 24 _); omega
    have ht₂ : T₂≤64*a := by have := (le_max_right T₁ T₂).trans (le_max_right 24 _); omega
    by_cases hbad : FractionalObstruction G
    · exact Or.inr hbad
    left
    intro roots hr _ p hp x y _ hxy
    let O := Fin a ⊕ (Fin p × Bool)
    let port : O → V := Sum.elim roots (fun z => if z.2 then y z.1 else x z.1)
    let Z := univ.image port
    have hO : Fintype.card O=a+2*p := by simp [O]; omega
    have hZ : Z.card≤7*a := by
      have hh := card_image_le (s:=univ) (f:=port)
      rw [card_univ,hO] at hh
      calc Z.card≤a+2*p := hh
           _≤7*a := by omega
    obtain ⟨proxy,hproxy,hadj⟩ := distinct_proxies G port Z hc
      (show Fintype.card O+Z.card≤K*a by rw [hO]; omega)
    let R := univ\Z
    let P := G.induce (↑R:Set V)
    let proxy' (o : O) : (↑R:Set V) := ⟨proxy o,mem_sdiff.mpr ⟨mem_univ _,(hadj o).1⟩⟩
    have hproxy' : Function.Injective proxy' := fun i j he => hproxy (congrArg Subtype.val he)
    let e : (Fin p × Bool) ≃ Fin (2*p) := Fintype.equivOfCardEq (by simp; omega)
    let r (i : Fin a) := proxy' (.inl i)
    let n (j : Fin (2*p)) := proxy' (.inr (e.symm j))
    have hr' : Function.Injective r := hproxy'.comp Sum.inl_injective
    have hn' : Function.Injective n := hproxy'.comp (Sum.inr_injective.comp e.symm.injective)
    have hrn (i j) : r i≠n j := by intro he; cases hproxy' he
    have hcR : KConnectedOn G R (30*a) := by
      apply Knitting.kConnected_mono (Knitting.delete_connected G hc (subset_univ Z) (by omega))
      omega
    have hcP : KConnectedOn P univ (30*a) := connected_induce_univ G R hcR
    have hmP : hadwigerNumber P<64*a := (Knitting.model_induce G R).hadwiger_le.trans_lt hm
    have hdel := ell_delete G univ Z
    rw [ell_univ] at hdel
    change listChromaticNumber G≤listChromaticNumber P+Z.card at hdel
    have hQAa := Nat.mul_lt_mul_of_pos_right hQA (show 0<a by omega)
    have hPA : A*a<listChromaticNumber P := by nlinarith only [hQAa,hdel,hl,hZ]
    have noP : ¬FractionalObstruction P := fun hb => hbad (obstruction_induce G R hb)
    obtain ⟨H,D,U,⟨routing⟩,hHD,hHc,hDc,hHl⟩ :=
      (houter a ha ht₁ p hp (↑R:Set V) P r n hr' hn' hrn hcP hmP hPA).resolve_right noP
    have hcall (W : Type) [Fintype W] [DecidableEq W] (L : SimpleGraph W)
        (hconn : KConnectedOn L univ (K*child a)) (hlist : Q*child a≤listChromaticNumber L) :
        Woven L (child a) (3*child a) ∨ FractionalObstruction L :=
      ih (child a) hclt hcpos W L hconn hlist
    have hsep : 3*S*(64*a)+3*a≤ell P H := by
      change listChromaticNumber P≤ell P H+c*(64*a) at hHl
      have hb : 192*S+10+64*c<Q := by omega
      have hh := Nat.mul_lt_mul_of_pos_right hb (show 0<a by omega)
      nlinarith only [hh,hHl,hdel,hl,hZ]
    have hstep : Q*child a+6*(K*child a)+2*S*(64*a)+3*a<ell P H := by
      change listChromaticNumber P≤ell P H+c*(64*a) at hHl
      have hq := Nat.mul_le_mul_left Q hcshrink
      have hk := Nat.mul_le_mul_left (6*K) hcshrink
      have hh := Nat.mul_lt_mul_of_pos_right hQbig (show 0<a by omega)
      nlinarith only [hh,hq,hk,hHl,hdel,hl,hZ]
    obtain ⟨M,hMH⟩ := (hfresh a K Q ha (by omega) ht₂ hcall (↑R:Set V) P H routing.fresh
      routing.fresh_injective routing.fresh_mem hmP hHc hsep hstep).resolve_right noP
    have hgroup : KConnectedOn P D (65536*Fintype.card (Roles a (2*p))) := by
      apply Knitting.kConnected_mono hDc
      simp only [Roles,Fintype.card_sum,Fintype.card_fin]
      dsimp [K₀]
      omega
    obtain ⟨C₀,hC₀,hCC₀,hE₀,hrC₀,hnC₀⟩ := junction_groups P ha r n e H D _ U hHD routing M hMH hgroup
    let lift := Knitting.model_induce G R
    let C (i : Fin a ⊕ Fin p) := lift.expand (C₀ i)
    have hC (i) : (G.induce (C i)).Connected := lift.expand_connected (hC₀ i)
    have hCC (i j) (hij : i≠j) : Disjoint (C i) (C j) := lift.expand_disjoint (hCC₀ i j hij)
    have hCZ (i v) (hv : v∈C i) : v∉Z := by
      obtain ⟨w,_,hw⟩ := hv
      have he : v=w.val := hw
      exact he ▸ (mem_sdiff.mp w.property).2
    have hpZ (o : O) : port o∈Z := mem_image.mpr ⟨o,mem_univ _,rfl⟩
    apply weaving_from_proxy_groups G roots x y hr hxy C hC hCC
      (fun i j hv => hCZ i _ hv (hpZ (.inl j)))
      (fun i j hv => hCZ i _ hv (hpZ (.inr (j,false))))
      (fun i j hv => hCZ i _ hv (hpZ (.inr (j,true))))
    · intro i j hij
      obtain ⟨v,hv,w,hw,he⟩ := hE₀ i j hij
      exact ⟨v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,he⟩
    · intro i
      exact ⟨proxy (.inl i),⟨r i,hrC₀ i,rfl⟩,(hadj (.inl i)).2⟩
    · intro i
      have hh := hnC₀ (i,false)
      have he : n (e (i,false))=proxy' (.inr (i,false)) := by simp [n]
      rw [he] at hh
      exact ⟨proxy (.inr (i,false)),⟨proxy' (.inr (i,false)),hh,rfl⟩,(hadj (.inr (i,false))).2⟩
    · intro i
      have hh := hnC₀ (i,true)
      have he : n (e (i,true))=proxy' (.inr (i,true)) := by simp [n]
      rw [he] at hh
      exact ⟨proxy (.inr (i,true)),⟨proxy' (.inr (i,true)),hh,rfl⟩,(hadj (.inr (i,true))).2⟩

end LinearListHadwiger.Recursion

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Reduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Recursion
open Finset Stage SmallList SimpleGraph
attribute [local instance] Classical.propDecidable

theorem final_bound_or_obstruction : ∃ C : ℕ, 1≤C ∧
    ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
      listChromaticNumber G≤C*hadwigerNumber G ∨
        FractionalObstruction G := by
  obtain ⟨K,Q,hK,hQ,hs⟩ := recursive_woven_or_obstruction
  refine ⟨2*(Q+6*K),by omega,?_⟩
  intro V _ _ G
  classical
  by_cases hb : FractionalObstruction G
  · exact Or.inr hb
  left
  have hminorfree (t : ℕ) (ht : 2≤t) (hm : hadwigerNumber G<t) :
      listChromaticNumber G≤(Q+6*K)*t := by
    by_contra hnot
    have hl : (Q+6*K)*t<listChromaticNumber G := by omega
    have hk : 1≤K*t := by nlinarith
    obtain ⟨P,hPc,hPl⟩ := list_connectivity_extraction G hk (by nlinarith)
    have hlist : Q*t≤listChromaticNumber (G.induce (↑P:Set V)) := by
      change listChromaticNumber G-6*(K*t)≤ell G P at hPl
      change Q*t≤ell G P
      have he : (Q+6*K)*t=Q*t+6*(K*t) := by ring
      rw [he] at hl
      omega
    rcases hs t (by omega) (↑P:Set V) (G.induce (↑P:Set V))
      (connected_induce_univ G P hPc) hlist with hw|hbad
    swap
    · exact hb (obstruction_induce G P hbad)
    obtain ⟨r,hr,hrP⟩ := choose_vertices (show t≤P.card by have hh:=hPc.1; nlinarith)
    have h0 (i : Fin 0) : V := Fin.elim0 i
    obtain ⟨A⟩ := woven_induce G P hw r hr hrP 0 (by omega) h0 h0
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    have hm' : HasCliqueMinor G t := ⟨A.model.branch,A.model.connected,A.model.disjoint,A.model.adjacent⟩
    exact (not_lt_of_ge (cliqueMinor_le_hadwigerNumber hm')) hm
  have hpos := one_le_hadwigerNumber G
  have hfinal := hminorfree (hadwigerNumber G+1) (by omega) (by omega)
  nlinarith

end LinearListHadwiger.Recursion

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

namespace Fractional
variable {V : Type} [Fintype V] [DecidableEq V]

theorem number_le_two_hadwiger (G : SimpleGraph V) :
    number G ≤ 2 * (hadwigerNumber G : ℝ) :=
  fractional_chromatic_le_two_hadwiger G

theorem number_le_four_hadwiger (G : SimpleGraph V) :
    number G ≤ 4 * (hadwigerNumber G : ℝ) := by
  have hh := number_le_two_hadwiger G
  have hp : (0 : ℝ) ≤ hadwigerNumber G := Nat.cast_nonneg _
  linarith
end Fractional

namespace SmallList
lemma no_fractionalObstruction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ¬ FractionalObstruction G := by
  rintro ⟨S,hS⟩
  exact (not_lt_of_ge (Fractional.number_le_four_hadwiger (G.induce (↑S : Set V)))) hS
end SmallList

theorem main_theorem_oai : MainStatement := by
  obtain ⟨C,hC,h⟩ := Recursion.final_bound_or_obstruction
  refine ⟨C,hC,?_⟩
  intro V _ _ G
  classical
  exact (h V G).resolve_right (SmallList.no_fractionalObstruction G)

end LinearListHadwiger

end OAI
end

theorem solution : type_of% @OAI.LinearListHadwiger.main_theorem_oai := @OAI.LinearListHadwiger.main_theorem_oai
