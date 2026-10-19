-- Prove2me | solution 1 for OAI.LinearListHadwiger.SmallList.additive_deletion_or_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:55:50.003726+00:00
-- url     : https://prove2.me/submissions/0439063a-3868-42e9-8560-89ab5d6e0dcf

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000
import Theorems.Thm_OAI_LinearListHadwiger_Sampling_source_thinning_failure_structure

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

lemma connected_induce_star {V : Type} (G : SimpleGraph V) (S : Set V)
    (r : V) (hr : r ∈ S) (hS : ∀ v ∈ S, v = r ∨ G.Adj r v) :
    (G.induce S).Connected := by
  have hre : ∀ v : S, (G.induce S).Reachable ⟨r, hr⟩ v := by
    intro v
    rcases hS v v.property with hv | hv
    · have he : v = ⟨r, hr⟩ := Subtype.ext hv
      rw [he]
    · exact (show (G.induce S).Adj ⟨r, hr⟩ v from hv).reachable
  exact { preconnected := fun u v => (hre u).symm.trans (hre v), nonempty := ⟨⟨r, hr⟩⟩ }

theorem cliqueMinor_of_subdivision {V : Type} {t : ℕ} (G : SimpleGraph V)
    (r : Fin t → V) (hr : Function.Injective r)
    (mid : {p : Fin t × Fin t // p.1 < p.2} → V)
    (hm : Function.Injective mid)
    (hd : ∀ p i, mid p ≠ r i)
    (ha : ∀ p, G.Adj (r p.val.1) (mid p) ∧ G.Adj (r p.val.2) (mid p)) :
    HasCliqueMinor G t := by
  let B : Fin t → Set V := fun i =>
    {v | v = r i ∨ ∃ j : Fin t, ∃ h : i < j, v = mid ⟨(i, j), h⟩}
  have hroot : ∀ i, r i ∈ B i := fun _ => Or.inl rfl
  have hc : ∀ i, (G.induce (B i)).Connected := by
    intro i
    apply connected_induce_star G (B i) (r i) (hroot i)
    intro v hv
    rcases hv with hv | ⟨j, hij, rfl⟩
    · exact Or.inl hv
    · exact Or.inr (ha ⟨(i, j), hij⟩).1
  refine ⟨B, hc, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hi hj
    rcases hi with rfl | ⟨a, hia, rfl⟩
    · rcases hj with he | ⟨b, hjb, he⟩
      · exact hij (hr he)
      · exact hd ⟨(j, b), hjb⟩ i he.symm
    · rcases hj with he | ⟨b, hjb, he⟩
      · exact hd ⟨(i, a), hia⟩ j he
      · have hh := hm he
        exact hij (congrArg (fun p => p.val.1) hh)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ⟨mid ⟨(i, j), hij⟩, Or.inr ⟨j, hij, rfl⟩,
        r j, hroot j, (ha ⟨(i, j), hij⟩).2.symm⟩
    · exact ⟨r i, hroot i, mid ⟨(j, i), hji⟩,
        Or.inr ⟨i, hji, rfl⟩, (ha ⟨(j, i), hji⟩).2⟩

lemma cliqueMinor_of_saturated_pairs {V : Type} [DecidableEq V]
    {t : ℕ} (G : SimpleGraph V) (X S N : Finset V)
    (hSX : Disjoint S X) (hNX : N ⊆ X) (hN : t ≤ N.card)
    (f : V → Sym2 V)
    (hf : ∀ w ∈ S, ∀ a ∈ f w, G.Adj w a)
    (hsat : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → ∃ w ∈ S, f w = s(a, b)) :
    HasCliqueMinor G t := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin t) (β := ↥N) (by simpa using hN)
  let r : Fin t → V := fun i => (e i).val
  have hr : Function.Injective r := fun i j h => e.injective (Subtype.ext h)
  have hrN : ∀ i, r i ∈ N := fun i => (e i).property
  have hw : ∀ p : {p : Fin t × Fin t // p.1 < p.2},
      ∃ w ∈ S, f w = s(r p.val.1, r p.val.2) := by
    intro p
    exact hsat _ (hrN _) _ (hrN _) (fun h => p.property.ne (hr h))
  choose mid hmS hmf using hw
  have hmi : Function.Injective mid := by
    intro p q hpq
    have he : s(r p.val.1, r p.val.2) = s(r q.val.1, r q.val.2) := by
      rw [← hmf p, ← hmf q, hpq]
    rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Subtype.ext (Prod.ext (hr h₁) (hr h₂))
    · have h₁' := hr h₁
      have h₂' := hr h₂
      have hp := p.property
      have hq := q.property
      omega
  refine cliqueMinor_of_subdivision G r hr mid hmi ?_ ?_
  · intro p i heq
    exact Finset.disjoint_left.mp hSX (hmS p) (heq ▸ hNX (hrN i))
  · intro p
    constructor
    · apply (hf _ (hmS p) _ ?_).symm
      rw [hmf p]
      exact Sym2.mem_iff.mpr (Or.inl rfl)
    · apply (hf _ (hmS p) _ ?_).symm
      rw [hmf p]
      exact Sym2.mem_iff.mpr (Or.inr rfl)

lemma mem_neighborPairs {V : Type} [DecidableEq V] {G : SimpleGraph V} {X : Finset V}
    {v : V} {p : Sym2 V} (hp : p ∈ neighborPairs G X v) :
    ∀ a ∈ p, a ∈ X ∧ G.Adj v a := by
  classical
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hab
  intro z hz
  rcases Sym2.mem_iff.mp hz with rfl | rfl
  · exact Finset.mem_filter.mp ha
  · exact Finset.mem_filter.mp hb

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

lemma exists_injective_neighborPairs {V : Type} [DecidableEq V]
    {t : ℕ} (G : SimpleGraph V) (X S : Finset V)
    (hminor : ¬HasCliqueMinor G t)
    (hSX : Disjoint S X)
    (hdeg : ∀ v ∈ S, t ≤ (X.filter (G.Adj v)).card) :
    ∃ f : V → Sym2 V, Set.InjOn f (↑S : Set V) ∧
      ∀ v ∈ S, f v ∈ neighborPairs G X v := by
  classical
  revert hSX hdeg
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    exact ⟨fun v => s(v, v), by simp [Set.InjOn], by simp⟩
  | @insert v S hv ih =>
    intro hSX hdeg
    obtain ⟨f, hfi, hfp⟩ := ih
      (hSX.mono_left (Finset.subset_insert _ _))
      (fun w hw => hdeg w (Finset.mem_insert_of_mem hw))
    by_cases hex : ∃ p ∈ neighborPairs G X v, p ∉ S.image f
    · obtain ⟨p, hp, hnp⟩ := hex
      let g : V → Sym2 V := fun w => if w = v then p else f w
      have hgv : g v = p := by simp [g]
      have hgS : ∀ w ∈ S, g w = f w := by
        intro w hw
        have hn : w ≠ v := by
          intro he
          subst w
          exact hv hw
        simp only [g, ite_eq_right hn]
      refine ⟨g, ?_, ?_⟩
      · intro a ha b hb hab
        by_cases hav : a = v
        · subst a
          by_cases hbv : b = v
          · exact hbv.symm
          · have hbS := (Finset.mem_insert.mp hb).resolve_left hbv
            rw [hgv, hgS b hbS] at hab
            exact (hnp (Finset.mem_image.mpr ⟨b, hbS, hab.symm⟩)).elim
        · have haS := (Finset.mem_insert.mp ha).resolve_left hav
          by_cases hbv : b = v
          · subst b
            rw [hgS a haS, hgv] at hab
            exact (hnp (Finset.mem_image.mpr ⟨a, haS, hab⟩)).elim
          · have hbS := (Finset.mem_insert.mp hb).resolve_left hbv
            rw [hgS a haS, hgS b hbS] at hab
            exact hfi haS hbS hab
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · rwa [hgv]
        · rw [hgS w hw]
          exact hfp w hw
    · exfalso
      apply hminor
      apply cliqueMinor_of_saturated_pairs G X S (X.filter (G.Adj v))
        (hSX.mono_left (Finset.subset_insert _ _)) (Finset.filter_subset _ _)
        (hdeg v (Finset.mem_insert_self _ _)) f
      · intro w hw a ha
        exact (mem_neighborPairs (hfp w hw) a ha).2
      · intro a ha b hb hab
        have hpair : s(a, b) ∈ neighborPairs G X v :=
          Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩
        have himage : s(a, b) ∈ S.image f := by
          by_contra hn
          exact hex ⟨s(a, b), hpair, hn⟩
        exact Finset.mem_image.mp himage

theorem high_neighbor_count {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {t : ℕ} (_ht : 2 ≤ t)
    (hminor : hadwigerNumber G < t) (X : Finset V) :
    (Finset.univ.filter (fun v => v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card)).card
      ≤ X.card.choose 2 := by
  classical
  let S := Finset.univ.filter (fun v => v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card)
  have hSX : Disjoint S X := Finset.disjoint_left.mpr fun v hv hx =>
    (Finset.mem_filter.mp hv).2.1 hx
  have hdeg : ∀ v ∈ S, t ≤ (X.filter (G.Adj v)).card :=
    fun _ hv => (Finset.mem_filter.mp hv).2.2
  obtain ⟨f, hfi, hfp⟩ := exists_injective_neighborPairs G X S
    (fun h => (Nat.not_le_of_lt hminor) (cliqueMinor_le_hadwigerNumber h)) hSX hdeg
  have hsub : S.image f ⊆ X.offDiag.image Sym2.mk.uncurry := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp (hfp v hv)
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr
      ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp hb).1, hne⟩, heq⟩
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injOn hfi).symm
    _ ≤ (X.offDiag.image Sym2.mk.uncurry).card := Finset.card_le_card hsub
    _ = X.card.choose 2 := Sym2.card_image_offDiag X

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

namespace PaletteReservation

lemma weight_nonneg {α : Type} [Fintype α] {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (σ : α → Bool) : 0 ≤ weight p σ := by
  apply Finset.prod_nonneg
  intro a _
  split <;> linarith

lemma weighted_product {α : Type} [Fintype α] (p : ℝ) (f : α → Bool → ℝ) :
    (∑ σ : α → Bool, weight p σ * ∏ a, f a (σ a)) =
      ∏ a, ((1 - p) * f a false + p * f a true) := by
  classical
  simp only [weight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (b : Bool) =>
    (if b then p else 1 - p) * f a b)]
  apply Finset.prod_congr rfl
  intro a _
  simp [add_comm]

lemma sum_weight {α : Type} [Fintype α] (p : ℝ) :
    ∑ σ : α → Bool, weight p σ = 1 := by
  have h := weighted_product p (fun (_ : α) (_ : Bool) => (1 : ℝ))
  simpa using h

lemma pow_count {α : Type} [Fintype α] (X : Finset α) (σ : α → Bool) (z : ℝ) :
    z ^ count X σ = ∏ a : α, if a ∈ X ∧ σ a = true then z else 1 := by
  classical
  have he : (Finset.univ.filter fun a : α => a ∈ X ∧ σ a = true) =
      X.filter (fun a => σ a = true) := by ext a; simp
  simp [count, Finset.prod_ite, he]

lemma moment {α : Type} [Fintype α] (p z : ℝ) (X : Finset α) :
    (∑ σ : α → Bool, weight p σ * z ^ count X σ) =
      (1 - p + p * z) ^ X.card := by
  classical
  simp_rw [pow_count]
  rw [weighted_product p (fun a b => if a ∈ X ∧ b = true then z else 1)]
  have hprod : (∏ a : α,
        ((1 - p) * (if a ∈ X ∧ false = true then z else 1) +
          p * (if a ∈ X ∧ true = true then z else 1))) =
      ∏ a : α, if a ∈ X then (1 - p + p * z) else 1 := by
    apply Finset.prod_congr rfl
    intro a _
    by_cases ha : a ∈ X <;> simp [ha]
  rw [hprod]
  simp

lemma exists_lt_of_mean_lt {Ω : Type} [Fintype Ω] (w F : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω, w ω = 1)
    (hF : (∑ ω, w ω * F ω) < 1) : ∃ ω, F ω < 1 := by
  by_contra hn
  push Not at hn
  have hh : (∑ ω, w ω) ≤ ∑ ω, w ω * F ω := by
    apply Finset.sum_le_sum
    intro ω _
    nlinarith [hw ω, hn ω]
  linarith

lemma lower_moment_bound {α : Type} [Fintype α] (X : Finset α)
    {u m : ℕ} (hu : X.card = u) (hu0 : 0 < u) (hm : 2 * m ≤ u) :
    (∑ σ : α → Bool, weight (2 * (m : ℝ) / u) σ *
      ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ count X σ)) ≤ (3 / 4 : ℝ) ^ m := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu0
  have hmR : 2 * (m : ℝ) ≤ u := by exact_mod_cast hm
  rw [show (∑ σ : α → Bool, weight (2 * (m : ℝ) / u) σ *
      ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ count X σ)) =
      (2 : ℝ) ^ m * ∑ σ : α → Bool,
        weight (2 * (m : ℝ) / u) σ * (1 / 2 : ℝ) ^ count X σ by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  rw [moment, hu]
  have hbase : 1 - 2 * (m : ℝ) / u + 2 * (m : ℝ) / u * (1 / 2) =
      1 - (m : ℝ) / u := by ring
  rw [hbase]
  have hnonneg : 0 ≤ 1 - (m : ℝ) / u := by
    have hle : (m : ℝ) / u ≤ 1 := (div_le_one huR).mpr (by linarith)
    linarith
  have he : 1 - (m : ℝ) / u ≤ Real.exp (-(m : ℝ) / u) := by
    have hh := Real.add_one_le_exp (-(m : ℝ) / u)
    simpa only [neg_div, sub_eq_add_neg, add_comm] using hh
  have hpow := pow_le_pow_left₀ hnonneg he u
  have heq : Real.exp (-(m : ℝ) / u) ^ u = Real.exp (-(m : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [heq] at hpow
  have he2 : Real.exp (-1) ≤ (3 / 8 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos (1 : ℝ))).mpr
    have hx := Real.exp_one_gt_d9
    norm_num at hx ⊢
    linarith
  calc
    (2 : ℝ) ^ m * (1 - (m : ℝ) / u) ^ u
        ≤ 2 ^ m * Real.exp (-(m : ℝ)) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * Real.exp (-1)) ^ m := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ (3 / 4 : ℝ) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      linarith

lemma upper_moment_bound {α : Type} [Fintype α] (X : Finset α)
    {u m : ℕ} (hu : X.card = u) (hu0 : 0 < u) :
    (∑ σ : α → Bool, weight (2 * (m : ℝ) / u) σ *
      ((2 : ℝ) ^ count X σ / (2 : ℝ) ^ (4 * m))) ≤ (3 / 4 : ℝ) ^ m := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu0
  rw [show (∑ σ : α → Bool, weight (2 * (m : ℝ) / u) σ *
      ((2 : ℝ) ^ count X σ / (2 : ℝ) ^ (4 * m))) =
      (∑ σ : α → Bool, weight (2 * (m : ℝ) / u) σ *
        (2 : ℝ) ^ count X σ) / (2 : ℝ) ^ (4 * m) by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intros; ring]
  rw [moment, hu]
  have hbase : 1 - 2 * (m : ℝ) / u + 2 * (m : ℝ) / u * 2 =
      1 + 2 * (m : ℝ) / u := by ring
  rw [hbase]
  have hpow := pow_le_pow_left₀
    (show 0 ≤ 1 + 2 * (m : ℝ) / u by positivity)
    (show 1 + 2 * (m : ℝ) / u ≤ Real.exp (2 * (m : ℝ) / u) by
      linarith [Real.add_one_le_exp (2 * (m : ℝ) / u)]) u
  have heq : Real.exp (2 * (m : ℝ) / u) ^ u = Real.exp (2 * (m : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [heq] at hpow
  have he3 : Real.exp 1 ≤ 3 := by
    have hh := Real.exp_one_lt_d9
    norm_num at hh
    linarith
  calc
    (1 + 2 * (m : ℝ) / u) ^ u / 2 ^ (4 * m)
        ≤ Real.exp (2 * (m : ℝ)) / 2 ^ (4 * m) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ = (Real.exp 1 ^ 2 / 16) ^ m := by
      have hnum : Real.exp (2 * (m : ℝ)) = (Real.exp 1 ^ 2) ^ m := by
        rw [← pow_mul, ← Real.exp_nat_mul]
        congr 1
        simp
      have hden : (2 : ℝ) ^ (4 * m) = (16 : ℝ) ^ m := by
        rw [pow_mul]
        norm_num
      rw [hnum, hden, div_pow]
    _ ≤ (3 / 4 : ℝ) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      have hh : Real.exp 1 ^ 2 ≤ (3 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) he3 _
      norm_num at hh ⊢
      linarith

theorem exists_reservation {V α : Type} [Fintype α] (L : V → Finset α)
    (X T : Finset V) {u m : ℕ} (hu0 : 0 < u) (hm : 2 * m ≤ u)
    (hL : ∀ v ∈ X ∪ T, (L v).card = u)
    (hsmall : ((X.card + T.card : ℕ) : ℝ) * (3 / 4 : ℝ) ^ m < 1) :
    ∃ R : Finset α, (∀ v ∈ X, m ≤ (L v ∩ R).card) ∧
      ∀ v ∈ T, (L v ∩ R).card ≤ 4 * m := by
  classical
  let p : ℝ := 2 * (m : ℝ) / u
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp' : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by exact_mod_cast hu0)).mpr
    exact_mod_cast hm
  let lower : V → (α → Bool) → ℝ := fun v σ =>
    (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ count (L v) σ
  let upper : V → (α → Bool) → ℝ := fun v σ =>
    (2 : ℝ) ^ count (L v) σ / (2 : ℝ) ^ (4 * m)
  let F : (α → Bool) → ℝ := fun σ => (∑ v ∈ X, lower v σ) + ∑ v ∈ T, upper v σ
  have hlow : ∀ v ∈ X, (∑ σ, weight p σ * lower v σ) ≤ (3 / 4 : ℝ) ^ m := by
    intro v hv
    exact lower_moment_bound (L v) (hL v (Finset.mem_union_left T hv)) hu0 hm
  have hup : ∀ v ∈ T, (∑ σ, weight p σ * upper v σ) ≤ (3 / 4 : ℝ) ^ m := by
    intro v hv
    exact upper_moment_bound (L v) (hL v (Finset.mem_union_right X hv)) hu0
  have hmean : ∑ σ, weight p σ * F σ < 1 := by
    have heq : (∑ σ, weight p σ * F σ) =
        (∑ v ∈ X, ∑ σ, weight p σ * lower v σ) +
          ∑ v ∈ T, ∑ σ, weight p σ * upper v σ := by
      simp only [F, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      congr 1 <;> rw [Finset.sum_comm]
    rw [heq]
    have h1 := Finset.sum_le_sum hlow
    have h2 := Finset.sum_le_sum hup
    simp only [Finset.sum_const, nsmul_eq_mul] at h1 h2
    have hsum : (X.card : ℝ) * (3 / 4 : ℝ) ^ m +
        (T.card : ℝ) * (3 / 4 : ℝ) ^ m =
        ((X.card + T.card : ℕ) : ℝ) * (3 / 4 : ℝ) ^ m := by push_cast; ring
    linarith
  obtain ⟨σ, hσ⟩ := exists_lt_of_mean_lt (weight p) F
    (weight_nonneg hp hp') (sum_weight p) hmean
  let R := Finset.univ.filter fun a : α => σ a = true
  have hcount : ∀ v, (L v ∩ R).card = count (L v) σ := by
    intro v
    apply congrArg Finset.card
    ext a
    simp [R]
  refine ⟨R, ?_, ?_⟩
  · intro v hv
    rw [hcount]
    by_contra hn
    have hcm : count (L v) σ ≤ m := by omega
    have hpen : 1 ≤ lower v σ := by
      dsimp [lower]
      rw [one_div_pow, one_div, ← div_eq_mul_inv]
      apply (one_le_div (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num) hcm
    have hterm : lower v σ ≤ F σ := by
      have h1 := Finset.single_le_sum
        (f := fun v => lower v σ) (s := X) (fun _ _ => by dsimp [lower]; positivity) hv
      have h2 : 0 ≤ ∑ v ∈ T, upper v σ := Finset.sum_nonneg
        (fun _ _ => by dsimp [upper]; positivity)
      dsimp [F]
      linarith
    linarith
  · intro v hv
    rw [hcount]
    by_contra hn
    have hcm : 4 * m ≤ count (L v) σ := by omega
    have hpen : 1 ≤ upper v σ := by
      dsimp [upper]
      apply (one_le_div (by positivity)).mpr
      exact pow_le_pow_right₀ (by norm_num) hcm
    have hterm : upper v σ ≤ F σ := by
      have h1 := Finset.single_le_sum
        (f := fun v => upper v σ) (s := T) (fun _ _ => by dsimp [upper]; positivity) hv
      have h2 : 0 ≤ ∑ v ∈ X, lower v σ := Finset.sum_nonneg
        (fun _ _ => by dsimp [lower]; positivity)
      dsimp [F]
      linarith
    linarith

end PaletteReservation

theorem choosable_iff_finite_colors {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    Choosable G k ↔ ∀ (Color : Type) [Fintype Color] (L : V → Finset Color),
      (∀ v, k ≤ (L v).card) → ListColorable G L := by
  classical
  constructor
  · intro h Color _ L hL
    exact h Color L hL
  · intro h Color L hL
    let C : Finset Color := Finset.univ.biUnion L
    have hc : ∀ v (c : ↥(L v)), c.val ∈ C := fun v c =>
      Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, c.property⟩
    let emb : ∀ v, ↥(L v) ↪ ↥C := fun v =>
      ⟨fun c => ⟨c.val, hc v c⟩, fun a b hab => Subtype.ext (congrArg (fun x : ↥C => x.val) hab)⟩
    let L' : V → Finset ↥C := fun v => (L v).attach.map (emb v)
    have hcard : ∀ v, (L' v).card = (L v).card := fun v => by simp [L']
    obtain ⟨c, hc', hp⟩ := h ↥C L' (fun v => by rw [hcard]; exact hL v)
    refine ⟨fun v => (c v).val, ?_, ?_⟩
    · intro v
      obtain ⟨a, _, heq⟩ := Finset.mem_map.mp (hc' v)
      have hh := congrArg Subtype.val heq
      change a.val = (c v).val at hh
      change (c v).val ∈ L v
      rw [← hh]
      exact a.property
    · intro v w hadj heq
      exact hp hadj (Subtype.ext heq)

lemma validOn_of_choosable {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (L : V → Finset Color) (φ : V → Color)
    {k : ℕ} (h : Choosable (G.induce (↑S : Set V)) k)
    (hL : ∀ v ∈ S, k ≤ (L v).card) : ∃ c, ValidOn G S L c := by
  classical
  obtain ⟨c, hc, hp⟩ := h Color (fun v => L v.val) (fun v => hL v.val v.property)
  let c' : V → Color := fun v => if hv : v ∈ S then c ⟨v, hv⟩ else φ v
  refine ⟨c', ?_, ?_⟩
  · intro v hv
    simpa only [c', dite_eq_left hv] using hc ⟨v, hv⟩
  · intro v hv w hw hadj
    simpa only [c', dite_eq_left hv, dite_eq_left hw] using
      hp (v := ⟨v, hv⟩) (w := ⟨w, hw⟩) hadj

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

lemma prune_card_loss {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (L : V → Finset Color) (c : V → Color) (v : V) :
    (L v).card ≤ (prune G S L c v).card + (S.filter (G.Adj v)).card := by
  have hh := Finset.card_le_card_sdiff_add_card (s := L v)
    (t := (S.filter (G.Adj v)).image c)
  have hh' := Finset.card_image_le (s := S.filter (G.Adj v)) (f := c)
  dsimp [prune]
  omega

lemma prune_subset {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (L : V → Finset Color) (c : V → Color) (v : V) :
    prune G S L c v ⊆ L v := Finset.sdiff_subset

lemma prune_avoids {V Color : Type} {G : SimpleGraph V} {S : Finset V}
    {L : V → Finset Color} {c : V → Color} {v w : V} {a : Color}
    (ha : a ∈ prune G S L c w) (hv : v ∈ S) (hadj : G.Adj v w) : c v ≠ a := by
  intro heq
  exact (Finset.mem_sdiff.mp ha).2
    (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hadj.symm⟩, heq⟩)

lemma prune_reserved_loss {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (L : V → Finset Color) (c : V → Color) (R : Finset Color)
    (hreserved : ∀ v ∈ S, c v ∈ R) (v : V) :
    (L v).card ≤ (prune G S L c v).card + (L v ∩ R).card := by
  classical
  have hsub : L v ∩ (S.filter (G.Adj v)).image c ⊆ L v ∩ R := by
    intro a ha
    obtain ⟨hla, hi⟩ := Finset.mem_inter.mp ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_inter.mpr ⟨hla, hreserved w (Finset.mem_filter.mp hw).1⟩
  have heq := Finset.card_sdiff_add_card_inter (L v) ((S.filter (G.Adj v)).image c)
  have hcard := Finset.card_le_card hsub
  dsimp [prune]
  omega

theorem additive_deletion_coloring {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X Y : Finset V) {t m d s : ℕ}
    (ht : 1 ≤ t) (hXY : Disjoint X Y)
    (hX : Choosable (G.induce (↑X : Set V)) m)
    (hY : DegenerateOn G Y (d * t))
    (hRY : ∀ v ∉ X ∪ Y, (Y.filter (G.Adj v)).card ≤ d * t)
    (hR : Choosable (G.induce (↑(Finset.univ \ (X ∪ Y)) : Set V)) s)
    (hsmall : ((X.card + (Finset.univ.filter
        (fun v => v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card)).card : ℕ) : ℝ) *
        (3 / 4 : ℝ) ^ m < 1) :
    Choosable G (s + 4 * m + d * t + 5 * t) := by
  classical
  apply (choosable_iff_finite_colors G _).mpr
  intro Color _ L₀ hL₀
  let u := s + 4 * m + d * t + 5 * t
  have hu0 : 0 < u := by dsimp [u]; omega
  have hmu : 2 * m ≤ u := by dsimp [u]; omega
  have hex : ∀ v, ∃ L' ⊆ L₀ v, L'.card = u := fun v =>
    Finset.exists_subset_card_eq (hL₀ v)
  choose L hsub hcard using hex
  have hn : ∀ v, (L v).Nonempty := fun v => Finset.card_pos.mp (by rw [hcard]; exact hu0)
  choose φ hφ using hn
  let T := Finset.univ.filter fun v => v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card
  obtain ⟨reserved, hresX, hresT⟩ := PaletteReservation.exists_reservation L X T
    hu0 hmu (fun v _ => hcard v) hsmall
  obtain ⟨cX, hcX⟩ := validOn_of_choosable G X (fun v => L v ∩ reserved) φ hX hresX
  have hcXL : ValidOn G X L cX :=
    ⟨fun v hv => (Finset.mem_inter.mp (hcX.1 v hv)).1, hcX.2⟩
  have hcXR : ∀ v ∈ X, cX v ∈ reserved :=
    fun v hv => (Finset.mem_inter.mp (hcX.1 v hv)).2
  let L₁ := prune G X L cX
  have hL₁ : ∀ v ∉ X, s + d * t + 4 * t ≤ (L₁ v).card := by
    intro v hv
    by_cases hT : v ∈ T
    · have hh := prune_reserved_loss G X L cX reserved hcXR v
      have hb := hresT v hT
      rw [hcard] at hh
      dsimp [u] at hh
      change _ ≤ (L₁ v).card + _ at hh
      omega
    · have hd : (X.filter (G.Adj v)).card < t := by
        have hh : ¬(v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card) := by
          simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hT
        exact lt_of_not_ge (fun hh' => hh ⟨hv, hh'⟩)
      have hh := prune_card_loss G X L cX v
      rw [hcard] at hh
      dsimp [u] at hh
      change _ ≤ (L₁ v).card + _ at hh
      omega
  have hYnotX : ∀ v ∈ Y, v ∉ X := fun v hv hx =>
    Finset.disjoint_left.mp hXY hx hv
  obtain ⟨cY, hcY⟩ := degenerate_coloring_on G Y L₁ φ hY (by
    intro v hv
    have hh := hL₁ v (hYnotX v hv)
    omega)
  have hcYL : ValidOn G Y L cY :=
    ⟨fun v hv => prune_subset G X L cX v (hcY.1 v hv), hcY.2⟩
  let cXY : V → Color := fun v => if v ∈ X then cX v else cY v
  have hcXY : ValidOn G (X ∪ Y) L cXY := hcXL.glue hcYL hXY
    (fun v hv w hw hadj => prune_avoids (hcY.1 w hw) hv hadj)
  let R := Finset.univ \ (X ∪ Y)
  let L₂ := prune G Y L₁ cY
  have hL₂ : ∀ v ∈ R, s ≤ (L₂ v).card := by
    intro v hv
    have hvXY : v ∉ X ∪ Y := (Finset.mem_sdiff.mp hv).2
    have hvX : v ∉ X := fun hx => hvXY (Finset.mem_union_left Y hx)
    have hh := hL₁ v hvX
    have hdrop := prune_card_loss G Y L₁ cY v
    have hdeg := hRY v hvXY
    change _ ≤ (L₂ v).card + _ at hdrop
    omega
  obtain ⟨cR, hcR⟩ := validOn_of_choosable G R L₂ φ hR hL₂
  have hcRL : ValidOn G R L cR :=
    ⟨fun v hv => prune_subset G X L cX v
      (prune_subset G Y L₁ cY v (hcR.1 v hv)), hcR.2⟩
  have hd : Disjoint (X ∪ Y) R := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_sdiff.mp hw).2 hv
  have hcross : ∀ v ∈ X ∪ Y, ∀ w ∈ R, G.Adj v w → cXY v ≠ cR w := by
    intro v hv w hw hadj
    by_cases hvX : v ∈ X
    · dsimp [cXY]
      rw [ite_eq_left hvX]
      exact prune_avoids (prune_subset G Y L₁ cY w (hcR.1 w hw)) hvX hadj
    · have hvY : v ∈ Y := (Finset.mem_union.mp hv).resolve_left hvX
      dsimp [cXY]
      rw [ite_eq_right hvX]
      exact prune_avoids (hcR.1 w hw) hvY hadj
  have hfinal := hcXY.glue hcRL hd hcross
  have heq : (X ∪ Y) ∪ R = Finset.univ := by ext v; simp [R]
  rw [heq] at hfinal
  refine ⟨fun v => if v ∈ X ∪ Y then cXY v else cR v, ?_, ?_⟩
  · intro v
    exact hsub v (hfinal.1 v (Finset.mem_univ _))
  · intro v w hadj
    exact hfinal.2 (Finset.mem_univ _) (Finset.mem_univ _) hadj

theorem reservation_cutoff :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ m ≥ t, ∀ a b : ℕ,
      a ≤ t ^ 2 → b ≤ a.choose 2 →
      ((a + b : ℕ) : ℝ) * (3 / 4 : ℝ) ^ m < 1 := by
  have hlim := (tendsto_pow_const_mul_const_pow_of_lt_one 4
    (show (0 : ℝ) ≤ 3 / 4 by norm_num) (by norm_num)).const_mul 2
  have hev : ∀ᶠ t : ℕ in Filter.atTop,
      2 * ((t : ℝ) ^ 4 * (3 / 4 : ℝ) ^ t) < 1 := by
    exact hlim.eventually (p := fun x : ℝ => x < 1) (by
      simpa using (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max t₀ 1, ?_⟩
  intro t ht m hm a b ha hb
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have htp : t ≤ t ^ 2 := by nlinarith
  have hap : a ≤ t ^ 4 := by nlinarith
  have hbp : b ≤ t ^ 4 := by
    have hh := Nat.choose_le_pow a 2
    have hh' : a ^ 2 ≤ (t ^ 2) ^ 2 := Nat.pow_le_pow_left ha 2
    nlinarith
  have hab : ((a + b : ℕ) : ℝ) ≤ 2 * (t : ℝ) ^ 4 := by
    exact_mod_cast (show a + b ≤ 2 * t ^ 4 by omega)
  have hp : (3 / 4 : ℝ) ^ m ≤ (3 / 4 : ℝ) ^ t :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  calc
    ((a + b : ℕ) : ℝ) * (3 / 4 : ℝ) ^ m
      ≤ (2 * (t : ℝ) ^ 4) * (3 / 4 : ℝ) ^ t :=
        mul_le_mul hab hp (by positivity) (by positivity)
    _ = 2 * ((t : ℝ) ^ 4 * (3 / 4 : ℝ) ^ t) := by ring
    _ < 1 := ht₀ t ((le_max_left _ _).trans ht)

lemma small_order_le_square {a t : ℕ} (ht : 1 ≤ t)
    (ha : (a : ℝ) ≤ (t : ℝ) ^ (11 / 10 : ℝ)) : a ≤ t ^ 2 := by
  have hh := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ t by exact_mod_cast ht) (show (11 / 10 : ℝ) ≤ (2 : ℕ) by norm_num)
  rw [Real.rpow_natCast] at hh
  exact_mod_cast ha.trans hh

theorem reservation_cutoff_minor :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (X : Finset V) (m : ℕ),
      t ≤ m → hadwigerNumber G < t →
      (X.card : ℝ) ≤ (t : ℝ) ^ (11 / 10 : ℝ) →
      ((X.card + (Finset.univ.filter
        (fun v => v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card)).card : ℕ) : ℝ) *
          (3 / 4 : ℝ) ^ m < 1 := by
  obtain ⟨t₀, ht₀⟩ := reservation_cutoff
  refine ⟨max t₀ 2, ?_⟩
  intro t ht V _ _ G X m hm hminor hsize
  have ht2 : 2 ≤ t := (le_max_right _ _).trans ht
  exact ht₀ t ((le_max_left _ _).trans ht) m hm X.card _
    (small_order_le_square (by omega) hsize) (high_neighbor_count G ht2 hminor X)

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

lemma number_le_iff (G : SimpleGraph V) (r : ℝ) :
    number G ≤ r ↔ ∃ μ, Cover G μ ∧ cost μ ≤ r := by
  constructor
  · intro h
    obtain ⟨μ,hμ,heq⟩ := optimum_exists G
    exact ⟨μ,hμ,heq ▸ h⟩
  · rintro ⟨μ,hμ,hcost⟩
    exact (number_le_cost hμ).trans hcost

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
-- module Solutions.OAIQW_ListHadwiger.FractionalSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end LinearListHadwiger.Sampling

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

theorem clique_of_occurrences {t : ℕ} (label : O → Fin t)
    (B : O → Set V) (C : Fin t → Set V)
    (hB : ∀ o, (G.induce (B o)).Connected)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hBB : ∀ o p, label o ≠ label p → Disjoint (B o) (B p))
    (hCC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hBC : ∀ o i, Disjoint (B o) (C i))
    (hattach : ∀ o, ∃ x ∈ B o, ∃ y ∈ C (label o), G.Adj x y)
    (hpairs : ∀ i j, i ≠ j → ∃ o p, label o = i ∧ label p = j ∧
      ∃ x ∈ B o, ∃ y ∈ B p, G.Adj x y) :
    HasCliqueMinor G t := by
  let S (i : Fin t) := C i ∪ {v | ∃ o, label o = i ∧ v ∈ B o}
  refine ⟨S,?_,?_,?_⟩
  · intro i
    have hh := connected_glue G (C i) (fun o : {o // label o = i} => B o.val)
      (hC i) (fun o => hB o.val) (fun o => by simpa [o.property] using hattach o.val)
    have he : S i = C i ∪ {v | ∃ o : {o // label o = i}, v ∈ B o.val} := by
      ext v
      simp only [S,Set.mem_union,Set.mem_ofPred_eq,Subtype.exists]
      aesop
    change (G.induce (S i)).Connected
    rw [he]
    exact hh
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    rcases hvi with hi | ⟨o,ho,hi⟩ <;> rcases hvj with hj | ⟨p,hp,hj⟩
    · exact Set.disjoint_left.mp (hCC i j hij) hi hj
    · exact Set.disjoint_left.mp (hBC p i) hj hi
    · exact Set.disjoint_left.mp (hBC o j) hi hj
    · exact Set.disjoint_left.mp (hBB o p (by simpa [ho,hp] using hij)) hi hj
  · intro i j hij
    obtain ⟨o,p,ho,hp,x,hx,y,hy,hxy⟩ := hpairs i j hij
    exact ⟨x,Or.inr ⟨o,ho,hx⟩,y,Or.inr ⟨p,hp,hy⟩,hxy⟩

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
-- module Solutions.OAIQW_ListHadwiger.DistrictAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Assembly
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V O : Type} [Fintype V] [DecidableEq V] [Fintype O] [DecidableEq O]

theorem clique_from_private_occurrences {V O : Type} [Fintype V] [DecidableEq V] [Fintype O] [DecidableEq O] (G : SimpleGraph V) {t : ℕ}
    (label : O → Fin t) (hs : Function.Surjective label) (hO : 1 ≤ Fintype.card O)
    (B : O → Set V) (U : Finset V)
    (hB : ∀ o, (G.induce (B o)).Connected)
    (hBB : ∀ o p, label o ≠ label p → Disjoint (B o) (B p))
    (hU : ∀ o, Disjoint (B o) (↑U : Set V))
    (hN : ∀ o, ∀ v ∈ B o, Fintype.card O ≤ (U.filter (G.Adj v)).card)
    (hconn : KConnectedOn G U (65536 * Fintype.card O))
    (hpairs : ∀ i j, i ≠ j → ∃ o p, label o = i ∧ label p = j ∧
      ∃ x ∈ B o, ∃ y ∈ B p, G.Adj x y) : HasCliqueMinor G t := by
  classical
  have hp : ∀ o, ∃ v, v ∈ B o := fun o => by
    obtain ⟨v⟩ := (hB o).nonempty
    exact ⟨v.val,v.property⟩
  choose port hp using hp
  obtain ⟨nbr,hni,hn⟩ := attach_ports (G := G) port U (fun o => hN o (port o) (hp o))
  let nr : O → (↑U : Set V) := fun o => ⟨nbr o,(hn o).1⟩
  have hnr : Function.Injective nr := fun _ _ he => hni (congrArg Subtype.val he)
  let A : Finset (↑U : Set V) := univ.image nr
  have hAc : A.card = Fintype.card O := by
    rw [card_image_of_injective _ hnr,card_univ]
  have ha (o : O) : nr o ∈ A := mem_image.mpr ⟨o,mem_univ _,rfl⟩
  have hpre : ∀ a : ↥A, ∃ o, nr o = a.val := by
    intro a
    obtain ⟨o,_,ho⟩ := mem_image.mp a.property
    exact ⟨o,ho⟩
  choose idx hidx using hpre
  have hi (o : O) : idx ⟨nr o,ha o⟩ = o := hnr (hidx ⟨nr o,ha o⟩)
  let lab : ↥A → Fin t := fun a => label (idx a)
  have hls : Function.Surjective lab := by
    intro i
    obtain ⟨o,rfl⟩ := hs i
    exact ⟨⟨nr o,ha o⟩,congrArg label (hi o)⟩
  have hc : KConnectedOn (G.induce (↑U : Set V)) univ (65536*A.card) := by
    rw [hAc]
    exact Knitting.induce_connected G U hconn
  obtain ⟨C,hC,hCC,hterm⟩ := Knitting.group_terminals (G.induce (↑U : Set V)) A lab hls
    (by omega) hc
  let M := Knitting.model_induce G U
  let D : Fin t → Set V := fun i => M.expand (C i)
  have hDU : ∀ i, D i ⊆ (↑U : Set V) := by
    intro i v hv
    obtain ⟨w,_,hw⟩ := hv
    have he : v = w.val := hw
    exact he ▸ w.property
  apply clique_of_occurrences (G := G) label B D hB
    (fun i => M.expand_connected (hC i)) hBB
    (fun i j hij => M.expand_disjoint (hCC i j hij))
    (fun o i => (hU o).mono_right (hDU i))
  · intro o
    refine ⟨port o,hp o,nbr o,?_,(hn o).2⟩
    refine ⟨nr o,?_,rfl⟩
    have ht := hterm ⟨nr o,ha o⟩
    simpa only [lab,hi] using ht
  · exact hpairs

theorem clique_from_private_models {Q : Type} [Fintype Q] [DecidableEq Q]
    (G : SimpleGraph V) {t a : ℕ} (ht : 1 ≤ t)
    (L : Q → Finset (Fin t)) (hL : ∀ q, (L q).card ≤ a)
    (hcover : ∀ i, ∃ q, i ∈ L q)
    (hpair : ∀ i j, i ≠ j → ∃ q, i ∈ L q ∧ j ∈ L q)
    (S : Q → Finset V) (U : Finset V)
    (hd : ∀ q r, q ≠ r → Disjoint (S q) (S r))
    (hSU : ∀ q, Disjoint (S q) U)
    (hm : ∀ q, HasCliqueMinor (G.induce (↑(S q) : Set V)) a)
    (hN : ∀ q, ∀ v ∈ S q, a*Fintype.card Q ≤ (U.filter (G.Adj v)).card)
    (hc : KConnectedOn G U (65536*(a*Fintype.card Q))) : HasCliqueMinor G t := by
  classical
  choose P hP using hm
  let M (q : Q) := Knitting.model_induce G (S q)
  let R (q : Q) (j : Fin a) : Set V := (M q).expand (P q j)
  have hRS : ∀ q j, R q j ⊆ (↑(S q) : Set V) := by
    intro q j v hv
    obtain ⟨w,_,hw⟩ := hv
    have he : v = w.val := hw
    exact he ▸ w.property
  let E (q : Q) : ↥(L q) ↪ Fin a :=
    (Fintype.equivFin ↥(L q)).toEmbedding.trans
      (Fin.castLEEmb (show Fintype.card ↥(L q) ≤ a by simpa using hL q))
  let O := Σ q : Q, ↥(L q)
  let label : O → Fin t := fun o => o.2.val
  let B : O → Set V := fun o => R o.1 (E o.1 o.2)
  have hsurj : Function.Surjective label := by
    intro i
    obtain ⟨q,hi⟩ := hcover i
    exact ⟨⟨q,⟨i,hi⟩⟩,rfl⟩
  have hbudget : Fintype.card O ≤ a*Fintype.card Q := by
    calc
      Fintype.card O = ∑ q, (L q).card := by simp [O,Fintype.card_sigma]
      _ ≤ ∑ _q : Q, a := sum_le_sum fun q _ => hL q
      _ = a*Fintype.card Q := by simp [mul_comm]
  have hO : 1 ≤ Fintype.card O := by
    have hx := Fintype.card_le_of_surjective label hsurj
    simp only [Fintype.card_fin] at hx
    omega
  apply clique_from_private_occurrences G label hsurj hO B U
  · intro o
    exact (M o.1).expand_connected ((hP o.1).1 _)
  · intro o p hop
    by_cases he : o.1 = p.1
    · obtain ⟨oq,oi⟩ := o
      obtain ⟨pq,pi⟩ := p
      dsimp at he
      subst pq
      apply (M oq).expand_disjoint
      apply (hP oq).2.1
      intro hij
      have hi := (E oq).injective hij
      exact hop (congrArg Subtype.val hi)
    · exact Set.disjoint_left.mpr (fun v hvo hvp =>
        Finset.disjoint_left.mp (hd o.1 p.1 he) (hRS _ _ hvo) (hRS _ _ hvp))
  · intro o
    exact Set.disjoint_left.mpr (fun v hv hu =>
      Finset.disjoint_left.mp (hSU o.1) (hRS _ _ hv) hu)
  · intro o v hv
    exact hbudget.trans (hN o.1 v (hRS _ _ hv))
  · exact Knitting.kConnected_mono hc (Nat.mul_le_mul_left 65536 hbudget)
  · intro i j hij
    obtain ⟨q,hi,hj⟩ := hpair i j hij
    let oi : O := ⟨q,⟨i,hi⟩⟩
    let oj : O := ⟨q,⟨j,hj⟩⟩
    have he : E q ⟨i,hi⟩ ≠ E q ⟨j,hj⟩ := fun h =>
      hij (congrArg Subtype.val ((E q).injective h))
    obtain ⟨v,hv,w,hw,hvw⟩ := (hP q).2.2 _ _ he
    exact ⟨oi,oj,rfl,rfl,v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,hvw⟩

theorem clique_from_block_models (G : SimpleGraph V) {t b x : ℕ}
    (ht : 1 ≤ t) (hx : 1 ≤ x) (htb : t ≤ b*x)
    (S : (Fin b × Fin b) → Finset V) (U : Finset V)
    (hd : ∀ q r, q ≠ r → Disjoint (S q) (S r))
    (hSU : ∀ q, Disjoint (S q) U)
    (hm : ∀ q, HasCliqueMinor (G.induce (↑(S q) : Set V)) (2*x))
    (hN : ∀ q, ∀ v ∈ S q, 2*x*b^2 ≤ (U.filter (G.Adj v)).card)
    (hc : KConnectedOn G U (65536*(2*x*b^2))) : HasCliqueMinor G t := by
  classical
  let block : Fin t → Fin b := fun i => ⟨i.val/x,(Nat.div_lt_iff_lt_mul (by omega)).mpr
    (i.isLt.trans_le htb)⟩
  let L (q : Fin b × Fin b) : Finset (Fin t) :=
    (univ.filter fun i => block i=q.1) ∪ (univ.filter fun i => block i=q.2)
  have hblock (j : Fin b) : (univ.filter fun i => block i=j).card ≤ x := by
    let A := univ.filter fun i => block i=j
    let f : ↥A → Fin x := fun i => ⟨i.val.val%x,Nat.mod_lt _ (by omega)⟩
    have hf : Function.Injective f := by
      intro i k he
      apply Subtype.ext
      apply Fin.ext
      have hid : i.val.val/x=j.val := congrArg Fin.val (mem_filter.mp i.property).2
      have hkd : k.val.val/x=j.val := congrArg Fin.val (mem_filter.mp k.property).2
      have hm : i.val.val%x=k.val.val%x := congrArg Fin.val he
      have hi := Nat.mod_add_div i.val.val x
      have hk := Nat.mod_add_div k.val.val x
      rw [hid] at hi
      rw [hkd] at hk
      omega
    have hh := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe,Fintype.card_fin] using hh
  refine clique_from_private_models G ht L (fun q => (card_union_le _ _).trans (by
    have h₁ := hblock q.1
    have h₂ := hblock q.2
    omega)) ?_ ?_ S U hd hSU hm ?_ ?_
  · intro i
    refine ⟨(block i,block i),?_⟩
    exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,rfl⟩)
  · intro i j _
    refine ⟨(block i,block j),?_,?_⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,rfl⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,rfl⟩)
  · intro q v hv
    simpa only [Fintype.card_prod,Fintype.card_fin,pow_two,mul_assoc] using hN q v hv
  · simpa only [Fintype.card_prod,Fintype.card_fin,pow_two,mul_assoc] using hc

end
end LinearListHadwiger.Assembly

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.ColorBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.ColorBins
open Finset Sampling
attribute [local instance] Classical.propDecidable
noncomputable section
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

lemma probability_all (μ : ι → Ω → ℝ) (A : ι → Ω → Prop) :
    probability (productMass μ) (fun f => ∀ i, A i (f i)) =
      ∏ i, probability (μ i) (A i) := by
  classical
  have he (f : ι → Ω) : (if ∀ i, A i (f i) then (1:ℝ) else 0) =
      ∏ i, if A i (f i) then (1:ℝ) else 0 := by
    by_cases h : ∀ i, A i (f i)
    · simp [h]
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨i,hi⟩ := h
      symm
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp_rw [probability_eq_expectation,he]
  exact expectation_product μ (fun i w => if A i w then (1:ℝ) else 0)

variable {Color Bin : Type} [Fintype Color] [Fintype Bin] [DecidableEq Color] [DecidableEq Bin]

lemma uniform_nonneg {Bin : Type} [Fintype Bin] [DecidableEq Bin] (b : Bin) : 0 ≤ uniform b := by dsimp [uniform]; positivity

lemma uniform_sum {Bin : Type} [Fintype Bin] [DecidableEq Bin] (hn : 1 ≤ Fintype.card Bin) : ∑ b : Bin, uniform b = 1 := by
  simp only [uniform,sum_const,nsmul_eq_mul,card_univ]
  have hh : (Fintype.card Bin : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card Bin ≠ 0)
  field_simp

lemma uniform_probability {Bin : Type} [Fintype Bin] [DecidableEq Bin] (R : Finset Bin) :
    probability uniform (fun b => b ∈ R) = R.card / (Fintype.card Bin : ℝ) := by
  classical
  unfold probability uniform
  have h := @Finset.sum_ite_mem_eq Bin ℝ _ _ R (fun _ => (1:ℝ) / Fintype.card Bin)
    (fun _ => Classical.propDecidable _)
  rw [h]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

lemma palette_miss (hn : 1 ≤ Fintype.card Bin) (L : Finset Color) (R : Finset Bin) :
    probability (productMass (fun _ : Color => (uniform : Bin → ℝ)))
      (fun f => ∀ c ∈ L, f c ∉ R) =
      (1-R.card/(Fintype.card Bin : ℝ))^L.card := by
  classical
  rw [probability_all (fun _ : Color => (uniform : Bin → ℝ))
    (fun c b => c ∈ L → b ∉ R)]
  have hc (c : Color) : probability (uniform : Bin → ℝ) (fun b => c ∈ L → b ∉ R) =
      if c ∈ L then 1-R.card/(Fintype.card Bin : ℝ) else 1 := by
    by_cases hc : c ∈ L
    · simp only [hc,true_implies,ite_true]
      rw [probability_not (uniform_sum hn),uniform_probability]
    · simp only [hc,false_implies,ite_false,probability,ite_true]
      exact uniform_sum hn
  simp_rw [hc]
  rw [←prod_filter]
  simp

lemma palette_miss_bound (hn : 1 ≤ Fintype.card Bin) (L : Finset Color) (R : Finset Bin) :
    probability (productMass (fun _ : Color => (uniform : Bin → ℝ)))
      (fun f => ∀ c ∈ L, f c ∉ R) ≤
      Real.exp (-(L.card:ℝ)*R.card/Fintype.card Bin) := by
  classical
  rw [palette_miss hn]
  have hn' : (0:ℝ) < Fintype.card Bin := by exact_mod_cast (by omega : 0 < Fintype.card Bin)
  have hR : (R.card:ℝ) ≤ Fintype.card Bin := by exact_mod_cast card_le_univ R
  have hp : 0 ≤ 1-(R.card:ℝ)/Fintype.card Bin := by
    have := (div_le_one hn').mpr hR
    linarith
  have he : 1-(R.card:ℝ)/Fintype.card Bin ≤ Real.exp (-(R.card:ℝ)/Fintype.card Bin) := by
    have hh := Real.add_one_le_exp (-(R.card:ℝ)/Fintype.card Bin)
    simp only [neg_div] at hh ⊢
    linarith
  calc
    _ ≤ (Real.exp (-(R.card:ℝ)/Fintype.card Bin))^L.card := pow_le_pow_left₀ hp he _
    _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring

lemma bad_block_witness {Color Bin : Type} [Fintype Color] [Fintype Bin] [DecidableEq Color] [DecidableEq Bin] (L : Finset Color) (T : Finset Bin) (f : Color → Bin)
    (h : 2*(occupied L T f).card < T.card) :
    ∃ R : ↥T.powerset, T.card ≤ 2*R.val.card ∧ ∀ c ∈ L, f c ∉ R.val := by
  classical
  let R := T \ L.image f
  have hR : R ⊆ T := sdiff_subset
  have hc : R.card+(occupied L T f).card=T.card := by
    simpa only [R,occupied] using card_sdiff_add_card_inter T (L.image f)
  refine ⟨⟨R,mem_powerset.mpr hR⟩,?_,?_⟩
  · change T.card ≤ 2*R.card
    omega
  · intro c hc hr
    exact (mem_sdiff.mp hr).2 (mem_image.mpr ⟨c,hc,rfl⟩)

lemma bad_block_probability (hn : 1 ≤ Fintype.card Bin) (L : Finset Color) (T : Finset Bin) :
    probability (productMass (fun _ : Color => (uniform : Bin → ℝ)))
      (fun f => 2*(occupied L T f).card < T.card) ≤
      (2:ℝ)^T.card * Real.exp (-(L.card:ℝ)*T.card/(2*Fintype.card Bin)) := by
  classical
  let μ := productMass (fun _ : Color => (uniform : Bin → ℝ))
  let A (R : ↥T.powerset) (f : Color → Bin) :=
    T.card ≤ 2*R.val.card ∧ ∀ c ∈ L, f c ∉ R.val
  have hμ : ∀ f, 0 ≤ μ f := productMass_nonneg (fun _ => uniform_nonneg)
  have hR (R : ↥T.powerset) : probability μ (A R) ≤
      Real.exp (-(L.card:ℝ)*T.card/(2*Fintype.card Bin)) := by
    by_cases hR : T.card ≤ 2*R.val.card
    · have hm := palette_miss_bound hn L R.val
      have hp : probability μ (A R) ≤ probability μ (fun f => ∀ c ∈ L, f c ∉ R.val) :=
        probability_mono hμ (fun _ h => h.2)
      refine hp.trans (hm.trans ?_)
      apply Real.exp_le_exp.mpr
      have hn' : (0:ℝ) < Fintype.card Bin := by exact_mod_cast (by omega : 0 < Fintype.card Bin)
      have hr : (T.card:ℝ) ≤ 2*R.val.card := by exact_mod_cast hR
      have hm : -(L.card:ℝ)*R.val.card ≤ -(L.card:ℝ)*T.card/2 := by
        nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg L.card : (0:ℝ) ≤ L.card)]
      calc
        _ ≤ (-(L.card:ℝ)*T.card/2)/Fintype.card Bin := div_le_div_of_nonneg_right hm hn'.le
        _ = _ := by ring
    · have he : probability μ (A R) = 0 := by simp [probability,A,hR]
      rw [he]
      exact (Real.exp_pos _).le
  calc
    _ ≤ probability μ (fun f => ∃ R, A R f) := probability_mono hμ (bad_block_witness L T)
    _ ≤ ∑ R, probability μ (A R) := probability_union_le hμ A
    _ ≤ ∑ _R : ↥T.powerset, Real.exp (-(L.card:ℝ)*T.card/(2*Fintype.card Bin)) :=
      sum_le_sum fun R _ => hR R
    _ = _ := by simp [Nat.cast_pow]

variable {V J : Type} [Fintype V] [Fintype J]

theorem exists_bins_finite (hn : 1 ≤ Fintype.card Bin)
    (L : V → Finset Color) (T : J → Finset Bin) {m : ℕ}
    (hm : ∀ v, m ≤ (L v).card)
    (htail : (Fintype.card V : ℝ) * ∑ j,
      (2:ℝ)^(T j).card * Real.exp (-(m:ℝ)*(T j).card/(2*Fintype.card Bin)) < 1) :
    ∃ f : Color → Bin, ∀ v j, (T j).card ≤ 2*(occupied (L v) (T j) f).card := by
  classical
  let μ := productMass (fun _ : Color => (uniform : Bin → ℝ))
  let bad (p : V × J) (f : Color → Bin) := 2*(occupied (L p.1) (T p.2) f).card < (T p.2).card
  have hμ : ∀ f, 0 ≤ μ f := productMass_nonneg (fun _ => uniform_nonneg)
  have hbad (p : V × J) : probability μ (bad p) ≤
      (2:ℝ)^(T p.2).card * Real.exp (-(m:ℝ)*(T p.2).card/(2*Fintype.card Bin)) := by
    apply (bad_block_probability hn (L p.1) (T p.2)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hm' : (m:ℝ) ≤ (L p.1).card := by exact_mod_cast hm p.1
    nlinarith [mul_le_mul_of_nonneg_right hm' (Nat.cast_nonneg (T p.2).card : (0:ℝ) ≤ (T p.2).card)]
  have hf : probability μ (fun f => ∃ p, bad p f) < 1 := by
    apply lt_of_le_of_lt (probability_union_le hμ bad)
    apply lt_of_le_of_lt (sum_le_sum fun p _ => hbad p)
    simpa [Fintype.sum_prod_type] using htail
  have hex : ∃ f, ¬ ∃ p, bad p f := by
    by_contra hn
    push Not at hn
    have he : probability μ (fun f => ∃ p, bad p f) = 1 := by
      simp only [probability,hn,ite_true]
      exact productMass_sum (fun _ => uniform_sum (by assumption))
    linarith
  obtain ⟨f,hf⟩ := hex
  refine ⟨f,?_⟩
  intro v j
  by_contra h
  exact hf ⟨(v,j),by dsimp [bad]; omega⟩

omit [Fintype Color] in

theorem exists_bins (hn : 1 ≤ Fintype.card Bin)
    (L : V → Finset Color) (T : J → Finset Bin) {m : ℕ}
    (hm : ∀ v, m ≤ (L v).card)
    (htail : (Fintype.card V : ℝ) * ∑ j,
      (2:ℝ)^(T j).card * Real.exp (-(m:ℝ)*(T j).card/(2*Fintype.card Bin)) < 1) :
    ∃ f : Color → Bin, ∀ v j, (T j).card ≤ 2*(occupied (L v) (T j) f).card := by
  classical
  let P : Finset Color := univ.biUnion L
  have hP {v : V} {c : Color} (hc : c ∈ L v) : c ∈ P :=
    mem_biUnion.mpr ⟨v,mem_univ _,hc⟩
  let emb (v : V) : ↥(L v) ↪ ↥P :=
    ⟨fun c => ⟨c.val,hP c.property⟩,fun a b h => Subtype.ext (congrArg (fun z : ↥P => z.val) h)⟩
  let L' (v : V) : Finset ↥P := (L v).attach.map (emb v)
  have hcard (v : V) : (L' v).card=(L v).card := by simp [L']
  obtain ⟨f,hf⟩ := exists_bins_finite hn L' T
    (m := m) (fun v => by rw [hcard]; exact hm v) htail
  have hne : Nonempty Bin := Fintype.card_pos_iff.mp (by omega)
  let b0 : Bin := Classical.choice hne
  let g : Color → Bin := fun c => if hc : c ∈ P then f ⟨c,hc⟩ else b0
  have hg (v : V) : (L' v).image f=(L v).image g := by
    ext b
    constructor
    · intro hb
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hc
      refine mem_image.mpr ⟨a.val,a.property,?_⟩
      simp only [g,dite_eq_left (hP a.property)]
      rfl
    · intro hb
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
      refine mem_image.mpr ⟨emb v ⟨c,hc⟩,mem_map.mpr ⟨⟨c,hc⟩,mem_attach _ _,rfl⟩,?_⟩
      simp only [g,dite_eq_left (hP hc)]
      rfl
  refine ⟨g,fun v j => ?_⟩
  simpa only [occupied, hg] using hf v j

omit [Fintype Color] [Fintype Bin] [DecidableEq Color] [DecidableEq Bin] [Fintype V] in

theorem listColorable_of_bin_cover (G : SimpleGraph V) (L : V → Finset Color)
    (f : Color → Bin) (S : Bin → Finset V)
    (hstable : ∀ b, Fractional.Stable G (S b))
    (hcover : ∀ v, ∃ b, v ∈ S b ∧ ∃ c ∈ L v, f c=b) :
    ListColorable G L := by
  classical
  choose b hb c hc he using hcover
  refine ⟨c,hc,?_⟩
  intro v w hav hcw
  have hbw : b v=b w := by rw [←he v,←he w,hcw]
  exact hstable (b v) v (hb v) w (hbw.symm ▸ hb w) hav

end
end LinearListHadwiger.ColorBins

namespace LinearListHadwiger.Fractional
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

theorem distribution (G : SimpleGraph V) {r : ℝ} (hr : 0 < r)
    (hf : number G ≤ r) :
    ∃ π : Finset V → ℝ, (∀ I, 0 ≤ π I) ∧ (∑ I, π I = 1) ∧
      (∀ I, π I ≠ 0 → Stable G I) ∧ ∀ v, marginal π v=1/r := by
  classical
  obtain ⟨μ,hμ,hm⟩ := (number_le_iff G r).mp hf
  obtain ⟨ν,hν,hcost,hex⟩ := exact_cover G hμ
  have hc : cost ν ≤ r := hcost ▸ hm
  let π : Finset V → ℝ := fun I => ν I/r + if I=∅ then 1-cost ν/r else 0
  have hp : 0 ≤ 1-cost ν/r := by have := (div_le_one hr).mpr hc; linarith
  refine ⟨π,?_,?_,?_,?_⟩
  · intro I
    exact add_nonneg (div_nonneg (hν.1 I) hr.le) (by split_ifs; exact hp; exact le_rfl)
  · simp only [π,sum_add_distrib,←sum_div,cost]
    simp
  · intro I hI
    by_cases he : I=∅
    · subst I; exact stable_empty G
    · by_contra h
      exact hI (by simp [π,he,hν.2.1 I h])
  · intro v
    have he (I : Finset V) : (if v ∈ I then π I else 0) =
        (if v ∈ I then ν I else 0)/r := by
      by_cases hv : v ∈ I
      · have hi : I ≠ ∅ := by rintro rfl; simp at hv
        simp [π,hv,hi]
      · simp [hv]
    simp only [marginal,he,←sum_div]
    rw [show (∑ I,if v∈I then ν I else 0)=1 from hex v]

end LinearListHadwiger.Fractional

namespace LinearListHadwiger.Cleanup
open Finset Sampling Fractional
attribute [local instance] Classical.propDecidable
variable {V Bin : Type} [Fintype V] [Fintype Bin] [DecidableEq V] [DecidableEq Bin]

lemma probability_membership (π : Finset V → ℝ) (v : V) :
    probability π (fun I => v∈I)=marginal π v := by
  unfold probability marginal
  apply sum_congr rfl
  intro I _
  split_ifs <;> rfl

theorem stable_cover (G : SimpleGraph V) {r e : ℝ} (hr : 0 < r) (he : 0 ≤ e)
    (hf : number G ≤ r) (E : Bin → Finset V)
    (hE : ∀ v, e ≤ (univ.filter (fun b => v ∈ E b)).card)
    (htail : (Fintype.card V : ℝ)*Real.exp (-e/r) < 1) :
    ∃ S : Bin → Finset V, (∀ b, Stable G (S b)) ∧
      ∀ v, ∃ b, v ∈ E b ∧ v ∈ S b := by
  classical
  obtain ⟨π,hπ,hs,hstable,hmarg⟩ := distribution G hr hf
  let μ := productMass (fun _ : Bin => π)
  let bad (v : V) (x : Bin → Finset V) := v ∈ remainder E id x
  have hμ : ∀ x, 0 ≤ μ x := productMass_nonneg (fun _ => hπ)
  have hsum : ∑ x, μ x=1 := productMass_sum (fun _ => hs)
  have hp (v : V) : probability μ (bad v) ≤ Real.exp (-e/r) := by
    have hm (b : Bin) (w : V) : probability π (fun I : Finset V => w ∈ id I)=1/r := by
      simpa only [id_eq,probability_membership] using hmarg w
    change probability (productMass (fun _ : Bin => π)) (fun x => v ∈ remainder E id x) ≤ _
    rw [remainder_survival_power (fun _ => hs) E id hm v]
    have hpr : 1/r ≤ 1 := by
      have hh : probability π (fun I => v∈I) ≤ 1 := by
        calc
          _ ≤ probability π (fun _ => True) := probability_mono hπ (fun _ _ => trivial)
          _ = 1 := by simpa [probability] using hs
      rw [probability_membership] at hh
      rwa [hmarg v] at hh
    have hb : 0 ≤ 1-1/r := by linarith
    have hex : 1-1/r ≤ Real.exp (-(1/r)) := by
      have hh := Real.add_one_le_exp (-(1/r)); linarith
    calc
      _ ≤ (Real.exp (-(1/r)))^(univ.filter (fun b => v∈E b)).card :=
        pow_le_pow_left₀ hb hex _
      _ = Real.exp (-((univ.filter (fun b => v∈E b)).card:ℝ)/r) := by
        rw [←Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg ((le_max_right 0 e).trans ((max_eq_right he).le.trans (hE v)))) hr.le)
  have hb : probability μ (fun x => ∃ v, bad v x) < 1 := by
    calc
      _ ≤ ∑ v, probability μ (bad v) := probability_union_le hμ bad
      _ ≤ ∑ _v : V, Real.exp (-e/r) := sum_le_sum fun v _ => hp v
      _ = (Fintype.card V:ℝ)*Real.exp (-e/r) := by simp [nsmul_eq_mul]
      _ < 1 := htail
  obtain ⟨x,hx,hgood⟩ := exists_positive_avoiding hμ hsum hb
  have hx' (b : Bin) : π (x b) ≠ 0 := by
    intro hz
    have hz' : μ x=0 := prod_eq_zero (mem_univ b) hz
    linarith
  refine ⟨x,fun b => hstable _ (hx' b),?_⟩
  intro v
  by_contra hv
  push Not at hv
  exact hgood ⟨v,(mem_remainder E id x v).mpr hv⟩

theorem cleanup_source (G : SimpleGraph V) {t : ℝ} (ht : 1 < t)
    (horder : (Fintype.card V:ℝ) ≤ t ^ (11/10:ℝ))
    (hf : number G ≤ t / Real.log t) (E : Bin → Finset V)
    (hE : ∀ v, 8*t ≤ (univ.filter (fun b => v∈E b)).card) :
    ∃ S : Bin → Finset V, (∀ b, Stable G (S b)) ∧
      ∀ v, ∃ b, v ∈ E b ∧ v ∈ S b := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  apply stable_cover G (div_pos ht0 hl) (by positivity) hf E hE
  have hex : -(8*t)/(t/Real.log t)= -8*Real.log t := by
    field_simp
  calc
    _ ≤ t^(11/10:ℝ)*Real.exp (-(8*t)/(t/Real.log t)) :=
      mul_le_mul_of_nonneg_right horder (Real.exp_pos _).le
    _ = Real.exp ((11/10-8)*Real.log t) := by
      rw [hex,Real.rpow_def_of_pos ht0,←Real.exp_add]
      congr 1
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)

end LinearListHadwiger.Cleanup

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

namespace LinearListHadwiger

lemma HasCliqueMinor.restrict {V : Type} {G : SimpleGraph V} {a b : ℕ}
    (h : HasCliqueMinor G b) (hab : a ≤ b) : HasCliqueMinor G a := by
  obtain ⟨B,hB,hBB,hE⟩ := h
  let e : Fin a → Fin b := fun i => ⟨i.val,i.isLt.trans_le hab⟩
  have he : Function.Injective e := fun _ _ h => Fin.ext (congrArg (fun z : Fin b => z.val) h)
  exact ⟨B ∘ e,fun i => hB (e i),fun i j hij => hBB _ _ (fun h => hij (he h)),
    fun i j hij => hE _ _ (fun h => hij (he h))⟩

namespace Sampling
open Filter Finset Fractional
attribute [local instance] Classical.propDecidable

theorem eligible_thinning_or_fractional_counterexample :
    ∃ T : ℝ, ∀ (t : ℕ) (n r : ℝ), T ≤ (t:ℝ) → 1 ≤ n → n ≤ (t:ℝ)^(11/10:ℝ) →
      (t:ℝ)/Real.log t ≤ r → r ≤ 4*t →
      let N := ⌈192*r*Real.log (2*max 1 ((t:ℝ)/r))⌉₊
      ∀ (V : Type) [Fintype V] [DecidableEq V], ∀ G : SimpleGraph V,
      (Fintype.card V : ℝ) ≤ n → hadwigerNumber G < t → number G ≤ r →
      ∀ E : Fin N → Finset V,
      (∀ v, (N:ℝ)/2 ≤ (univ.filter (fun j => v∈E j)).card) →
      (∃ J : Fin N → Finset V, (∀ j, Stable G (J j)) ∧
        number (G.induce (↑(univ\univ.biUnion (fun j => J j∩E j)) : Set V)) ≤ r/2) ∨
      ∃ S : Finset V, 4*(hadwigerNumber (G.induce (↑S:Set V)):ℝ) <
        number (G.induce (↑S:Set V)) := by
  classical
  obtain ⟨T₀,hT₀⟩ := source_thinning_failure_structure
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp parameter_range_cutoff
  refine ⟨max (max T₀ T₁) 2,?_⟩
  intro t n r ht hn hnt hrl hru
  dsimp only
  intro V _ _ G hord hminor hf E hE
  by_contra hnone
  have hfail : ∀ J : Fin ⌈192*r*Real.log (2*max 1 ((t:ℝ)/r))⌉₊ → Finset V,
      (∀ j, Stable G (J j)) →
      r/2 < number (G.induce
        (↑(univ\univ.biUnion (fun j => J j∩E j)) : Set V)) := by
    intro J hJ
    by_contra hj
    exact hnone (Or.inl ⟨J,hJ,le_of_not_gt hj⟩)
  have hbound (S : Finset V) : number (G.induce (↑S:Set V)) ≤
      4*(hadwigerNumber (G.induce (↑S:Set V)):ℝ) :=
    le_of_not_gt (fun hs => hnone (Or.inr ⟨S,hs⟩))
  have ht₀ := ((le_max_left T₀ T₁).trans (le_max_left _ _)).trans ht
  have ht₁ := ((le_max_right T₀ T₁).trans (le_max_left _ _)).trans ht
  have ht₂ : (2:ℝ) ≤ t := (le_max_right _ _).trans ht
  have htpos : 0 < (t:ℝ) := by linarith
  have htNat : 1 ≤ t := by exact_mod_cast (show (1:ℝ) ≤ t by linarith)
  have hp := hT₁ (t:ℝ) ht₁
  obtain ⟨hr,hy,_,_,_⟩ := hp.2.2 r hrl hru
  let x := ⌊r/200⌋₊
  let b := ⌈(t:ℝ)/(x:ℝ)⌉₊
  let q := b^2
  let k := ⌈(1000000*65536:ℝ)*(t:ℝ)*max 1 ((t:ℝ)/r)⌉₊
  have hx : 1 ≤ x := (floor_parameter htpos hr hy (le_max_right _ _)).1
  have hxpos : 0 < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have htb : t ≤ b*x := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    exact (div_le_iff₀ hxpos).mp (Nat.le_ceil ((t:ℝ)/(x:ℝ)))
  obtain ⟨H,U,S,hH,hSS,hSU,hfS,hN,hC⟩ :=
    hT₀ (t:ℝ) n r ht₀ hn hnt hrl hru V G hord hf E hE hfail
  have hb := attachment_budget (γ := 65536) htpos hr hru hy
    (le_max_right 1 ((t:ℝ)/r)) (by norm_num)
  change r ≤ (k:ℝ) ∧ 64*(2*x*q) < k ∧ 65536*(2*x*q) ≤ k/32 at hb
  let e : (Fin b × Fin b) ≃ Fin q := Fintype.equivOfCardEq (by simp [q,pow_two])
  have hm (i : Fin q) : HasCliqueMinor (G.induce (↑(S i):Set V)) (2*x) := by
    apply (hasCliqueMinor_hadwigerNumber (G.induce (↑(S i):Set V))).restrict
    have hs := hbound (S i)
    have hf' := hfS i
    have hx' : (x:ℝ) ≤ r/200 := Nat.floor_le (by linarith)
    have hh : ((2*x:ℕ):ℝ) ≤ hadwigerNumber (G.induce (↑(S i):Set V)) := by
      push_cast
      nlinarith
    exact_mod_cast hh
  have hcl := Assembly.clique_from_block_models G htNat hx htb
    (fun z => S (e z)) (H\U)
    (fun i j hij => hSS _ _ (fun he => hij (e.injective he)))
    (fun i => disjoint_left.mpr (fun v hv hu =>
      (mem_sdiff.mp hu).2 (mem_inter.mp (hSU _ hv)).2))
    (fun i => hm (e i))
    (fun i v hv => by
      have hh := hN v (mem_inter.mp (hSU _ hv)).1
      change k ≤ 2*((H\U).filter (G.Adj v)).card at hh
      change 2*x*q ≤ ((H\U).filter (G.Adj v)).card
      omega)
    (Knitting.kConnected_mono hC hb.2.2)
  exact (not_lt_of_ge (cliqueMinor_le_hadwigerNumber hcl)) hminor

end Sampling
end LinearListHadwiger

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

lemma rate_pos {t : ℝ} (ht : 0 < t) (j : ℕ) : 0 < rate t j := by
  unfold rate
  positivity

lemma rate_zero (t : ℝ) : rate t 0=4*t := by simp [rate]
lemma rate_succ (t : ℝ) (j : ℕ) : rate t (j+1)=rate t j/2 := by
  simp only [rate,pow_succ]
  ring

lemma rate_le {t : ℝ} (ht : 0 ≤ t) (j : ℕ) : rate t j ≤ 4*t := by
  exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))

lemma geometric_budget (m : ℕ) :
    ∑ j ∈ range m, ((j:ℝ)+1)/(2:ℝ)^j ≤ 4 := by
  have he : (∑ j ∈ range m, ((j:ℝ)+1)/(2:ℝ)^j)+2*((m:ℝ)+2)/(2:ℝ)^m=4 := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [sum_range_succ]
      push_cast
      rw [pow_succ]
      calc
        _ = (∑ j ∈ range m, ((j:ℝ)+1)/(2:ℝ)^j)+2*((m:ℝ)+2)/(2:ℝ)^m := by ring
        _ = 4 := ih
  have : 0 ≤ 2*((m:ℝ)+2)/(2:ℝ)^m := by positivity
  linarith

lemma bins_upper {t : ℝ} (ht : 0 < t) (j : ℕ) :
    (bins t j : ℝ) ≤ 768*t*(((j:ℝ)+1)/(2:ℝ)^j)+1 := by
  have hp : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have he : t/rate t j=(2:ℝ)^j/4 := by unfold rate; field_simp
  have hy : max 1 (t/rate t j) ≤ (2:ℝ)^j := by rw [he]; exact max_le hp (by linarith)
  have hy0 : 0 < 2*max 1 (t/rate t j) := by have := le_max_left 1 (t/rate t j); linarith
  have hl : Real.log (2*max 1 (t/rate t j)) ≤ (j:ℝ)+1 := by
    calc
      _ ≤ Real.log ((2:ℝ)^(j+1)) := Real.log_le_log hy0 (by rw [pow_succ]; nlinarith)
      _ = ((j:ℝ)+1)*Real.log 2 := by rw [Real.log_pow]; push_cast; rfl
      _ ≤ _ := by nlinarith [Real.log_two_lt_d9]
  have hnonneg : 0 ≤ 192*rate t j*Real.log (2*max 1 (t/rate t j)) := by
    have hh : 1 ≤ 2*max 1 (t/rate t j) := by have := le_max_left 1 (t/rate t j); linarith
    exact mul_nonneg (by positivity [rate_pos ht j]) (Real.log_nonneg hh)
  have hb := (Nat.ceil_lt_add_one hnonneg).le
  change (bins t j:ℝ) ≤ _ at hb
  calc
    _ ≤ 192*rate t j*Real.log (2*max 1 (t/rate t j))+1 := hb
    _ ≤ 192*rate t j*((j:ℝ)+1)+1 := by gcongr; have := rate_pos ht j; positivity
    _ = _ := by unfold rate; ring

lemma bins_lower {t : ℝ} (ht : 1 < t) (j : ℕ)
    (hr : t/Real.log t ≤ rate t j) : t/Real.log t ≤ (bins t j:ℝ) := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < Real.log t := Real.log_pos ht
  have hlog : Real.log 2 ≤ Real.log (2*max 1 (t/rate t j)) :=
    Real.log_le_log (by norm_num) (by have := le_max_left 1 (t/rate t j); linarith)
  have hlg : 1 ≤ 192*Real.log (2*max 1 (t/rate t j)) := by linarith [Real.log_two_gt_d9]
  calc
    _ ≤ rate t j := hr
    _ ≤ 192*rate t j*Real.log (2*max 1 (t/rate t j)) := by nlinarith [rate_pos ht0 j]
    _ ≤ (bins t j:ℝ) := Nat.le_ceil _

lemma power_two_lower (m : ℕ) : (m:ℝ)+1 ≤ (2:ℝ)^m := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [pow_succ]; push_cast; nlinarith

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

theorem schedule_exists (t : ℕ) (ht : 1 < (t:ℝ))
    (hl : 1 ≤ Real.log t) (hlog : 4*Real.log t ≤ t)
    (hp : (t:ℝ)^(7/10:ℝ) ≤ (t:ℝ)/Real.log t) :
    ∃ m : ℕ, m ≤ t ∧ rate t m < (t:ℝ)/Real.log t ∧
      (∀ j < m, (t:ℝ)/Real.log t ≤ rate t j ∧ rate t j ≤ 4*t) ∧
      (∑ j ∈ range m, bins t j)+16*t ≤ 4096*t ∧
      (∀ j < m, (t:ℝ)^(7/10:ℝ) ≤ (bins t j:ℝ)) ∧
      (t:ℝ)^(7/10:ℝ) ≤ 16*t := by
  have ht0 : 0 < (t:ℝ) := by linarith
  have hl0 : 0 < Real.log t := by linarith
  have hlast : rate t t < (t:ℝ)/Real.log t := by
    dsimp [rate]
    apply (div_lt_div_iff₀ (by positivity) hl0).mpr
    have hh := power_two_lower t
    nlinarith
  let m := Nat.find (show ∃ m, rate t m < (t:ℝ)/Real.log t from ⟨t,hlast⟩)
  have hm : m ≤ t := Nat.find_min' _ hlast
  have hterm : rate t m < (t:ℝ)/Real.log t :=
    Nat.find_spec (show ∃ m, rate t m < (t:ℝ)/Real.log t from ⟨t,hlast⟩)
  have hvalid : ∀ j < m, (t:ℝ)/Real.log t ≤ rate t j := by
    intro j hj
    exact le_of_not_gt (Nat.find_min (show ∃ m, rate t m < (t:ℝ)/Real.log t from ⟨t,hlast⟩) hj)
  refine ⟨m,hm,hterm,fun j hj => ⟨hvalid j hj,rate_le ht0.le j⟩,?_,?_,?_⟩
  · apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    have hs : (∑ j ∈ range m, (bins t j:ℝ)) ≤ 3072*t+(m:ℝ) := by
      calc
        _ ≤ ∑ j ∈ range m, (768*(t:ℝ)*(((j:ℝ)+1)/(2:ℝ)^j)+1) :=
          sum_le_sum fun j _ => bins_upper ht0 j
        _ = 768*(t:ℝ)*(∑ j ∈ range m, ((j:ℝ)+1)/(2:ℝ)^j)+(m:ℝ) := by
          rw [sum_add_distrib,←mul_sum]; simp
        _ ≤ _ := by have := geometric_budget m; nlinarith
    have hm' : (m:ℝ) ≤ t := by exact_mod_cast hm
    nlinarith
  · exact fun j hj => hp.trans (bins_lower ht j (hvalid j hj))
  · exact hp.trans ((div_le_self ht0.le hl).trans (by nlinarith))

theorem palette_tail_cutoff : ∀ᶠ t : ℝ in atTop,
    ∀ (n b j : ℕ) (u : Fin j → ℕ), n ≤ t^(11/10:ℝ) → 1 ≤ b →
      (b:ℝ) ≤ 4096*t → (j:ℝ) ≤ t+1 →
      (∀ i, t^(7/10:ℝ) ≤ (u i:ℝ)) →
      (n:ℝ)*(∑ i, (2:ℝ)^(u i)*Real.exp (-(32768*t)*(u i)/(2*b))) < 1 := by
  have hh := Sampling.polynomial_tail_cutoff 1 (21/10) (show (0:ℝ)<1 by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hh] with t ht hh
  intro n b j u hn hb hb' hj hu
  have ht0 : 0<t := by linarith
  have hb0 : 0 < (b:ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hratio : 4 ≤ (32768*t)/(2*b) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hterm (i : Fin j) : (2:ℝ)^(u i)*Real.exp (-(32768*t)*(u i)/(2*b)) ≤
      Real.exp (-t^(7/10:ℝ)) := by
    have he : (2:ℝ)^(u i)=Real.exp ((u i:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [he,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he' : -(32768*t)*(u i)/(2*b)= -((32768*t)/(2*b))*(u i) := by ring
    rw [he']
    have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hmul := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg (u i))
    have hmul' := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (u i))
    nlinarith [hu i]
  calc
    _ ≤ (n:ℝ)*(∑ _i : Fin j, Real.exp (-t^(7/10:ℝ))) := by gcongr with i; exact hterm i
    _ = (n:ℝ)*((j:ℝ)*Real.exp (-t^(7/10:ℝ))) := by simp [nsmul_eq_mul]
    _ ≤ t^(11/10:ℝ)*((2*t)*Real.exp (-t^(7/10:ℝ))) := by gcongr; linarith
    _ = 1*t^(21/10:ℝ)*(2*Real.exp (-t^(7/10:ℝ))) := by
      have he : t^(11/10:ℝ)*t=t^(21/10:ℝ) := by
        calc
          _ = t^(11/10:ℝ)*t^(1:ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [←Real.rpow_add ht0]; norm_num
      rw [show t^(11/10:ℝ)*((2*t)*Real.exp (-t^(7/10:ℝ))) =
        2*(t^(11/10:ℝ)*t)*Real.exp (-t^(7/10:ℝ)) by ring,he]
      ring
    _ < 1 := hh

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

lemma number_le_four (G : SimpleGraph V) (h : ¬FractionalObstruction G) :
    number G ≤ 4*(hadwigerNumber G:ℝ) := by
  have hh : number (G.induce (↑(univ:Finset V):Set V)) ≤
      4*(hadwigerNumber (G.induce (↑(univ:Finset V):Set V)):ℝ) :=
    le_of_not_gt (fun hn => h ⟨univ,hn⟩)
  have he : G=(G.induce (↑(univ:Finset V):Set V)).comap
      (fun v => ⟨v,mem_univ v⟩) := rfl
  have hn : number G ≤ number (G.induce (↑(univ:Finset V):Set V)) := by
    rw [he]
    exact number_comap _ _
  have hm := (Knitting.model_induce G univ).hadwiger_le
  have hm' : (hadwigerNumber (G.induce (↑(univ:Finset V):Set V)):ℝ) ≤ hadwigerNumber G := by
    exact_mod_cast hm
  linarith

omit [Fintype V] in
lemma stable_image {G : SimpleGraph V} {R : Finset V} {A : Finset (↑R:Set V)}
    (h : Stable (G.induce (↑R:Set V)) A) : Stable G (A.image Subtype.val) := by
  intro u hu v hv hav
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
  exact h a ha b hb hav

lemma runBlock_none (t m : ℕ) : (runBlock t m none).card=16*t := by
  simp [runBlock]

lemma runBlock_some (t m : ℕ) (j : Fin m) :
    (runBlock t m (some j)).card=bins t j.val := by simp [runBlock]

lemma runPalette_card (t m : ℕ) :
    Fintype.card (RunPalette t m)=(∑ j∈range m,bins t j)+16*t := by
  simp only [RunPalette,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range]

omit [Fintype V] [DecidableEq V] in
lemma stable_extend {A B : Type} [DecidableEq B] (G : SimpleGraph V)
    (e : A → B) (he : Function.Injective e) (S : A → Finset V)
    (hs : ∀ a, Stable G (S a)) (b : B) :
    Stable G (Function.extend e S (fun _ => ∅) b) := by
  by_cases hb : ∃ a,e a=b
  · obtain ⟨a,rfl⟩ := hb
    rw [he.extend_apply]
    exact hs a
  · rw [Function.extend_apply' _ _ _ hb]
    intro v hv
    simp at hv

theorem stage_cover_or_obstruction :
    ∃ T : ℝ, ∀ (t m : ℕ), T ≤ (t:ℝ) →
      (∀ j < m, (t:ℝ)/Real.log t ≤ rate t j ∧ rate t j ≤ 4*t) →
      ∀ (V : Type) [Fintype V] [DecidableEq V], ∀ G : SimpleGraph V,
      (Fintype.card V:ℝ) ≤ (t:ℝ)^(11/10:ℝ) → hadwigerNumber G < t →
      ∀ E : RunPalette t m → Finset V,
      (∀ (j : Fin m) (v : V), (bins t j.val:ℝ)/2 ≤
        (univ.filter (fun b => v ∈ E (stageBin t m j b))).card) →
      FractionalObstruction G ∨ ∀ k ≤ m, ∃ (R : Finset V) (S : RunPalette t m → Finset V),
        number (G.induce (↑R:Set V)) ≤ rate t k ∧
        (∀ b, Stable G (S b)) ∧
        (∀ b v, v∈S b → binIndex b < k) ∧
        (∀ v, v∉R → ∃ b, v∈S b ∧ v∈E b) := by
  classical
  obtain ⟨T,hT⟩ := Sampling.eligible_thinning_or_fractional_counterexample
  refine ⟨max T 2,?_⟩
  intro t m ht hvalid V _ _ G hord hminor E hE
  by_cases hob : FractionalObstruction G
  · exact Or.inl hob
  right
  have htT : T ≤ (t:ℝ) := (le_max_left _ _).trans ht
  have ht2 : (2:ℝ) ≤ t := (le_max_right _ _).trans ht
  have hn : 1 ≤ (t:ℝ)^(11/10:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  intro k hk
  induction k with
  | zero =>
    refine ⟨univ,fun _ => ∅,?_,?_,?_,?_⟩
    · rw [rate_zero]
      have hh := number_le_four G hob
      have hm : (hadwigerNumber G:ℝ) ≤ t := by exact_mod_cast hminor.le
      have hb : number G ≤ 4*(t:ℝ) := by linarith only [hh,hm]
      exact (number_comap G (Subtype.val : (↑(univ:Finset V):Set V) → V)).trans hb
    · intro b v hv; simp at hv
    · intro b v hv; simp at hv
    · intro v hv; exact (hv (mem_univ v)).elim
  | succ k ih =>
    obtain ⟨R,S,hf,hS,hsupp,hcover⟩ := ih (by omega)
    let j : Fin m := ⟨k,by omega⟩
    let H := G.induce (↑R:Set V)
    let E' (b : Fin (bins t k)) : Finset (↑R:Set V) :=
      univ.filter (fun v => v.val ∈ E (stageBin t m j b))
    have hE' (v : (↑R:Set V)) : (bins t k:ℝ)/2 ≤
        (univ.filter (fun b => v∈E' b)).card := by
      simpa only [E',mem_filter,mem_univ,true_and] using hE j v.val
    have hhord : (Fintype.card (↑R:Set V):ℝ) ≤ (t:ℝ)^(11/10:ℝ) := by
      have hc : Fintype.card (↑R:Set V) ≤ Fintype.card V := Fintype.card_subtype_le _
      have hc' : (Fintype.card (↑R:Set V):ℝ) ≤ Fintype.card V := by exact_mod_cast hc
      exact hc'.trans hord
    have hhminor : hadwigerNumber H < t := (Knitting.model_induce G R).hadwiger_le.trans_lt hminor
    have hh := hT t ((t:ℝ)^(11/10:ℝ)) (rate t k) htT hn le_rfl
      (hvalid k (by omega)).1 (hvalid k (by omega)).2
      (↑R:Set V) H hhord hhminor hf E' hE'
    rcases hh with ⟨A,hA,hrem⟩ | hbad
    · change Fin (bins t k) → Finset (↑R:Set V) at A
      let Q : Finset (↑R:Set V) := univ\univ.biUnion (fun b => A b∩E' b)
      let R' := Q.image Subtype.val
      let e := stageBin t m j
      have he : Function.Injective e := stageBin_injective t m j
      let A' (b : Fin (bins t k)) : Finset V := (A b).image Subtype.val
      let D := Function.extend e A' (fun _ => ∅)
      have hD : ∀ b, Stable G (D b) := stable_extend G e he A' (fun b => stable_image (hA b))
      have hs (b : RunPalette t m) (hb : binIndex b=k) : S b=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        have := hsupp b v hv
        omega
      have hds (b : RunPalette t m) (v : V) (hv : v∈D b) : binIndex b=k := by
        by_cases hb : ∃ a,e a=b
        · obtain ⟨a,rfl⟩ := hb; rfl
        · have hd : D b=∅ := Function.extend_apply' _ _ _ hb
          rw [hd] at hv
          simp at hv
      refine ⟨R',fun b => S b∪D b,?_,?_,?_,?_⟩
      · rw [←number_iso (induceImageIso G R Q),rate_succ]
        exact hrem
      · intro b
        change Stable G (S b∪D b)
        by_cases hb : binIndex b=k
        · rw [hs b hb,empty_union]; exact hD b
        · have hd : D b=∅ := eq_empty_iff_forall_notMem.mpr (fun v hv => hb (hds b v hv))
          rw [hd,union_empty]; exact hS b
      · intro b v hv
        rcases mem_union.mp hv with hv | hv
        · exact (hsupp b v hv).trans (Nat.lt_succ_self _)
        · rw [hds b v hv]; omega
      · intro v hv
        by_cases hvr : v∈R
        · let v' : (↑R:Set V) := ⟨v,hvr⟩
          have hvq : v'∉Q := fun hh => hv (mem_image.mpr ⟨v',hh,rfl⟩)
          have hva : v'∈univ.biUnion (fun b => A b∩E' b) := by
            by_contra h
            exact hvq (mem_sdiff.mpr ⟨mem_univ _,h⟩)
          obtain ⟨a,_,ha⟩ := mem_biUnion.mp hva
          refine ⟨e a,mem_union_right _ ?_,(mem_filter.mp (mem_inter.mp ha).2).2⟩
          change v ∈ Function.extend e A' (fun _ => ∅) (e a)
          erw [he.extend_apply]
          exact mem_image.mpr ⟨v',(mem_inter.mp ha).1,rfl⟩
        · obtain ⟨b,hb,hbe⟩ := hcover v hvr
          exact ⟨b,mem_union_left _ hb,hbe⟩
    · exact (hob (obstruction_induce G R hbad)).elim

lemma occupied_image_card {A B Color : Type} [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (L : Finset Color) (f : Color → B) :
    (ColorBins.occupied L (univ.map e) f).card=
      (univ.filter (fun a => ∃ c∈L, f c=e a)).card := by
  classical
  have he : ColorBins.occupied L (univ.map e) f =
      (univ.filter (fun a => ∃ c∈L, f c=e a)).map e := by
    ext b
    simp only [ColorBins.occupied,mem_inter,mem_map,mem_univ,true_and,mem_image,mem_filter]
    constructor
    · rintro ⟨⟨a,rfl⟩,c,hc,he⟩
      exact ⟨a,⟨c,hc,he⟩,rfl⟩
    · rintro ⟨a,⟨c,hc,he⟩,rfl⟩
      exact ⟨⟨a,rfl⟩,c,hc,he⟩
  rw [he,card_map]

lemma finish_cover (t m : ℕ) (G : SimpleGraph V) (ht : 1 < (t:ℝ))
    (horder : (Fintype.card V:ℝ) ≤ (t:ℝ)^(11/10:ℝ))
    (hterm : rate t m < (t:ℝ)/Real.log t) (E : RunPalette t m → Finset V)
    (hE : ∀ v, 8*(t:ℝ) ≤ (univ.filter (fun b : Fin (16*t) => v∈E (Sum.inr b))).card)
    (R : Finset V) (S : RunPalette t m → Finset V)
    (hf : number (G.induce (↑R:Set V)) ≤ rate t m)
    (hS : ∀ b, Stable G (S b))
    (hsupp : ∀ b v, v∈S b → binIndex b < m)
    (hcover : ∀ v, v∉R → ∃ b, v∈S b ∧ v∈E b) :
    ∃ S' : RunPalette t m → Finset V, (∀ b, Stable G (S' b)) ∧
      ∀ v, ∃ b, v∈S' b ∧ v∈E b := by
  classical
  let E' (b : Fin (16*t)) : Finset (↑R:Set V) :=
    univ.filter (fun v => v.val ∈ E (Sum.inr b))
  have hord : (Fintype.card (↑R:Set V):ℝ) ≤ (t:ℝ)^(11/10:ℝ) := by
    have hc : (Fintype.card (↑R:Set V):ℝ) ≤ Fintype.card V := by
      exact_mod_cast Fintype.card_subtype_le (·∈(↑R:Set V))
    exact hc.trans horder
  obtain ⟨A,hA,hcov⟩ := Cleanup.cleanup_source (G.induce (↑R:Set V)) ht hord
    (hf.trans hterm.le) E' (fun v => by
      simpa only [E',mem_filter,mem_univ,true_and] using hE v.val)
  refine ⟨Sum.elim (fun b => S (Sum.inl b)) (fun b => (A b).image Subtype.val),?_,?_⟩
  · intro b
    rcases b with b | b
    · exact hS (Sum.inl b)
    · exact stable_image (hA b)
  · intro v
    by_cases hv : v∈R
    · obtain ⟨b,hbe,hba⟩ := hcov ⟨v,hv⟩
      exact ⟨Sum.inr b,mem_image.mpr ⟨⟨v,hv⟩,hba,rfl⟩,(mem_filter.mp hbe).2⟩
    · obtain ⟨b,hb,he⟩ := hcover v hv
      rcases b with b | b
      · exact ⟨Sum.inl b,hb,he⟩
      · have hh := hsupp (Sum.inr b) v hb
        simp only [binIndex,Sum.elim_inr] at hh
        omega

theorem choosable_or_fractional_obstruction :
    ∃ T : ℝ, ∀ (t : ℕ), T ≤ (t:ℝ) →
      ∀ (V : Type) [Fintype V] [DecidableEq V], ∀ G : SimpleGraph V,
      (Fintype.card V:ℝ) ≤ (t:ℝ)^(11/10:ℝ) → hadwigerNumber G < t →
      Choosable G (32768*t) ∨ FractionalObstruction G := by
  classical
  obtain ⟨T₀,hT₀⟩ := stage_cover_or_obstruction
  obtain ⟨T₁,hT₁⟩ := Filter.eventually_atTop.mp schedule_cutoff
  obtain ⟨T₂,hT₂⟩ := Filter.eventually_atTop.mp palette_tail_cutoff
  refine ⟨max T₀ (max T₁ T₂),?_⟩
  intro t ht V _ _ G hord hminor
  by_cases hob : FractionalObstruction G
  · exact Or.inr hob
  left
  have ht₀ := (le_max_left T₀ _).trans ht
  have ht₁ := ((le_max_left T₁ T₂).trans (le_max_right T₀ _)).trans ht
  have ht₂ := ((le_max_right T₁ T₂).trans (le_max_right T₀ _)).trans ht
  obtain ⟨ht1,hl,hlog,hp⟩ := hT₁ (t:ℝ) ht₁
  obtain ⟨m,hm,hterm,hvalid,hbudget,hblocks,hcleanup⟩ := schedule_exists t ht1 hl hlog hp
  have htN : 1 ≤ t := by exact_mod_cast (show (1:ℝ) ≤ t by linarith)
  have hb : 1 ≤ Fintype.card (RunPalette t m) := by rw [runPalette_card]; omega
  have hb' : (Fintype.card (RunPalette t m):ℝ) ≤ 4096*t := by
    rw [runPalette_card]
    exact_mod_cast hbudget
  intro Color L hL
  let u (j : Option (Fin m)) := (runBlock t m j).card
  let e : Option (Fin m) ≃ Fin (Fintype.card (Option (Fin m))) := Fintype.equivFin _
  have hj : (Fintype.card (Option (Fin m)):ℝ) ≤ (t:ℝ)+1 := by
    simp only [Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    exact_mod_cast Nat.add_le_add_right hm 1
  have hu (j : Option (Fin m)) : (t:ℝ)^(7/10:ℝ) ≤ (u j:ℝ) := by
    cases j with
    | none => simpa only [u,runBlock_none,Nat.cast_mul,Nat.cast_ofNat] using hcleanup
    | some j => simpa only [u,runBlock_some] using hblocks j.val j.isLt
  have htail₀ := hT₂ (t:ℝ) ht₂ (Fintype.card V) (Fintype.card (RunPalette t m))
    (Fintype.card (Option (Fin m))) (fun i => u (e.symm i)) hord hb hb' hj (fun i => hu (e.symm i))
  have hsum : (∑ i : Fin (Fintype.card (Option (Fin m))),
      (2:ℝ)^(u (e.symm i))*Real.exp (-(32768*(t:ℝ))*(u (e.symm i))/(2*Fintype.card (RunPalette t m)))) =
      ∑ j : Option (Fin m), (2:ℝ)^(u j)*Real.exp (-(32768*(t:ℝ))*(u j)/(2*Fintype.card (RunPalette t m))) := by
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  rw [hsum] at htail₀
  have htail : (Fintype.card V:ℝ)*(∑ j, (2:ℝ)^(runBlock t m j).card*
      Real.exp (-(32768*t:ℕ)*(runBlock t m j).card/(2*Fintype.card (RunPalette t m)))) < 1 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,u] using htail₀
  obtain ⟨f,hf⟩ := ColorBins.exists_bins hb L (runBlock t m) hL htail
  let E (b : RunPalette t m) : Finset V := univ.filter (fun v => ∃ c∈L v, f c=b)
  have hEstage (j : Fin m) (v : V) : (bins t j.val:ℝ)/2 ≤
      (univ.filter (fun b => v∈E (stageBin t m j b))).card := by
    have hh := hf v (some j)
    rw [runBlock_some] at hh
    have he := occupied_image_card
      (⟨stageBin t m j,stageBin_injective t m j⟩ : Fin (bins t j.val) ↪ RunPalette t m) (L v) f
    change (ColorBins.occupied (L v) (runBlock t m (some j)) f).card=_ at he
    rw [he] at hh
    have hh' : (bins t j.val:ℝ) ≤ 2*(univ.filter (fun b => ∃ c∈L v, f c=stageBin t m j b)).card := by
      exact_mod_cast hh
    simpa only [E,mem_filter,mem_univ,true_and] using (show (bins t j.val:ℝ)/2 ≤
      (univ.filter (fun b => ∃ c∈L v, f c=stageBin t m j b)).card by linarith)
  have hEcleanup (v : V) : 8*(t:ℝ) ≤ (univ.filter (fun b : Fin (16*t) => v∈E (Sum.inr b))).card := by
    have hh := hf v none
    rw [runBlock_none] at hh
    have he := occupied_image_card (Function.Embedding.inr : Fin (16*t) ↪ RunPalette t m) (L v) f
    change (ColorBins.occupied (L v) (runBlock t m none) f).card=_ at he
    rw [he] at hh
    have hh' : 16*(t:ℝ) ≤ 2*(univ.filter (fun b : Fin (16*t) => ∃ c∈L v, f c=Sum.inr b)).card := by
      exact_mod_cast hh
    simpa only [E,mem_filter,mem_univ,true_and] using (show 8*(t:ℝ) ≤
      (univ.filter (fun b : Fin (16*t) => ∃ c∈L v, f c=Sum.inr b)).card by linarith)
  rcases hT₀ t m ht₀ hvalid V G hord hminor E hEstage with hbad | hstates
  · exact (hob hbad).elim
  obtain ⟨R,S,hrem,hS,hsupp,hcover⟩ := hstates m le_rfl
  obtain ⟨S',hS',hcover'⟩ := finish_cover t m G ht1 hord hterm E hEcleanup R S hrem hS hsupp hcover
  apply ColorBins.listColorable_of_bin_cover G L f S' hS'
  intro v
  obtain ⟨b,hb,he⟩ := hcover' v
  exact ⟨b,hb,(mem_filter.mp he).2⟩

end LinearListHadwiger.SmallList

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.HistoryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.SmallList
open Finset

attribute [local instance] Classical.propDecidable

theorem additive_deletion_or_obstruction_oai : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (X Y : Finset V) (d : ℕ),
    hadwigerNumber G < t → (X.card:ℝ) ≤ (t:ℝ)^(11/10:ℝ) → Disjoint X Y →
    DegenerateOn G Y (d*t) →
    (∀ v ∉ X∪Y, (Y.filter (G.Adj v)).card ≤ d*t) →
    listChromaticNumber G ≤ listChromaticNumber (G.induce (↑(univ\(X∪Y)):Set V)) +
      (4*32768+d+5)*t ∨ FractionalObstruction G := by
  classical
  obtain ⟨T,hT⟩ := choosable_or_fractional_obstruction
  obtain ⟨t₁,ht₁⟩ := reservation_cutoff_minor
  refine ⟨max 1 (max ⌈T⌉₊ t₁),?_⟩
  intro t ht V _ _ G X Y d hminor hsize hXY hY hRY
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htT : T ≤ (t:ℝ) := (Nat.le_ceil T).trans (by
    exact_mod_cast ((le_max_left ⌈T⌉₊ t₁).trans (le_max_right 1 _)).trans ht)
  have htt : t₁ ≤ t := ((le_max_right ⌈T⌉₊ t₁).trans (le_max_right 1 _)).trans ht
  have hord : (Fintype.card (↑X:Set V):ℝ) ≤ (t:ℝ)^(11/10:ℝ) := by
    rw [show Fintype.card (↑X:Set V)=X.card from Fintype.card_coe X]
    exact hsize
  have hmin := (Knitting.model_induce G X).hadwiger_le.trans_lt hminor
  rcases hT t htT (↑X:Set V) (G.induce (↑X:Set V)) hord hmin with hsmall | hbad
  · left
    have hm : t ≤ 32768*t := by omega
    have htail := ht₁ t htt V G X (32768*t) hm hminor hsize
    have hh := additive_deletion_coloring G X Y ht1 hXY hsmall hY hRY
      (choosable_listChromaticNumber (G.induce (↑(univ\(X∪Y)):Set V))) htail
    have he : listChromaticNumber (G.induce (↑(univ\(X∪Y)):Set V)) +
        4*(32768*t)+d*t+5*t = listChromaticNumber (G.induce (↑(univ\(X∪Y)):Set V)) +
        (4*32768+d+5)*t := by ring
    rw [he] at hh
    exact (listChromaticNumber_le_iff G _).mpr hh
  · exact Or.inr (obstruction_induce G X hbad)

end LinearListHadwiger.SmallList

end OAI
end

theorem solution : type_of% @OAI.LinearListHadwiger.SmallList.additive_deletion_or_obstruction_oai := @OAI.LinearListHadwiger.SmallList.additive_deletion_or_obstruction_oai
