-- Prove2me | solution 1 for OAI.LinearListHadwiger.Footprint.History.list_loss_or_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:49:46.06582+00:00
-- url     : https://prove2.me/submissions/f8edec5e-65b4-46fa-a336-0257b7bfdfb3

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

theorem collection_incidence : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V J : Type) [Fintype V] [Fintype J] [DecidableEq V],
    ∀ (G : SimpleGraph V) (B : J → Finset V) (T : Finset V),
    hadwigerNumber G < t →
    (∀ j, (G.induce (↑(B j) : Set V)).Connected) →
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
    (∀ j, Disjoint T (B j)) →
    (∀ v ∈ T, 3202*t ≤ (univ.filter (fun j => ∃ w ∈ B j, G.Adj v w)).card) →
    (3202*t:ℝ)*T.card ≤ (t:ℝ)^(101/100:ℝ)*Fintype.card J := by
  classical
  obtain ⟨t₀,ht₀⟩ := Incidence.incidence_bound
  refine ⟨t₀,?_⟩
  intro t ht V J _ _ _ G B T hex hc hd hdis hlarge
  let C : J → Set V := fun j => ↑(B j)
  let H := BagContraction.graph G C
  let M := BagContraction.model G C hc (fun i j hij => by
    exact Set.disjoint_left.mpr (fun v hvi hvj => disjoint_left.mp (hd i j hij) hvi hvj))
  let A : Finset (BagContraction.Vertex C) := univ.image Sum.inr
  let f : ↥T → BagContraction.Vertex C := fun v => Sum.inl ⟨v.val,by
    intro j hj
    exact disjoint_left.mp (hdis j) v.property hj⟩
  have hf : Function.Injective f := by
    intro v w he
    exact Subtype.ext (congrArg (fun z : BagContraction.Vertex C =>
      match z with | Sum.inl x => x.val | Sum.inr _ => v.val) he)
  let T' := univ.image f
  have hAT : Disjoint A T' := by
    apply disjoint_left.mpr
    intro z hzA hzT
    obtain ⟨j,_,rfl⟩ := mem_image.mp hzA
    obtain ⟨v,_,hv⟩ := mem_image.mp hzT
    simp [f] at hv
  have hAc : A.card = Fintype.card J := by
    simp [A,card_image_of_injective _ Sum.inr_injective]
  have hTc : T'.card = T.card := by
    simp [T',card_image_of_injective _ hf]
  have hdegree : ∀ v : ↥T,
      (univ.filter (fun j => ∃ w ∈ B j, G.Adj v.val w)).card ≤
        (A.filter (H.Adj (f v))).card := by
    intro v
    let N := univ.filter (fun j => ∃ w ∈ B j, G.Adj v.val w)
    have hsub : N.image (Sum.inr : J → BagContraction.Vertex C) ⊆
        A.filter (H.Adj (f v)) := by
      intro z hz
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hz
      obtain ⟨w,hw,hadj⟩ := (mem_filter.mp hj).2
      refine mem_filter.mpr ⟨mem_image.mpr ⟨j,mem_univ _,rfl⟩,?_⟩
      exact ⟨by simp [f],
        v.val,rfl,w,hw,hadj⟩
    simpa only [card_image_of_injective _ Sum.inr_injective] using card_le_card hsub
  have hTlarge : ∀ z ∈ T', 3202*t ≤ (A.filter (H.Adj z)).card := by
    intro z hz
    obtain ⟨v,_,rfl⟩ := mem_image.mp hz
    exact (hlarge v.val v.property).trans (hdegree v)
  have hbound := ht₀ t ht (BagContraction.Vertex C) H
    (M.hadwiger_le.trans_lt hex) A T' hAT
  have he : T'.filter (fun z => 3202*t ≤ (A.filter (H.Adj z)).card) = T' :=
    filter_eq_self.mpr hTlarge
  rw [he,hAc] at hbound
  have hl : (3202*t:ℝ)*T'.card ≤ ∑ z ∈ T', ((A.filter (H.Adj z)).card : ℝ) := by
    calc
      _ = ∑ _z ∈ T', (3202*t:ℝ) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun z hz => by exact_mod_cast hTlarge z hz
  rw [hTc] at hl
  exact hl.trans hbound

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

theorem exceptional_card : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V J : Type) [Fintype V] [Fintype J] [DecidableEq V],
    ∀ (G : SimpleGraph V) (B : J → Finset V) (F : Finset V),
    hadwigerNumber G < t →
    (∀ j, (G.induce (↑(B j) : Set V)).Connected) →
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
    (∀ j, B j ⊆ F) →
    ((exceptional G B F t).card : ℝ) ≤ (t:ℝ)^(1/100:ℝ)*Fintype.card J := by
  classical
  obtain ⟨t₀,ht₀⟩ := collection_incidence
  refine ⟨max t₀ 1,?_⟩
  intro t ht V J _ _ _ G B F hex hc hd hBF
  let T := exceptional G B F t
  have hT := ht₀ t ((le_max_left _ _).trans ht) V J G B T hex hc hd
    (fun j => disjoint_left.mpr (fun v hv hvB => (mem_filter.mp hv).2.1 (hBF j hvB)))
    (fun v hv => (mem_filter.mp hv).2.2)
  have htnat : 1 ≤ t := (le_max_right _ _).trans ht
  have htpos : (0:ℝ) < t := by exact_mod_cast (Nat.zero_lt_of_lt htnat)
  have hp : (t:ℝ)^(101/100:ℝ) = (t:ℝ)^(1/100:ℝ)*t := by
    rw [←Real.rpow_add_one htpos.ne']
    norm_num
  rw [hp] at hT
  have hcnt : (0:ℝ) ≤ T.card := by positivity
  have hm : (t:ℝ)*T.card ≤ (3202*t:ℝ)*T.card := by nlinarith
  have hle := hm.trans hT
  nlinarith

theorem path_erase_start_connected {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {u v : V} (p : G.Path u v) (huv : u ≠ v) :
    (G.induce (↑(p.val.support.toFinset.erase u) : Set V)).Connected := by
  obtain ⟨p,hp⟩ := p
  cases p with
  | nil => exact (huv rfl).elim
  | @cons u w v huv' q =>
    have hu : u ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
    have he : ((SimpleGraph.Walk.cons huv' q).support.toFinset.erase u) = q.support.toFinset := by
      simp only [SimpleGraph.Walk.support_cons,List.toFinset_cons]
      exact erase_insert (by simpa using hu)
    have hs : (↑(q.support.toFinset) : Set V) = {x | x ∈ q.support} := by
      ext x
      simp
    rw [he,hs]
    exact q.connected_induce_support

end LinearListHadwiger.Footprint

namespace LinearListHadwiger.Footprint
open Filter Real

lemma rounds_le_log {t : ℝ} (hlog : 1 ≤ Real.log t) :
    (rounds t : ℝ) ≤ 4*(Real.log t)^4 := by
  have hm : (⌈(Real.log t)^2⌉₊ : ℝ) ≤ 2*(Real.log t)^2 := by
    have hh := Nat.ceil_lt_add_one (sq_nonneg (Real.log t))
    nlinarith
  have hm0 : 1 ≤ ⌈(Real.log t)^2⌉₊ := by
    have hh := Nat.le_ceil ((Real.log t)^2)
    have : (1:ℝ) ≤ ⌈(Real.log t)^2⌉₊ := by nlinarith
    exact_mod_cast this
  have hround : rounds t ≤ ⌈(Real.log t)^2⌉₊^2 := by
    dsimp [rounds]
    apply Nat.div_le_of_le_mul
    nlinarith
  have hh : (rounds t : ℝ) ≤ (⌈(Real.log t)^2⌉₊ : ℝ)^2 := by exact_mod_cast hround
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ⌈(Real.log t)^2⌉₊) hm 2
  nlinarith

lemma exceptional_size_cutoff :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ 1 ≤ Real.log t ∧
      2*(rounds t:ℝ)*t^(106/100:ℝ)+(13*(rounds t:ℝ)+1)*t+
        6*(rounds t:ℝ)*((rounds t:ℝ)+1)*t^(101/100:ℝ) ≤ t^(11/10:ℝ) := by
  have hl := (isLittleO_log_rpow_rpow_atTop (8:ℝ)
    (show (0:ℝ)<4/100 by norm_num)).bound (show (0:ℝ)<1/181 by norm_num)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [eventually_ge_atTop (1:ℝ),hlog,hl] with t ht hlog hl
  have ht0 : 0<t := by linarith
  have hp : (Real.log t)^8 ≤ (1/181:ℝ)*t^(4/100:ℝ) := by
    simpa only [Real.norm_eq_abs, Real.rpow_ofNat,
      abs_of_nonneg (by positivity : 0 ≤ (Real.log t)^8),
      abs_of_nonneg (Real.rpow_nonneg ht0.le (4/100:ℝ))] using hl
  have ht1 : t ≤ t^(106/100:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le ht (show (1:ℝ)≤106/100 by norm_num)
  have ht2 : t^(101/100:ℝ) ≤ t^(106/100:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have h4 : 1 ≤ (Real.log t)^4 := one_le_pow₀ hlog
  have h48 : (Real.log t)^4 ≤ (Real.log t)^8 := pow_le_pow_right₀ hlog (by norm_num)
  have h8 : 1 ≤ (Real.log t)^8 := one_le_pow₀ hlog
  have hr := rounds_le_log hlog
  have hmid : 13*(rounds t:ℝ)+1 ≤ 53*(Real.log t)^8 := by nlinarith
  have hlast : 6*(rounds t:ℝ)*((rounds t:ℝ)+1) ≤ 120*(Real.log t)^8 := by
    have hnext : (rounds t:ℝ)+1 ≤ 5*(Real.log t)^4 := by linarith
    have hh := mul_le_mul hr hnext (by positivity : (0:ℝ)≤(rounds t:ℝ)+1)
      (by positivity : (0:ℝ)≤4*(Real.log t)^4)
    nlinarith
  refine ⟨ht,hlog,?_⟩
  calc
    _ ≤ 8*(Real.log t)^8*t^(106/100:ℝ)+53*(Real.log t)^8*t^(106/100:ℝ)+
        120*(Real.log t)^8*t^(106/100:ℝ) := by
      apply add_le_add (add_le_add ?_ ?_) ?_
      · exact mul_le_mul_of_nonneg_right (by linarith : 2*(rounds t:ℝ) ≤ 8*(Real.log t)^8)
          (by positivity)
      · exact mul_le_mul hmid ht1 ht0.le (by positivity)
      · exact mul_le_mul hlast ht2 (by positivity) (by positivity)
    _ = 181*(Real.log t)^8*t^(106/100:ℝ) := by ring
    _ ≤ t^(4/100:ℝ)*t^(106/100:ℝ) := by gcongr; linarith
    _ = t^(11/10:ℝ) := by rw [←Real.rpow_add ht0]; norm_num

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

lemma path_subset_used (S : System G) (i : Fin S.n) : S.path i ⊆ S.used :=
  fun _ hv => (S.mem_used _).mpr ⟨i,hv⟩

lemma used_subset_domain (S : System G) : S.used ⊆ S.domain := by
  intro v hv
  obtain ⟨i,hi⟩ := (S.mem_used v).mp hv
  exact S.path_subset_domain i hi

lemma start_mem_path (S : System G) (i : Fin S.n) : (S.source i).val ∈ S.path i :=
  mem_image.mpr ⟨_,List.mem_toFinset.mpr (S.routes.paths i).2.val.start_mem_support,rfl⟩

lemma starts_card (S : System G) : S.starts.card ≤ S.n := by
  exact (card_image_le).trans (by simp)

lemma ends_card (S : System G) : S.ends.card ≤ S.n := by
  exact (card_image_le).trans (by simp)

lemma start_on_path (S : System G) (i : Fin S.n) {v : V}
    (hv : v ∈ S.path i) (hs : v ∈ S.starts) : v = (S.source i).val := by
  obtain ⟨j,_,rfl⟩ := mem_image.mp hs
  by_cases he : i=j
  · subst j; rfl
  · exact (S.overlap he hv (S.start_mem_path j)).1

lemma stripped_disjoint (S : System G) {i j : Fin S.n} (hij : i ≠ j) :
    Disjoint (S.stripped i) (S.stripped j) := by
  apply disjoint_left.mpr
  intro v hvi hvj
  exact (mem_sdiff.mp hvi).2 (mem_singleton.mpr
    (S.overlap hij (mem_sdiff.mp hvi).1 (mem_sdiff.mp hvj).1).1)

lemma paths_disjoint (S : System G) (hinj : Function.Injective S.source)
    {i j : Fin S.n} (hij : i ≠ j) : Disjoint (S.path i) (S.path j) := by
  apply disjoint_left.mpr
  intro v hv hw
  obtain ⟨hi,hj⟩ := S.overlap hij hv hw
  exact hij (hinj (Subtype.ext (hi.symm.trans hj)))

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

lemma path_connected (S : System G) (i : Fin S.n) :
    (G.induce (↑(S.path i) : Set V)).Connected := by
  let f : G.induce (↑S.domain : Set V) →g G := ⟨Subtype.val,fun h => h⟩
  let p := (S.routes.paths i).2.val.map f
  have he : (↑(S.path i) : Set V) = {v | v ∈ p.support} := by
    ext v
    simp only [path,mem_coe,mem_image,List.mem_toFinset,Set.mem_ofPred_eq,p,
      SimpleGraph.Walk.support_map,List.mem_map]
    rfl
  rw [he]
  exact p.connected_induce_support

lemma stripped_connected (S : System G) (i : Fin S.n)
    (hne : (S.source i).val ≠ (S.routes.paths i).1.val) :
    (G.induce (↑(S.stripped i) : Set V)).Connected := by
  let f : G.induce (↑S.domain : Set V) →g G := ⟨Subtype.val,fun h => h⟩
  let p : G.Path (S.source i).val (S.routes.paths i).1.val :=
    ⟨(S.routes.paths i).2.val.map f,(S.routes.paths i).2.property.map Subtype.val_injective⟩
  have hp : S.path i = p.val.support.toFinset := by
    ext v
    simp only [path,mem_image,List.mem_toFinset,p,SimpleGraph.Walk.support_map,List.mem_map]
    rfl
  have he : S.stripped i = p.val.support.toFinset.erase (S.source i).val := by
    rw [stripped,hp,sdiff_singleton_eq_erase]
  rw [he]
  exact path_erase_start_connected p hne

end System
end LinearListHadwiger.Footprint

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}
namespace History

lemma step_subset (H : History G t) (i : Fin H.q) :
    H.footprint i.val ⊆ H.footprint (i.val+1) := by
  rw [H.next i]
  exact subset_union_left.trans (subset_union_left.trans
    (subset_union_left.trans subset_union_left))

lemma footprint_mono (H : History G t) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ H.q) :
    H.footprint a ⊆ H.footprint b := by
  induction hab with
  | refl => exact Subset.rfl
  | @step b hab ih =>
    exact (ih (by omega)).trans (H.step_subset ⟨b,by omega⟩)

lemma first_used_next (H : History G t) (i : Fin H.q) :
    (H.first i).used ⊆ H.footprint (i.val+1) := by
  rw [H.next i]
  exact subset_union_right.trans subset_union_left

lemma second_used_next (H : History G t) (i : Fin H.q) :
    (H.second i).used ⊆ H.footprint (i.val+1) := by
  rw [H.next i]
  exact subset_union_right

lemma district_next (H : History G t) (i : Fin H.q) :
    H.district i ⊆ H.footprint (i.val+1) := by
  rw [H.next i]
  exact subset_union_right.trans (subset_union_left.trans (subset_union_left.trans subset_union_left))

lemma roots_next (H : History G t) (i : Fin H.q) :
    H.roots i ⊆ H.footprint (i.val+1) := (H.roots_subset i).trans (H.district_next i)

lemma first_stripped_avoids (H : History G t) (i : Fin H.q) (j : Fin (H.first i).n) :
    Disjoint ((H.first i).stripped j) (H.footprint i.val) := by
  apply disjoint_left.mpr
  intro v hv hvF
  have hvp := (mem_sdiff.mp hv).1
  have hvD := (H.first i).path_subset_domain j hvp
  rw [H.first_domain i] at hvD
  have hvt : v ∈ H.tips i := by
    by_contra hnt
    exact (mem_sdiff.mp hvD).2 (mem_sdiff.mpr ⟨hvF,hnt⟩)
  have he := (H.first i).start_on_path j hvp (H.tips_start i hvt)
  exact (mem_sdiff.mp hv).2 (mem_singleton.mpr he)

lemma second_avoids (H : History G t) (i : Fin H.q) :
    Disjoint (H.second i).used (H.footprint i.val) := by
  apply disjoint_left.mpr
  intro v hv hvF
  have hvD := (H.second i).used_subset_domain hv
  rw [H.second_domain i] at hvD
  exact (mem_sdiff.mp hvD).2 (mem_union_left _ hvF)

lemma firstPath_next (H : History G t) (i : H.FirstIndex) :
    H.firstPath i ⊆ H.footprint (i.1.val+1) :=
  sdiff_subset.trans (((H.first i.1).path_subset_used i.2).trans (H.first_used_next i.1))

lemma secondPath_next (H : History G t) (i : H.SecondIndex) :
    H.secondPath i ⊆ H.footprint (i.1.val+1) :=
  ((H.second i.1).path_subset_used i.2).trans (H.second_used_next i.1)

lemma firstPath_connected (H : History G t) (i : H.FirstIndex) :
    (G.induce (↑(H.firstPath i) : Set V)).Connected := by
  apply System.stripped_connected
  intro he
  have hs := H.first_starts i.1 (show ((H.first i.1).source i.2).val ∈ (H.first i.1).starts from
    mem_image.mpr ⟨i.2,mem_univ _,rfl⟩)
  have hs' : ((H.first i.1).source i.2).val ∈ H.footprint i.1.val ∪ H.district i.1 := by
    rcases mem_union.mp hs with hs | hs
    · exact mem_union_left _ (H.tips_subset i.1 hs)
    · exact mem_union_right _ (H.roots_subset i.1 hs)
  have he' := H.first_ends i.1 (show ((H.first i.1).routes.paths i.2).1.val ∈
      (H.first i.1).ends from mem_image.mpr ⟨i.2,mem_univ _,rfl⟩)
  rw [he] at hs'
  exact disjoint_left.mp (H.junction_disjoint i.1) he' hs'

lemma secondPath_connected (H : History G t) (i : H.SecondIndex) :
    (G.induce (↑(H.secondPath i) : Set V)).Connected := (H.second i.1).path_connected i.2

lemma firstPath_disjoint (H : History G t) (i j : H.FirstIndex) (hij : i ≠ j) :
    Disjoint (H.firstPath i) (H.firstPath j) := by
  rcases lt_trichotomy i.1.val j.1.val with hlt | he | hgt
  · apply Disjoint.mono_left ((H.firstPath_next i).trans (H.footprint_mono (b := j.1.val) (by omega) (by omega)))
    exact (H.first_stripped_avoids j.1 j.2).symm
  · obtain ⟨i,a⟩ := i
    obtain ⟨j,b⟩ := j
    have he' : i=j := Fin.ext he
    subst j
    apply System.stripped_disjoint
    intro he
    exact hij (by cases he; rfl)
  · apply Disjoint.mono_right ((H.firstPath_next j).trans (H.footprint_mono (b := i.1.val) (by omega) (by omega)))
    exact H.first_stripped_avoids i.1 i.2

lemma secondPath_disjoint (H : History G t) (i j : H.SecondIndex) (hij : i ≠ j) :
    Disjoint (H.secondPath i) (H.secondPath j) := by
  rcases lt_trichotomy i.1.val j.1.val with hlt | he | hgt
  · apply Disjoint.mono_left ((H.secondPath_next i).trans (H.footprint_mono (b := j.1.val) (by omega) (by omega)))
    exact ((H.second_avoids j.1).mono_left ((H.second j.1).path_subset_used j.2)).symm
  · obtain ⟨i,a⟩ := i
    obtain ⟨j,b⟩ := j
    have he' : i=j := Fin.ext he
    subst j
    apply System.paths_disjoint _ (H.second_injective i)
    intro he
    exact hij (by cases he; rfl)
  · apply Disjoint.mono_right ((H.secondPath_next j).trans (H.footprint_mono (b := i.1.val) (by omega) (by omega)))
    exact (H.second_avoids i.1).mono_left ((H.second i.1).path_subset_used i.2)

lemma firstIndex_card (H : History G t) : Fintype.card H.FirstIndex ≤ 4*t*H.q := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : Fin H.q, 4*t := sum_le_sum (fun i _ => by simpa using H.first_count i)
    _ = _ := by simp [mul_comm]

lemma secondIndex_card (H : History G t) : Fintype.card H.SecondIndex ≤ 2*t*H.q := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : Fin H.q, 2*t := sum_le_sum (fun i _ => by simpa using H.second_count i)
    _ = _ := by simp [mul_comm]

end History
end LinearListHadwiger.Footprint

namespace LinearListHadwiger.Footprint.History
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

lemma firstPast_subset (H : History G t) {r : ℕ} (hr : r ≤ H.q) (i : H.FirstPast r) :
    H.firstPath i.val ⊆ H.footprint r :=
  (H.firstPath_next i.val).trans (H.footprint_mono (by omega) hr)

lemma secondPast_subset (H : History G t) {r : ℕ} (hr : r ≤ H.q) (i : H.SecondPast r) :
    H.secondPath i.val ⊆ H.footprint r :=
  (H.secondPath_next i.val).trans (H.footprint_mono (by omega) hr)

lemma firstPast_card (H : History G t) (r : ℕ) : Fintype.card (H.FirstPast r) ≤ 4*t*H.q :=
  (Fintype.card_subtype_le _).trans H.firstIndex_card

lemma secondPast_card (H : History G t) (r : ℕ) : Fintype.card (H.SecondPast r) ≤ 2*t*H.q :=
  (Fintype.card_subtype_le _).trans H.secondIndex_card

lemma exceptions_card : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : History G t),
    hadwigerNumber G < t → ∀ r ≤ H.q,
    ((H.firstException r ∪ H.secondException r).card : ℝ) ≤
      6*(H.q:ℝ)*(t:ℝ)^(101/100:ℝ) := by
  classical
  obtain ⟨t₀,ht₀⟩ := exceptional_card
  refine ⟨max t₀ 1,?_⟩
  intro t ht V _ _ G H hex r hr
  have ht' : t₀ ≤ t := (le_max_left _ _).trans ht
  have htp : (0:ℝ) < t := by
    exact_mod_cast (Nat.zero_lt_of_lt ((le_max_right t₀ 1).trans ht))
  have hA := ht₀ t ht' V (H.FirstPast r) G (fun i => H.firstPath i.val)
    (H.footprint r) hex (fun i => H.firstPath_connected i.val)
    (fun i j hij => H.firstPath_disjoint i.val j.val (fun he => hij (Subtype.ext he)))
    (H.firstPast_subset hr)
  have hB := ht₀ t ht' V (H.SecondPast r) G (fun i => H.secondPath i.val)
    (H.footprint r) hex (fun i => H.secondPath_connected i.val)
    (fun i j hij => H.secondPath_disjoint i.val j.val (fun he => hij (Subtype.ext he)))
    (H.secondPast_subset hr)
  have hAc : (Fintype.card (H.FirstPast r) : ℝ) ≤ 4*t*H.q := by
    exact_mod_cast H.firstPast_card r
  have hBc : (Fintype.card (H.SecondPast r) : ℝ) ≤ 2*t*H.q := by
    exact_mod_cast H.secondPast_card r
  calc
    _ ≤ ((H.firstException r).card : ℝ) + (H.secondException r).card := by
      exact_mod_cast card_union_le (H.firstException r) (H.secondException r)
    _ ≤ (t:ℝ)^(1/100:ℝ)*(4*t*H.q)+(t:ℝ)^(1/100:ℝ)*(2*t*H.q) :=
      add_le_add (hA.trans (mul_le_mul_of_nonneg_left hAc (by positivity)))
        (hB.trans (mul_le_mul_of_nonneg_left hBc (by positivity)))
    _ = _ := by
      have he : (t:ℝ)^(101/100:ℝ) = (t:ℝ)^(1/100:ℝ)*t := by
        rw [←Real.rpow_add_one htp.ne']; norm_num
      rw [he]; ring

lemma small_round_card (H : History G t) (i : Fin H.q) :
    ((H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends).card : ℝ) ≤
      2*(t:ℝ)^(106/100:ℝ)+13*t := by
  have h1 : ((H.first i).starts.card : ℝ) ≤ 4*t := by
    exact_mod_cast ((H.first i).starts_card.trans (H.first_count i))
  have h2 : ((H.first i).ends.card : ℝ) ≤ 4*t := by
    exact_mod_cast ((H.first i).ends_card.trans (H.first_count i))
  have h3 : ((H.second i).starts.card : ℝ) ≤ 2*t := by
    exact_mod_cast ((H.second i).starts_card.trans (H.second_count i))
  have h4 : ((H.second i).ends.card : ℝ) ≤ 2*t := by
    exact_mod_cast ((H.second i).ends_card.trans (H.second_count i))
  have h5 : ((H.tips i).card : ℝ) ≤ t := by exact_mod_cast H.tips_card i
  have hu (A B : Finset V) : ((A ∪ B).card : ℝ) ≤ A.card+B.card := by
    exact_mod_cast card_union_le A B
  calc
    _ ≤ ((((((H.district i).card : ℝ)+(H.junction i).card)+(H.tips i).card)+
        (H.first i).starts.card)+(H.first i).ends.card)+(H.second i).starts.card+
        (H.second i).ends.card := by
      linarith only [hu (H.district i) (H.junction i),
        hu (H.district i ∪ H.junction i) (H.tips i),
        hu (H.district i ∪ H.junction i ∪ H.tips i) (H.first i).starts,
        hu (H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts) (H.first i).ends,
        hu (H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪ (H.first i).ends)
          (H.second i).starts,
        hu (H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪ (H.first i).ends ∪
          (H.second i).starts) (H.second i).ends]
    _ ≤ _ := by linarith [H.district_card i,H.junction_card i]

lemma small_card (H : History G t) : (H.small.card : ℝ) ≤
    2*(H.q:ℝ)*(t:ℝ)^(106/100:ℝ)+(13*(H.q:ℝ)+1)*t := by
  have hf : ((H.footprint 0).card : ℝ) ≤ t := by exact_mod_cast H.initial_card
  have hu := card_union_le (H.footprint 0) (univ.biUnion (fun i : Fin H.q =>
    H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends))
  have hb := card_biUnion_le (s := (univ : Finset (Fin H.q)))
    (t := fun i => H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends)
  have hu' : (H.small.card : ℝ) ≤ (H.footprint 0).card+
      ∑ i : Fin H.q, ((H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends).card : ℝ) := by
    exact_mod_cast hu.trans (Nat.add_le_add_left hb _)
  have hs := sum_le_sum (s := (univ : Finset (Fin H.q))) (fun i _ => H.small_round_card i)
  have hs' : (∑ i : Fin H.q, ((H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends).card : ℝ)) ≤
      (H.q:ℝ)*(2*(t:ℝ)^(106/100:ℝ)+13*t) := by simpa [mul_add] using hs
  nlinarith

lemma deleted_card : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : History G t),
    hadwigerNumber G < t →
    (H.deleted.card : ℝ) ≤ 2*(H.q:ℝ)*(t:ℝ)^(106/100:ℝ)+(13*(H.q:ℝ)+1)*t+
      6*(H.q:ℝ)*((H.q:ℝ)+1)*(t:ℝ)^(101/100:ℝ) := by
  classical
  obtain ⟨t₀,ht₀⟩ := exceptions_card
  refine ⟨t₀,?_⟩
  intro t ht V _ _ G H hex
  have hu := card_union_le H.small (univ.biUnion
    (fun r : Fin (H.q+1) => H.firstException r ∪ H.secondException r))
  have hb := card_biUnion_le (s := (univ : Finset (Fin (H.q+1))))
    (t := fun r => H.firstException r ∪ H.secondException r)
  have hu' : (H.deleted.card : ℝ) ≤ H.small.card+
      ∑ r : Fin (H.q+1), ((H.firstException r ∪ H.secondException r).card : ℝ) := by
    exact_mod_cast hu.trans (Nat.add_le_add_left hb _)
  have hs := sum_le_sum (s := (univ : Finset (Fin (H.q+1))))
    (fun r _ => ht₀ t ht V G H hex r.val (by omega))
  have hs' : (∑ r : Fin (H.q+1), ((H.firstException r ∪ H.secondException r).card : ℝ)) ≤
      ((H.q:ℝ)+1)*(6*(H.q:ℝ)*(t:ℝ)^(101/100:ℝ)) := by simpa [mul_add] using hs
  nlinarith [H.small_card]

end LinearListHadwiger.Footprint.History

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

lemma degenerate_union {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (d a b : ℕ) (hA : DegenerateOn G A d)
    (hB : DegenerateOn G B a) (hback : ∀ v ∈ B, (A.filter (G.Adj v)).card ≤ b)
    (hab : a+b ≤ d) : DegenerateOn G (A ∪ B) d := by
  intro T hT hn
  by_cases hnew : (T ∩ B).Nonempty
  · obtain ⟨v,hv,hd⟩ := hB (T ∩ B) inter_subset_right hnew
    have hvB := (mem_inter.mp hv).2
    have hsub : T.filter (G.Adj v) ⊆ ((T ∩ B).filter (G.Adj v)) ∪ (A.filter (G.Adj v)) := by
      intro w hw
      obtain ⟨hwT,hadj⟩ := mem_filter.mp hw
      rcases mem_union.mp (hT hwT) with hwA | hwB
      · exact mem_union_right _ (mem_filter.mpr ⟨hwA,hadj⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_inter.mpr ⟨hwT,hwB⟩,hadj⟩)
    refine ⟨v,(mem_inter.mp hv).1,?_⟩
    exact (card_le_card hsub).trans ((card_union_le _ _).trans
      ((Nat.add_le_add hd (hback v hvB)).trans hab))
  · apply hA T ?_ hn
    intro v hv
    rcases mem_union.mp (hT hv) with hvA | hvB
    · exact hvA
    · exact False.elim (hnew ⟨v,mem_inter.mpr ⟨hv,hvB⟩⟩)

namespace History
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

lemma initial_small (H : History G t) : H.footprint 0 ⊆ H.small := subset_union_left

lemma round_small (H : History G t) (i : Fin H.q) :
    H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends ⊆ H.small := by
  intro v hv
  exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,hv⟩)

lemma district_small (H : History G t) (i : Fin H.q) : H.district i ⊆ H.small := by
  intro v hv; apply H.round_small i
  simp only [mem_union]; tauto
lemma junction_small (H : History G t) (i : Fin H.q) : H.junction i ⊆ H.small := by
  intro v hv; apply H.round_small i
  simp only [mem_union]; tauto
lemma first_starts_small (H : History G t) (i : Fin H.q) : (H.first i).starts ⊆ H.small := by
  intro v hv; apply H.round_small i
  simp only [mem_union]; tauto

lemma small_deleted (H : History G t) : H.small ⊆ H.deleted := subset_union_left

lemma footprint_path (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∈ H.footprint r) (hsmall : v ∉ H.small) :
    (∃ i : H.FirstPast r, v ∈ H.firstPath i.val) ∨
      (∃ i : H.SecondPast r, v ∈ H.secondPath i.val) := by
  induction r with
  | zero => exact False.elim (hsmall (H.initial_small hv))
  | succ r ih =>
    let j : Fin H.q := ⟨r,by omega⟩
    rw [H.next j] at hv
    rcases mem_union.mp hv with hv | hv2
    · rcases mem_union.mp hv with hv | hv1
      · rcases mem_union.mp hv with hv | hvJ
        · rcases mem_union.mp hv with hvF | hvD
          · rcases ih (by omega) hvF with ⟨i,hi⟩ | ⟨i,hi⟩
            · exact Or.inl ⟨⟨i.val,by have := i.property; omega⟩,hi⟩
            · exact Or.inr ⟨⟨i.val,by have := i.property; omega⟩,hi⟩
          · exact False.elim (hsmall (H.district_small j hvD))
        · exact False.elim (hsmall (H.junction_small j hvJ))
      · rw [(H.first j).used_eq] at hv1
        obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv1
        left
        refine ⟨⟨⟨j,i⟩,by dsimp [j]; omega⟩,mem_sdiff.mpr ⟨hi,?_⟩⟩
        intro he
        have he' := mem_singleton.mp he
        exact hsmall (H.first_starts_small j (mem_image.mpr ⟨i,mem_univ _,he'.symm⟩))
    · rw [(H.second j).used_eq] at hv2
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hv2
      exact Or.inr ⟨⟨⟨j,i⟩,by dsimp [j]; omega⟩,hi⟩

lemma first_exception_deleted (H : History G t) {r : ℕ} (hr : r ≤ H.q) :
    H.firstException r ⊆ H.deleted := by
  intro v hv
  exact mem_union_right _ (mem_biUnion.mpr ⟨⟨r,by omega⟩,mem_univ _,mem_union_left _ hv⟩)
lemma second_exception_deleted (H : History G t) {r : ℕ} (hr : r ≤ H.q) :
    H.secondException r ⊆ H.deleted := by
  intro v hv
  exact mem_union_right _ (mem_biUnion.mpr ⟨⟨r,by omega⟩,mem_univ _,mem_union_right _ hv⟩)

lemma first_nonexceptional (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∉ H.footprint r) (hx : v ∉ H.deleted) :
    (univ.filter (fun i : H.FirstPast r => ∃ w ∈ H.firstPath i.val, G.Adj v w)).card ≤ 3202*t := by
  apply Nat.le_of_lt
  apply Nat.lt_of_not_ge
  intro hle
  exact hx (H.first_exception_deleted hr (mem_filter.mpr ⟨mem_univ _,hv,hle⟩))
lemma second_nonexceptional (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∉ H.footprint r) (hx : v ∉ H.deleted) :
    (univ.filter (fun i : H.SecondPast r => ∃ w ∈ H.secondPath i.val, G.Adj v w)).card ≤ 3202*t := by
  apply Nat.le_of_lt
  apply Nat.lt_of_not_ge
  intro hle
  exact hx (H.second_exception_deleted hr (mem_filter.mpr ⟨mem_univ _,hv,hle⟩))

lemma first_past_neighbors (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∉ H.footprint r) (i : H.FirstPast r) :
    ((H.firstPath i.val).filter (G.Adj v)).card ≤ 3 := by
  let j := i.val.1
  have hj : j.val+1 ≤ r := by have := i.property; dsimp [j]; omega
  have hnot : v ∉ H.footprint j.val := fun hh => hv (H.footprint_mono (by omega) hr hh)
  have hdomain : v ∈ (H.first j).domain := by
    rw [H.first_domain j]
    exact mem_sdiff.mpr ⟨mem_univ _,fun hh => hnot (mem_sdiff.mp hh).1⟩
  have hout : v ∉ (H.first j).used := fun hh => hv
    (H.footprint_mono hj hr (H.first_used_next j hh))
  exact (card_le_card (filter_subset_filter _ sdiff_subset)).trans
    ((H.first j).path_neighbors i.val.2 v hdomain hout)

lemma second_past_neighbors (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∉ H.footprint r) (i : H.SecondPast r) :
    ((H.secondPath i.val).filter (G.Adj v)).card ≤ 3 := by
  let j := i.val.1
  have hj : j.val+1 ≤ r := by have := i.property; dsimp [j]; omega
  have hdomain : v ∈ (H.second j).domain := by
    rw [H.second_domain j]
    refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact hv (H.footprint_mono (by omega) hr hh)
    · exact hv (H.footprint_mono hj hr (H.roots_next j hh))
  have hout : v ∉ (H.second j).used := fun hh => hv
    (H.footprint_mono hj hr (H.second_used_next j hh))
  exact (H.second j).path_neighbors i.val.2 v hdomain hout

lemma past_neighbors (H : History G t) {r : ℕ} (hr : r ≤ H.q) {v : V}
    (hv : v ∉ H.footprint r) (hx : v ∉ H.deleted) :
    ((H.footprint r \ H.deleted).filter (G.Adj v)).card ≤ 6*3202*t := by
  let A := univ.biUnion (fun i : H.FirstPast r => H.firstPath i.val)
  let B := univ.biUnion (fun i : H.SecondPast r => H.secondPath i.val)
  have hA : (A.filter (G.Adj v)).card ≤ 3*(3202*t) :=
    neighbors_in_collection G _ v _ _ (H.first_past_neighbors hr hv) (H.first_nonexceptional hr hv hx)
  have hB : (B.filter (G.Adj v)).card ≤ 3*(3202*t) :=
    neighbors_in_collection G _ v _ _ (H.second_past_neighbors hr hv) (H.second_nonexceptional hr hv hx)
  have hsub : H.footprint r \ H.deleted ⊆ A ∪ B := by
    intro w hw
    obtain ⟨hw,hn⟩ := mem_sdiff.mp hw
    rcases H.footprint_path hr hw (fun hh => hn (H.small_deleted hh)) with ⟨i,hi⟩ | ⟨i,hi⟩
    · exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_univ _,hi⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,hi⟩)
  calc
    _ ≤ ((A ∪ B).filter (G.Adj v)).card := card_le_card (filter_subset_filter _ hsub)
    _ ≤ (A.filter (G.Adj v)).card+(B.filter (G.Adj v)).card := by
      rw [filter_union]; exact card_union_le _ _
    _ ≤ _ := by omega

end History
end LinearListHadwiger.Footprint

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.HistoryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Footprint.History
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

lemma phase_decomposition (H : History G t) (i : Fin H.q) :
    H.footprint (i.val+1) \ H.deleted =
      ((H.footprint i.val \ H.deleted) ∪ H.firstPhase i) ∪ H.secondPhase i := by
  ext v
  have hD : v ∈ H.district i → v ∈ H.deleted := fun h => H.small_deleted (H.district_small i h)
  have hJ : v ∈ H.junction i → v ∈ H.deleted := fun h => H.small_deleted (H.junction_small i h)
  rw [H.next i]
  simp only [firstPhase,secondPhase,mem_sdiff,mem_union]
  tauto

lemma firstPhase_degenerate (H : History G t) (i : Fin H.q) :
    DegenerateOn G (H.firstPhase i) (8*t) := by
  intro T hT hn
  obtain ⟨v,hv,hd⟩ := (H.first i).degenerate T (hT.trans (sdiff_subset.trans sdiff_subset)) hn
  exact ⟨v,hv,hd.trans (by have := H.first_count i; omega)⟩

lemma secondPhase_degenerate (H : History G t) (i : Fin H.q) :
    DegenerateOn G (H.secondPhase i) (8*t) := by
  intro T hT hn
  obtain ⟨v,hv,hd⟩ := (H.second i).degenerate T (hT.trans (sdiff_subset.trans sdiff_subset)) hn
  exact ⟨v,hv,hd.trans (by have := H.second_count i; omega)⟩

lemma secondPhase_first_neighbors (H : History G t) (i : Fin H.q) {v : V}
    (hv : v ∈ H.secondPhase i) : ((H.firstPhase i).filter (G.Adj v)).card ≤ 12*t := by
  obtain ⟨⟨_,hv⟩,_⟩ := mem_sdiff.mp hv |>.imp_left mem_sdiff.mp
  have hF : v ∉ H.footprint i.val := fun hh => hv (mem_union_left _ hh)
  have hp : v ∉ (H.first i).used := fun hh => hv (mem_union_right _ hh)
  have hd : v ∈ (H.first i).domain := by
    rw [H.first_domain i]
    exact mem_sdiff.mpr ⟨mem_univ _,fun hh => hF (mem_sdiff.mp hh).1⟩
  exact (card_le_card (filter_subset_filter _ (sdiff_subset.trans sdiff_subset))).trans
    (((H.first i).used_neighbors v hd hp).trans (by have := H.first_count i; omega))

lemma footprint_degenerate (H : History G t) {r : ℕ} (hr : r ≤ H.q) :
    DegenerateOn G (H.footprint r \ H.deleted) ((6*3202+20)*t) := by
  induction r with
  | zero =>
    intro T hT hn
    obtain ⟨v,hv⟩ := hn
    obtain ⟨hvF,hvX⟩ := mem_sdiff.mp (hT hv)
    exact False.elim (hvX (H.small_deleted (H.initial_small hvF)))
  | succ r ih =>
    let i : Fin H.q := ⟨r,by omega⟩
    have hfirst : DegenerateOn G ((H.footprint r \ H.deleted) ∪ H.firstPhase i)
        ((6*3202+20)*t) := by
      apply degenerate_union G _ _ _ (8*t) (6*3202*t) (ih (by omega)) (H.firstPhase_degenerate i)
      · intro v hv
        obtain ⟨⟨_,hvF⟩,hvX⟩ := mem_sdiff.mp hv |>.imp_left mem_sdiff.mp
        exact H.past_neighbors (by omega) hvF hvX
      · omega
    rw [H.phase_decomposition i]
    apply degenerate_union G _ _ _ (8*t) (6*3202*t+12*t) hfirst (H.secondPhase_degenerate i)
    · intro v hv
      obtain ⟨⟨_,hvF⟩,hvX⟩ := mem_sdiff.mp hv |>.imp_left mem_sdiff.mp
      have hF : v ∉ H.footprint r := fun hh => hvF (mem_union_left _ hh)
      have h1 := H.past_neighbors (by omega : r ≤ H.q) hF hvX
      have h2 := H.secondPhase_first_neighbors i hv
      rw [filter_union]
      exact (card_union_le _ _).trans (Nat.add_le_add h1 h2)
    · omega

lemma footprint_external_neighbors (H : History G t) {v : V}
    (hv : v ∉ H.deleted ∪ (H.footprint H.q \ H.deleted)) :
    ((H.footprint H.q \ H.deleted).filter (G.Adj v)).card ≤ (6*3202+20)*t := by
  have hx : v ∉ H.deleted := fun h => hv (mem_union_left _ h)
  have hF : v ∉ H.footprint H.q := fun h => hv (mem_union_right _ (mem_sdiff.mpr ⟨h,hx⟩))
  exact (H.past_neighbors le_rfl hF hx).trans (by omega)

theorem footprint_deletion_data : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : History G t),
    hadwigerNumber G < t → H.q ≤ rounds t →
    (H.deleted.card : ℝ) ≤ (t:ℝ)^(11/10:ℝ) ∧
    Disjoint H.deleted (H.footprint H.q \ H.deleted) ∧
    DegenerateOn G (H.footprint H.q \ H.deleted) ((6*3202+20)*t) ∧
    (∀ v ∉ H.deleted ∪ (H.footprint H.q \ H.deleted),
      ((H.footprint H.q \ H.deleted).filter (G.Adj v)).card ≤ (6*3202+20)*t) := by
  classical
  obtain ⟨t₁,ht₁⟩ := deleted_card
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp exceptional_size_cutoff
  refine ⟨max t₁ ⌈T⌉₊,?_⟩
  intro t ht V _ _ G H hex hround
  have ht₁' : t₁ ≤ t := (le_max_left _ _).trans ht
  have hT' : T ≤ (t:ℝ) := (Nat.le_ceil T).trans (by exact_mod_cast (le_max_right _ _).trans ht)
  have hc := (hT t hT').2.2
  have hq : (H.q:ℝ) ≤ rounds (t:ℝ) := by exact_mod_cast hround
  refine ⟨?_,disjoint_sdiff_self_right,H.footprint_degenerate le_rfl,fun v hv => H.footprint_external_neighbors hv⟩
  apply (ht₁ t ht₁' V G H hex).trans
  apply le_trans ?_ hc
  gcongr

end LinearListHadwiger.Footprint.History

namespace LinearListHadwiger.Footprint.History
open Finset SmallList

theorem list_loss_or_obstruction_oai : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : History G t),
    hadwigerNumber G < t → H.q ≤ rounds t →
    listChromaticNumber G ≤ listChromaticNumber (G.induce (↑(univ\H.footprint H.q):Set V)) +
      (4*32768+6*3202+25)*t ∨ FractionalObstruction G := by
  classical
  obtain ⟨t₁,ht₁⟩ := footprint_deletion_data
  obtain ⟨t₂,ht₂⟩ := additive_deletion_or_obstruction
  refine ⟨max t₁ t₂,?_⟩
  intro t ht V _ _ G H hminor hround
  obtain ⟨hsize,hdis,hdeg,hext⟩ := ht₁ t ((le_max_left _ _).trans ht) V G H hminor hround
  rcases ht₂ t ((le_max_right _ _).trans ht) V G H.deleted
    (H.footprint H.q\H.deleted) (6*3202+20) hminor hsize hdis hdeg hext with hbound | hbad
  · left
    have hsub : (↑(univ\(H.deleted∪(H.footprint H.q\H.deleted))):Set V) ⊆
        (↑(univ\H.footprint H.q):Set V) := by
      intro v hv
      obtain ⟨hu,hn⟩ := mem_sdiff.mp hv
      refine mem_sdiff.mpr ⟨hu,?_⟩
      intro hh
      by_cases hx : v∈H.deleted
      · exact hn (mem_union_left _ hx)
      · exact hn (mem_union_right _ (mem_sdiff.mpr ⟨hh,hx⟩))
    have hmono := (listChromaticNumber_le_iff _ _).mpr
      (choosable_induce_subset
        (choosable_listChromaticNumber (G.induce (↑(univ\H.footprint H.q):Set V))) hsub)
    have he : 4*32768+(6*3202+20)+5=4*32768+6*3202+25 := by norm_num
    rw [he] at hbound
    exact hbound.trans (Nat.add_le_add_right hmono _)
  · exact Or.inr hbad

end LinearListHadwiger.Footprint.History

end OAI
end

theorem solution : type_of% @OAI.LinearListHadwiger.Footprint.History.list_loss_or_obstruction_oai := @OAI.LinearListHadwiger.Footprint.History.list_loss_or_obstruction_oai
