-- Prove2me | solution 1 for OAI.LinearListHadwiger.Stage.districts_woven
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:56:12.498997+00:00
-- url     : https://prove2.me/submissions/14e0d944-ee81-416a-bdc8-e879daf61ac5

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

end LinearListHadwiger.Sampling

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

end LinearListHadwiger.CoarseDensity

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
-- module Solutions.OAIQW_ListHadwiger.PaletteSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open Finset ConnectivityTests
variable {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω]

theorem complement_failure_thousand (G : SimpleGraph V) [DecidableRel G.Adj]
    {n r ε : ℝ} {k : ℕ} (hk : 64 ≤ k) (hr : 0 < r) (hrk : r ≤ k)
    (hord : (Fintype.card V : ℝ) ≤ n) (hconn : KConnectedOn G univ k)
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (U : Ω → Finset V)
    (hsurv : ∀ v, probability μ (fun ω => v ∈ U ω) ≤ 1/1000)
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
      have hm : expectation μ (fun z => ((U z ∩ A i).card : ℝ)) ≤ (k:ℝ)/1000 := by
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

lemma coin_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ coin p b := by cases b <;> simp [coin] <;> linarith

lemma coin_sum (p : ℝ) : ∑ b : Bool, coin p b = 1 := by
  simp [coin]

lemma chosen_marginal (p : ℝ) (v : V) :
    probability (productMass (fun _ : V => coin p)) (fun x => v ∈ chosen x) = p := by
  classical
  have he : (fun x : V → Bool => v ∈ chosen x) = (fun x => x v = true) := by
    funext x
    simp [chosen]
  rw [he,probability_coordinate (fun _ => coin_sum p) v (fun b => b = true)]
  simp [probability,coin]

lemma chosen_mean (p : ℝ) (D : Finset V) :
    expectation (productMass (fun _ : V => coin p))
      (fun x => ((chosen x ∩ D).card : ℝ)) = (D.card : ℝ)*p := by
  rw [expectation_inter_card]
  simp only [chosen_marginal,sum_const,nsmul_eq_mul]

lemma chosen_bounded_change (D : Finset V) (i : V) (x y : V → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |((chosen x ∩ D).card : ℝ)-(chosen y ∩ D).card| ≤ 1 := by
  classical
  have he : (chosen x ∩ D).erase i = (chosen y ∩ D).erase i := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [chosen,hj,hxy j hj]
  have hx := card_erase_le (s := chosen x ∩ D) (a := i)
  have hy := card_erase_le (s := chosen y ∩ D) (a := i)
  have hx' := pred_card_le_card_erase (s := chosen x ∩ D) (a := i)
  have hy' := pred_card_le_card_erase (s := chosen y ∩ D) (a := i)
  have hec := congrArg Finset.card he
  have h₁ : (chosen x ∩ D).card ≤ (chosen y ∩ D).card+1 := by omega
  have h₂ : (chosen y ∩ D).card ≤ (chosen x ∩ D).card+1 := by omega
  have h₁r : ((chosen x ∩ D).card : ℝ) ≤ (chosen y ∩ D).card+1 := by exact_mod_cast h₁
  have h₂r : ((chosen y ∩ D).card : ℝ) ≤ (chosen x ∩ D).card+1 := by exact_mod_cast h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma chosen_concentration {p u : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hn : 1 ≤ Fintype.card V) (hu : 0 < u) (D : Finset V) :
    probability (productMass (fun _ : V => coin p))
      (fun x => u ≤ |((chosen x ∩ D).card : ℝ)-(D.card : ℝ)*p|) ≤
      2*Real.exp (-u^2/(2*Fintype.card V)) := by
  have hh := bounded_differences_general hn (fun _ : V => coin p)
    (fun _ => coin_nonneg hp hp1) (fun _ => coin_sum p)
    (fun x => ((chosen x ∩ D).card : ℝ)) (by norm_num : (0:ℝ)<1) hu
    (chosen_bounded_change D)
  simpa only [chosen_mean,one_pow,mul_one] using hh

theorem exists_sparse_split {I : Type} [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} {n : ℝ}
    (hk : 64 ≤ k) (hord : (Fintype.card V : ℝ) ≤ n)
    (hc : KConnectedOn G univ k) (D : I → Finset V)
    (hD : ∀ i, (D i).card = k)
    (hsmall : ((Fintype.card I : ℝ)+n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1)) *
      (2*Real.exp (-((k:ℝ)/2000)^2/(2*Fintype.card V))) < 1) :
    ∃ A : Finset V,
      (∀ i, k ≤ 2000*(A ∩ D i).card ∧ k ≤ 2*((univ \ A) ∩ D i).card) ∧
      KConnectedOn G (univ \ A) (k/32) := by
  classical
  let μ := productMass (fun _ : V => coin (1/1000))
  let ε := 2*Real.exp (-((k:ℝ)/2000)^2/(2*Fintype.card V))
  have hkpos : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have hn : 1 ≤ Fintype.card V := by
    have hh := hc.1
    simp only [card_univ] at hh
    omega
  have hμ : ∀ x, 0 ≤ μ x := productMass_nonneg
    (fun _ => coin_nonneg (by norm_num) (by norm_num))
  have hμs : ∑ x, μ x = 1 := productMass_sum (fun _ => coin_sum _)
  let bad (i : I) (x : V → Bool) : Prop := ¬(k ≤ 2000*(chosen x ∩ D i).card ∧
    k ≤ 2*((univ \ chosen x) ∩ D i).card)
  have hbad (i : I) : probability μ (bad i) ≤ ε := by
    have hh := chosen_concentration (V := V) (p := 1/1000) (by norm_num)
      (by norm_num) hn (show (0:ℝ)<k/2000 by positivity) (D i)
    refine (probability_mono hμ ?_).trans hh
    intro x hx
    by_contra hd
    have hdev := abs_lt.mp (lt_of_not_ge hd)
    rw [hD i] at hdev
    have he : ((univ \ chosen x) ∩ D i).card + (chosen x ∩ D i).card = k := by
      rw [show (univ \ chosen x) ∩ D i = D i \ chosen x by ext; simp; tauto,
        inter_comm (chosen x)]
      exact (card_sdiff_add_card_inter _ _).trans (hD i)
    have he' : (((univ \ chosen x) ∩ D i).card : ℝ) + (chosen x ∩ D i).card = k := by
      exact_mod_cast he
    apply hx
    constructor
    · have hh : (k:ℝ) ≤ 2000*(chosen x ∩ D i).card := by linarith
      exact_mod_cast hh
    · have hh : (k:ℝ) ≤ 2*((univ \ chosen x) ∩ D i).card := by linarith
      exact_mod_cast hh
  let cbad (x : V → Bool) : Prop := ¬((∀ v,
    k ≤ 2*((univ \ chosen x).filter (G.Adj v)).card) ∧
    KConnectedOn G (univ \ chosen x) (k/32))
  have hcomp : probability μ cbad ≤
      (n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε := by
    apply complement_failure_thousand G hk hkpos le_rfl hord hc hμ chosen
    · intro v
      exact (chosen_marginal (1/1000) v).le
    · dsimp [ε]; positivity
    · intro A
      have hh := chosen_concentration (V := V) (p := 1/1000) (by norm_num)
        (by norm_num) hn (show (0:ℝ)<k/2000 by positivity) A
      refine (probability_mono hμ ?_).trans hh
      intro x hx
      rw [chosen_mean] at hx
      exact (by linarith : (k:ℝ)/2000 ≤ k/100).trans hx
  have hfail : probability μ (fun x => (∃ i, bad i x) ∨ cbad x) < 1 := by
    have hu := probability_union_le hμ bad
    have hs : (∑ i, probability μ (bad i)) ≤ (Fintype.card I : ℝ)*ε := by
      calc
        _ ≤ ∑ _i : I, ε := sum_le_sum (fun i _ => hbad i)
        _ = _ := by simp
    have ho := probability_or_le hμ (fun x => ∃ i, bad i x) cbad
    have he : ((Fintype.card I:ℝ)+n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε =
        (Fintype.card I : ℝ)*ε+(n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1))*ε := by ring
    rw [he] at hsmall
    linarith
  obtain ⟨x,_,hx⟩ := exists_positive_avoiding hμ hμs hfail
  refine ⟨chosen x,?_,?_⟩
  · intro i
    by_contra hh
    exact hx (Or.inl ⟨i,hh⟩)
  · have hh : ¬cbad x := fun hh => hx (Or.inr hh)
    exact (not_not.mp hh).2

open Filter

lemma sparse_split_numeric_cutoff :
    ∀ᶠ t : ℝ in atTop, ∀ n k N m : ℝ,
      1 ≤ N → N ≤ n → n ≤ t^(11/10:ℝ) → t ≤ k → 0 ≤ m → m ≤ n →
      (m+n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1)) *
        (2*Real.exp (-(k/2000)^2/(2*N))) < 1 := by
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<1/5 by norm_num)).eventually
    (eventually_ge_atTop (8000000:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hp,complement_numeric_cutoff]
    with t ht hp hc
  intro n k N m hN hNn hn htk hm hmn
  have htpos : 0<t := by linarith
  have hkpos : 0<k := lt_of_lt_of_le htpos htk
  have hn1 : 1≤n := hN.trans hNn
  have hp7 : 0≤t^(7/10:ℝ) := Real.rpow_nonneg htpos.le _
  have hpow : t^(7/10:ℝ)*(t^(1/5:ℝ)*t^(11/10:ℝ))=t^2 := by
    rw [← Real.rpow_add htpos,← Real.rpow_add htpos]
    norm_num
  have hbase : t^(7/10:ℝ)*(8000000*N) ≤ k^2 := by
    calc
      _ ≤ t^(7/10:ℝ)*(8000000*t^(11/10:ℝ)) := by gcongr; exact hNn.trans hn
      _ ≤ t^(7/10:ℝ)*(t^(1/5:ℝ)*t^(11/10:ℝ)) := by gcongr
      _ = t^2 := hpow
      _ ≤ k^2 := by nlinarith
  have he : t^(7/10:ℝ) ≤ (k/2000)^2/(2*N) := by
    apply (le_div_iff₀ (by linarith : 0<2*N)).mpr
    nlinarith
  have htail : 2*Real.exp (-(k/2000)^2/(2*N)) ≤ 2*Real.exp (-t^(7/10:ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  let H : ℝ := n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1)
  have hHpos : 0 ≤ H := by dsimp [H]; positivity
  have hcoef : m+n+(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1) ≤ 2*H := by
    dsimp [H]
    have hp0 : 0≤(n+1)^(⌈10*(n/k)*Real.log (2*n)⌉₊+1) := by positivity
    linarith
  calc
    _ ≤ (2*H)*(2*Real.exp (-(k/2000)^2/(2*N))) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ (2*H)*(2*Real.exp (-t^(7/10:ℝ))) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 2*(H*(2*Real.exp (-t^(7/10:ℝ)))) := by ring
    _ ≤ 2*(1/100) := mul_le_mul_of_nonneg_left (hc n k hn1 hn htk) (by norm_num)
    _ < 1 := by norm_num

theorem sparse_split_cutoff :
    ∃ T : ℝ, ∀ t n : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      ∀ (V I : Type) [Fintype V] [DecidableEq V] [Fintype I],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      ∀ k : ℕ, t ≤ k → (Fintype.card V : ℝ) ≤ n → (Fintype.card I : ℝ) ≤ n →
      KConnectedOn G univ k → ∀ D : I → Finset V, (∀ i, (D i).card=k) →
      ∃ A : Finset V,
        (∀ i, k ≤ 2000*(A ∩ D i).card ∧ k ≤ 2*((univ \ A) ∩ D i).card) ∧
        KConnectedOn G (univ \ A) (k/32) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp sparse_split_numeric_cutoff
  refine ⟨max T 64,?_⟩
  intro t n ht hn hnt V I _ _ _ G _ k htk hord hI hc D hD
  have hk : 64≤k := by
    have hh : (64:ℝ)≤k := (le_max_right T 64).trans (ht.trans htk)
    exact_mod_cast hh
  apply exists_sparse_split G hk hord hc D hD
  have hN : (1:ℝ)≤Fintype.card V := by
    have hh := hc.1
    simp only [card_univ] at hh
    exact_mod_cast (by omega : 1≤Fintype.card V)
  exact hT t ((le_max_left _ _).trans ht) n k (Fintype.card V) (Fintype.card I)
    hN hord hnt htk (Nat.cast_nonneg _) hI

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open Finset
variable {V : Type} [Fintype V] [DecidableEq V]

theorem sparse_split_on_cutoff :
    ∃ T : ℝ, ∀ t n : ℝ, T ≤ t → 1 ≤ n → n ≤ t^(11/10:ℝ) →
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      ∀ (S : Finset V) (k : ℕ), t ≤ k → (Fintype.card V : ℝ) ≤ n →
      KConnectedOn G S k → (∀ v, k ≤ (S.filter (G.Adj v)).card) →
      ∃ A B : Finset V, A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧
        (∀ v, k ≤ 2000*(A.filter (G.Adj v)).card ∧
          k ≤ 2*(B.filter (G.Adj v)).card) ∧ KConnectedOn G B (k/32) := by
  obtain ⟨T,hT⟩ := sparse_split_cutoff
  refine ⟨T,?_⟩
  intro t n ht hn hnt V _ _ G _ S k htk hord hc hdeg
  classical
  let N (v : V) : Finset (↑S : Set V) := univ.filter (fun w => G.Adj v w.val)
  have hNc (v : V) : (N v).card=(S.filter (G.Adj v)).card := by
    rw [←card_image_of_injective (N v) Subtype.val_injective]
    congr 1
    ext w
    simp only [N,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,hu⟩
    · rintro ⟨hw,hvw⟩
      exact ⟨⟨w,hw⟩,hvw,rfl⟩
  have hD : ∀ v, ∃ D ⊆ N v, D.card=k := fun v =>
    exists_subset_card_eq (by rw [hNc]; exact hdeg v)
  choose D hDN hDc using hD
  have hSord : (Fintype.card (↑S : Set V) : ℝ) ≤ n := by
    have hs : Fintype.card (↑S : Set V) ≤ Fintype.card V := Fintype.card_subtype_le _
    exact (show (Fintype.card (↑S : Set V) : ℝ) ≤ Fintype.card V by
      exact_mod_cast hs).trans hord
  obtain ⟨A',hA',hB'⟩ := hT t n ht hn hnt (↑S : Set V) V (G.induce (↑S : Set V))
    k htk hSord hord (Knitting.induce_connected G S hc) D hDc
  let A := A'.image Subtype.val
  let B := (univ\A').image Subtype.val
  have himage_subset (E : Finset (↑S : Set V)) : E.image Subtype.val ⊆ S := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := mem_image.mp hv
    exact w.property
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    obtain ⟨u,hu,huv⟩ := mem_image.mp hva
    obtain ⟨w,hw,hwv⟩ := mem_image.mp hvb
    have he : u=w := Subtype.val_injective (huv.trans hwv.symm)
    exact (mem_sdiff.mp hw).2 (he ▸ hu)
  have hcount (E : Finset (↑S : Set V)) (v : V) :
      (E ∩ D v).card ≤ ((E.image Subtype.val).filter (G.Adj v)).card := by
    rw [←card_image_of_injective (E ∩ D v) Subtype.val_injective]
    apply card_le_card
    intro w hw
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨mem_image.mpr ⟨u,(mem_inter.mp hu).1,rfl⟩,
      (mem_filter.mp (hDN v (mem_inter.mp hu).2)).2⟩
  refine ⟨A,B,himage_subset _,himage_subset _,hdis,?_,?_⟩
  · intro v
    exact ⟨(hA' v).1.trans (Nat.mul_le_mul_left _ (hcount A' v)),
      (hA' v).2.trans (Nat.mul_le_mul_left _ (hcount (univ\A') v))⟩
  · exact Knitting.kConnected_image G Subtype.val Subtype.val_injective hB'

end LinearListHadwiger.Sampling

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
open Filter Real

lemma small_woven_order_cutoff :
    ∀ᶠ t : ℝ in atTop, 2 ≤ t ∧ ∀ s : ℕ,
      1 ≤ s → s ≤ 2*⌈t/(Real.log t)^2⌉₊ →
      (s:ℝ) ≤ t ∧ 100000000*s*Real.log (2*s) < t/8000 := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (2:ℝ)
    (show (0:ℝ)<1 by norm_num)).bound (show (0:ℝ)<1/2 by norm_num)
  have hbig := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (10000000000000:ℝ))
  filter_upwards [eventually_ge_atTop (2:ℝ),hlog,hbig] with t ht hl hb
  have ht0 : 0<t := by linarith
  have hln : 0 < Real.log t := by linarith
  have hl2 : (Real.log t)^2 ≤ t/2 := by
    have hh : (Real.log t)^2 ≤ (1/2:ℝ)*t := by
      rw [←Real.rpow_natCast (Real.log t) 2]
      simpa only [Nat.cast_ofNat,Real.norm_eq_abs,Real.rpow_one,
        abs_of_nonneg (Real.rpow_nonneg hln.le (2:ℝ)),abs_of_pos ht0] using hl
    linarith
  refine ⟨ht,?_⟩
  intro s hs hsc
  have hs0 : (0:ℝ)<s := by exact_mod_cast (by omega : 0<s)
  have hsc' : (s:ℝ)≤2*(⌈t/(Real.log t)^2⌉₊:ℝ) := by exact_mod_cast hsc
  have hceil := Nat.ceil_lt_add_one (div_nonneg ht0.le (sq_nonneg (Real.log t)))
  have hsbound : (s:ℝ)*(Real.log t)^2 ≤ 3*t := by
    have hx : (s:ℝ)<2*(t/(Real.log t)^2+1) := by linarith
    have hm := mul_lt_mul_of_pos_right hx (sq_pos_of_pos hln)
    have he : (t/(Real.log t)^2)*((Real.log t)^2)=t :=
      div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hln))
    nlinarith
  have hst : (s:ℝ)≤t := by
    have hc : (3:ℝ)≤(Real.log t)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hc hs0.le
    nlinarith
  refine ⟨hst,?_⟩
  have hlogs : Real.log (2*s) ≤ 2*Real.log t := by
    have hh := Real.log_le_log (show (0:ℝ)<2*s by positivity)
      (show (2:ℝ)*s≤2*t by linarith)
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) ht0.ne'] at hh
    have htwo := Real.log_le_log (by norm_num : (0:ℝ)<2) ht
    linarith
  have hleft : 100000000*s*Real.log (2*s) ≤ 200000000*((s:ℝ)*Real.log t) := by
    have hh := mul_le_mul_of_nonneg_left hlogs (show (0:ℝ)≤100000000*s by positivity)
    nlinarith
  have hb' : (4800000000000:ℝ)<Real.log t := by linarith
  have hmul := mul_lt_mul_of_pos_left hb' (mul_pos hs0 hln)
  have htail : 200000000*((s:ℝ)*Real.log t)<t/8000 := by nlinarith [hsbound]
  exact hleft.trans_lt htail

end LinearListHadwiger.Assembly

namespace LinearListHadwiger.Assembly
open SimpleGraph Finset
variable {V O I : Type} [Fintype V] [DecidableEq V]
  [Fintype O] [Fintype I] [DecidableEq I]

theorem group_ports (G : SimpleGraph V) [DecidableRel G.Adj]
    (port : O → V) (label : O → I) (hs : Function.Surjective label)
    (hO : 1 ≤ Fintype.card O) (U : Finset V)
    (hN : ∀ o, Fintype.card O ≤ (U.filter (G.Adj (port o))).card)
    (hconn : KConnectedOn G U (65536*Fintype.card O)) :
    ∃ C : I → Set V,
      (∀ i, (G.induce (C i)).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (∀ i, C i ⊆ (↑U : Set V)) ∧
      ∀ o, ∃ v ∈ C (label o), G.Adj (port o) v := by
  classical
  obtain ⟨nbr,hni,hn⟩ := attach_ports (G := G) port U hN
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
  let lab : ↥A → I := fun a => label (idx a)
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
  let D : I → Set V := fun i => M.expand (C i)
  have hDU : ∀ i, D i ⊆ (↑U : Set V) := by
    intro i v hv
    obtain ⟨w,_,hw⟩ := hv
    have he : v = w.val := hw
    exact he ▸ w.property
  refine ⟨D,fun i => M.expand_connected (hC i),
    fun i j hij => M.expand_disjoint (hCC i j hij),hDU,?_⟩
  intro o
  refine ⟨nbr o,?_,(hn o).2⟩
  refine ⟨nr o,?_,rfl⟩
  have ht := hterm ⟨nr o,ha o⟩
  simpa only [lab,hi] using ht

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

theorem weaving_from_core_groups (G : SimpleGraph V) {a p : ℕ}
    (roots : Fin a → V) (x y : Fin p → V) (hr : Function.Injective roots)
    (he : ∀ i j, i ≠ j → Disjoint ({x i,y i} : Set V) {x j,y j})
    (A B : Set V) (hAB : Disjoint A B)
    (hroot : ∀ j, roots j ∉ A ∧ roots j ∉ B)
    (hend : ∀ i, x i ∉ A ∧ x i ∉ B ∧ y i ∉ A ∧ y i ∉ B)
    (core : Fin a → Set V)
    (hcore : ∀ j, (G.induce (core j)).Connected)
    (hcoreA : ∀ j, core j ⊆ A)
    (hcores : ∀ i j, i ≠ j → Disjoint (core i) (core j))
    (hclique : ∀ i j, i ≠ j → ∃ v ∈ core i, ∃ w ∈ core j, G.Adj v w)
    (C : (Fin a ⊕ Fin p) → Set V)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hCB : ∀ i, C i ⊆ B)
    (hCC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hattach : ∀ j, ∃ v ∈ core j, ∃ w ∈ C (.inl j), G.Adj v w)
    (hattachRoot : ∀ j, ∃ w ∈ C (.inl j), G.Adj (roots j) w)
    (hattachX : ∀ i, ∃ w ∈ C (.inr i), G.Adj (x i) w)
    (hattachY : ∀ i, ∃ w ∈ C (.inr i), G.Adj (y i) w) :
    Nonempty (WeavingWithin G Set.univ roots x y) := by
  classical
  let bag (j : Fin a) := insert (roots j) (core j ∪ C (.inl j))
  have hb (j : Fin a) : (G.induce (bag j)).Connected := by
    obtain ⟨v,hv,w,hw,hvw⟩ := hattach j
    have hh := SimpleGraph.connected_induce_union (hcore j).preconnected
      (hC (.inl j)).preconnected hv hw hvw
    obtain ⟨w,hw,hew⟩ := hattachRoot j
    exact Incidence.connected_insert hh (Or.inr hw) hew
  have hbd (i j : Fin a) (hij : i ≠ j) : Disjoint (bag i) (bag j) := by
    apply Set.disjoint_left.mpr
    intro v hi hj
    rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj
    · exact hij (hr (hi.symm.trans hj))
    · exact (hroot i).1 (hi ▸ hcoreA j hj)
    · exact (hroot i).2 (hi ▸ hCB (.inl j) hj)
    · exact (hroot j).1 (hj ▸ hcoreA i hi)
    · exact Set.disjoint_left.mp (hcores i j hij) hi hj
    · exact Set.disjoint_left.mp hAB (hcoreA i hi) (hCB (.inl j) hj)
    · exact (hroot j).2 (hj ▸ hCB (.inl i) hi)
    · exact Set.disjoint_left.mp hAB (hcoreA j hj) (hCB (.inl i) hi)
    · exact Set.disjoint_left.mp (hCC (.inl i) (.inl j) (by simpa using hij)) hi hj
  let M : RootedCliqueModel G roots :=
    { branch := bag
      connected := hb
      disjoint := hbd
      adjacent := fun i j hij => by
        obtain ⟨v,hv,w,hw,hvw⟩ := hclique i j hij
        exact ⟨v,Or.inr (Or.inl hv),w,Or.inr (Or.inl hw),hvw⟩
      root_mem := fun _ => Or.inl rfl }
  let S (i : Fin p) := insert (x i) (insert (y i) (C (.inr i)))
  have hS (i : Fin p) : (G.induce (S i)).Connected := by
    obtain ⟨w,hw,hew⟩ := hattachY i
    have hh := Incidence.connected_insert (hC (.inr i)) hw hew
    obtain ⟨w,hw,hew⟩ := hattachX i
    exact Incidence.connected_insert hh (Or.inr hw) hew
  have hpaths : ∀ i, ∃ Q : G.Path (x i) (y i), ∀ v ∈ Q.val.support, v ∈ S i :=
    fun i => path_in_connected (hS i) (Or.inl rfl) (Or.inr (Or.inl rfl))
  choose Q hQ using hpaths
  refine ⟨⟨M,fun _ _ _ => Set.mem_univ _,Q,fun _ _ _ => Set.mem_univ _,?_,?_⟩⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hi hj
    have hi' := hQ i v hi
    have hj' := hQ j v hj
    have hterm : ∀ i, ∀ v ∈ ({x i,y i} : Set V), v ∉ B := by
      intro i v hv
      rcases hv with rfl | hv
      · exact (hend i).2.1
      · exact hv ▸ (hend i).2.2.2
    have hsplit : ∀ i v, v ∈ S i → v ∈ ({x i,y i} : Set V) ∨ v ∈ C (.inr i) := by
      intro i v hv
      rcases hv with hv | hv | hv
      · exact Or.inl (Or.inl hv)
      · exact Or.inl (Or.inr hv)
      · exact Or.inr hv
    rcases hsplit i v hi' with hi' | hi' <;> rcases hsplit j v hj' with hj' | hj'
    · exact Set.disjoint_left.mp (he i j hij) hi' hj'
    · exact hterm i v hi' (hCB (.inr j) hj')
    · exact hterm j v hj' (hCB (.inr i) hi')
    · exact Set.disjoint_left.mp (hCC (.inr i) (.inr j) (by simpa using hij)) hi' hj'
  · intro i j v hv hbag
    have hs := hQ i v hv
    change v ∈ insert (roots j) (core j ∪ C (.inl j)) at hbag
    rcases hs with hs | hs | hs
    · subst v
      rcases hbag with hb | hb | hb
      · exact ⟨⟨j,hb.symm⟩,Or.inl rfl⟩
      · exact ((hend i).1 (hcoreA j hb)).elim
      · exact ((hend i).2.1 (hCB (.inl j) hb)).elim
    · subst v
      rcases hbag with hb | hb | hb
      · exact ⟨⟨j,hb.symm⟩,Or.inr rfl⟩
      · exact ((hend i).2.2.1 (hcoreA j hb)).elim
      · exact ((hend i).2.2.2 (hCB (.inl j) hb)).elim
    · rcases hbag with hb | hb | hb
      · exact ((hroot j).2 (hb ▸ hCB (.inr i) hs)).elim
      · exact (Set.disjoint_left.mp hAB (hcoreA j hb) (hCB (.inr i) hs)).elim
      · exact (Set.disjoint_left.mp (hCC (.inr i) (.inl j) (by simp)) hs hb).elim

theorem weaving_from_connected_complement (G : SimpleGraph V) [DecidableRel G.Adj]
    {a p : ℕ} (ha : 1 ≤ a)
    (roots : Fin a → V) (x y : Fin p → V) (hr : Function.Injective roots)
    (he : ∀ i j, i ≠ j → Disjoint ({x i,y i} : Set V) {x j,y j})
    (A : Set V) (B : Finset V) (hAB : Disjoint A (↑B : Set V))
    (hroot : ∀ j, roots j ∉ A ∧ roots j ∉ B)
    (hend : ∀ i, x i ∉ A ∧ x i ∉ B ∧ y i ∉ A ∧ y i ∉ B)
    (core : Fin a → Set V)
    (hcore : ∀ j, (G.induce (core j)).Connected)
    (hcoreA : ∀ j, core j ⊆ A)
    (hcores : ∀ i j, i ≠ j → Disjoint (core i) (core j))
    (hclique : ∀ i j, i ≠ j → ∃ v ∈ core i, ∃ w ∈ core j, G.Adj v w)
    (hN : ∀ v, 2*(a+p) ≤ (B.filter (G.Adj v)).card)
    (hconn : KConnectedOn G B (65536*(2*(a+p)))) :
    Nonempty (WeavingWithin G Set.univ roots x y) := by
  classical
  have hp : ∀ j, ∃ v, v ∈ core j := fun j => by
    obtain ⟨v⟩ := (hcore j).nonempty
    exact ⟨v.val,v.property⟩
  choose cp hcp using hp
  let O := (Fin a ⊕ Fin p) × Bool
  let port : O → V := fun o => match o.1 with
    | .inl j => if o.2 then roots j else cp j
    | .inr i => if o.2 then y i else x i
  have hc : Fintype.card O = 2*(a+p) := by simp [O,Nat.mul_comm]
  obtain ⟨C,hC,hCC,hCB,hports⟩ := group_ports G port Prod.fst
    (fun i => ⟨(i,false),rfl⟩) (by rw [hc]; omega) B
    (fun _ => by rw [hc]; exact hN _) (by rw [hc]; exact hconn)
  apply weaving_from_core_groups G roots x y hr he A (↑B : Set V) hAB
    hroot hend core hcore hcoreA hcores hclique C hC hCB hCC
  · intro j
    obtain ⟨v,hv,he⟩ := hports (.inl j,false)
    exact ⟨cp j,hcp j,v,hv,he⟩
  · intro j
    exact hports (.inl j,true)
  · intro i
    exact hports (.inr i,false)
  · intro i
    exact hports (.inr i,true)

end LinearListHadwiger.Assembly

namespace LinearListHadwiger.Assembly
open SimpleGraph Finset
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in

lemma clique_minor_restrict {G : SimpleGraph V} {s t : ℕ}
    (h : HasCliqueMinor G t) (hst : s ≤ t) : HasCliqueMinor G s := by
  obtain ⟨B,hB,hD,hE⟩ := h
  refine ⟨fun i => B (Fin.castLE hst i),fun i => hB _,?_,?_⟩
  · intro i j hij
    exact hD _ _ (fun he => hij (Fin.ext (congrArg (fun x : Fin t => x.val) he)))
  · intro i j hij
    exact hE _ _ (fun he => hij (Fin.ext (congrArg (fun x : Fin t => x.val) he)))

lemma density_of_scaled_degree [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k c : ℕ} (hd : ∀ v, k ≤ c*G.degree v) :
    (k:ℚ) ≤ 2*c*Knitting.density G := by
  classical
  have hs := Finset.sum_le_sum (s := univ) (fun v _ => hd v)
  rw [←Finset.mul_sum,G.sum_degrees_eq_twice_card_edges] at hs
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  have hsq : (Fintype.card V : ℚ)*k ≤ c*(2*G.edgeFinset.card) := by exact_mod_cast hs
  have he : Knitting.density G * (Fintype.card V:ℚ) = (G.edgeFinset.card:ℚ) := by
    simpa only [SimpleGraph.edgeFinset_card,Fintype.card_eq_nat_card] using
      Knitting.density_mul_order G Fintype.card_pos
  have hnq : (0:ℚ)<Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  apply le_of_mul_le_mul_right ?_ hnq
  calc
    (k:ℚ)*Fintype.card V ≤ c*(2*G.edgeFinset.card) := by nlinarith [hsq]
    _ = (2*c*Knitting.density G)*Fintype.card V := by
      have hh := congrArg (fun q : ℚ => (2:ℚ)*c*q) he
      nlinarith only [hh]

lemma dense_split_core [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {s k : ℕ} (hs : 1 ≤ s) (hk : 1 ≤ k)
    (hdeg : ∀ v, k ≤ 2000*(A.filter (G.Adj v)).card)
    (hthreshold : 100000000*s*Real.log (2*s) < (k:ℝ)/4000) :
    ∃ B : Fin s → Set V,
      (∀ i, (G.induce (B i)).Connected) ∧ (∀ i, B i ⊆ (↑A:Set V)) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w) := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  have hA : A.Nonempty := by
    have hh := hdeg v
    have hp : 0<(A.filter (G.Adj v)).card := by omega
    exact (Finset.card_pos.mp hp).mono (Finset.filter_subset _ _)
  let : Nonempty (↑A:Set V) := by obtain ⟨v,hv⟩ := hA; exact ⟨⟨v,hv⟩⟩
  let H := G.induce (↑A:Set V)
  have hd : (k:ℚ) ≤ 4000*Knitting.density H := by
    have hh := density_of_scaled_degree H (k := k) (c := 2000) (fun v => by
      rw [CoarseDensity.degree_induce_finset]
      exact hdeg v.val)
    norm_num at hh ⊢
    exact hh
  have hd' : (k:ℝ) ≤ 4000*((Knitting.density H:ℚ):ℝ) := by exact_mod_cast hd
  have hminor : HasCliqueMinor H s := by
    by_cases hs2 : 2 ≤ s
    · have hh : s ≤ hadwigerNumber H := by
        by_contra hn
        have hc := CoarseDensity.density_bound H hs2 (lt_of_not_ge hn)
        linarith
      exact clique_minor_restrict (hasCliqueMinor_hadwigerNumber H) hh
    · have he : s=1 := by omega
      rw [he]
      exact cliqueMinor_one H
  obtain ⟨C,hC,hD,hE⟩ := hminor
  let M := Knitting.model_induce G A
  refine ⟨fun i => M.expand (C i),fun i => M.expand_connected (hC i),?_,
    fun i j hij => M.expand_disjoint (hD i j hij),?_⟩
  · intro i v hv
    obtain ⟨w,_,hw⟩ := hv
    have he : v=w.val := hw
    exact he ▸ w.property
  · intro i j hij
    obtain ⟨v,hv,w,hw,hvw⟩ := hE i j hij
    exact ⟨v.val,⟨v,hv,rfl⟩,w.val,⟨w,hw,rfl⟩,hvw⟩

end LinearListHadwiger.Assembly

namespace LinearListHadwiger.Assembly
open SimpleGraph Finset Filter

theorem small_districts_woven :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → ∀ s : ℕ,
      1 ≤ s → s ≤ 2*⌈(t:ℝ)/(Real.log t)^2⌉₊ →
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      (Fintype.card V : ℝ) ≤ (t:ℝ)^(53/50:ℝ) →
      KConnectedOn G univ ((100000*65536)*t) → Woven G s (3*t) := by
  obtain ⟨Tsplit,hTsplit⟩ := Sampling.sparse_split_on_cutoff
  obtain ⟨Torder,hTorder⟩ := eventually_atTop.mp small_woven_order_cutoff
  refine ⟨⌈max Tsplit Torder⌉₊,?_⟩
  intro t ht s hs hsc V _ _ G _ hord hc
  classical
  have htr : max Tsplit Torder ≤ (t:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast ht)
  obtain ⟨ht2,hnum⟩ := hTorder t ((le_max_right _ _).trans htr)
  obtain ⟨hstr,hthreshold⟩ := hnum s hs hsc
  have hst : s ≤ t := by exact_mod_cast hstr
  have htpos : 0<t := by exact_mod_cast (by linarith : (0:ℝ)<t)
  have : Nonempty V := Fintype.card_pos_iff.mp (by
    have hh := hc.1
    simp only [card_univ] at hh
    omega)
  intro roots hr _ p hp x y _ he
  let Z : Finset V := (univ.image roots) ∪ (univ.image x) ∪ (univ.image y)
  have hZ : Z.card ≤ 7*t := by
    have h1 : (univ.image roots).card ≤ s := by simpa using card_image_le (s := univ) (f := roots)
    have h2 : (univ.image x).card ≤ p := by simpa using card_image_le (s := univ) (f := x)
    have h3 : (univ.image y).card ≤ p := by simpa using card_image_le (s := univ) (f := y)
    have hu1 := card_union_le (univ.image roots) (univ.image x)
    have hu2 := card_union_le ((univ.image roots) ∪ (univ.image x)) (univ.image y)
    dsimp [Z]
    omega
  let S := univ \ Z
  let k : ℕ := 3276800000*t
  have hk : 1 ≤ k := by dsimp [k]; omega
  have htk : (t:ℝ)≤k := by dsimp [k]; push_cast; nlinarith
  have hZk : Z.card < (100000*65536)*t := by omega
  have hSk : KConnectedOn G S k := by
    have hh := Knitting.delete_connected G hc (subset_univ Z) hZk
    exact Knitting.kConnected_mono hh (by dsimp [k]; omega)
  have hdeg : ∀ v, k ≤ (S.filter (G.Adj v)).card := by
    intro v
    have hd := Knitting.min_degree G hc (mem_univ v)
    have hsub : Density.neighbors G univ v ⊆ (S.filter (G.Adj v)) ∪ Z := by
      intro w hw
      by_cases hwZ : w∈Z
      · exact mem_union_right _ hwZ
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,hwZ⟩,
          ((Density.mem_neighbors G).mp hw).2⟩)
    have hcount := (card_le_card hsub).trans (card_union_le _ _)
    dsimp [k]
    omega
  have hn : (1:ℝ)≤(t:ℝ)^(53/50:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hpow : (t:ℝ)^(53/50:ℝ) ≤ (t:ℝ)^(11/10:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  obtain ⟨A,B,hAS,hBS,hAB,hN,hB⟩ := hTsplit t ((t:ℝ)^(53/50:ℝ))
    ((le_max_left _ _).trans htr) hn hpow V G S k htk hord hSk hdeg
  obtain ⟨core,hcore,hcoreA,hcores,hclique⟩ := dense_split_core G A hs hk
    (fun v => (hN v).1) (hthreshold.trans_le (by linarith))
  have hnot (F : Finset V) (hFS : F ⊆ S) (v : V) (hv : v∈Z) : v∉F :=
    fun hf => (mem_sdiff.mp (hFS hf)).2 hv
  apply weaving_from_connected_complement G hs roots x y hr he (↑A:Set V) B
    (by exact_mod_cast hAB) ?_ ?_ core hcore hcoreA hcores hclique ?_ ?_
  · intro j
    have hz : roots j∈Z := by simp [Z]
    exact ⟨hnot A hAS _ hz,hnot B hBS _ hz⟩
  · intro i
    have hx : x i∈Z := by simp [Z]
    have hy : y i∈Z := by simp [Z]
    exact ⟨hnot A hAS _ hx,hnot B hBS _ hx,hnot A hAS _ hy,hnot B hBS _ hy⟩
  · intro v
    have hh := (hN v).2
    dsimp [k] at hh
    omega
  · exact Knitting.kConnected_mono hB (by dsimp [k]; omega)

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

theorem districts_woven_oai : ∃ T : ℕ, ∀ t : ℕ, T≤t → ∀ s : ℕ,
    1 ≤ s → s ≤ 2*⌈(t:ℝ)/(Real.log t)^2⌉₊ →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (J : Finset V),
    (J.card:ℝ)≤(t:ℝ)^(53/50:ℝ) → KConnectedOn G J ((100000*65536)*t) →
    WovenOn G (↑J:Set V) s (3*t) := by
  classical
  obtain ⟨T,hT⟩ := Assembly.small_districts_woven
  refine ⟨T,?_⟩
  intro t ht s hs hst V _ _ G J hJs hJc
  apply woven_induce
  exact hT t ht s hs hst (↑J:Set V) (G.induce (↑J:Set V))
    (by rw [show Fintype.card (↑J:Set V)=J.card from Fintype.card_coe J]; exact hJs) (Knitting.induce_connected G J hJc)

end LinearListHadwiger.Stage

end OAI
end

theorem solution : type_of% @OAI.LinearListHadwiger.Stage.districts_woven_oai := @OAI.LinearListHadwiger.Stage.districts_woven_oai
