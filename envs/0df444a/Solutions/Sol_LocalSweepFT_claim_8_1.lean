-- Prove2me | solution 1 for LocalSweepFT.claim_8_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T00:55:57.631683+00:00
-- url     : https://prove2.me/submissions/8b9ac8a9-4180-40ba-9f56-6971ea04d40e

import Mathlib

namespace LocalSweepFT
open Relation

variable {V : Type} [DecidableEq V] (G : SimpleGraph V)

def RS (S : Finset V) (a b : V) : Prop := G.Adj a b ∧ a ∈ S ∧ b ∈ S

def Conn (S : Finset V) : Prop := ∀ x ∈ S, ∀ y ∈ S, ReflTransGen (RS G S) x y

def A (r : V) (n : ℕ) : Set (Finset V) := {S | r ∈ S ∧ S.card = n ∧ Conn G S}

lemma RS_symm (S : Finset V) {a b : V} (h : RS G S a b) : RS G S b a :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

lemma rtg_symm (S : Finset V) {a b : V} (h : ReflTransGen (RS G S) a b) :
    ReflTransGen (RS G S) b a := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (RS_symm G S hbc) ih

lemma decomp (r : V) (m : ℕ) (S : Finset V) (hS : S ∈ A G r (m + 2)) :
    ∃ (C W : Finset V) (u : V), S = C ∪ W ∧ Disjoint C W ∧ G.Adj r u ∧ u ∈ C ∧
      Conn G C ∧ r ∈ W ∧ Conn G W ∧ C.card + W.card = m + 2 := by
  classical
  obtain ⟨hr, hcard, hconn⟩ := hS
  -- another element
  have : ∃ x ∈ S, x ≠ r := by
    by_contra h
    push Not at h
    have : S ⊆ {r} := fun x hx => by simpa using h x hx
    have := Finset.card_le_card this
    simp at this; omega
  obtain ⟨x, hx, hxr⟩ := this
  -- a neighbor of r in S
  have hnb : ∃ u ∈ S, u ≠ r ∧ G.Adj r u := by
    have h := hconn r hr x hx
    rcases h.cases_head with h | ⟨c, hc, _⟩
    · exact absurd h.symm hxr
    · exact ⟨c, hc.2.2, fun e => by have := hc.1.ne; exact this e.symm, hc.1⟩
  obtain ⟨u, huS, hur, hadj⟩ := hnb
  set T := S.erase r with hT
  have huT : u ∈ T := Finset.mem_erase.2 ⟨hur, huS⟩
  set C : Finset V := T.filter (fun x => ReflTransGen (RS G T) u x) with hC
  have hCmem : ∀ x, x ∈ C ↔ x ∈ T ∧ ReflTransGen (RS G T) u x := fun x => by simp [hC]
  have huC : u ∈ C := (hCmem u).2 ⟨huT, ReflTransGen.refl⟩
  have hCS : C ⊆ S := fun x hx => Finset.mem_of_mem_erase ((hCmem x).1 hx).1
  have hrC : r ∉ C := fun h => by simpa [hT] using ((hCmem r).1 h).1
  have hCconn : Conn G C := by
    have key : ∀ x, ReflTransGen (RS G T) u x → x ∈ C ∧ ReflTransGen (RS G C) u x := by
      intro x hx
      induction hx with
      | refl => exact ⟨huC, ReflTransGen.refl⟩
      | tail hb hbc ih =>
        rename_i b c
        have hcT : c ∈ T := hbc.2.2
        have hcC : c ∈ C := (hCmem c).2 ⟨hcT, hb.tail hbc⟩
        exact ⟨hcC, ih.2.tail ⟨hbc.1, ih.1, hcC⟩⟩
    intro x hx y hy
    have h1 := (key x ((hCmem x).1 hx).2).2
    have h2 := (key y ((hCmem y).1 hy).2).2
    exact (rtg_symm G C h1).trans h2
  set W := S \ C with hW
  have hrW : r ∈ W := Finset.mem_sdiff.2 ⟨hr, hrC⟩
  have hWconn : Conn G W := by
    have key : ∀ a, ReflTransGen (RS G S) a r → a ∈ W → ReflTransGen (RS G W) a r := by
      intro a ha
      induction ha using ReflTransGen.head_induction_on with
      | refl => intro _; exact ReflTransGen.refl
      | head hab hbr ih =>
        rename_i a b
        intro haW
        by_cases hb : b ∈ C
        · by_cases har : a = r
          · subst har; exact ReflTransGen.refl
          · exfalso
            have haT : a ∈ T := Finset.mem_erase.2 ⟨har, hab.2.1⟩
            have hubb := ((hCmem b).1 hb).2
            have : RS G T b a := ⟨hab.1.symm, ((hCmem b).1 hb).1, haT⟩
            exact (Finset.mem_sdiff.1 haW).2 ((hCmem a).2 ⟨haT, hubb.tail this⟩)
        · have hbW : b ∈ W := Finset.mem_sdiff.2 ⟨hab.2.2, hb⟩
          exact ReflTransGen.head ⟨hab.1, haW, hbW⟩ (ih hbW)
    intro x hx y hy
    have h1 := key x (hconn x (Finset.mem_sdiff.1 hx).1 r hr) hx
    have h2 := key y (hconn y (Finset.mem_sdiff.1 hy).1 r hr) hy
    exact h1.trans (rtg_symm G W h2)
  refine ⟨C, W, u, ?_, ?_, hadj, huC, hCconn, hrW, hWconn, ?_⟩
  · rw [hW]; exact (Finset.union_sdiff_of_subset hCS).symm
  · rw [hW]; exact Finset.disjoint_sdiff
  · have := Finset.card_sdiff_add_card_eq_card hCS
    rw [hW]; omega


lemma A_one (r : V) : A G r 1 ⊆ {({r} : Finset V)} := by
  rintro S ⟨hr, hc, -⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc
  simp at hr; simp [hr]

lemma count_step [G.LocallyFinite] (D : ℕ) (hdeg : ∀ v, G.degree v ≤ D) (m : ℕ)
    (ih : ∀ i ≤ m, ∀ r, (A G r (i + 1)).Finite ∧ (A G r (i + 1)).ncard ≤ D ^ i * catalan i)
    (r : V) :
    (A G r (m + 2)).Finite ∧ (A G r (m + 2)).ncard ≤ D ^ (m + 1) * catalan (m + 1) := by
  classical
  let B : ℕ → Set (Finset V) := fun i => ⋃ u ∈ G.neighborFinset r, A G u (i + 1)
  have hBfin : ∀ i ≤ m, (B i).Finite := fun i hi =>
    Set.Finite.biUnion (Finset.finite_toSet _) (fun u _ => (ih i hi u).1)
  have hBcard : ∀ i ≤ m, (B i).ncard ≤ D * (D ^ i * catalan i) := by
    intro i hi
    calc (B i).ncard ≤ ∑ u ∈ G.neighborFinset r, (A G u (i + 1)).ncard :=
          Finset.set_ncard_biUnion_le _ _
      _ ≤ ∑ u ∈ G.neighborFinset r, (D ^ i * catalan i) :=
          Finset.sum_le_sum (fun u _ => (ih i hi u).2)
      _ = (G.neighborFinset r).card * (D ^ i * catalan i) := by simp
      _ ≤ D * (D ^ i * catalan i) := by
          apply Nat.mul_le_mul_right
          rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg r
  let F : ℕ → Set (Finset V) := fun i =>
    (fun p : Finset V × Finset V => p.1 ∪ p.2) '' (B i ×ˢ A G r (m - i + 1))
  have hsub : A G r (m + 2) ⊆ ⋃ i ∈ Finset.range (m + 1), F i := by
    intro S hS
    obtain ⟨C, W, u, hSe, hdis, hadj, huC, hCc, hrW, hWc, hcard⟩ := decomp G r m S hS
    have hC1 : 1 ≤ C.card := Finset.card_pos.2 ⟨u, huC⟩
    have hW1 : 1 ≤ W.card := Finset.card_pos.2 ⟨r, hrW⟩
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨C.card - 1, by omega, ?_⟩
    refine ⟨(C, W), ⟨?_, ?_⟩, hSe.symm⟩
    · simp only [B, Set.mem_iUnion]
      exact ⟨u, by simpa using hadj, huC, by omega, hCc⟩
    · exact ⟨hrW, show W.card = _ by omega, hWc⟩
  have hFfin : ∀ i ∈ Finset.range (m + 1), (F i).Finite := by
    intro i hi
    have hi' : i < m + 1 := Finset.mem_range.1 hi
    exact ((hBfin i (by omega)).prod (ih (m - i) (by omega) r).1).image _
  refine ⟨(Set.Finite.biUnion (Finset.finite_toSet _) hFfin).subset hsub, ?_⟩
  calc (A G r (m + 2)).ncard
      ≤ (⋃ i ∈ Finset.range (m + 1), F i).ncard :=
        Set.ncard_le_ncard hsub (Set.Finite.biUnion (Finset.finite_toSet _) hFfin)
    _ ≤ ∑ i ∈ Finset.range (m + 1), (F i).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), D ^ (m + 1) * (catalan i * catalan (m - i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i < m + 1 := Finset.mem_range.1 hi
        have h1 := hBcard i (by omega)
        have h2 := (ih (m - i) (by omega) r).2
        calc (F i).ncard ≤ (B i ×ˢ A G r (m - i + 1)).ncard :=
              Set.ncard_image_le ((hBfin i (by omega)).prod (ih (m - i) (by omega) r).1)
          _ = (B i).ncard * (A G r (m - i + 1)).ncard := Set.ncard_prod
          _ ≤ (D * (D ^ i * catalan i)) * (D ^ (m - i) * catalan (m - i)) :=
              Nat.mul_le_mul h1 h2
          _ = D ^ (m + 1) * (catalan i * catalan (m - i)) := by
              have : D ^ (m + 1) = D * (D ^ i * D ^ (m - i)) := by
                rw [← pow_add, ← pow_succ']; congr 1; omega
              rw [this]; ring
    _ = D ^ (m + 1) * catalan (m + 1) := by
        rw [← Finset.mul_sum, catalan_succ, Fin.sum_univ_eq_sum_range
          (fun i => catalan i * catalan (m - i))]

lemma count [G.LocallyFinite] (D : ℕ) (hdeg : ∀ v, G.degree v ≤ D) (m : ℕ) :
    ∀ r, (A G r (m + 1)).Finite ∧ (A G r (m + 1)).ncard ≤ D ^ m * catalan m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro r
    rcases m with _ | m
    · have h := A_one G r
      refine ⟨(Set.finite_singleton _).subset h, ?_⟩
      have := Set.ncard_le_ncard h (Set.finite_singleton _)
      simpa using this
    · exact count_step G D hdeg m (fun i hi r' => ih i (by omega) r') r


section Final
variable {G}

lemma verts_finite (H : G.Subgraph) (hc : H.Connected) (r : V) (hr : r ∈ H.verts)
    (hE : H.edgeSet.Finite) : H.verts.Finite := by
  have hsub : H.verts ⊆ {r} ∪ ⋃ e ∈ H.edgeSet, {x | x ∈ e} := by
    intro v hv
    by_cases hvr : v = r
    · left; simp [hvr]
    · right
      obtain ⟨p⟩ := hc.preconnected ⟨v, hv⟩ ⟨r, hr⟩
      cases p with
      | nil => exact absurd rfl hvr
      | @cons _ w _ h _ =>
        simp only [Set.mem_iUnion]
        exact ⟨s(v, w.1), by simpa using h, by simp⟩
  refine (Set.Finite.subset ?_ hsub)
  refine (Set.finite_singleton r).union (hE.biUnion fun e _ => ?_)
  induction e using Sym2.ind with
  | _ a b =>
    have : {x | x ∈ s(a, b)} = {a, b} := by ext x; simp
    rw [this]; exact Set.toFinite _

lemma verts_conn (H : G.Subgraph) (hc : H.Connected) (W : Finset V)
    (hW : ∀ x, x ∈ W ↔ x ∈ H.verts) : Conn G W := by
  have key : ∀ (a b : H.verts) (p : H.coe.Walk a b), ReflTransGen (RS G W) a.1 b.1 := by
    intro a b p
    induction p with
    | nil => exact ReflTransGen.refl
    | @cons x y z h _ ih =>
      exact ReflTransGen.head ⟨H.adj_sub h, (hW _).2 x.2, (hW _).2 y.2⟩ ih
  intro x hx y hy
  obtain ⟨p⟩ := hc.preconnected ⟨x, (hW x).1 hx⟩ ⟨y, (hW y).1 hy⟩
  exact key _ _ p

lemma verts_card (H : G.Subgraph) (hc : H.Connected) (hfin : H.verts.Finite)
    (hE : H.edgeSet.Finite) : hfin.toFinset.card ≤ H.edgeSet.ncard + 1 := by
  have h1 := SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one hc.coe
  have : Finite H.verts := hfin.to_subtype
  have h2 : Nat.card H.coe.edgeSet ≤ Nat.card H.edgeSet := by
    have : Finite H.edgeSet := hE.to_subtype
    refine Nat.card_le_card_of_injective
      (fun e => ⟨Sym2.map Subtype.val e.1, ?_⟩) ?_
    · obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with
      | _ a b => simpa using he
    · intro e e' h
      apply Subtype.ext
      apply Sym2.map.injective Subtype.val_injective
      simpa using h
  have h3 : Nat.card H.verts = hfin.toFinset.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  rw [← h3]
  have : Nat.card H.edgeSet = H.edgeSet.ncard := rfl
  omega


def mk (G : SimpleGraph V) (p : Finset V × Finset (Sym2 V)) : G.Subgraph where
  verts := p.1
  Adj a b := s(a, b) ∈ p.2 ∧ G.Adj a b ∧ a ∈ p.1 ∧ b ∈ p.1
  adj_sub h := h.2.1
  edge_vert h := h.2.2.1
  symm := ⟨fun a b h => ⟨by simpa [Sym2.eq_swap] using h.1, h.2.1.symm, h.2.2.2, h.2.2.1⟩⟩

def T [G.LocallyFinite] (W : Finset V) : Finset (Sym2 V) :=
  W.biUnion (fun v => (G.neighborFinset v).image (fun w => s(v, w)))

lemma T_card [G.LocallyFinite] (D : ℕ) (hdeg : ∀ v, G.degree v ≤ D) (W : Finset V) :
    (T (G := G) W).card ≤ W.card * D := by
  unfold T
  calc _ ≤ ∑ v ∈ W, ((G.neighborFinset v).image (fun w => s(v, w))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ v ∈ W, D := Finset.sum_le_sum (fun v _ => by
        refine (Finset.card_image_le).trans ?_
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg v)
    _ = W.card * D := by simp

lemma catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow n)

theorem main (Δ : ℕ) :
    ∃ α : ℕ, ∀ {V : Type} (G : SimpleGraph V) [G.LocallyFinite],
    (∀ v, G.degree v ≤ Δ + 1) → ∀ (r : V) (k : ℕ),
      {H : G.Subgraph | H.Connected ∧ r ∈ H.verts ∧ H.edgeSet.Finite ∧ H.edgeSet.ncard < k}.Finite ∧
      {H : G.Subgraph | H.Connected ∧ r ∈ H.verts ∧ H.edgeSet.Finite ∧ H.edgeSet.ncard < k}.ncard
        ≤ α ^ k := by
  refine ⟨2 * (4 * (Δ + 1)) * 2 ^ (Δ + 1), ?_⟩
  intro V G _ hdeg r k
  classical
  set D := Δ + 1 with hD
  let Wset : Finset (Finset V) :=
    (Finset.range k).biUnion (fun m => (count G D hdeg m r).1.toFinset)
  have hWmem : ∀ W ∈ Wset, r ∈ W ∧ W.card ≤ k ∧ Conn G W := by
    intro W hW
    simp only [Wset, Finset.mem_biUnion, Finset.mem_range, Set.Finite.mem_toFinset] at hW
    obtain ⟨m, hm, hr, hc, hconn⟩ := hW
    exact ⟨hr, by omega, hconn⟩
  have hWcard : Wset.card ≤ k * (4 * D) ^ k := by
    calc Wset.card ≤ ∑ m ∈ Finset.range k, ((count G D hdeg m r).1.toFinset).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ m ∈ Finset.range k, (4 * D) ^ k := by
          apply Finset.sum_le_sum
          intro m hm
          have hm' := Finset.mem_range.1 hm
          rw [← Set.ncard_eq_toFinset_card _ (count G D hdeg m r).1]
          refine (count G D hdeg m r).2.trans ?_
          calc D ^ m * catalan m ≤ D ^ m * 4 ^ m := Nat.mul_le_mul_left _ (catalan_le_four_pow m)
            _ = (4 * D) ^ m := by rw [← mul_pow, mul_comm]
            _ ≤ (4 * D) ^ k := Nat.pow_le_pow_right (by omega) hm'.le
      _ = k * (4 * D) ^ k := by simp
  let P : Finset (Σ _ : Finset V, Finset (Sym2 V)) :=
    Wset.sigma (fun W => (T (G := G) W).powerset)
  have hPcard : P.card ≤ Wset.card * 2 ^ (k * D) := by
    rw [Finset.card_sigma]
    calc ∑ W ∈ Wset, ((T (G := G) W).powerset).card ≤ ∑ W ∈ Wset, 2 ^ (k * D) := by
          apply Finset.sum_le_sum
          intro W hW
          rw [Finset.card_powerset]
          exact Nat.pow_le_pow_right (by omega)
            ((T_card D hdeg W).trans (Nat.mul_le_mul_right _ (hWmem W hW).2.1))
      _ = Wset.card * 2 ^ (k * D) := by simp
  have hsub : {H : G.Subgraph | H.Connected ∧ r ∈ H.verts ∧ H.edgeSet.Finite ∧
      H.edgeSet.ncard < k} ⊆ (fun p : (Σ _ : Finset V, Finset (Sym2 V)) => mk G (p.1, p.2)) '' ↑P := by
    rintro H ⟨hc, hr, hE, hlt⟩
    have hvf := verts_finite H hc r hr hE
    have hvc := verts_card H hc hvf hE
    have hconn := verts_conn H hc hvf.toFinset (fun x => by simp)
    -- W ∈ Wset
    have hWA : hvf.toFinset ∈ A G r (hvf.toFinset.card) := ⟨by simpa using hr, rfl, hconn⟩
    have hpos : 1 ≤ hvf.toFinset.card := Finset.card_pos.2 ⟨r, by simpa using hr⟩
    have hWin : hvf.toFinset ∈ Wset := by
      simp only [Wset, Finset.mem_biUnion, Finset.mem_range, Set.Finite.mem_toFinset]
      refine ⟨hvf.toFinset.card - 1, by omega, ?_⟩
      have : hvf.toFinset.card - 1 + 1 = hvf.toFinset.card := by omega
      rw [this]; exact hWA
    refine ⟨⟨hvf.toFinset, hE.toFinset⟩, ?_, ?_⟩
    · simp only [P, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_powerset]
      refine ⟨hWin, ?_⟩
      intro e he
      rw [Set.Finite.mem_toFinset] at he
      induction e using Sym2.ind with
      | _ a b =>
        have hab : H.Adj a b := he
        unfold T
        simp only [Finset.mem_biUnion, Finset.mem_image, SimpleGraph.mem_neighborFinset]
        exact ⟨a, by simpa using H.edge_vert hab, b, H.adj_sub hab, rfl⟩
    · apply SimpleGraph.Subgraph.ext
      · ext x; simp only [mk, Set.Finite.mem_toFinset, Finset.mem_coe]
      · funext a b
        apply propext
        simp only [mk, Set.Finite.mem_toFinset]
        constructor
        · intro h; exact h.1
        · intro h
          exact ⟨h, H.adj_sub h, by simpa using H.edge_vert h, by simpa using H.edge_vert h.symm⟩
  have hfin : (↑(P.image (fun p : (Σ _ : Finset V, Finset (Sym2 V)) => mk G (p.1, p.2))) : Set G.Subgraph).Finite :=
    Finset.finite_toSet _
  have himg : ((fun p : (Σ _ : Finset V, Finset (Sym2 V)) => mk G (p.1, p.2)) '' ↑P) =
      ↑(P.image (fun p : (Σ _ : Finset V, Finset (Sym2 V)) => mk G (p.1, p.2))) := by
    rw [Finset.coe_image]
  rw [himg] at hsub
  refine ⟨hfin.subset hsub, ?_⟩
  calc _ ≤ (↑(P.image (fun p : (Σ _ : Finset V, Finset (Sym2 V)) => mk G (p.1, p.2))) :
        Set G.Subgraph).ncard := Set.ncard_le_ncard hsub hfin
    _ = (P.image (fun p : (Σ _ : Finset V, Finset (Sym2 V)) => mk G (p.1, p.2))).card :=
        Set.ncard_coe_finset _
    _ ≤ P.card := Finset.card_image_le
    _ ≤ k * (4 * D) ^ k * 2 ^ (k * D) := hPcard.trans (Nat.mul_le_mul_right _ hWcard)
    _ ≤ 2 ^ k * (4 * D) ^ k * 2 ^ (k * D) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.lt_two_pow_self).le)
    _ = (2 * (4 * D) * 2 ^ D) ^ k := by
        have : (2:ℕ) ^ (k * D) = (2 ^ D) ^ k := by rw [← pow_mul, mul_comm]
        rw [this, mul_pow (2 * (4 * D)) (2 ^ D) k, mul_pow 2 (4 * D) k, mul_pow 4 D k]

end Final

end LocalSweepFT

theorem solution (Δ : ℕ) : ∃ α : ℕ, ∀ {V : Type} (G : SimpleGraph V) [G.LocallyFinite],
    (∀ v, G.degree v ≤ Δ + 1) → ∀ (r : V) (k : ℕ),
      {H : G.Subgraph | H.Connected ∧ r ∈ H.verts ∧ H.edgeSet.Finite ∧ H.edgeSet.ncard < k}.Finite ∧
      {H : G.Subgraph | H.Connected ∧ r ∈ H.verts ∧ H.edgeSet.Finite ∧ H.edgeSet.ncard < k}.ncard
        ≤ α ^ k := LocalSweepFT.main Δ
