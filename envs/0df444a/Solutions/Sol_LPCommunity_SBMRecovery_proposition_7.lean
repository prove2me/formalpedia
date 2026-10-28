-- Prove2me | solution 1 for LPCommunity.SBMRecovery.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T04:02:03.147991+00:00
-- url     : https://prove2.me/submissions/e7b08958-ca60-463b-919a-3ef70033669d

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Factors

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Filter Topology
open scoped Classical

namespace FF51

variable {V : Type*} [Fintype V]

/-- vertex type of the Tutte gadget: darts of `G` and `k v` cores at each vertex `v`. -/
abbrev GW (G : SimpleGraph V) (k : V → ℕ) := G.Dart ⊕ (Σ v : V, Fin (k v))

def gAdj (G : SimpleGraph V) (k : V → ℕ) : GW G k → GW G k → Prop
  | .inl d, .inl d' => d' = d.symm
  | .inl d, .inr c => c.1 = d.fst
  | .inr c, .inl d => c.1 = d.fst
  | .inr _, .inr _ => False

def gad (G : SimpleGraph V) (k : V → ℕ) : SimpleGraph (GW G k) where
  Adj := gAdj G k
  symm := ⟨by
    rintro (d|c) (d'|c') h <;> simp only [gAdj] at h ⊢
    · subst h; exact (SimpleGraph.Dart.symm_symm d).symm
    · exact h
    · exact h⟩
  loopless := ⟨by
    rintro (d|c) h <;> simp only [gAdj] at h
    exact d.symm_ne h.symm⟩

section adj
variable {G : SimpleGraph V} {k : V → ℕ}
@[simp] lemma gad_ll (d d' : G.Dart) : (gad G k).Adj (.inl d) (.inl d') ↔ d' = d.symm := Iff.rfl
@[simp] lemma gad_lr (d : G.Dart) (c : Σ v : V, Fin (k v)) :
    (gad G k).Adj (.inl d) (.inr c) ↔ c.1 = d.fst := Iff.rfl
@[simp] lemma gad_rl (d : G.Dart) (c : Σ v : V, Fin (k v)) :
    (gad G k).Adj (.inr c) (.inl d) ↔ c.1 = d.fst := Iff.rfl
@[simp] lemma gad_rr (c c' : Σ v : V, Fin (k v)) : ¬ (gad G k).Adj (.inr c) (.inr c') := id
end adj

/-- card of the cores at `v`. -/
lemma card_cores (k : V → ℕ) (v : V) :
    (univ.filter (fun c : Σ w : V, Fin (k w) => c.1 = v)).card = k v := by
  have : (univ.filter (fun c : Σ w : V, Fin (k w) => c.1 = v)) =
      (univ : Finset (Fin (k v))).image (Sigma.mk v) := by
    ext ⟨w, i⟩
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro rfl; exact ⟨i, rfl⟩
    · rintro ⟨j, hj⟩; cases hj; rfl
  rw [this, card_image_of_injective _ sigma_mk_injective, card_univ, Fintype.card_fin]

lemma card_darts (G : SimpleGraph V) (v : V) :
    (univ.filter (fun d : G.Dart => d.fst = v)).card = G.degree v := by
  convert G.dart_fst_fiber_card_eq_degree v

/-- STEP 2: a perfect matching of the gadget gives an `f`-factor. -/
theorem factor_of_pm (G : SimpleGraph V) (f k : V → ℕ) (hk : ∀ v, f v + k v = G.degree v)
    (M : (gad G k).Subgraph) (hM : M.IsPerfectMatching) :
    LPCommunity.SBMRecovery.HasFactor G f := by
  have hU := SimpleGraph.Subgraph.isPerfectMatching_iff.1 hM
  -- partner function
  let p : GW G k → GW G k := fun x => (hU x).exists.choose
  have hp : ∀ x, M.Adj x (p x) := fun x => (hU x).exists.choose_spec
  have hpu : ∀ x y, M.Adj x y → y = p x := fun x y h => (hU x).unique h (hp x)
  have hpp : ∀ x, p (p x) = x := fun x => ((hpu _ _ (hp x).symm)).symm
  let F : SimpleGraph V :=
    { Adj := fun u v => ∃ h : G.Adj u v, M.Adj (Sum.inl ⟨(u, v), h⟩) (Sum.inl ⟨(v, u), h.symm⟩)
      symm := ⟨fun u v ⟨h, hm⟩ => ⟨h.symm, hm.symm⟩⟩
      loopless := ⟨fun u ⟨h, _⟩ => G.loopless.irrefl u h⟩ }
  refine ⟨F, fun u v ⟨h, _⟩ => h, fun v => ?_⟩
  set Dv := univ.filter (fun d : G.Dart => d.fst = v)
  set A1 := Dv.filter (fun d => M.Adj (.inl d) (.inl d.symm))
  set A2 := Dv.filter (fun d => ¬ M.Adj (.inl d) (.inl d.symm))
  have hsplit : A1.card + A2.card = G.degree v := by
    rw [← card_darts G v]; exact card_filter_add_card_filter_not _
  -- A1 ↔ F-neighbours
  have h1 : A1.card = F.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun d _ => d.snd) ?_ ?_ ?_
    · rintro ⟨⟨a, b⟩, hab⟩ hd
      simp only [A1, Dv, mem_filter, mem_univ, true_and] at hd
      obtain ⟨rfl, hm⟩ := hd
      simp only [SimpleGraph.mem_neighborFinset]
      exact ⟨hab, hm⟩
    · rintro ⟨⟨a, b⟩, hab⟩ hd ⟨⟨a', b'⟩, hab'⟩ hd' he
      simp only [A1, Dv, mem_filter, mem_univ, true_and] at hd hd'
      obtain ⟨rfl, -⟩ := hd; obtain ⟨rfl, -⟩ := hd'
      simp only at he; subst he; rfl
    · intro u hu
      simp only [SimpleGraph.mem_neighborFinset] at hu
      obtain ⟨h, hm⟩ := hu
      refine ⟨⟨(v, u), h⟩, ?_, rfl⟩
      simp only [A1, Dv, mem_filter, mem_univ, true_and]
      first | exact ⟨rfl, hm⟩ | exact hm
  -- A2 ↔ cores at v, through the partner involution
  have h2 : A2.card = k v := by
    let Cv := univ.filter (fun c : Σ w : V, Fin (k w) => c.1 = v)
    have e1 : A2.card = (A2.map (Function.Embedding.inl : G.Dart ↪ GW G k)).card :=
      (card_map _).symm
    have e2 : Cv.card = (Cv.map (Function.Embedding.inr : (Σ w : V, Fin (k w)) ↪ GW G k)).card :=
      (card_map _).symm
    rw [e1, ← card_cores k v]
    change _ = Cv.card
    rw [e2]
    refine Finset.card_nbij p ?_ ?_ ?_
    · intro x hx
      rw [mem_coe, Finset.mem_map] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      simp only [A2, Dv, mem_filter, mem_univ, true_and] at hd
      obtain ⟨hdv, hnm⟩ := hd
      have ha := M.adj_sub (hp (Sum.inl d))
      rw [mem_coe, Finset.mem_map]
      rcases hpd : p (Sum.inl d) with d' | c
      · rw [hpd] at ha; simp only [gad_ll] at ha
        exact absurd (by rw [← ha, ← hpd]; exact hp _) hnm
      · rw [hpd] at ha; simp only [gad_lr] at ha
        exact ⟨c, by simp only [Cv, mem_filter, mem_univ, true_and]; exact ha.trans hdv, hpd.symm⟩
    · intro x _ y _ hxy
      rw [← hpp x, ← hpp y, hxy]
    · intro y hy
      rw [mem_coe, Finset.mem_map] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      simp only [Cv, mem_filter, mem_univ, true_and] at hc
      have ha := M.adj_sub (hp (Sum.inr c))
      rcases hpc : p (Sum.inr c) with d | c'
      · rw [hpc] at ha; simp only [gad_rl] at ha
        have h2 : p (Sum.inl d) = Sum.inr c := by rw [← hpc, hpp]
        refine ⟨Sum.inl d, ?_, h2⟩
        rw [mem_coe, Finset.mem_map]
        refine ⟨d, ?_, rfl⟩
        simp only [A2, Dv, mem_filter, mem_univ, true_and]
        refine ⟨ha.symm.trans hc, fun hm => ?_⟩
        have h1 := hpu _ _ hm
        rw [h2] at h1; exact Sum.inl_ne_inr h1
      · rw [hpc] at ha; exact absurd ha (gad_rr _ _)
  have := hk v
  rw [show f v = A1.card by omega]
  convert h1.symm

lemma pm_of_invol {W : Type*} (H : SimpleGraph W) (q : W → W) (hq : ∀ x, q (q x) = x)
    (hadj : ∀ x, H.Adj x (q x)) : ∃ M : H.Subgraph, M.IsPerfectMatching := by
  let M : H.Subgraph :=
    { verts := Set.univ
      Adj := fun x y => y = q x
      adj_sub := by rintro x y rfl; exact hadj x
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨by rintro x y rfl; exact (hq x).symm⟩ }
  exact ⟨M, SimpleGraph.Subgraph.isPerfectMatching_iff.2 fun x => ⟨q x, rfl, fun y hy => hy⟩⟩

lemma card_darts_in (G F : SimpleGraph V) (hFG : F ≤ G) (v : V) :
    (univ.filter (fun d : G.Dart => d.fst = v ∧ F.Adj d.fst d.snd)).card = F.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun d _ => d.snd) ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, hab⟩ hd
    simp only [mem_filter, mem_univ, true_and] at hd
    obtain ⟨rfl, hm⟩ := hd
    simpa using hm
  · rintro ⟨⟨a, b⟩, hab⟩ hd ⟨⟨a', b'⟩, hab'⟩ hd' he
    simp only [mem_filter, mem_univ, true_and] at hd hd'
    obtain ⟨rfl, -⟩ := hd; obtain ⟨rfl, -⟩ := hd'
    simp only at he; subst he; rfl
  · intro u hu
    simp only [SimpleGraph.mem_neighborFinset] at hu
    refine ⟨⟨(v, u), hFG hu⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    first | exact ⟨rfl, hu⟩ | exact hu

/-- STEP 3: an `f`-factor gives a perfect matching of the gadget. -/
theorem pm_of_factor (G : SimpleGraph V) (f k : V → ℕ) (hk : ∀ v, f v + k v = G.degree v)
    (F : SimpleGraph V) (hFG : F ≤ G) (hF : ∀ v, F.degree v = f v) :
    ∃ M : (gad G k).Subgraph, M.IsPerfectMatching := by
  let B := {d : G.Dart // ¬ F.Adj d.fst d.snd}
  have hcard : ∀ v, Fintype.card (Fin (k v)) = Fintype.card {b : B // b.1.fst = v} := by
    intro v
    rw [Fintype.card_fin]
    have e : {b : B // b.1.fst = v} ≃ {d : G.Dart // d.fst = v ∧ ¬ F.Adj d.fst d.snd} :=
      { toFun := fun b => ⟨b.1.1, b.2, b.1.2⟩
        invFun := fun d => ⟨⟨d.1, d.2.2⟩, d.2.1⟩
        left_inv := fun b => rfl
        right_inv := fun d => rfl }
    rw [Fintype.card_congr e, Fintype.card_subtype]
    have h1 : (univ.filter (fun d : G.Dart => d.fst = v ∧ F.Adj d.fst d.snd)).card = f v := by
      rw [← hF v]; convert card_darts_in G F hFG v
    have h2 := card_darts G v
    have hs := card_filter_add_card_filter_not (s := univ.filter (fun d : G.Dart => d.fst = v))
      (fun d => F.Adj d.fst d.snd)
    rw [filter_filter, filter_filter] at hs
    have := hk v
    omega
  let Φ0 : ∀ v, Fin (k v) ≃ {b : B // b.1.fst = v} := fun v => Fintype.equivOfCardEq (hcard v)
  let Φ : (Σ v, Fin (k v)) ≃ B :=
    (Equiv.sigmaCongrRight Φ0).trans (Equiv.sigmaFiberEquiv (fun b : B => b.1.fst))
  have hΦ : ∀ c, (Φ c).1.fst = c.1 := fun c => (Φ0 c.1 c.2).2
  let q : GW G k → GW G k := fun x => match x with
    | .inr c => .inl (Φ c).1
    | .inl d => if h : F.Adj d.fst d.snd then .inl d.symm else .inr (Φ.symm ⟨d, h⟩)
  refine pm_of_invol (gad G k) q ?_ ?_
  · rintro (d | c)
    · by_cases h : F.Adj d.fst d.snd
      · have h' : F.Adj d.symm.fst d.symm.snd := h.symm
        simp only [q, dif_pos h, dif_pos h', SimpleGraph.Dart.symm_symm]
      · simp only [q, dif_neg h, Equiv.apply_symm_apply]
    · have h : ¬ F.Adj (Φ c).1.fst (Φ c).1.snd := (Φ c).2
      simp only [q, dif_neg h, Subtype.coe_eta, Equiv.symm_apply_apply]
  · rintro (d | c)
    · by_cases h : F.Adj d.fst d.snd
      · simp only [q, dif_pos h, gad_ll]
      · simp only [q, dif_neg h, gad_lr]
        have := hΦ (Φ.symm ⟨d, h⟩)
        rw [Equiv.apply_symm_apply] at this
        exact this.symm
    · simp only [q, gad_rl]
      exact (hΦ c).symm

/-! ### Shared infrastructure for the region counts -/

open LPCommunity.SBMRecovery Classical in
lemma card_filter_sum {α β : Type*} [Fintype α] [Fintype β] (p : α ⊕ β → Prop) :
    (univ.filter p).card = (univ.filter (fun a => p (.inl a))).card +
      (univ.filter (fun b => p (.inr b))).card := by
  simp only [card_filter]
  exact Fintype.sum_sum_type _

lemma card_darts_mem (G : SimpleGraph V) (U : Finset V) :
    (univ.filter (fun d : G.Dart => d.fst ∈ U)).card = ∑ w ∈ U, G.degree w := by
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.fst) (t := U)
    (by intro d hd; simpa using hd)]
  refine sum_congr rfl fun w hw => ?_
  rw [← card_darts G w, filter_filter]
  congr 1; ext d; simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · rintro rfl; exact ⟨hw, rfl⟩

lemma card_cores_mem (k : V → ℕ) (U : Finset V) :
    (univ.filter (fun c : Σ w : V, Fin (k w) => c.1 ∈ U)).card = ∑ w ∈ U, k w := by
  rw [card_eq_sum_card_fiberwise (f := fun c : Σ w : V, Fin (k w) => c.1) (t := U)
    (by intro d hd; simpa using hd)]
  refine sum_congr rfl fun w hw => ?_
  rw [← card_cores k w, filter_filter]
  congr 1; ext d; simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · rintro rfl; exact ⟨hw, rfl⟩

open LPCommunity.SBMRecovery Classical in
lemma edgeCount_eq (G : SimpleGraph V) (U U' : Finset V) (hUU : Disjoint U U') :
    edgeCount G U U' = (univ.filter (fun d : G.Dart => d.fst ∈ U' ∧ d.snd ∈ U)).card := by
  unfold edgeCount
  symm
  refine card_bij (fun d _ => d.edge) ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd
    simp only [mem_filter, SimpleGraph.mem_edgeFinset]
    refine ⟨d.edge_mem, d.snd, hd.2, d.fst, hd.1, ?_⟩
    simp only [SimpleGraph.Dart.edge]; exact Sym2.eq_swap
  · intro d hd d' hd' he
    simp only [mem_filter, mem_univ, true_and] at hd hd'
    rcases (G.dart_edge_eq_iff d d').1 he with h | h
    · exact h
    · exfalso
      have h1 : d.fst = d'.snd := by rw [h]; rfl
      exact Finset.disjoint_left.1 hUU (h1 ▸ hd'.2) hd.1
  · intro e he
    simp only [mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨he, u, hu, u', hu', rfl⟩ := he
    have hadj : G.Adj u' u := (G.mem_edgeSet.1 he).symm
    refine ⟨⟨(u', u), hadj⟩, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]; exact ⟨hu', hu⟩
    · simp only [SimpleGraph.Dart.edge]; exact Sym2.eq_swap

open LPCommunity.SBMRecovery

section regions
variable (G : SimpleGraph V) (k : V → ℕ) (S T : Finset V)

/-- membership in the special barrier `X(S,T)`. -/
def inX : GW G k → Prop
  | .inl d => d.fst ∈ S
  | .inr c => c.1 ∈ T

/-- the region `Q_C` of a component `C` of `G - (S ∪ T)`. -/
def inQ (C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent) : GW G k → Prop
  | .inr c => c.1 ∈ compVerts G (S ∪ T) C
  | .inl d => d.fst ∈ compVerts G (S ∪ T) C ∨ (d.fst ∈ T ∧ d.snd ∈ compVerts G (S ∪ T) C)

lemma card_X : (univ.filter (inX G k S T)).card = ∑ w ∈ S, G.degree w + ∑ w ∈ T, k w := by
  rw [card_filter_sum]
  have e1 : (univ.filter (fun a => inX G k S T (.inl a))) =
      univ.filter (fun d : G.Dart => d.fst ∈ S) := by
    ext a; simp only [mem_filter, mem_univ, true_and]; rfl
  have e2 : (univ.filter (fun b => inX G k S T (.inr b))) =
      univ.filter (fun c : Σ w : V, Fin (k w) => c.1 ∈ T) := by
    ext a; simp only [mem_filter, mem_univ, true_and]; rfl
  rw [e1, e2, card_darts_mem, card_cores_mem]

lemma not_mem_of_compVerts {U : Finset V} {C : (G.induce ((↑U : Set V)ᶜ)).ConnectedComponent}
    {v : V} (hv : v ∈ compVerts G U C) : v ∉ U := by
  simp only [compVerts, mem_filter, mem_univ, true_and] at hv
  obtain ⟨h, -⟩ := hv
  simpa using h

lemma compVerts_adj {U : Finset V} {C : (G.induce ((↑U : Set V)ᶜ)).ConnectedComponent}
    {w u : V} (hw : w ∈ compVerts G U C) (hu : u ∉ U) (hadj : G.Adj w u) :
    u ∈ compVerts G U C := by
  simp only [compVerts, mem_filter, mem_univ, true_and] at hw ⊢
  obtain ⟨hw', rfl⟩ := hw
  refine ⟨by simpa using hu, ?_⟩
  symm
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  simpa using hadj

lemma Q_closed (C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent) (x y : GW G k)
    (hx : inQ G k S T C x) (hy : ¬ inX G k S T y) (hxy : (gad G k).Adj x y) :
    inQ G k S T C y := by
  rcases x with d | c <;> rcases y with d' | c'
  · simp only [gad_ll] at hxy; subst hxy
    simp only [inX] at hy
    simp only [inQ] at hx ⊢
    rcases hx with hx | ⟨hT, hx⟩
    · by_cases hT : d.snd ∈ T
      · exact Or.inr ⟨hT, hx⟩
      · left
        refine compVerts_adj G hx ?_ d.adj
        simp only [mem_union, not_or]; exact ⟨hy, hT⟩
    · exact Or.inl hx
  · simp only [gad_lr] at hxy
    simp only [inX] at hy
    simp only [inQ] at hx ⊢
    rcases hx with hx | ⟨hT, hx⟩
    · rw [hxy]; exact hx
    · exact absurd (hxy ▸ hT) hy
  · simp only [gad_rl] at hxy
    simp only [inQ] at hx ⊢
    left; rw [← hxy]; exact hx
  · exact absurd hxy (gad_rr _ _)

/-- parity bookkeeping: `|Q_C| = 2 k(C) + f(C) + N(C,T)`. -/
lemma card_Q (f : V → ℕ) (hk : ∀ v, f v + k v = G.degree v) (hST : Disjoint S T)
    (C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent) :
    (univ.filter (inQ G k S T C)).card =
      2 * ∑ w ∈ compVerts G (S ∪ T) C, k w + ∑ w ∈ compVerts G (S ∪ T) C, f w +
        edgeCount G (compVerts G (S ∪ T) C) T := by
  have hdisj : Disjoint (compVerts G (S ∪ T) C) T := by
    rw [Finset.disjoint_left]; intro v hv hvT
    exact not_mem_of_compVerts G hv (mem_union_right _ hvT)
  rw [card_filter_sum]
  have e1 : (univ.filter (fun a => inQ G k S T C (.inl a))) =
      univ.filter (fun d : G.Dart => d.fst ∈ compVerts G (S ∪ T) C) ∪
        univ.filter (fun d : G.Dart => d.fst ∈ T ∧ d.snd ∈ compVerts G (S ∪ T) C) := by
    ext a; simp only [mem_filter, mem_union, mem_univ, true_and]; rfl
  have e2 : (univ.filter (fun b => inQ G k S T C (.inr b))) =
      univ.filter (fun c : Σ w : V, Fin (k w) => c.1 ∈ compVerts G (S ∪ T) C) := by
    ext a; simp only [mem_filter, mem_union, mem_univ, true_and]; rfl
  rw [e1, e2, card_cores_mem, card_union_of_disjoint, card_darts_mem, ← edgeCount_eq G _ _ hdisj]
  · have : ∑ w ∈ compVerts G (S ∪ T) C, G.degree w =
        ∑ w ∈ compVerts G (S ∪ T) C, k w + ∑ w ∈ compVerts G (S ∪ T) C, f w := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun w _ => by have := hk w; omega
    omega
  · rw [Finset.disjoint_left]
    intro d h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact Finset.disjoint_left.1 hdisj h1 h2.1

end regions

lemma even_card_invol {α : Type*} [DecidableEq α] (p : α → α) (hpp : ∀ x, p (p x) = x)
    (hne : ∀ x, p x ≠ x) : ∀ s : Finset α, (∀ x ∈ s, p x ∈ s) → Even s.card := by
  intro s
  induction' h : s.card using Nat.strong_induction_on with n ih generalizing s
  intro hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · rw [← h]; simp
  · have hpx : p x ∈ s.erase x := mem_erase.2 ⟨hne x, hs x hx⟩
    have hc : ((s.erase x).erase (p x)).card + 2 = n := by
      rw [card_erase_of_mem hpx, card_erase_of_mem hx]
      have : 2 ≤ s.card := by
        have := card_le_card (show {x, p x} ⊆ s by
          intro y hy; simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hx
          · exact hs x hx)
        rw [card_pair (hne x).symm] at this; exact this
      omega
    have hev := ih _ (by omega) ((s.erase x).erase (p x)) rfl (by
      intro y hy
      simp only [mem_erase] at hy ⊢
      obtain ⟨hy1, hy2, hy3⟩ := hy
      refine ⟨fun h => hy2 (by rw [← hpp y, h, hpp]), fun h => hy1 (by rw [← h, hpp]), hs y hy3⟩)
    rw [← hc]; exact hev.add (by decide)

lemma Q_eq_of_mem (G : SimpleGraph V) (k : V → ℕ) (S T : Finset V)
    (C C' : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent) (x : GW G k)
    (h : inQ G k S T C x) (h' : inQ G k S T C' x) : C = C' := by
  have key : ∀ v, v ∈ compVerts G (S ∪ T) C → v ∈ compVerts G (S ∪ T) C' → C = C' := by
    intro v hv hv'
    simp only [compVerts, mem_filter, mem_univ, true_and] at hv hv'
    obtain ⟨h1, rfl⟩ := hv; obtain ⟨h2, rfl⟩ := hv'
    rfl
  rcases x with d | c
  · simp only [inQ] at h h'
    rcases h with h | ⟨hT, h⟩ <;> rcases h' with h' | ⟨hT', h'⟩
    · exact key _ h h'
    · exact absurd (mem_union_right _ hT') (not_mem_of_compVerts G h)
    · exact absurd (mem_union_right _ hT) (not_mem_of_compVerts G h')
    · exact key _ h h'
  · exact key _ h h'

/-- STEP 6: necessity of Tutte's condition. -/
theorem necessity (G : SimpleGraph V) (f : V → ℕ) (hF : HasFactor G f) (S T : Finset V)
    (hST : Disjoint S T) :
    0 ≤ (∑ v ∈ S, (f v : ℤ)) - (∑ v ∈ T, (f v : ℤ)) + (∑ v ∈ T, (G.degree v : ℤ))
      - (edgeCount G S T : ℤ) - (oddComps G f S T : ℤ) := by
  obtain ⟨F, hFG, hFd⟩ := hF
  have hle : ∀ v, f v ≤ G.degree v := by
    intro v
    rw [← hFd v, ← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    exact card_le_card (fun u hu => by
      simp only [SimpleGraph.mem_neighborFinset] at hu ⊢; exact hFG hu)
  let k : V → ℕ := fun v => G.degree v - f v
  have hk : ∀ v, f v + k v = G.degree v := fun v => by have := hle v; simp only [k]; omega
  obtain ⟨M, hM⟩ := pm_of_factor G f k hk F hFG hFd
  have hU := SimpleGraph.Subgraph.isPerfectMatching_iff.1 hM
  let p : GW G k → GW G k := fun x => (hU x).exists.choose
  have hp : ∀ x, M.Adj x (p x) := fun x => (hU x).exists.choose_spec
  have hpu : ∀ x y, M.Adj x y → y = p x := fun x y h => (hU x).unique h (hp x)
  have hpp : ∀ x, p (p x) = x := fun x => ((hpu _ _ (hp x).symm)).symm
  have hadj : ∀ x, (gad G k).Adj x (p x) := fun x => M.adj_sub (hp x)
  have hne : ∀ x, p x ≠ x := fun x h => by
    have := hadj x; rw [h] at this; exact (gad G k).loopless.irrefl x this
  -- odd regions contain a vertex matched into X
  have hodd : ∀ C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent,
      Odd ((∑ v ∈ compVerts G (S ∪ T) C, f v) + edgeCount G (compVerts G (S ∪ T) C) T) →
      ∃ x, inQ G k S T C x ∧ inX G k S T (p x) := by
    intro C hC
    by_contra hcon
    push_neg at hcon
    have hev := even_card_invol p hpp hne (univ.filter (inQ G k S T C)) (by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact Q_closed G k S T C x (p x) hx (hcon x hx) (hadj x))
    rw [card_Q G k S T f hk hST C] at hev
    have : Odd (2 * ∑ w ∈ compVerts G (S ∪ T) C, k w + (∑ w ∈ compVerts G (S ∪ T) C, f w +
        edgeCount G (compVerts G (S ∪ T) C) T)) := (even_two_mul _).add_odd hC
    rw [← add_assoc] at this
    exact (Nat.not_even_iff_odd.2 this) hev
  let oddset := univ.filter (fun C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent =>
      Odd ((∑ v ∈ compVerts G (S ∪ T) C, f v) + edgeCount G (compVerts G (S ∪ T) C) T))
  have hmemC : ∀ C : oddset, Odd ((∑ v ∈ compVerts G (S ∪ T) C.1, f v) +
      edgeCount G (compVerts G (S ∪ T) C.1) T) := fun C => by
    have := C.2; simp only [oddset, mem_filter, mem_univ, true_and] at this; exact this
  let zz : oddset → GW G k := fun C => (hodd C.1 (hmemC C)).choose
  have hz : ∀ C : oddset, inQ G k S T C.1 (zz C) ∧ inX G k S T (p (zz C)) := fun C =>
    (hodd C.1 (hmemC C)).choose_spec
  have hzinj : Function.Injective zz := by
    intro C C' h
    exact Subtype.ext (Q_eq_of_mem G k S T C.1 C'.1 (zz C) (hz C).1 (h ▸ (hz C').1))
  let A1 := (univ.filter (fun c : Σ w : V, Fin (k w) => c.1 ∈ S)).map
    (Function.Embedding.inr : (Σ w : V, Fin (k w)) ↪ GW G k)
  let A2 := (univ.filter (fun d : G.Dart => d.fst ∈ T ∧ d.snd ∈ S)).map
    (Function.Embedding.inl : G.Dart ↪ GW G k)
  let A3 := (univ : Finset oddset).image zz
  have c1 : A1.card = ∑ w ∈ S, k w := by rw [card_map, card_cores_mem]
  have c2 : A2.card = edgeCount G S T := by rw [card_map, edgeCount_eq G S T hST]
  have c3 : A3.card = oddComps G f S T := by
    rw [card_image_of_injective _ hzinj, card_univ, Fintype.card_coe]
    unfold oddComps; convert rfl
  have d12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [A1, A2, Finset.mem_map, Function.Embedding.inl_apply,
      Function.Embedding.inr_apply] at h1 h2
    obtain ⟨c, -, rfl⟩ := h1; obtain ⟨d, -, h⟩ := h2
    exact Sum.inl_ne_inr h
  have d3 : Disjoint (A1 ∪ A2) A3 := by
    rw [Finset.disjoint_left]; intro x h12 h3
    simp only [A3, mem_image, mem_univ, true_and] at h3
    obtain ⟨C, rfl⟩ := h3
    have hq := (hz C).1
    rcases mem_union.1 h12 with h1 | h2
    · simp only [A1, Finset.mem_map, mem_filter, mem_univ, true_and,
        Function.Embedding.inr_apply] at h1
      obtain ⟨c, hcS, hc⟩ := h1
      rw [← hc] at hq
      simp only [inQ] at hq
      exact not_mem_of_compVerts G hq (mem_union_left _ hcS)
    · simp only [A2, Finset.mem_map, mem_filter, mem_univ, true_and,
        Function.Embedding.inl_apply] at h2
      obtain ⟨d, ⟨hdT, hdS⟩, hd⟩ := h2
      rw [← hd] at hq
      simp only [inQ] at hq
      rcases hq with hq | ⟨-, hq⟩
      · exact not_mem_of_compVerts G hq (mem_union_right _ hdT)
      · exact not_mem_of_compVerts G hq (mem_union_left _ hdS)
  have hmaps : ∀ x ∈ (A1 ∪ A2) ∪ A3, p x ∈ univ.filter (inX G k S T) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and]
    rcases mem_union.1 hx with h12 | h3
    · rcases mem_union.1 h12 with h1 | h2
      · simp only [A1, Finset.mem_map, mem_filter, mem_univ, true_and,
          Function.Embedding.inr_apply] at h1
        obtain ⟨c, hcS, rfl⟩ := h1
        have ha := hadj (Sum.inr c)
        rcases hpx : p (Sum.inr c) with d | c'
        · rw [hpx] at ha; simp only [gad_rl] at ha
          simp only [inX]; rw [← ha]; exact hcS
        · rw [hpx] at ha; exact absurd ha (gad_rr _ _)
      · simp only [A2, Finset.mem_map, mem_filter, mem_univ, true_and,
          Function.Embedding.inl_apply] at h2
        obtain ⟨d, ⟨hdT, hdS⟩, rfl⟩ := h2
        have ha := hadj (Sum.inl d)
        rcases hpx : p (Sum.inl d) with d' | c'
        · rw [hpx] at ha; simp only [gad_ll] at ha
          simp only [inX]; rw [ha]; exact hdS
        · rw [hpx] at ha; simp only [gad_lr] at ha
          simp only [inX]; rw [ha]; exact hdT
    · simp only [A3, mem_image, mem_univ, true_and] at h3
      obtain ⟨C, rfl⟩ := h3
      exact (hz C).2
  have hcard := card_le_card_of_injOn p (by intro x hx; exact hmaps x hx)
    (by intro x _ y _ h; rw [← hpp x, ← hpp y]; exact congrArg p h)
  rw [card_union_of_disjoint d3, card_union_of_disjoint d12, c1, c2, c3, card_X] at hcard
  have hdS : ∑ w ∈ S, G.degree w = ∑ w ∈ S, f w + ∑ w ∈ S, k w := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun w _ => (hk w).symm
  have hdT : ∑ w ∈ T, G.degree w = ∑ w ∈ T, f w + ∑ w ∈ T, k w := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun w _ => (hk w).symm
  rw [← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum]
  omega

/-! ### Generic lemmas on `H - u` as used by `IsTutteViolator` -/

section tutteGraph
variable {W : Type*} [Fintype W] (H : SimpleGraph W)

abbrev Vu (u : Set W) := ↥((⊤ : H.Subgraph).deleteVerts u).verts

abbrev Gm (u : Set W) : SimpleGraph (Vu H u) := ((⊤ : H.Subgraph).deleteVerts u).coe

lemma Gm_mem (u : Set W) (x : W) : x ∈ ((⊤ : H.Subgraph).deleteVerts u).verts ↔ x ∉ u := by
  simp [SimpleGraph.Subgraph.deleteVerts_verts]

lemma Gm_adj (u : Set W) (a b : Vu H u) : (Gm H u).Adj a b ↔ H.Adj a.1 b.1 := by
  have ha := (Gm_mem H u a.1).1 a.2
  have hb := (Gm_mem H u b.1).1 b.2
  simp only [Gm, SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteVerts_adj,
    SimpleGraph.Subgraph.top_adj, SimpleGraph.Subgraph.verts_top, Set.mem_univ, true_and]
  tauto

/-- vertex packaging -/
def gv (u : Set W) (x : W) (hx : x ∉ u) : Vu H u := ⟨x, (Gm_mem H u x).2 hx⟩

lemma reach_closed (u : Set W) (P : W → Prop)
    (hP : ∀ x y, P x → y ∉ u → H.Adj x y → P y)
    (a b : Vu H u) (hr : (Gm H u).Reachable a b) (ha : P a.1) : P b.1 := by
  obtain ⟨w⟩ := hr
  revert ha
  induction w with
  | nil => exact id
  | @cons x y z h p ih =>
    intro hx
    exact ih (hP _ _ hx ((Gm_mem H u _).1 y.2) ((Gm_adj H u _ _).1 h))

/-- STEP 9 core: deleting `y` from `u` loses at most two odd components when the neighbours of
`y` outside `u` lie in the components of `a` and `b`. -/
lemma oc_remove (u : Set W) (y a b : W) (ha : a ∉ u) (hb : b ∉ u)
    (hnb : ∀ z (hz : z ∉ u), H.Adj y z →
      (Gm H u).Reachable (gv H u a ha) (gv H u z hz) ∨
        (Gm H u).Reachable (gv H u b hb) (gv H u z hz)) :
    (Gm H u).oddComponents.ncard ≤ (Gm H (u \ {y})).oddComponents.ncard + 2 := by
  let ι : Gm H u →g Gm H (u \ {y}) :=
    { toFun := fun x => gv H (u \ {y}) x.1 (fun h => (Gm_mem H u x.1).1 x.2 h.1)
      map_rel' := fun h => (Gm_adj H _ _ _).2 ((Gm_adj H u _ _).1 h) }
  have hι : ∀ x, (ι x).1 = x.1 := fun x => rfl
  let Ka := (Gm H u).connectedComponentMk (gv H u a ha)
  let Kb := (Gm H u).connectedComponentMk (gv H u b hb)
  have key : ∀ z : Vu H u, (Gm H u).connectedComponentMk z ≠ Ka →
      (Gm H u).connectedComponentMk z ≠ Kb → ∀ w : Vu H (u \ {y}),
      (Gm H (u \ {y})).Reachable (ι z) w → ∃ hw : w.1 ∉ u, (Gm H u).Reachable z (gv H u w.1 hw) := by
    intro z hza hzb w hw
    refine reach_closed H (u \ {y}) (fun x => ∃ hx : x ∉ u, (Gm H u).Reachable z (gv H u x hx))
      ?_ (ι z) w hw ⟨(Gm_mem H u z.1).1 z.2, by rfl⟩
    rintro x y' ⟨hx, hzx⟩ hy' hxy'
    by_cases hyy : y' = y
    · subst hyy
      exfalso
      rcases hnb x hx hxy'.symm with h | h
      · exact hza (SimpleGraph.ConnectedComponent.sound (hzx.trans h.symm))
      · exact hzb (SimpleGraph.ConnectedComponent.sound (hzx.trans h.symm))
    · have hy'u : y' ∉ u := fun h => hy' ⟨h, hyy⟩
      exact ⟨hy'u, hzx.trans (SimpleGraph.Adj.reachable ((Gm_adj H u _ _).2 hxy'))⟩
  let O := (Gm H u).oddComponents
  let O' := (Gm H (u \ {y})).oddComponents
  have hsub : O ⊆ (O \ {Ka, Kb}) ∪ {Ka, Kb} := by
    intro K hK; by_cases h : K ∈ ({Ka, Kb} : Set _)
    · exact Or.inr h
    · exact Or.inl ⟨hK, h⟩
  have h2 : ({Ka, Kb} : Set (Gm H u).ConnectedComponent).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  have hmain : (O \ {Ka, Kb}).ncard ≤ O'.ncard := by
    refine Set.ncard_le_ncard_of_injOn (SimpleGraph.ConnectedComponent.map ι) ?_ ?_
      (Set.toFinite O')
    · rintro K ⟨hKo, hK⟩
      revert hKo hK
      refine K.ind (fun z => ?_)
      intro hKo hK
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hK
      have hsupp : (SimpleGraph.ConnectedComponent.map ι ((Gm H u).connectedComponentMk z)).supp =
          ι '' ((Gm H u).connectedComponentMk z).supp := by
        ext w
        simp only [SimpleGraph.ConnectedComponent.map_mk, SimpleGraph.ConnectedComponent.mem_supp_iff,
          Set.mem_image]
        constructor
        · intro hw
          obtain ⟨hw', hr⟩ := key z hK.1 hK.2 w
            (SimpleGraph.ConnectedComponent.exact hw.symm)
          exact ⟨gv H u w.1 hw', (SimpleGraph.ConnectedComponent.sound hr).symm, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact SimpleGraph.ConnectedComponent.sound
            ((SimpleGraph.ConnectedComponent.exact hx).map ι)
      show Odd _
      rw [hsupp, Set.ncard_image_of_injective _ (fun x x' h => Subtype.ext (by
        have := congrArg Subtype.val h; exact this))]
      exact hKo
    · rintro K ⟨-, hK⟩ K' ⟨-, hK'⟩ heq
      revert hK hK' heq
      refine K.ind (fun z => ?_)
      refine K'.ind (fun z' => ?_)
      intro hK hK' heq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hK hK'
      simp only [SimpleGraph.ConnectedComponent.map_mk] at heq
      obtain ⟨hw', hr⟩ := key z hK.1 hK.2 (ι z') (SimpleGraph.ConnectedComponent.exact heq)
      exact SimpleGraph.ConnectedComponent.sound hr
  calc O.ncard ≤ ((O \ {Ka, Kb}) ∪ {Ka, Kb}).ncard := Set.ncard_le_ncard hsub
    _ ≤ (O \ {Ka, Kb}).ncard + ({Ka, Kb} : Set _).ncard := Set.ncard_union_le _ _
    _ ≤ O'.ncard + 2 := by omega

lemma natcard_Vu (u : Set W) : Nat.card (Vu H u) = (Set.univ \ u).ncard := by
  rw [Nat.card_coe_set_eq, SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top]

lemma ncard_remove_aux (u : Set W) (y : W) (hy : y ∈ u) :
    (u \ {y}).ncard + 1 = u.ncard ∧
      (Set.univ \ (u \ {y})).ncard = (Set.univ \ u).ncard + 1 := by
  constructor
  · have : u = insert y (u \ {y}) := by
      ext z; by_cases hz : z = y
      · subst hz; simp [hy]
      · simp [hz]
    conv_rhs => rw [this]
    rw [Set.ncard_insert_of_notMem (by simp)]
  · have : Set.univ \ (u \ {y}) = insert y (Set.univ \ u) := by
      ext z; by_cases hz : z = y
      · subst hz; simp [hy]
      · simp [hz]
    rw [this, Set.ncard_insert_of_notMem (by simp [hy])]

/-- removability of `y` from a violator `u`. -/
def Removable (u : Set W) (y : W) : Prop :=
  (∀ z, z ∉ u → ¬ H.Adj y z) ∨
  ∃ a b : W, ∃ (ha : a ∉ u) (hb : b ∉ u), ∀ z (hz : z ∉ u), H.Adj y z →
      (Gm H u).Reachable (gv H u a ha) (gv H u z hz) ∨
        (Gm H u).Reachable (gv H u b hb) (gv H u z hz)

lemma violator_remove (u : Set W) (y : W) (hy : y ∈ u) (hr : Removable H u y)
    (hv : H.IsTutteViolator u) : H.IsTutteViolator (u \ {y}) := by
  unfold SimpleGraph.IsTutteViolator at hv ⊢
  change u.ncard < (Gm H u).oddComponents.ncard at hv
  change (u \ {y}).ncard < (Gm H (u \ {y})).oddComponents.ncard
  obtain ⟨h1, h2⟩ := ncard_remove_aux u y hy
  have hle : (Gm H u).oddComponents.ncard ≤ (Gm H (u \ {y})).oddComponents.ncard + 2 := by
    rcases hr with hiso | ⟨a, b, ha, hb, hnb⟩
    · by_cases hex : ∃ a, a ∉ u
      · obtain ⟨a, ha⟩ := hex
        exact oc_remove H u y a a ha ha (fun z hz h => absurd h (hiso z hz))
      · push_neg at hex
        have : IsEmpty (Vu H u) := ⟨fun x => (Gm_mem H u x.1).1 x.2 (hex x.1)⟩
        have h0 : (Gm H u).oddComponents.ncard = 0 := by
          rw [Set.ncard_eq_zero]; ext K; exact isEmptyElim K.out
        omega
    · exact oc_remove H u y a b ha hb hnb
  have p1 := (Gm H u).odd_ncard_oddComponents
  have p2 := (Gm H (u \ {y})).odd_ncard_oddComponents
  rw [natcard_Vu] at p1 p2
  rw [h2] at p2
  have hpar : (Gm H u).oddComponents.ncard ≠ (Gm H (u \ {y})).oddComponents.ncard + 2 := by
    intro h
    rw [h] at p1
    simp only [Nat.odd_iff] at p1 p2
    omega
  omega

/-- every violator can be shrunk to one where no vertex is removable. -/
lemma exists_tight_violator : ∀ (n : ℕ) (u : Set W), u.ncard = n → H.IsTutteViolator u →
    ∃ u' : Set W, H.IsTutteViolator u' ∧ ∀ y ∈ u', ¬ Removable H u' y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u hn hv
  by_cases h : ∀ y ∈ u, ¬ Removable H u y
  · exact ⟨u, hv, h⟩
  · push Not at h
    obtain ⟨y, hy, hr⟩ := h
    have := (ncard_remove_aux u y hy).1
    exact ih _ (by omega) (u \ {y}) rfl (violator_remove H u y hy hr hv)

end tutteGraph

lemma gm_reach_adj {W : Type*} [Fintype W] (H : SimpleGraph W) (u : Set W) (x z : W)
    (hx : x ∉ u) (hz : z ∉ u) (h : H.Adj x z) :
    (Gm H u).Reachable (gv H u x hx) (gv H u z hz) :=
  SimpleGraph.Adj.reachable ((Gm_adj H u _ _).2 h)

/-- STEP 10: a violator of the gadget with no removable vertex has the special form `X(S,T)`. -/
lemma tight_normal_form (G : SimpleGraph V) (k : V → ℕ) (u : Set (GW G k))
    (hu : ∀ y ∈ u, ¬ Removable (gad G k) u y) :
    ∃ S T : Finset V, Disjoint S T ∧ (∀ x, x ∈ u ↔ inX G k S T x) ∧
      ∀ v, v ∉ S → v ∉ T → 1 ≤ k v := by
  -- Fact A: darts
  have hA : ∀ d : G.Dart, Sum.inl d ∈ u →
      (∃ c : Σ w : V, Fin (k w), c.1 = d.fst ∧ Sum.inr c ∉ u) ∧
        ∀ d' : G.Dart, d'.fst = d.fst → Sum.inl d' ∈ u := by
    intro d hd
    have hc : ∃ c : Σ w : V, Fin (k w), c.1 = d.fst ∧ Sum.inr c ∉ u := by
      by_contra hcon
      push Not at hcon
      apply hu _ hd
      by_cases hs : Sum.inl d.symm ∈ u
      · left
        rintro (d' | c) hz h
        · simp only [gad_ll] at h; subst h; exact hz hs
        · simp only [gad_lr] at h; exact hz (hcon c h)
      · right
        refine ⟨_, _, hs, hs, ?_⟩
        rintro (d' | c) hz h
        · simp only [gad_ll] at h; subst h; exact Or.inl (SimpleGraph.Reachable.refl _)
        · simp only [gad_lr] at h; exact absurd (hcon c h) hz
    refine ⟨hc, ?_⟩
    obtain ⟨c0, hc0, hc0u⟩ := hc
    intro d' hd'
    by_contra hd'u
    apply hu _ hd
    right
    by_cases hs : Sum.inl d.symm ∈ u
    · refine ⟨_, _, hd'u, hd'u, ?_⟩
      rintro (e | c) hz h
      · simp only [gad_ll] at h; subst h; exact absurd hs hz
      · simp only [gad_lr] at h
        left
        exact gm_reach_adj _ u _ _ hd'u hz (by simp only [gad_lr]; rw [h, hd'])
    · refine ⟨_, _, hd'u, hs, ?_⟩
      rintro (e | c) hz h
      · simp only [gad_ll] at h; subst h; exact Or.inr (SimpleGraph.Reachable.refl _)
      · simp only [gad_lr] at h
        left
        exact gm_reach_adj _ u _ _ hd'u hz (by simp only [gad_lr]; rw [h, hd'])
  -- Fact B: cores
  have hB : ∀ c : Σ w : V, Fin (k w), Sum.inr c ∈ u →
      (∀ d : G.Dart, d.fst = c.1 → Sum.inl d ∉ u) ∧
        ∀ c' : Σ w : V, Fin (k w), c'.1 = c.1 → Sum.inr c' ∈ u := by
    intro c hc
    have h0 : ∃ d0 : G.Dart, d0.fst = c.1 ∧ Sum.inl d0 ∉ u := by
      by_contra hcon
      push Not at hcon
      apply hu _ hc
      left
      rintro (d' | c') hz h
      · simp only [gad_rl] at h; exact hz (hcon d' h.symm)
      · exact gad_rr _ _ h
    obtain ⟨d0, hd0, hd0u⟩ := h0
    have hnod : ∀ d : G.Dart, d.fst = c.1 → Sum.inl d ∉ u := by
      intro d hd hdu
      exact hd0u ((hA d hdu).2 d0 (hd0.trans hd.symm))
    refine ⟨hnod, ?_⟩
    intro c' hc'
    by_contra hc'u
    apply hu _ hc
    right
    refine ⟨_, _, hc'u, hc'u, ?_⟩
    rintro (d' | c'') hz h
    · simp only [gad_rl] at h
      left
      exact gm_reach_adj _ u _ _ hc'u hz (by simp only [gad_rl]; rw [hc', h])
    · exact absurd h (gad_rr _ _)
  let S := univ.filter (fun v => ∃ d : G.Dart, d.fst = v ∧ Sum.inl d ∈ u)
  let T := univ.filter (fun v => (∀ d : G.Dart, d.fst = v → Sum.inl d ∉ u) ∧
    ∀ c : Σ w : V, Fin (k w), c.1 = v → Sum.inr c ∈ u)
  refine ⟨S, T, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hS hT
    simp only [S, T, mem_filter, mem_univ, true_and] at hS hT
    obtain ⟨d, hd, hdu⟩ := hS
    exact hT.1 d hd hdu
  · rintro (d | c)
    · simp only [inX, S, mem_filter, mem_univ, true_and]
      constructor
      · intro hd; exact ⟨d, rfl, hd⟩
      · rintro ⟨d', hd', hd'u⟩; exact (hA d' hd'u).2 d (hd'.symm ▸ rfl)
    · simp only [inX, T, mem_filter, mem_univ, true_and]
      constructor
      · intro hc; exact hB c hc
      · rintro ⟨-, h⟩; exact h c rfl
  · intro v hS hT
    simp only [S, T, mem_filter, mem_univ, true_and, not_exists, not_and] at hS hT
    have h1 : ∀ d : G.Dart, d.fst = v → Sum.inl d ∉ u := fun d hd hdu => hS d hd hdu
    have := hT h1
    push Not at this
    obtain ⟨c, hcv, -⟩ := this
    have := c.2.pos
    rw [hcv] at this
    exact this

lemma reach_ind {α : Type*} (G' : SimpleGraph α) (P : α → Prop)
    (h : ∀ x y, G'.Adj x y → P x → P y) {a b : α} (hr : G'.Reachable a b) (ha : P a) : P b := by
  obtain ⟨w⟩ := hr
  revert ha
  induction w with
  | nil => exact id
  | cons hadj p ih => exact fun hx => ih (h _ _ hadj hx)

section upper
variable (G : SimpleGraph V) (k : V → ℕ) (S T : Finset V) (u : Set (GW G k))

lemma notX_of_Q (hST : Disjoint S T) (C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent)
    (x : GW G k) (h : inQ G k S T C x) : ¬ inX G k S T x := by
  rcases x with d | c <;> simp only [inQ, inX] at h ⊢
  · rcases h with h | ⟨hT, -⟩
    · exact fun hS => not_mem_of_compVerts G h (mem_union_left _ hS)
    · exact fun hS => Finset.disjoint_left.1 hST hS hT
  · exact fun hT => not_mem_of_compVerts G h (mem_union_right _ hT)

/-- the core `⟨v, 0⟩` as a vertex of `H - u`. -/
noncomputable def cvu (hu : ∀ x, x ∈ u ↔ inX G k S T x) (hk1 : ∀ v, v ∉ S → v ∉ T → 1 ≤ k v)
    (v : V) (hv : v ∉ S ∪ T) : Vu (gad G k) u :=
  gv _ u (.inr ⟨v, ⟨0, hk1 v (fun h => hv (mem_union_left _ h))
      (fun h => hv (mem_union_right _ h))⟩⟩)
    (fun h => hv (mem_union_right _ ((hu _).1 h)))

lemma cvu_adj (hu : ∀ x, x ∈ u ↔ inX G k S T x) (hk1 : ∀ v, v ∉ S → v ∉ T → 1 ≤ k v)
    (v v' : V) (hv : v ∉ S ∪ T) (hv' : v' ∉ S ∪ T) (h : G.Adj v v') :
    (Gm (gad G k) u).Reachable (cvu G k S T u hu hk1 v hv) (cvu G k S T u hu hk1 v' hv') := by
  have hvS : v ∉ S := fun h => hv (mem_union_left _ h)
  have hv'S : v' ∉ S := fun h => hv' (mem_union_left _ h)
  have h1 : (Sum.inl (⟨(v, v'), h⟩ : G.Dart) : GW G k) ∉ u := fun hh => hvS ((hu _).1 hh)
  have h2 : (Sum.inl (⟨(v', v), h.symm⟩ : G.Dart) : GW G k) ∉ u := fun hh => hv'S ((hu _).1 hh)
  exact ((gm_reach_adj _ u _ _ _ h1 ((gad_rl _ _).2 rfl)).trans
    (gm_reach_adj _ u _ _ h1 h2 ((gad_ll _ _).2 rfl))).trans
    (gm_reach_adj _ u _ _ h2 _ ((gad_lr _ _).2 rfl))

lemma cores_reach (hu : ∀ x, x ∈ u ↔ inX G k S T x) (hk1 : ∀ v, v ∉ S → v ∉ T → 1 ≤ k v)
    (C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent)
    (w w' : V) (hw : w ∈ compVerts G (S ∪ T) C) (hw' : w' ∈ compVerts G (S ∪ T) C) :
    (Gm (gad G k) u).Reachable (cvu G k S T u hu hk1 w (not_mem_of_compVerts G hw))
      (cvu G k S T u hu hk1 w' (not_mem_of_compVerts G hw')) := by
  have hw0 := hw
  have hw0' := hw'
  simp only [compVerts, mem_filter, mem_univ, true_and] at hw0 hw0'
  obtain ⟨h1, e1⟩ := hw0
  obtain ⟨h2, e2⟩ := hw0'
  have hr := SimpleGraph.ConnectedComponent.exact (e1.trans e2.symm)
  refine reach_ind _ (fun x => (Gm (gad G k) u).Reachable
      (cvu G k S T u hu hk1 w (not_mem_of_compVerts G hw))
      (cvu G k S T u hu hk1 x.1 (by simpa using x.2))) ?_ hr (SimpleGraph.Reachable.refl _)
  intro x y hxy hx
  exact hx.trans (cvu_adj G k S T u hu hk1 _ _ _ _ (by simpa using hxy))

lemma Q_reach_core (f : V → ℕ) (hk : ∀ v, f v + k v = G.degree v)
    (hu : ∀ x, x ∈ u ↔ inX G k S T x) (hk1 : ∀ v, v ∉ S → v ∉ T → 1 ≤ k v)
    (C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent) (x : Vu (gad G k) u)
    (hx : inQ G k S T C x.1) : ∃ w, ∃ hw : w ∈ compVerts G (S ∪ T) C,
      (Gm (gad G k) u).Reachable x (cvu G k S T u hu hk1 w (not_mem_of_compVerts G hw)) := by
  rcases x with ⟨d | c, hxu⟩
  · have hxu' := (Gm_mem _ u _).1 hxu
    simp only [inQ] at hx
    rcases hx with hx | ⟨hT, hx⟩
    · exact ⟨d.fst, hx, gm_reach_adj _ u _ _ hxu' _ ((gad_lr _ _).2 rfl)⟩
    · refine ⟨d.snd, hx, ?_⟩
      have hs : (Sum.inl d.symm : GW G k) ∉ u := fun h =>
        not_mem_of_compVerts G hx (mem_union_left _ ((hu _).1 h))
      exact (gm_reach_adj _ u _ _ hxu' hs ((gad_ll _ _).2 rfl)).trans
        (gm_reach_adj _ u _ _ hs _ ((gad_lr _ _).2 rfl))
  · have hxu' := (Gm_mem _ u _).1 hxu
    simp only [inQ] at hx
    refine ⟨c.1, hx, ?_⟩
    have hpos : 0 < G.degree c.1 := by
      have h1 := c.2.pos
      have := hk c.1
      omega
    rw [← card_darts G c.1] at hpos
    obtain ⟨d, hd⟩ := Finset.card_pos.1 hpos
    simp only [mem_filter, mem_univ, true_and] at hd
    have hdu : (Sum.inl d : GW G k) ∉ u := fun h =>
      not_mem_of_compVerts G hx (mem_union_left _ (hd ▸ (hu _).1 h))
    exact (gm_reach_adj _ u _ _ hxu' hdu ((gad_rl _ _).2 hd.symm)).trans
      (gm_reach_adj _ u _ _ hdu _ ((gad_lr _ _).2 hd.symm))

lemma Q_supp (f : V → ℕ) (hk : ∀ v, f v + k v = G.degree v)
    (hu : ∀ x, x ∈ u ↔ inX G k S T x) (hk1 : ∀ v, v ∉ S → v ∉ T → 1 ≤ k v)
    (C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent) (z : Vu (gad G k) u)
    (hz : inQ G k S T C z.1) :
    ((Gm (gad G k) u).connectedComponentMk z).supp = {y | inQ G k S T C y.1} := by
  ext y
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    exact reach_closed _ u (inQ G k S T C)
      (fun x y hx hy hxy => Q_closed G k S T C x y hx (fun h => hy ((hu y).2 h)) hxy) z y
      (SimpleGraph.ConnectedComponent.exact h.symm) hz
  · intro hy
    obtain ⟨w, hw, h1⟩ := Q_reach_core G k S T u f hk hu hk1 C z hz
    obtain ⟨w', hw', h2⟩ := Q_reach_core G k S T u f hk hu hk1 C y hy
    exact (SimpleGraph.ConnectedComponent.sound
      ((h1.trans (cores_reach G k S T u hu hk1 C w w' hw hw')).trans h2.symm)).symm

lemma Q_ncard (hST : Disjoint S T) (hu : ∀ x, x ∈ u ↔ inX G k S T x)
    (C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent) :
    ({y : Vu (gad G k) u | inQ G k S T C y.1} : Set _).ncard =
      (univ.filter (inQ G k S T C)).card := by
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, mem_coe, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx
    exact ⟨gv _ u x (fun h => notX_of_Q G k S T hST C x hx ((hu x).1 h)), hx, rfl⟩

lemma TT_even (hu : ∀ x, x ∈ u ↔ inX G k S T x) (d : G.Dart) (hT1 : d.fst ∈ T)
    (hT2 : d.snd ∈ T) (hS2 : d.snd ∉ S) (hdu : (Sum.inl d : GW G k) ∉ u) :
    ¬ Odd ((Gm (gad G k) u).connectedComponentMk (gv _ u _ hdu)).supp.ncard := by
  have hsu : (Sum.inl d.symm : GW G k) ∉ u := fun h => hS2 ((hu _).1 h)
  have key : Subtype.val '' ((Gm (gad G k) u).connectedComponentMk (gv _ u _ hdu)).supp =
      ({Sum.inl d, Sum.inl d.symm} : Set (GW G k)) := by
    ext x
    simp only [Set.mem_image, SimpleGraph.ConnectedComponent.mem_supp_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine reach_closed _ u (fun x => x = Sum.inl d ∨ x = Sum.inl d.symm) ?_ _ _
        (SimpleGraph.ConnectedComponent.exact hy.symm) (Or.inl rfl)
      rintro x (e | c) (rfl | rfl) hy hxy
      · simp only [gad_ll] at hxy; exact Or.inr (by rw [hxy])
      · simp only [gad_ll, SimpleGraph.Dart.symm_symm] at hxy; exact Or.inl (by rw [hxy])
      · simp only [gad_lr] at hxy
        exact absurd ((hu (Sum.inr c)).2 (show c.1 ∈ T by rw [hxy]; exact hT1)) hy
      · simp only [gad_lr] at hxy
        exact absurd ((hu (Sum.inr c)).2 (show c.1 ∈ T by rw [hxy]; exact hT2)) hy
    · rintro (rfl | rfl)
      · exact ⟨gv _ u _ hdu, rfl, rfl⟩
      · exact ⟨gv _ u _ hsu, SimpleGraph.ConnectedComponent.sound
          (gm_reach_adj _ u _ _ hdu hsu ((gad_ll _ _).2 rfl)).symm, rfl⟩
  intro hodd
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, key,
    Set.ncard_pair (fun h => d.symm_ne (Sum.inl_injective h).symm)] at hodd
  exact Nat.not_odd_iff_even.2 even_two hodd

/-- STEP D2: the odd components of `H - X(S,T)` number at most `k(S) + N(S,T) + Q̃(S,T)`. -/
theorem oc_upper (f : V → ℕ) (hk : ∀ v, f v + k v = G.degree v) (hST : Disjoint S T)
    (hu : ∀ x, x ∈ u ↔ inX G k S T x) (hk1 : ∀ v, v ∉ S → v ∉ T → 1 ≤ k v) :
    (Gm (gad G k) u).oddComponents.ncard ≤
      ∑ w ∈ S, k w + edgeCount G S T + oddComps G f S T := by
  let oddset := univ.filter (fun C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent =>
      Odd ((∑ v ∈ compVerts G (S ∪ T) C, f v) + edgeCount G (compVerts G (S ∪ T) C) T))
  have hmk : ∀ v (h : v ∈ ((↑(S ∪ T) : Set V)ᶜ)),
      v ∈ compVerts G (S ∪ T) ((G.induce ((↑(S ∪ T) : Set V)ᶜ)).connectedComponentMk ⟨v, h⟩) :=
    fun v h => mem_filter.2 ⟨mem_univ _, h, rfl⟩
  have hout : ∀ C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent,
      C.out.1 ∈ compVerts G (S ∪ T) C := by
    intro C; simp only [compVerts, mem_filter, mem_univ, true_and]; exact ⟨C.out.2, C.out_eq⟩
  let r : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent → GW G k := fun C =>
    (cvu G k S T u hu hk1 C.out.1 (not_mem_of_compVerts G (hout C))).1
  let A1 := (univ.filter (fun c : Σ w : V, Fin (k w) => c.1 ∈ S)).map
    (Function.Embedding.inr : (Σ w : V, Fin (k w)) ↪ GW G k)
  let A2 := (univ.filter (fun d : G.Dart => d.fst ∈ T ∧ d.snd ∈ S)).map
    (Function.Embedding.inl : G.Dart ↪ GW G k)
  let A3 := oddset.image r
  let B := A1 ∪ A2 ∪ A3
  have hB : B.card ≤ ∑ w ∈ S, k w + edgeCount G S T + oddComps G f S T := by
    show (A1 ∪ A2 ∪ A3).card ≤ _
    have c1 : A1.card = ∑ w ∈ S, k w := by rw [card_map, card_cores_mem]
    have c2 : A2.card = edgeCount G S T := by rw [card_map, edgeCount_eq G S T hST]
    have c3 : A3.card ≤ oddComps G f S T :=
      card_image_le.trans (le_of_eq (by unfold oddComps; convert rfl))
    have := card_union_le (A1 ∪ A2) A3
    have := card_union_le A1 A2
    omega
  have hQcase : ∀ (C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent)
      (z : Vu (gad G k) u), inQ G k S T C z.1 →
      Odd ((Gm (gad G k) u).connectedComponentMk z).supp.ncard →
      ∃ x ∈ B, ∃ hx : x ∉ u, gv _ u x hx ∈ ((Gm (gad G k) u).connectedComponentMk z).supp := by
    intro C z hz hodd
    have hs := Q_supp G k S T u f hk hu hk1 C z hz
    rw [hs, Q_ncard G k S T u hST hu C, card_Q G k S T f hk hST C] at hodd
    have hCo : C ∈ oddset := by
      simp only [oddset, mem_filter, mem_univ, true_and]
      rw [Nat.odd_iff] at hodd ⊢; omega
    have hx : r C ∉ u := (Gm_mem _ u _).1
      (cvu G k S T u hu hk1 C.out.1 (not_mem_of_compVerts G (hout C))).2
    refine ⟨r C, mem_union_right _ (mem_image_of_mem r hCo), hx, ?_⟩
    rw [hs]
    show inQ G k S T C (r C)
    exact hout C
  have hmeet : ∀ K ∈ (Gm (gad G k) u).oddComponents,
      ∃ x ∈ B, ∃ hx : x ∉ u, gv _ u x hx ∈ K.supp := by
    intro K
    refine K.ind (fun z => ?_)
    intro hK
    change Odd _ at hK
    rcases z with ⟨d | c, hzu⟩
    · have hzu' := (Gm_mem _ u _).1 hzu
      have hdS : d.fst ∉ S := fun h => hzu' ((hu _).2 h)
      by_cases hdT : d.fst ∈ T
      · by_cases hsS : d.snd ∈ S
        · refine ⟨Sum.inl d, mem_union_left _ (mem_union_right _ ?_), hzu',
            (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl⟩
          simp only [A2, Finset.mem_map, mem_filter, mem_univ, true_and,
            Function.Embedding.inl_apply]
          exact ⟨d, ⟨hdT, hsS⟩, rfl⟩
        · by_cases hsT : d.snd ∈ T
          · exact absurd hK (TT_even G k S T u hu d hdT hsT hsS hzu')
          · have hR : d.snd ∉ S ∪ T := by rw [mem_union]; tauto
            exact hQcase _ _ (Or.inr ⟨hdT, hmk d.snd (Set.mem_compl fun h => hR (mem_coe.1 h))⟩) hK
      · have hR : d.fst ∉ S ∪ T := by rw [mem_union]; tauto
        exact hQcase _ _ (Or.inl (hmk d.fst (Set.mem_compl fun h => hR (mem_coe.1 h)))) hK
    · have hzu' := (Gm_mem _ u _).1 hzu
      have hcT : c.1 ∉ T := fun h => hzu' ((hu _).2 h)
      by_cases hcS : c.1 ∈ S
      · refine ⟨Sum.inr c, mem_union_left _ (mem_union_left _ ?_), hzu',
          (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl⟩
        simp only [A1, Finset.mem_map, mem_filter, mem_univ, true_and,
          Function.Embedding.inr_apply]
        exact ⟨c, hcS, rfl⟩
      · have hR : c.1 ∉ S ∪ T := by rw [mem_union]; tauto
        exact hQcase _ _ (hmk c.1 (Set.mem_compl fun h => hR (mem_coe.1 h))) hK
  let φ : (Gm (gad G k) u).ConnectedComponent → GW G k := fun K =>
    if h : K ∈ (Gm (gad G k) u).oddComponents then (hmeet K h).choose else K.out.1
  have hφB : ∀ K ∈ (Gm (gad G k) u).oddComponents,
      φ K ∈ (B : Set (GW G k)) ∧ ∃ hx : φ K ∉ u, gv _ u (φ K) hx ∈ K.supp := by
    intro K hK
    have hspec := (hmeet K hK).choose_spec
    simp only [φ, dif_pos hK]
    exact ⟨mem_coe.2 hspec.1, hspec.2⟩
  calc (Gm (gad G k) u).oddComponents.ncard ≤ (B : Set (GW G k)).ncard := by
        refine Set.ncard_le_ncard_of_injOn φ (fun K hK => (hφB K hK).1) ?_ (Set.toFinite _)
        intro K hK K' hK' he
        obtain ⟨-, hx, h1⟩ := hφB K hK
        obtain ⟨-, hx', h2⟩ := hφB K' hK'
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at h1 h2
        exact h1.symm.trans ((congrArg _ (Subtype.ext he : gv _ u (φ K) hx = gv _ u (φ K') hx')).trans h2)
    _ = B.card := Set.ncard_coe_finset B
    _ ≤ _ := hB

end upper

end FF51

open LPCommunity.SBMRecovery Classical in
theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ) :
    HasFactor G f ↔
      ∀ S T : Finset V, Disjoint S T →
        0 ≤ (∑ v ∈ S, (f v : ℤ)) - (∑ v ∈ T, (f v : ℤ)) + (∑ v ∈ T, (G.degree v : ℤ))
          - (edgeCount G S T : ℤ) - (oddComps G f S T : ℤ) := by
  refine ⟨fun h S T hST => FF51.necessity G f h S T hST, fun h => ?_⟩
  have hle : ∀ v, f v ≤ G.degree v := by
    intro v
    have h1 := h ∅ {v} (Finset.disjoint_empty_left _)
    have h0 : edgeCount G ∅ {v} = 0 := by simp [edgeCount]
    simp only [Finset.sum_empty, Finset.sum_singleton, h0, Nat.cast_zero] at h1
    omega
  let k : V → ℕ := fun v => G.degree v - f v
  have hk : ∀ v, f v + k v = G.degree v := fun v => by have := hle v; simp only [k]; omega
  by_contra hno
  have hpm : ¬ ∃ M : (FF51.gad G k).Subgraph, M.IsPerfectMatching :=
    fun ⟨M, hM⟩ => hno (FF51.factor_of_pm G f k hk M hM)
  rw [SimpleGraph.tutte] at hpm
  push_neg at hpm
  obtain ⟨u0, hu0⟩ := hpm
  obtain ⟨u, hv, ht⟩ := FF51.exists_tight_violator _ u0.ncard u0 rfl hu0
  obtain ⟨S, T, hST, hu, hk1⟩ := FF51.tight_normal_form G k u ht
  have hup := FF51.oc_upper G k S T u f hk hST hu hk1
  have hcard : u.ncard = ∑ w ∈ S, G.degree w + ∑ w ∈ T, k w := by
    have : u = ↑(Finset.univ.filter (FF51.inX G k S T)) := by
      ext x; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, hu x]
    rw [this, Set.ncard_coe_finset, FF51.card_X]
  have hv' : u.ncard < (FF51.Gm (FF51.gad G k) u).oddComponents.ncard := hv
  have h2 := h S T hST
  have hdS : ∑ w ∈ S, G.degree w = ∑ w ∈ S, f w + ∑ w ∈ S, k w := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun w _ => (hk w).symm
  have hdT : ∑ w ∈ T, G.degree w = ∑ w ∈ T, f w + ∑ w ∈ T, k w := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun w _ => (hk w).symm
  rw [← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum] at h2
  omega
