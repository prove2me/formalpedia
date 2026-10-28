-- Prove2me | solution 1 for LPCommunity.SBMRecovery.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T04:13:23.701207+00:00
-- url     : https://prove2.me/submissions/82069522-de55-4b09-9d07-779c9beb9903

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Factors

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Filter Topology
open scoped Classical

namespace BF5

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

/-! ### Counting helpers -/

lemma card_iff {α : Type*} [Fintype α] (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x ↔ Q x) : (univ.filter P).card = (univ.filter Q).card := by
  congr 1; ext x; simp only [mem_filter, mem_univ, true_and]; exact h x

lemma card_imp {α : Type*} [Fintype α] (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x → Q x) : (univ.filter P).card ≤ (univ.filter Q).card := by
  apply card_le_card
  intro x hx
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  exact h x hx

lemma card_split {α : Type*} [Fintype α] (P Q R1 R2 : α → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred R1] [DecidablePred R2]
    (h1 : ∀ x, R1 x ↔ P x ∧ Q x) (h2 : ∀ x, R2 x ↔ P x ∧ ¬ Q x) :
    (univ.filter P).card = (univ.filter R1).card + (univ.filter R2).card := by
  rw [← card_filter_add_card_filter_not (s := univ.filter P) Q, filter_filter, filter_filter]
  congr 1 <;> congr 1 <;> ext x <;> simp only [mem_filter, mem_univ, true_and, h1, h2]

lemma card_sum_split {α β : Type*} [Fintype α] [Fintype β] (P : α ⊕ β → Prop) (P1 : α → Prop)
    (P2 : β → Prop) [DecidablePred P] [DecidablePred P1] [DecidablePred P2]
    (h1 : ∀ a, P (.inl a) ↔ P1 a) (h2 : ∀ b, P (.inr b) ↔ P2 b) :
    (univ.filter P).card = (univ.filter P1).card + (univ.filter P2).card := by
  simp only [card_filter]
  rw [Fintype.sum_sum_type]
  congr 1
  · refine sum_congr rfl fun a _ => ?_
    by_cases h : P1 a <;> simp [h, h1]
  · refine sum_congr rfl fun a _ => ?_
    by_cases h : P2 a <;> simp [h, h2]

@[simp] lemma symm_fst' {G : SimpleGraph V} (d : G.Dart) : d.symm.fst = d.snd := rfl
@[simp] lemma symm_snd' {G : SimpleGraph V} (d : G.Dart) : d.symm.snd = d.fst := rfl

lemma card_symm (G : SimpleGraph V) (P Q : G.Dart → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ d, Q d ↔ P d.symm) : (univ.filter P).card = (univ.filter Q).card := by
  refine card_bij' (fun d _ => d.symm) (fun d _ => d.symm) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    rw [h, SimpleGraph.Dart.symm_symm]; exact hd
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    exact (h d).1 hd
  · intro d _; exact SimpleGraph.Dart.symm_symm d
  · intro d _; exact SimpleGraph.Dart.symm_symm d

lemma card_darts_memP (G : SimpleGraph V) (U : Finset V) (P : G.Dart → Prop) [DecidablePred P] :
    (univ.filter (fun d : G.Dart => d.fst ∈ U ∧ P d)).card =
      ∑ w ∈ U, (univ.filter (fun d : G.Dart => d.fst = w ∧ P d)).card := by
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.fst) (t := U)
    (by intro d hd; simp only [mem_coe, mem_filter, mem_univ, true_and] at hd ⊢; exact hd.1)]
  refine sum_congr rfl fun w hw => ?_
  rw [filter_filter]
  congr 1; ext d; simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨_, h⟩, rfl⟩; exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact ⟨⟨hw, h⟩, rfl⟩

open LPCommunity.SBMRecovery Classical in
lemma edgeCount_self (G : SimpleGraph V) (U : Finset V) :
    2 * edgeCount G U U = (univ.filter (fun d : G.Dart => d.fst ∈ U ∧ d.snd ∈ U)).card := by
  unfold edgeCount
  rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.edge)
    (t := G.edgeFinset.filter fun e => ∃ u ∈ U, ∃ u' ∈ U, e = s(u, u'))
    (by
      intro d hd
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hd ⊢
      exact ⟨G.mem_edgeFinset.2 d.edge_mem, d.fst, hd.1, d.snd, hd.2, rfl⟩)]
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun e he => ?_
  rw [mem_filter] at he
  obtain ⟨he1, u, hu, u', hu', rfl⟩ := he
  rw [← G.dart_edge_fiber_card s(u, u') (G.mem_edgeFinset.1 he1)]
  congr 1; ext d
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h; refine ⟨?_, h⟩
    have h' : s(d.fst, d.snd) = s(u, u') := h
    rcases Sym2.eq_iff.1 h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> exact ⟨‹_›, ‹_›⟩
  · exact fun h => h.2

/-! ### Necessity -/

open LPCommunity.SBMRecovery Classical in
theorem nec (G : SimpleGraph V) (b : V → ℕ) (hF : HasFactor G b) (U : Finset V) :
    (edgeCount G U U : ℝ) ≥ (∑ v ∈ U, (b v : ℝ)) - (∑ v, (b v : ℝ)) / 2 := by
  obtain ⟨F, hFG, hF⟩ := hF
  have hb : ∀ W : Finset V, ∑ v ∈ W, b v =
      (univ.filter (fun d : G.Dart => d.fst ∈ W ∧ F.Adj d.fst d.snd)).card := by
    intro W
    rw [card_darts_memP]
    refine sum_congr rfl fun w _ => ?_
    rw [← hF w]
    convert (card_darts_in G F hFG w).symm
  have hU := hb U
  have hUc := hb Uᶜ
  have s1 := card_split (fun d : G.Dart => d.fst ∈ U ∧ F.Adj d.fst d.snd) (fun d => d.snd ∈ U)
    (fun d => d.fst ∈ U ∧ d.snd ∈ U ∧ F.Adj d.fst d.snd)
    (fun d => d.fst ∈ U ∧ d.snd ∉ U ∧ F.Adj d.fst d.snd) (fun d => by tauto) (fun d => by tauto)
  have s2 := card_split (fun d : G.Dart => d.fst ∈ Uᶜ ∧ F.Adj d.fst d.snd) (fun d => d.snd ∈ U)
    (fun d => d.fst ∉ U ∧ d.snd ∈ U ∧ F.Adj d.fst d.snd)
    (fun d => d.fst ∉ U ∧ d.snd ∉ U ∧ F.Adj d.fst d.snd)
    (fun d => by rw [mem_compl]; tauto) (fun d => by rw [mem_compl]; tauto)
  have s3 := card_symm G (fun d : G.Dart => d.fst ∈ U ∧ d.snd ∉ U ∧ F.Adj d.fst d.snd)
    (fun d => d.fst ∉ U ∧ d.snd ∈ U ∧ F.Adj d.fst d.snd)
    (fun d => by
      simp only [symm_fst', symm_snd']
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3.symm⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3.symm⟩)
  have s4 := card_imp (fun d : G.Dart => d.fst ∈ U ∧ d.snd ∈ U ∧ F.Adj d.fst d.snd)
    (fun d => d.fst ∈ U ∧ d.snd ∈ U) (fun d h => ⟨h.1, h.2.1⟩)
  have s5 := edgeCount_self G U
  have tot : ∑ v ∈ U, (b v : ℝ) + ∑ v ∈ Uᶜ, (b v : ℝ) = ∑ v, (b v : ℝ) := sum_add_sum_compl U _
  have hU' : (∑ v ∈ U, (b v : ℝ)) = ((∑ v ∈ U, b v : ℕ) : ℝ) := by push_cast; rfl
  have hUc' : (∑ v ∈ Uᶜ, (b v : ℝ)) = ((∑ v ∈ Uᶜ, b v : ℕ) : ℝ) := by push_cast; rfl
  rw [hU, s1] at hU'
  rw [hUc, s2] at hUc'
  have s4' : ((univ.filter (fun d : G.Dart => d.fst ∈ U ∧ d.snd ∈ U ∧ F.Adj d.fst d.snd)).card : ℝ)
      ≤ 2 * (edgeCount G U U : ℝ) := by exact_mod_cast s4.trans s5.symm.le
  rw [s3] at hU'
  push_cast at hU' hUc'
  linarith

/-! ### Sufficiency -/

def sd (G : SimpleGraph V) (k : V → ℕ) (A : Finset V) : GW G k → Prop
  | .inl d => d.fst ∈ A
  | .inr c => c.1 ∉ A

open LPCommunity.SBMRecovery Classical in
lemma key (G : SimpleGraph V) (A : Finset V) (hA : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (b : V → ℕ)
    (H : ∀ U : Finset V, (edgeCount G U U : ℝ) ≥ (∑ v ∈ U, (b v : ℝ)) - (∑ v, (b v : ℝ)) / 2)
    (S T : Finset V) (hS : S ⊆ A) (hT : T ⊆ Aᶜ) :
    (∑ v ∈ S, (b v : ℝ)) - ∑ v ∈ T, (b v : ℝ) + ((∑ v ∈ Aᶜ, (b v : ℝ)) - ∑ v ∈ A, (b v : ℝ)) / 2
      ≤ ((univ.filter (fun d : G.Dart => d.fst ∈ S ∧ d.snd ∉ T)).card : ℝ) := by
  have h1 := H (S ∪ (Aᶜ \ T))
  have h2 := edgeCount_self G (S ∪ (Aᶜ \ T))
  have hS' : ∀ v, v ∈ S → v ∈ A := fun v hv => hS hv
  have hT' : ∀ v, v ∈ T → v ∉ A := fun v hv => mem_compl.1 (hT hv)
  have h3 := card_split (fun d : G.Dart => d.fst ∈ S ∪ (Aᶜ \ T) ∧ d.snd ∈ S ∪ (Aᶜ \ T))
    (fun d => d.fst ∈ S) (fun d => d.fst ∈ S ∧ d.snd ∉ T) (fun d => d.snd ∈ S ∧ d.fst ∉ T)
    (fun d => by
      have := hA _ _ d.adj
      have := hS' d.fst; have := hS' d.snd; have := hT' d.fst; have := hT' d.snd
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
      tauto)
    (fun d => by
      have := hA _ _ d.adj
      have := hS' d.fst; have := hS' d.snd; have := hT' d.fst; have := hT' d.snd
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
      tauto)
  have h4 := card_symm G (fun d : G.Dart => d.fst ∈ S ∧ d.snd ∉ T)
    (fun d => d.snd ∈ S ∧ d.fst ∉ T) (fun d => Iff.rfl)
  have hdisj : Disjoint S (Aᶜ \ T) := by
    rw [Finset.disjoint_left]; intro v hv hv'
    exact (mem_compl.1 (mem_sdiff.1 hv').1) (hS hv)
  have h5 : ∑ v ∈ S ∪ (Aᶜ \ T), (b v : ℝ) = ∑ v ∈ S, (b v : ℝ) + ∑ v ∈ Aᶜ \ T, (b v : ℝ) :=
    sum_union hdisj
  have h6 : ∑ v ∈ Aᶜ \ T, (b v : ℝ) + ∑ v ∈ T, (b v : ℝ) = ∑ v ∈ Aᶜ, (b v : ℝ) := sum_sdiff hT
  have h7 : ∑ v ∈ A, (b v : ℝ) + ∑ v ∈ Aᶜ, (b v : ℝ) = ∑ v, (b v : ℝ) := sum_add_sum_compl A _
  rw [h3, ← h4] at h2
  have h2' : 2 * (edgeCount G (S ∪ (Aᶜ \ T)) (S ∪ (Aᶜ \ T)) : ℝ) =
      2 * ((univ.filter (fun d : G.Dart => d.fst ∈ S ∧ d.snd ∉ T)).card : ℝ) := by
    exact_mod_cast (show 2 * edgeCount G (S ∪ (Aᶜ \ T)) (S ∪ (Aᶜ \ T)) =
      2 * (univ.filter (fun d : G.Dart => d.fst ∈ S ∧ d.snd ∉ T)).card by omega)
  linarith

open LPCommunity.SBMRecovery Classical in
lemma hall_GW (G : SimpleGraph V) (k b : V → ℕ) (hk : ∀ v, b v + k v = G.degree v)
    (A : Finset V) (hA : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (K' : ∀ S T : Finset V, S ⊆ A → T ⊆ Aᶜ → ∑ v ∈ S, b v ≤
      ∑ v ∈ T, b v + (univ.filter (fun d : G.Dart => d.fst ∈ S ∧ d.snd ∉ T)).card)
    (X : Finset (GW G k)) (hX : ∀ x ∈ X, sd G k A x) :
    X.card ≤ (univ.filter (fun y : GW G k => ¬ sd G k A y ∧ ∃ x ∈ X, (gad G k).Adj x y)).card := by
  let S : Finset V := (univ.filter (fun d : G.Dart => (Sum.inl d : GW G k) ∈ X)).image
    (fun d => d.fst)
  let T : Finset V := (univ.filter (fun c : (Σ v, Fin (k v)) => (Sum.inr c : GW G k) ∈ X)).image
    (fun c => c.1)
  have hXS : ∀ d : G.Dart, (Sum.inl d : GW G k) ∈ X → d.fst ∈ S := fun d hd =>
    mem_image.2 ⟨d, mem_filter.2 ⟨mem_univ _, hd⟩, rfl⟩
  have hXT : ∀ c : (Σ v, Fin (k v)), (Sum.inr c : GW G k) ∈ X → c.1 ∈ T := fun c hc =>
    mem_image.2 ⟨c, mem_filter.2 ⟨mem_univ _, hc⟩, rfl⟩
  have hS : S ⊆ A := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hv
    exact hX _ (mem_filter.1 hd).2
  have hT : T ⊆ Aᶜ := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hv
    exact mem_compl.2 (hX _ (mem_filter.1 hc).2)
  have hSimg : ∀ v ∈ S, ∃ d : G.Dart, (Sum.inl d : GW G k) ∈ X ∧ d.fst = v := by
    intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hv
    exact ⟨d, (mem_filter.1 hd).2, rfl⟩
  have hTimg : ∀ v ∈ T, ∃ c : (Σ v, Fin (k v)), (Sum.inr c : GW G k) ∈ X ∧ c.1 = v := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hv
    exact ⟨c, (mem_filter.1 hc).2, rfl⟩
  -- split X
  have e1 : X.card = (univ.filter (fun d : G.Dart => (Sum.inl d : GW G k) ∈ X)).card +
      (univ.filter (fun c : (Σ v, Fin (k v)) => (Sum.inr c : GW G k) ∈ X)).card := by
    have : X = univ.filter (fun x => x ∈ X) := by ext x; simp
    conv_lhs => rw [this]
    exact card_sum_split _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : (univ.filter (fun c : (Σ v, Fin (k v)) => (Sum.inr c : GW G k) ∈ X)).card ≤
      ∑ v ∈ T, k v := by
    rw [← card_cores_mem k T]
    exact card_imp _ _ (fun c hc => hXT c hc)
  -- split N
  have e3 := card_sum_split (fun y : GW G k => ¬ sd G k A y ∧ ∃ x ∈ X, (gad G k).Adj x y)
    (fun d : G.Dart => d.fst ∉ A ∧ ∃ x ∈ X, (gad G k).Adj x (.inl d))
    (fun c : (Σ v, Fin (k v)) => c.1 ∈ A ∧ ∃ x ∈ X, (gad G k).Adj x (.inr c))
    (fun _ => Iff.rfl) (fun c => by simp only [sd, not_not])
  have e4 : ∑ v ∈ S, k v ≤
      (univ.filter (fun c : (Σ v, Fin (k v)) => c.1 ∈ A ∧ ∃ x ∈ X, (gad G k).Adj x (.inr c))).card := by
    rw [← card_cores_mem k S]
    apply card_imp
    intro c hc
    obtain ⟨d, hd, hdc⟩ := hSimg _ hc
    exact ⟨hS hc, Sum.inl d, hd, hdc.symm⟩
  have e5a := card_split
    (fun d : G.Dart => d.fst ∈ T ∨ ((Sum.inl d.symm : GW G k) ∈ X ∧ d.fst ∉ T))
    (fun d => d.fst ∈ T) (fun d => d.fst ∈ T)
    (fun d => (Sum.inl d.symm : GW G k) ∈ X ∧ d.fst ∉ T) (fun d => by tauto) (fun d => by tauto)
  have e5 : (univ.filter
      (fun d : G.Dart => d.fst ∈ T ∨ ((Sum.inl d.symm : GW G k) ∈ X ∧ d.fst ∉ T))).card ≤
      (univ.filter (fun d : G.Dart => d.fst ∉ A ∧ ∃ x ∈ X, (gad G k).Adj x (.inl d))).card := by
    apply card_imp
    intro d hd
    rcases hd with hd | ⟨hd, -⟩
    · obtain ⟨c, hc, hcd⟩ := hTimg _ hd
      exact ⟨mem_compl.1 (hT hd), Sum.inr c, hc, hcd⟩
    · have h1 : d.symm.fst ∈ A := hX _ hd
      have h2 := hA _ _ d.adj
      simp only [symm_fst'] at h1
      refine ⟨fun h => (h2.1 h) h1, Sum.inl d.symm, hd, ?_⟩
      show d = d.symm.symm
      rw [SimpleGraph.Dart.symm_symm]
  have e6 : (univ.filter (fun d : G.Dart => d.fst ∈ T)).card = ∑ v ∈ T, G.degree v :=
    card_darts_mem G T
  have e7 := card_split (fun d : G.Dart => (Sum.inl d.symm : GW G k) ∈ X)
    (fun d => d.fst ∈ T) (fun d => (Sum.inl d.symm : GW G k) ∈ X ∧ d.fst ∈ T)
    (fun d => (Sum.inl d.symm : GW G k) ∈ X ∧ d.fst ∉ T) (fun d => Iff.rfl) (fun d => Iff.rfl)
  have e8 := card_symm G (fun d : G.Dart => (Sum.inl d : GW G k) ∈ X)
    (fun d => (Sum.inl d.symm : GW G k) ∈ X) (fun d => Iff.rfl)
  have e9 : (univ.filter (fun d : G.Dart => (Sum.inl d.symm : GW G k) ∈ X ∧ d.fst ∈ T)).card ≤
      (univ.filter (fun d : G.Dart => d.fst ∈ T ∧ d.snd ∈ S)).card := by
    apply card_imp
    intro d hd
    exact ⟨hd.2, hXS _ hd.1⟩
  have e10 := card_symm G (fun d : G.Dart => d.fst ∈ S ∧ d.snd ∈ T)
    (fun d => d.fst ∈ T ∧ d.snd ∈ S) (fun d => by simp only [symm_fst', symm_snd']; tauto)
  have e11 := card_split (fun d : G.Dart => d.fst ∈ S) (fun d => d.snd ∈ T)
    (fun d => d.fst ∈ S ∧ d.snd ∈ T) (fun d => d.fst ∈ S ∧ d.snd ∉ T)
    (fun d => Iff.rfl) (fun d => Iff.rfl)
  have e12 : (univ.filter (fun d : G.Dart => d.fst ∈ S)).card = ∑ v ∈ S, G.degree v :=
    card_darts_mem G S
  have e13 := K' S T hS hT
  have e14 : ∑ v ∈ S, b v + ∑ v ∈ S, k v = ∑ v ∈ S, G.degree v := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => hk v
  have e15 : ∑ v ∈ T, b v + ∑ v ∈ T, k v = ∑ v ∈ T, G.degree v := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => hk v
  omega

open LPCommunity.SBMRecovery Classical in
theorem suff (G : SimpleGraph V) (A : Finset V) (hA : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (b : V → ℕ)
    (H : ∀ U : Finset V, (edgeCount G U U : ℝ) ≥ (∑ v ∈ U, (b v : ℝ)) - (∑ v, (b v : ℝ)) / 2) :
    HasFactor G b := by
  have K := key G A hA b H
  have bal : ∑ v ∈ Aᶜ, (b v : ℝ) = ∑ v ∈ A, (b v : ℝ) := by
    have k1 := K A Aᶜ subset_rfl subset_rfl
    have k2 := K ∅ ∅ (empty_subset _) (empty_subset _)
    have z1 : (univ.filter (fun d : G.Dart => d.fst ∈ A ∧ d.snd ∉ Aᶜ)).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro d - ⟨h1, h2⟩
      rw [mem_compl, not_not] at h2
      exact ((hA _ _ d.adj).1 h1) h2
    have z2 : (univ.filter (fun d : G.Dart => d.fst ∈ (∅ : Finset V) ∧
        d.snd ∉ (∅ : Finset V))).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro d - ⟨h1, -⟩
      exact Finset.notMem_empty _ h1
    rw [z1] at k1
    rw [z2] at k2
    simp only [sum_empty, Nat.cast_zero] at k1 k2
    linarith
  have K' : ∀ S T : Finset V, S ⊆ A → T ⊆ Aᶜ → ∑ v ∈ S, b v ≤
      ∑ v ∈ T, b v + (univ.filter (fun d : G.Dart => d.fst ∈ S ∧ d.snd ∉ T)).card := by
    intro S T hS hT
    have := K S T hS hT
    rw [bal] at this
    have h' : ((∑ v ∈ S, b v : ℕ) : ℝ) ≤ ((∑ v ∈ T, b v +
        (univ.filter (fun d : G.Dart => d.fst ∈ S ∧ d.snd ∉ T)).card : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h'
  have hbd : ∀ v, b v ≤ G.degree v := by
    intro v
    by_cases hv : v ∈ A
    · have h := K' {v} ∅ (singleton_subset_iff.2 hv) (empty_subset _)
      have e : (univ.filter (fun d : G.Dart => d.fst ∈ ({v} : Finset V) ∧
          d.snd ∉ (∅ : Finset V))).card = G.degree v := by
        rw [← card_darts G v]
        exact card_iff _ _ (fun d => by simp)
      rw [e, sum_singleton, sum_empty] at h
      omega
    · have h := K' A (Aᶜ.erase v) subset_rfl (erase_subset _ _)
      have e : (univ.filter (fun d : G.Dart => d.fst ∈ A ∧ d.snd ∉ Aᶜ.erase v)).card =
          G.degree v := by
        rw [← card_darts G v]
        apply card_symm
        intro d
        have h1 := hA _ _ d.adj
        simp only [symm_fst', symm_snd', mem_erase, mem_compl]
        constructor
        · rintro rfl; exact ⟨by tauto, by tauto⟩
        · rintro ⟨h2, h3⟩; by_contra h4; exact h3 ⟨h4, by tauto⟩
      rw [e] at h
      have e2 := sum_erase_add (Aᶜ) b (mem_compl.2 hv)
      have bal' : ∑ v ∈ Aᶜ, b v = ∑ v ∈ A, b v := by exact_mod_cast bal
      omega
  let k : V → ℕ := fun v => G.degree v - b v
  have hk : ∀ v, b v + k v = G.degree v := fun v => by have := hbd v; simp only [k]; omega
  -- Hall
  let r : {x : GW G k // sd G k A x} → {y : GW G k // ¬ sd G k A y} → Prop :=
    fun x y => (gad G k).Adj x.1 y.1
  have hall : ∃ f : {x : GW G k // sd G k A x} → {y : GW G k // ¬ sd G k A y},
      Function.Injective f ∧ ∀ x, r x (f x) := by
    apply (Fintype.all_card_le_filter_rel_iff_exists_injective r).1
    intro X
    have h := hall_GW G k b hk A hA K' (X.map (Function.Embedding.subtype _)) (by
      intro x hx; rw [Finset.mem_map] at hx; obtain ⟨a, _, rfl⟩ := hx; exact a.2)
    rw [card_map] at h
    refine h.trans (le_of_eq ?_)
    rw [← card_map (Function.Embedding.subtype (fun y => ¬ sd G k A y))]
    congr 1; ext y
    simp only [Finset.mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨hy, x, ⟨a, ha, rfl⟩, hr⟩; exact ⟨⟨y, hy⟩, ⟨a, ha, hr⟩, rfl⟩
    · rintro ⟨y', ⟨a, ha, hr⟩, rfl⟩; exact ⟨y'.2, a.1, ⟨a, ha, rfl⟩, hr⟩
  obtain ⟨f, hfi, hfr⟩ := hall
  -- cardinalities
  have bal' : ∑ v ∈ Aᶜ, b v = ∑ v ∈ A, b v := by exact_mod_cast bal
  have c1 : Fintype.card {x : GW G k // sd G k A x} =
      ∑ v ∈ A, G.degree v + ∑ v ∈ Aᶜ, k v := by
    rw [Fintype.card_subtype, card_sum_split (sd G k A) (fun d : G.Dart => d.fst ∈ A)
      (fun c : (Σ v, Fin (k v)) => c.1 ∈ Aᶜ) (fun _ => Iff.rfl)
      (fun c => by simp only [sd, mem_compl]), card_darts_mem, card_cores_mem]
  have c2 : Fintype.card {y : GW G k // ¬ sd G k A y} =
      ∑ v ∈ Aᶜ, G.degree v + ∑ v ∈ A, k v := by
    rw [Fintype.card_subtype, card_sum_split (fun y => ¬ sd G k A y)
      (fun d : G.Dart => d.fst ∈ Aᶜ)
      (fun c : (Σ v, Fin (k v)) => c.1 ∈ A) (fun d => by simp only [sd, mem_compl])
      (fun c => by simp only [sd, not_not]), card_darts_mem, card_cores_mem]
  have c3 : ∑ v ∈ A, G.degree v = ∑ v ∈ Aᶜ, G.degree v := by
    rw [← card_darts_mem, ← card_darts_mem]
    apply card_symm
    intro d
    have := hA _ _ d.adj
    simp only [symm_fst', mem_compl]
    tauto
  have c4 : ∑ v ∈ A, b v + ∑ v ∈ A, k v = ∑ v ∈ A, G.degree v := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => hk v
  have c5 : ∑ v ∈ Aᶜ, b v + ∑ v ∈ Aᶜ, k v = ∑ v ∈ Aᶜ, G.degree v := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun v _ => hk v
  have hcard : Fintype.card {x : GW G k // sd G k A x} =
      Fintype.card {y : GW G k // ¬ sd G k A y} := by
    rw [c1, c2]; omega
  have hfb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hfi, hcard⟩
  let fe := Equiv.ofBijective f hfb
  let q : GW G k → GW G k := fun x =>
    if h : sd G k A x then (fe ⟨x, h⟩).1 else (fe.symm ⟨x, h⟩).1
  have q1 : ∀ x (h : sd G k A x), q x = (fe ⟨x, h⟩).1 := fun x h => dif_pos h
  have q2 : ∀ y (h : ¬ sd G k A y), q y = (fe.symm ⟨y, h⟩).1 := fun y h => dif_neg h
  have hqq : ∀ x, q (q x) = x := by
    intro x
    by_cases h : sd G k A x
    · rw [q1 x h, q2 _ (fe ⟨x, h⟩).2]; simp
    · rw [q2 x h, q1 _ (fe.symm ⟨x, h⟩).2]; simp
  have hadj : ∀ x, (gad G k).Adj x (q x) := by
    intro x
    by_cases h : sd G k A x
    · rw [q1 x h]; exact hfr ⟨x, h⟩
    · rw [q2 x h]
      have h1 := hfr (fe.symm ⟨x, h⟩)
      have e : f (fe.symm ⟨x, h⟩) = ⟨x, h⟩ := fe.apply_symm_apply _
      rw [e] at h1
      exact h1.symm
  obtain ⟨M, hM⟩ := pm_of_invol (gad G k) q hqq hadj
  exact factor_of_pm G b k hk M hM

end BF5

-- Proposition 5 (p. 20; Schrijver, Corollary 21.4a): bipartite b-factor criterion.
open LPCommunity.SBMRecovery in
theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hbip : ∃ A : Finset V, ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A)) (b : V → ℕ) :
    HasFactor G b ↔
      ∀ U : Finset V, (edgeCount G U U : ℝ) ≥ (∑ v ∈ U, (b v : ℝ)) - (∑ v, (b v : ℝ)) / 2 := by
  obtain ⟨A, hA⟩ := hbip
  exact ⟨fun h U => BF5.nec G b h U, fun H => BF5.suff G A hA b H⟩
