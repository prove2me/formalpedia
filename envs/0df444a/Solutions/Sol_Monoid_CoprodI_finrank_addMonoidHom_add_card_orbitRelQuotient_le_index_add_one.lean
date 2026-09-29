-- Prove2me | solution 1 for Monoid.CoprodI.finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2e2f1caa-8f9b-575e-8cf7-76c8c75f34cd

import Mathlib
import Theorems.Thm_SimpleGraph_exists_walkConnected_transversal_of_preconnected
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Subgroup SimpleGraph

namespace GroupTheory

namespace BassSerre

p2m_open "Monoid Monoid.CoprodI"

variable {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)]

abbrev Vertex : Type _ :=
  (i : ι) × (CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := i)).range)

variable {G} in

abbrev Vertex.mk (i : ι) (g : CoprodI G) : Vertex G :=
  ⟨i, QuotientGroup.mk g⟩

def graph : SimpleGraph (Vertex G) where
  Adj v w := v.1 ≠ w.1 ∧ ∃ g : CoprodI G, Vertex.mk v.1 g = v ∧ Vertex.mk w.1 g = w
  symm := ⟨by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨hij, g, hgv, hgw⟩
    exact ⟨hij.symm, g, hgw, hgv⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G}

theorem mk_eq_mk_iff {i : ι} {g h : CoprodI G} :
    Vertex.mk (G := G) i g = Vertex.mk i h ↔ g⁻¹ * h ∈ (of (M := G) (i := i)).range := by
  constructor
  · intro H
    exact QuotientGroup.eq.mp
      (sigma_mk_injective (β := fun j => CoprodI G ⧸ (of (M := G) (i := j)).range) H)
  · intro H
    exact congrArg (Sigma.mk i) (QuotientGroup.eq.mpr H)

theorem adj_mk {i j : ι} (hij : i ≠ j) (g : CoprodI G) :
    (graph G).Adj (Vertex.mk i g) (Vertex.mk j g) :=
  ⟨hij, g, rfl, rfl⟩

theorem adj_iff_exists {v w : Vertex G} :
    (graph G).Adj v w ↔ v.1 ≠ w.1 ∧ ∃ g, Vertex.mk v.1 g = v ∧ Vertex.mk w.1 g = w :=
  Iff.rfl

theorem adj_one {i j : ι} (hij : i ≠ j) :
    (graph G).Adj (Vertex.mk i (1 : CoprodI G)) (Vertex.mk j 1) :=
  adj_mk hij 1

scoped instance : SMul (CoprodI G) (Vertex G) where
  smul g v := ⟨v.1, g • v.2⟩

theorem smul_def (g : CoprodI G) (v : Vertex G) : g • v = ⟨v.1, g • v.2⟩ :=
  rfl

@[scoped simp]
theorem smul_mk (g : CoprodI G) (i : ι) (h : CoprodI G) :
    g • Vertex.mk i h = Vertex.mk i (g * h) :=
  rfl

scoped instance : MulAction (CoprodI G) (Vertex G) where
  one_smul := by
    rintro ⟨i, x⟩
    show (⟨i, (1 : CoprodI G) • x⟩ : Vertex G) = ⟨i, x⟩
    rw [one_smul]
  mul_smul g h := by
    rintro ⟨i, x⟩
    show (⟨i, (g * h) • x⟩ : Vertex G) = ⟨i, g • h • x⟩
    rw [mul_smul]

theorem smul_adj {v w : Vertex G} (g : CoprodI G) (h : (graph G).Adj v w) :
    (graph G).Adj (g • v) (g • w) := by
  obtain ⟨hvw, e, hev, hew⟩ := h
  exact ⟨hvw, g * e, by rw [← hev]; rfl, by rw [← hew]; rfl⟩

def smulHom (g : CoprodI G) : graph G →g graph G where
  toFun v := g • v
  map_rel' := smul_adj g

@[scoped simp]
theorem smulHom_apply (g : CoprodI G) (v : Vertex G) : smulHom g v = g • v :=
  rfl

theorem reachable_smul {v w : Vertex G} (g : CoprodI G) (h : (graph G).Reachable v w) :
    (graph G).Reachable (g • v) (g • w) :=
  h.map (smulHom g)

theorem smul_eq_self_iff {h : CoprodI G} {i : ι} {g : CoprodI G} :
    h • Vertex.mk i g = Vertex.mk i g ↔ g⁻¹ * h * g ∈ (of (M := G) (i := i)).range := by
  rw [smul_mk, mk_eq_mk_iff, show (h * g)⁻¹ * g = (g⁻¹ * h * g)⁻¹ by group, inv_mem_iff]

theorem mk_of_eq_mk_one {i : ι} (m : G i) :
    Vertex.mk (G := G) i (of m) = Vertex.mk i 1 :=
  mk_eq_mk_iff.mpr (MonoidHom.mem_range.mpr ⟨m⁻¹, by simp⟩)

theorem reachable_one_one (i j : ι) :
    (graph G).Reachable (Vertex.mk i (1 : CoprodI G)) (Vertex.mk j 1) := by
  classical
  by_cases h : i = j
  · subst h; exact Reachable.refl _
  · exact (adj_one h).reachable

theorem reachable_one_of {i k : ι} (m : G k) :
    (graph G).Reachable (Vertex.mk i (1 : CoprodI G)) (Vertex.mk i (of m)) := by
  classical
  by_cases hki : k = i
  · subst hki
    rw [mk_of_eq_mk_one]
  · refine (reachable_one_one i k).trans ?_
    rw [← mk_of_eq_mk_one m]
    exact (adj_mk hki (of m)).reachable

theorem reachable_one (i : ι) (g : CoprodI G) (j : ι) :
    (graph G).Reachable (Vertex.mk i (1 : CoprodI G)) (Vertex.mk j g) := by
  induction g using CoprodI.induction_left with
  | one => exact reachable_one_one i j
  | mul m x ih =>
    have step := reachable_smul (of m) ih
    rw [smul_mk, smul_mk, mul_one] at step
    exact (reachable_one_of m).trans step

theorem connected [Nonempty ι] : (graph G).Connected := by
  inhabit ι
  rw [connected_iff_exists_forall_reachable]
  refine ⟨Vertex.mk default 1, ?_⟩
  rintro ⟨j, x⟩
  induction x using QuotientGroup.induction_on with
  | H g => exact reachable_one default g j

theorem eq_one_of_mem_range_of_mem_range {i j : ι} (hij : i ≠ j) {x : CoprodI G}
    (hi : x ∈ (of (M := G) (i := i)).range) (hj : x ∈ (of (M := G) (i := j)).range) :
    x = 1 := by
  classical
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hi
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hj
  have key := congrArg (lift (Pi.mulSingle i (MonoidHom.id (G i)))) hb
  rw [lift_of, lift_of, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm] at key
  simp only [MonoidHom.one_apply, MonoidHom.id_apply] at key
  rw [← key, map_one]

theorem range_inf_range_eq_bot {i j : ι} (hij : i ≠ j) :
    (of (M := G) (i := i)).range ⊓ (of (M := G) (i := j)).range = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  exact mem_bot.mpr (eq_one_of_mem_range_of_mem_range hij hx.1 hx.2)

theorem eq_of_mk_eq_mk {i j : ι} (hij : i ≠ j) {g g' : CoprodI G}
    (hgi : Vertex.mk (G := G) i g = Vertex.mk i g')
    (hgj : Vertex.mk (G := G) j g = Vertex.mk j g') :
    g = g' :=
  inv_mul_eq_one.mp
    (eq_one_of_mem_range_of_mem_range hij (mk_eq_mk_iff.mp hgi) (mk_eq_mk_iff.mp hgj))

theorem adj_base_iff {i : ι} {w : Vertex G} :
    (graph G).Adj (Vertex.mk i (1 : CoprodI G)) w ↔
      i ≠ w.1 ∧ ∃ a : G i, Vertex.mk w.1 (of a) = w := by
  constructor
  · rintro ⟨hiw, g, hgi, hgw⟩
    refine ⟨hiw, ?_⟩
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp
      (show g ∈ (of (M := G) (i := i)).range by simpa using mk_eq_mk_iff.mp hgi)
    exact ⟨a, by rw [ha]; exact hgw⟩
  · rintro ⟨hiw, a, haw⟩
    exact ⟨hiw, of a, (mk_of_eq_mk_one a), haw⟩

end BassSerre
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre"

end GroupTheory
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

open Subgroup MulAction SimpleGraph Monoid

namespace GroupTheory

namespace GraphTransversal

def WalkConnected {V : Type*} (T : SimpleGraph V) (s : Set V) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, ∃ p : T.Walk v w, ∀ x ∈ p.support, x ∈ s

structure IsConnectedTransversal {V : Type*} (T : SimpleGraph V) (Γ : Type*) [Group Γ]
    [MulAction Γ V] (D : Set V) : Prop where

  walkConnected : WalkConnected T D

  eq_of_mem_orbit : ∀ v ∈ D, ∀ w ∈ D, v ∈ orbit Γ w → v = w

  exists_mem_orbit : ∀ u : V, ∃ v ∈ D, v ∈ orbit Γ u

variable {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]

theorem walkConnected_singleton (T : SimpleGraph V) (v₀ : V) : WalkConnected T {v₀} := by
  intro v hv w hw
  rw [Set.mem_singleton_iff] at hv hw
  subst hv; subst hw
  exact ⟨Walk.nil, by simp⟩

theorem WalkConnected.insert_of_adj {s : Set V} (hs : WalkConnected T s) {v w : V}
    (hv : v ∈ s) (hadj : T.Adj v w) : WalkConnected T (insert w s) := by
  have key : ∀ x ∈ insert w s, ∃ p : T.Walk v x, ∀ y ∈ p.support, y ∈ insert w s := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · refine ⟨Walk.cons hadj Walk.nil, fun y hy => ?_⟩
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact Set.mem_insert_of_mem _ hv
      · exact Set.mem_insert _ _
    · obtain ⟨p, hp⟩ := hs v hv x hx
      exact ⟨p, fun y hy => Set.mem_insert_of_mem _ (hp y hy)⟩
  intro a ha b hb
  obtain ⟨p, hp⟩ := key a ha
  obtain ⟨q, hq⟩ := key b hb
  refine ⟨p.reverse.append q, fun y hy => ?_⟩
  rw [Walk.support_append, List.mem_append] at hy
  rcases hy with hy | hy
  · rw [Walk.support_reverse, List.mem_reverse] at hy
    exact hp y hy
  · exact hq y (List.mem_of_mem_tail hy)

theorem walkConnected_sUnion {c : Set (Set V)} (hchain : IsChain (· ⊆ ·) c)
    (hwc : ∀ s ∈ c, WalkConnected T s) : WalkConnected T (⋃₀ c) := by
  rintro v ⟨s, hs, hvs⟩ w ⟨t, ht, hwt⟩
  rcases hchain.total hs ht with hst | hts
  · obtain ⟨p, hp⟩ := hwc t ht v (hst hvs) w hwt
    exact ⟨p, fun x hx => Set.mem_sUnion.mpr ⟨t, ht, hp x hx⟩⟩
  · obtain ⟨p, hp⟩ := hwc s hs v hvs w (hts hwt)
    exact ⟨p, fun x hx => Set.mem_sUnion.mpr ⟨s, hs, hp x hx⟩⟩

private theorem mem_orbit_symm' {a b : V} (h : a ∈ orbit Γ b) : b ∈ orbit Γ a := by
  obtain ⟨γ, rfl⟩ := h
  exact ⟨γ⁻¹, inv_smul_smul γ b⟩

theorem eq_of_mem_orbit_sUnion {c : Set (Set V)} (hchain : IsChain (· ⊆ ·) c)
    (hinj : ∀ s ∈ c, ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w) :
    ∀ v ∈ ⋃₀ c, ∀ w ∈ ⋃₀ c, v ∈ orbit Γ w → v = w := by
  rintro v ⟨s, hs, hvs⟩ w ⟨t, ht, hwt⟩ hvw
  rcases hchain.total hs ht with hst | hts
  · exact hinj t ht v (hst hvs) w hwt hvw
  · exact hinj s hs v hvs w (hts hwt) hvw

theorem eq_of_mem_orbit_insert {s : Set V}
    (hs : ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w) {w : V}
    (hw : ¬∃ v ∈ s, v ∈ orbit Γ w) :
    ∀ v ∈ insert w s, ∀ v' ∈ insert w s, v ∈ orbit Γ v' → v = v' := by
  intro v hv v' hv' hvv'
  rcases Set.mem_insert_iff.mp hv with rfl | hvs <;>
    rcases Set.mem_insert_iff.mp hv' with rfl | hv's
  · rfl
  · exact absurd ⟨v', hv's, mem_orbit_symm' hvv'⟩ hw
  · exact absurd ⟨v, hvs, hvv'⟩ hw
  · exact hs v hvs v' hv's hvv'

theorem exists_adj_of_walk (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    {s : Set V} {a b : V} (p : T.Walk a b) :
    (∃ v ∈ s, v ∈ orbit Γ a) → (¬∃ v ∈ s, v ∈ orbit Γ b) →
      ∃ v ∈ s, ∃ w, T.Adj v w ∧ ¬∃ v' ∈ s, v' ∈ orbit Γ w := by
  induction p with
  | nil => exact fun ha hb => absurd ha hb
  | @cons a c b hac p ih =>
    intro ha hb
    by_cases hc : ∃ v ∈ s, v ∈ orbit Γ c
    · exact ih hc hb
    · obtain ⟨v, hvs, γ, hγ⟩ := ha
      refine ⟨v, hvs, γ • c, ?_, ?_⟩
      · rw [← hγ]
        exact hsmul γ hac
      · rintro ⟨v', hv's, hv'⟩
        rw [MulAction.orbit_smul] at hv'
        exact hc ⟨v', hv's, hv'⟩

theorem exists_isConnectedTransversal
    (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    (hpre : T.Preconnected) (v₀ : V) :
    ∃ D : Set V, v₀ ∈ D ∧ IsConnectedTransversal T Γ D := by
  obtain ⟨D, h0, h1, h2, h3⟩ := SimpleGraph.exists_walkConnected_transversal_of_preconnected hsmul hpre v₀
  exact ⟨D, h0, ⟨h1, h2, h3⟩⟩

variable {D : Set V}

noncomputable def orbitRepr (hD : IsConnectedTransversal T Γ D) (v : V) : V :=
  (hD.exists_mem_orbit v).choose

theorem orbitRepr_mem (hD : IsConnectedTransversal T Γ D) (v : V) : orbitRepr hD v ∈ D :=
  (hD.exists_mem_orbit v).choose_spec.1

theorem orbitRepr_mem_orbit (hD : IsConnectedTransversal T Γ D) (v : V) :
    orbitRepr hD v ∈ orbit Γ v :=
  (hD.exists_mem_orbit v).choose_spec.2

noncomputable def transl (hD : IsConnectedTransversal T Γ D) (v : V) : Γ :=
  (orbitRepr_mem_orbit hD v).choose⁻¹

theorem transl_smul_orbitRepr (hD : IsConnectedTransversal T Γ D) (v : V) :
    transl hD v • orbitRepr hD v = v :=
  inv_smul_eq_iff.mpr (orbitRepr_mem_orbit hD v).choose_spec.symm

theorem orbitRepr_eq_self (hD : IsConnectedTransversal T Γ D) {v : V} (hv : v ∈ D) :
    orbitRepr hD v = v :=
  hD.eq_of_mem_orbit _ (orbitRepr_mem hD v) _ hv (orbitRepr_mem_orbit hD v)

theorem orbitRepr_smul (hD : IsConnectedTransversal T Γ D) (γ : Γ) (v : V) :
    orbitRepr hD (γ • v) = orbitRepr hD v := by
  refine hD.eq_of_mem_orbit _ (orbitRepr_mem hD _) _ (orbitRepr_mem hD _) ?_
  rw [MulAction.orbit_eq_iff.mpr (orbitRepr_mem_orbit hD v), ← MulAction.orbit_smul γ v]
  exact orbitRepr_mem_orbit hD (γ • v)

theorem eq_of_smul_eq_smul_of_free (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1)
    {γ γ' : Γ} {v : V} (h : γ • v = γ' • v) : γ = γ' := by
  have h1 : (γ'⁻¹ * γ) • v = v := by rw [mul_smul, h, inv_smul_smul]
  have h2 := hfree _ _ h1
  rwa [inv_mul_eq_one, eq_comm] at h2

theorem transl_eq_one (hD : IsConnectedTransversal T Γ D)
    (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) {v : V} (hv : v ∈ D) :
    transl hD v = 1 := by
  apply hfree _ v
  have h := transl_smul_orbitRepr hD v
  rwa [orbitRepr_eq_self hD hv] at h

theorem mem_of_transl_eq_one (hD : IsConnectedTransversal T Γ D) {v : V}
    (h : transl hD v = 1) : v ∈ D := by
  have h1 := transl_smul_orbitRepr hD v
  rw [h, one_smul] at h1
  rw [← h1]
  exact orbitRepr_mem hD v

theorem transl_smul (hD : IsConnectedTransversal T Γ D)
    (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (γ : Γ) (v : V) :
    transl hD (γ • v) = γ * transl hD v := by
  refine eq_of_smul_eq_smul_of_free hfree (v := orbitRepr hD v) ?_
  rw [mul_smul, transl_smul_orbitRepr, ← orbitRepr_smul hD γ v, transl_smul_orbitRepr]

end GraphTransversal
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

namespace BassSerre

open GraphTransversal

variable {G : Fin 2 → Type*} [∀ i, Group (G i)] {H : Subgroup (CoprodI G)}
  {D : Set (Vertex G)}

theorem smul_adj_subgroup (η : H) {v w : Vertex G} (h : (graph G).Adj v w) :
    (graph G).Adj (η • v) (η • w) :=
  smul_adj (η : CoprodI G) h

theorem exists_transversal (H : Subgroup (CoprodI G)) (v₀ : Vertex G) :
    ∃ D : Set (Vertex G), v₀ ∈ D ∧ IsConnectedTransversal (graph G) H D :=
  GraphTransversal.exists_isConnectedTransversal
    (fun η {_ _} h => smul_adj_subgroup η h) connected.preconnected v₀

theorem forall_smul_eq_of_forall_mem
    (hfree : ∀ h ∈ H, ∀ v : Vertex G, h • v = v → h = 1) :
    ∀ (η : H) (v : Vertex G), η • v = v → η = 1 := fun η v hv =>
  Subtype.ext (hfree (η : CoprodI G) η.2 v hv)

noncomputable def edgeGen (hD : IsConnectedTransversal (graph G) H D) (g : CoprodI G) : H :=
  (transl hD (Vertex.mk 0 g))⁻¹ * transl hD (Vertex.mk 1 g)

theorem transl_mk_one_eq (hD : IsConnectedTransversal (graph G) H D) (g : CoprodI G) :
    transl hD (Vertex.mk 1 g) = transl hD (Vertex.mk 0 g) * edgeGen hD g :=
  (mul_inv_cancel_left _ _).symm

theorem transl_mk_mul (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) (η : H) (i : Fin 2)
    (g : CoprodI G) :
    transl hD (Vertex.mk i ((η : CoprodI G) * g)) = η * transl hD (Vertex.mk i g) :=
  transl_smul hD hfree η (Vertex.mk i g)

theorem edgeGen_smul (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) (η : H) (g : CoprodI G) :
    edgeGen hD ((η : CoprodI G) * g) = edgeGen hD g := by
  show (transl hD (Vertex.mk 0 ((η : CoprodI G) * g)))⁻¹ *
      transl hD (Vertex.mk 1 ((η : CoprodI G) * g)) =
    (transl hD (Vertex.mk 0 g))⁻¹ * transl hD (Vertex.mk 1 g)
  rw [transl_mk_mul hD hfree, transl_mk_mul hD hfree]
  group

theorem edgeGen_eq_one_iff (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) (g : CoprodI G) :
    edgeGen hD g = 1 ↔ ∃ η : H, Vertex.mk 0 ((η : CoprodI G) * g) ∈ D ∧
      Vertex.mk 1 ((η : CoprodI G) * g) ∈ D := by
  constructor
  · intro h
    have hτ : transl hD (Vertex.mk 1 g) = transl hD (Vertex.mk 0 g) := by
      rw [transl_mk_one_eq hD g, h, mul_one]
    refine ⟨(transl hD (Vertex.mk 0 g))⁻¹, ?_, ?_⟩
    · exact mem_of_transl_eq_one hD
        (by rw [transl_mk_mul hD hfree]; exact inv_mul_cancel _)
    · exact mem_of_transl_eq_one hD
        (by rw [transl_mk_mul hD hfree, hτ]; exact inv_mul_cancel _)
  · rintro ⟨η, h0, h1⟩
    have e0 := transl_eq_one hD hfree h0
    have e1 := transl_eq_one hD hfree h1
    rw [transl_mk_mul hD hfree] at e0 e1
    show (transl hD (Vertex.mk 0 g))⁻¹ * transl hD (Vertex.mk 1 g) = 1
    rw [(inv_eq_of_mul_eq_one_right e0).symm, (inv_eq_of_mul_eq_one_right e1).symm]
    group

theorem inv_mul_transl_mem_closure (hD : IsConnectedTransversal (graph G) H D)
    {v w : Vertex G} (hadj : (graph G).Adj v w) :
    (transl hD v)⁻¹ * transl hD w ∈ Subgroup.closure (Set.range (edgeGen hD)) := by
  obtain ⟨hne, g, hgv, hgw⟩ := hadj
  rw [← hgv, ← hgw]
  rcases (by decide : ∀ a b : Fin 2, a ≠ b → a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) v.1 w.1 hne with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact Subgroup.subset_closure (Set.mem_range_self g)
  · rw [h1, h2]
    have hkey : (transl hD (Vertex.mk 1 g))⁻¹ * transl hD (Vertex.mk 0 g) =
        (edgeGen hD g)⁻¹ := by
      show _ = ((transl hD (Vertex.mk 0 g))⁻¹ * transl hD (Vertex.mk 1 g))⁻¹
      group
    rw [hkey]
    exact (Subgroup.closure _).inv_mem (Subgroup.subset_closure (Set.mem_range_self g))

theorem inv_mul_transl_mem_closure_of_walk (hD : IsConnectedTransversal (graph G) H D)
    {a b : Vertex G} (p : (graph G).Walk a b) :
    (transl hD a)⁻¹ * transl hD b ∈ Subgroup.closure (Set.range (edgeGen hD)) := by
  induction p with
  | nil =>
    rw [inv_mul_cancel]
    exact (Subgroup.closure _).one_mem
  | @cons a c b hac p ih =>
    have key : (transl hD a)⁻¹ * transl hD b =
        ((transl hD a)⁻¹ * transl hD c) * ((transl hD c)⁻¹ * transl hD b) := by group
    rw [key]
    exact (Subgroup.closure _).mul_mem (inv_mul_transl_mem_closure hD hac) ih

theorem transl_mem_closure (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) (v : Vertex G) :
    transl hD v ∈ Subgroup.closure (Set.range (edgeGen hD)) := by
  obtain ⟨d, hd, -⟩ := hD.exists_mem_orbit v
  obtain ⟨p⟩ := connected.preconnected d v
  have h := inv_mul_transl_mem_closure_of_walk hD p
  rwa [transl_eq_one hD hfree hd, inv_one, one_mul] at h

theorem closure_range_edgeGen (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ (η : H) (v : Vertex G), η • v = v → η = 1) :
    Subgroup.closure (Set.range (edgeGen hD)) = ⊤ := by
  rw [eq_top_iff]
  intro η _
  obtain ⟨d, hd, -⟩ := hD.exists_mem_orbit (Vertex.mk 0 1)
  have h1 : transl hD (η • d) = η := by
    have h1' := transl_smul hD hfree η d
    rw [transl_eq_one hD hfree hd, mul_one] at h1'
    exact h1'
  rw [← h1]
  exact transl_mem_closure hD hfree _

theorem closure_range_edgeGen_of_forall_mem (hD : IsConnectedTransversal (graph G) H D)
    (hfree : ∀ h ∈ H, ∀ v : Vertex G, h • v = v → h = 1) :
    Subgroup.closure (Set.range (edgeGen hD)) = ⊤ :=
  closure_range_edgeGen hD (forall_smul_eq_of_forall_mem hfree)

end BassSerre
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

end GroupTheory
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

open Subgroup MulAction SimpleGraph Monoid

namespace GroupTheory

namespace OrbifoldBound

open BassSerre GraphTransversal

variable {G : Fin 2 → Type*} [∀ i, Group (G i)]

abbrev ComponentOrbits (H : Subgroup (CoprodI G)) (i : Fin 2) : Type _ :=
  orbitRel.Quotient H (CoprodI G ⧸ (CoprodI.of (M := G) (i := i)).range)

def vertexToSigma (H : Subgroup (CoprodI G)) (v : Vertex G) :
    Σ i : Fin 2, ComponentOrbits H i :=
  ⟨v.1, Quotient.mk'' v.2⟩

theorem vertexToSigma_smul (H : Subgroup (CoprodI G)) (η : H) (v : Vertex G) :
    vertexToSigma H ((η : CoprodI G) • v) = vertexToSigma H v := by
  obtain ⟨i, x⟩ := v
  show (⟨i, Quotient.mk'' ((η : CoprodI G) • x)⟩ : Σ i, ComponentOrbits H i)
    = ⟨i, Quotient.mk'' x⟩
  refine congrArg (Sigma.mk i) (Quotient.sound' ?_)
  exact mem_orbit_iff.mpr ⟨η, rfl⟩

theorem vertexToSigma_eq_of_mem_orbit (H : Subgroup (CoprodI G)) {v w : Vertex G}
    (hvw : v ∈ orbit H w) : vertexToSigma H v = vertexToSigma H w := by
  obtain ⟨η, hη⟩ := hvw
  rw [← hη]
  exact vertexToSigma_smul H η w

def sigmaToVertexOrbit (H : Subgroup (CoprodI G)) (p : Σ i : Fin 2, ComponentOrbits H i) :
    orbitRel.Quotient H (Vertex G) :=
  Quotient.liftOn' p.2
    (fun x => Quotient.mk'' (⟨p.1, x⟩ : Vertex G)) fun x y hxy => by
      obtain ⟨η, hη⟩ : x ∈ orbit H y := hxy
      refine Quotient.sound' (mem_orbit_iff.mpr ⟨η, ?_⟩)
      show (⟨p.1, (η : CoprodI G) • y⟩ : Vertex G) = ⟨p.1, x⟩
      rw [show (η : CoprodI G) • y = x from hη]

def vertexOrbitEquivSigma (H : Subgroup (CoprodI G)) :
    orbitRel.Quotient H (Vertex G) ≃ Σ i : Fin 2, ComponentOrbits H i where
  toFun q := Quotient.liftOn' q (vertexToSigma H)
    fun _ _ h => vertexToSigma_eq_of_mem_orbit H h
  invFun := sigmaToVertexOrbit H
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h v =>
      obtain ⟨i, x⟩ := v
      rfl
  right_inv p := by
    obtain ⟨i, ω⟩ := p
    induction ω using Quotient.inductionOn' with
    | h x => rfl

section Bridge

variable {H : Subgroup (CoprodI G)} {D : Set (Vertex G)} (hD : IsConnectedTransversal (graph G) H D)

theorem transl_smul_orbitRepr' (v : Vertex G) : ((transl hD v : H) : CoprodI G) • orbitRepr hD v = v :=
  transl_smul_orbitRepr hD v

theorem orbitRepr_smul' (η : H) (v : Vertex G) :
    orbitRepr hD ((η : CoprodI G) • v) = orbitRepr hD v :=
  orbitRepr_smul hD η v

theorem exists_transl_smul (η : H) (v : Vertex G) :
    ∃ s : H, (s : CoprodI G) • orbitRepr hD v = orbitRepr hD v ∧
      transl hD ((η : CoprodI G) • v) = η * transl hD v * s := by
  refine ⟨(transl hD v)⁻¹ * η⁻¹ * transl hD ((η : CoprodI G) • v), ?_, by group⟩
  have h1 : ((transl hD ((η : CoprodI G) • v) : H) : CoprodI G) • orbitRepr hD v = (η : CoprodI G) • v := by
    have h := transl_smul_orbitRepr' hD ((η : CoprodI G) • v)
    rwa [orbitRepr_smul'] at h
  have h2 := transl_smul_orbitRepr' hD v
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, mul_smul, mul_smul, h1,
    inv_smul_smul, inv_smul_eq_iff]
  exact h2.symm

theorem transl_smul_self_of_mem {v : Vertex G} (hv : v ∈ D) : ((transl hD v : H) : CoprodI G) • v = v := by
  have h := transl_smul_orbitRepr' hD v
  rwa [orbitRepr_eq_self hD hv] at h

end Bridge
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

section Characters

variable (H : Subgroup (CoprodI G)) (K : Type*) [Field K]

theorem apply_eq_zero_of_smul_eq (hK : ∀ i, (Nat.card (G i) : K) ≠ 0) (φ : Additive H →+ K)
    (η : H) (v : Vertex G) (hfix : (η : CoprodI G) • v = v) : φ (Additive.ofMul η) = 0 := by
  obtain ⟨i, x⟩ := v
  induction x using QuotientGroup.induction_on with | H g =>
  have hmem : g⁻¹ * (η : CoprodI G) * g ∈ (CoprodI.of (M := G) (i := i)).range :=
    smul_eq_self_iff.mp hfix
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
  have hpow : (η : CoprodI G) ^ Nat.card (G i) = 1 := by
    have h1 : (g⁻¹ * (η : CoprodI G) * g) ^ Nat.card (G i) = 1 := by
      rw [← ha, ← map_pow, pow_card_eq_one', map_one]
    have h2 : g⁻¹ * (η : CoprodI G) ^ Nat.card (G i) * g⁻¹⁻¹ = 1 := by
      rw [← conj_pow, inv_inv]; exact h1
    have h3 : (η : CoprodI G) ^ Nat.card (G i)
        = g * (g⁻¹ * (η : CoprodI G) ^ Nat.card (G i) * g⁻¹⁻¹) * g⁻¹ := by
      group
    rw [h3, h2, mul_one, mul_inv_cancel]
  have hpow' : η ^ Nat.card (G i) = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hpow)
  have key : (Nat.card (G i) : K) * φ (Additive.ofMul η) = 0 := by
    rw [← nsmul_eq_mul, ← map_nsmul, ← ofMul_pow, hpow', ofMul_one, map_zero]
  exact (mul_eq_zero.mp key).resolve_left (hK i)

variable {H} {D : Set (Vertex G)} (hK : ∀ i, (Nat.card (G i) : K) ≠ 0) (φ : Additive H →+ K)
  (hD : IsConnectedTransversal (graph G) H D)
include hK

theorem apply_transl_eq_zero_of_mem {v : Vertex G} (hv : v ∈ D) : φ (Additive.ofMul (transl hD v)) = 0 :=
  apply_eq_zero_of_smul_eq H K hK φ _ v (transl_smul_self_of_mem hD hv)

theorem apply_transl_smul (η : H) (v : Vertex G) :
    φ (Additive.ofMul (transl hD ((η : CoprodI G) • v)))
      = φ (Additive.ofMul η) + φ (Additive.ofMul (transl hD v)) := by
  obtain ⟨s, hs, heq⟩ := exists_transl_smul hD η v
  rw [heq, ofMul_mul, ofMul_mul, map_add, map_add, apply_eq_zero_of_smul_eq H K hK φ s _ hs,
    add_zero]

theorem apply_edgeGen_smul (η : H) (g : CoprodI G) :
    φ (Additive.ofMul (edgeGen hD ((η : CoprodI G) * g))) = φ (Additive.ofMul (edgeGen hD g)) := by
  show φ (Additive.ofMul ((transl hD (Vertex.mk 0 ((η : CoprodI G) * g)))⁻¹
      * transl hD (Vertex.mk 1 ((η : CoprodI G) * g))))
    = φ (Additive.ofMul ((transl hD (Vertex.mk 0 g))⁻¹ * transl hD (Vertex.mk 1 g)))
  have h0 : Vertex.mk 0 ((η : CoprodI G) * g) = (η : CoprodI G) • Vertex.mk 0 g := rfl
  have h1 : Vertex.mk 1 ((η : CoprodI G) * g) = (η : CoprodI G) • Vertex.mk 1 g := rfl
  rw [h0, h1, ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, map_add, map_add, map_neg, map_neg,
    apply_transl_smul K hK φ hD, apply_transl_smul K hK φ hD]
  ring

theorem apply_edgeGen_eq_zero_of_mem {g : CoprodI G}
    (h0 : Vertex.mk 0 g ∈ D) (h1 : Vertex.mk 1 g ∈ D) : φ (Additive.ofMul (edgeGen hD g)) = 0 := by
  show φ (Additive.ofMul ((transl hD (Vertex.mk 0 g))⁻¹ * transl hD (Vertex.mk 1 g))) = 0
  rw [ofMul_mul, ofMul_inv, map_add, map_neg, apply_transl_eq_zero_of_mem K hK φ hD h0,
    apply_transl_eq_zero_of_mem K hK φ hD h1, neg_zero, add_zero]

omit hK in
theorem apply_eq_zero_of_mem_closure {S : Set H} (hS : ∀ s ∈ S, φ (Additive.ofMul s) = 0) {x : H}
    (hx : x ∈ Subgroup.closure S) : φ (Additive.ofMul x) = 0 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => rw [ofMul_one, map_zero]
  | mul y z _ _ hy hz => rw [ofMul_mul, map_add, hy, hz, add_zero]
  | inv y _ hy => rw [ofMul_inv, map_neg, hy, neg_zero]

theorem eq_zero_of_forall_edgeGen {v₀ : Vertex G}
    (hv₀ : v₀ ∈ D) (hφ : ∀ g : CoprodI G, φ (Additive.ofMul (edgeGen hD g)) = 0) : φ = 0 := by
  have hcl : ∀ x ∈ Subgroup.closure (Set.range (edgeGen hD)), φ (Additive.ofMul x) = 0 :=
    fun x hx => apply_eq_zero_of_mem_closure K φ (by rintro _ ⟨g, rfl⟩; exact hφ g) hx
  have htransl : ∀ v : Vertex G, φ (Additive.ofMul (transl hD v)) = 0 := by
    intro v
    obtain ⟨p⟩ := connected.preconnected v₀ v
    have h := hcl _ (inv_mul_transl_mem_closure_of_walk hD p)
    rw [ofMul_mul, ofMul_inv, map_add, map_neg, apply_transl_eq_zero_of_mem K hK φ hD hv₀,
      neg_zero, zero_add] at h
    exact h
  ext x
  have h := apply_transl_smul K hK φ hD (Additive.toMul x) v₀
  rw [htransl, htransl, add_zero] at h
  exact h.symm

end Characters
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

end OrbifoldBound
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

end GroupTheory
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

namespace GroupTheory

namespace OrbifoldBound

open BassSerre GraphTransversal

variable {G : Fin 2 → Type*} [∀ i, Group (G i)] (H : Subgroup (CoprodI G))

abbrev EdgeOrbits : Type _ := orbitRel.Quotient H (CoprodI G)

def edgeOrbitsEquiv : EdgeOrbits H ≃ CoprodI G ⧸ H :=
  (Quotient.congrRight (r := orbitRel H (CoprodI G)) (r' := QuotientGroup.rightRel H) (fun x y => by
      rw [QuotientGroup.rightRel_apply]
      try rfl)).trans
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)

theorem card_edgeOrbits : Nat.card (EdgeOrbits H) = H.index := by
  rw [Nat.card_congr (edgeOrbitsEquiv H), Subgroup.index]

theorem finite_edgeOrbits [H.FiniteIndex] : Finite (EdgeOrbits H) :=
  Finite.of_equiv _ (edgeOrbitsEquiv H).symm

def edgeToComponent (i : Fin 2) : EdgeOrbits H → ComponentOrbits H i :=
  Quotient.map' (fun g : CoprodI G => (QuotientGroup.mk g :
      CoprodI G ⧸ (CoprodI.of (M := G) (i := i)).range)) (fun a b hab => by
    obtain ⟨η, rfl⟩ := hab
    exact ⟨η, rfl⟩)

theorem edgeToComponent_surjective (i : Fin 2) : Function.Surjective (edgeToComponent H i) := by
  intro c
  induction c using Quotient.inductionOn' with | h x =>
  induction x using QuotientGroup.induction_on with | H g =>
  exact ⟨Quotient.mk'' g, rfl⟩

theorem finite_componentOrbits [H.FiniteIndex] (i : Fin 2) : Finite (ComponentOrbits H i) := by
  haveI := finite_edgeOrbits H
  exact Finite.of_surjective _ (edgeToComponent_surjective H i)

variable {H} {D : Set (Vertex G)}

def IsInternal (D : Set (Vertex G)) (c : EdgeOrbits H) : Prop :=
  ∃ g : CoprodI G, Quotient.mk _ g = c ∧ Vertex.mk 0 g ∈ D ∧ Vertex.mk 1 g ∈ D

theorem card_int_add_card_rep [H.FiniteIndex] (D : Set (Vertex G)) :
    Nat.card {c : EdgeOrbits H // IsInternal D c} + Nat.card {c : EdgeOrbits H // ¬ IsInternal D c}
      = H.index := by
  classical
  haveI := finite_edgeOrbits H
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl (IsInternal (H := H) D)), card_edgeOrbits]

theorem exists_smul_eq_of_mk_eq {g g' : CoprodI G}
    (h : (Quotient.mk (orbitRel H (CoprodI G)) g : EdgeOrbits H) = Quotient.mk _ g') :
    ∃ η : H, (η : CoprodI G) * g' = g := by
  obtain ⟨η, hη⟩ : g ∈ orbit H g' := Quotient.exact h
  exact ⟨η, hη⟩

section Ev

variable (K : Type*) [Field K]

noncomputable def ev (hD : IsConnectedTransversal (graph G) H D) : (Additive H →+ K) →ₗ[K] ({c : EdgeOrbits H // ¬ IsInternal D c} → K) where
  toFun φ c := φ (Additive.ofMul (edgeGen hD c.1.out))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_injective (hD : IsConnectedTransversal (graph G) H D) (hK : ∀ i, (Nat.card (G i) : K) ≠ 0)
    {v₀ : Vertex G} (hv₀ : v₀ ∈ D) : Function.Injective (ev K hD) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  apply eq_zero_of_forall_edgeGen K hK φ hD hv₀
  intro g
  by_cases hint : IsInternal D (Quotient.mk _ g : EdgeOrbits H)
  · obtain ⟨g', hg', h0, h1⟩ := hint
    obtain ⟨η, rfl⟩ := exists_smul_eq_of_mk_eq hg'.symm
    rw [apply_edgeGen_smul K hK φ hD]
    exact apply_edgeGen_eq_zero_of_mem K hK φ hD h0 h1
  · have hout : (Quotient.mk _ (Quotient.out (Quotient.mk (orbitRel H (CoprodI G)) g)) : EdgeOrbits H)
        = Quotient.mk _ g := Quotient.out_eq _
    obtain ⟨η, hη⟩ := exists_smul_eq_of_mk_eq hout.symm
    have key := congrFun hφ ⟨Quotient.mk _ g, hint⟩
    change φ (Additive.ofMul (edgeGen hD (Quotient.out (Quotient.mk (orbitRel H (CoprodI G)) g)))) = 0
      at key
    rw [← hη, apply_edgeGen_smul K hK φ hD]
    exact key

theorem finrank_le_card_rep [H.FiniteIndex] (hD : IsConnectedTransversal (graph G) H D)
    (hK : ∀ i, (Nat.card (G i) : K) ≠ 0) {v₀ : Vertex G} (hv₀ : v₀ ∈ D) :
    Module.finrank K (Additive H →+ K) ≤ Nat.card {c : EdgeOrbits H // ¬ IsInternal D c} := by
  classical
  haveI := finite_edgeOrbits H
  haveI : Fintype {c : EdgeOrbits H // ¬ IsInternal D c} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card K]
  exact LinearMap.finrank_le_finrank_of_injective (ev_injective K hD hK hv₀)

end Ev
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

section Count

variable (hD : IsConnectedTransversal (graph G) H D)
include hD

theorem induce_connected {v₀ : Vertex G} (hv₀ : v₀ ∈ D) : ((graph G).induce D).Connected := by
  haveI : Nonempty D := ⟨⟨v₀, hv₀⟩⟩
  refine Connected.mk fun v w => ?_
  obtain ⟨p, hp⟩ := hD.walkConnected v.1 v.2 w.1 w.2
  exact ⟨p.induce D hp⟩

theorem eq_of_internal {g g' : CoprodI G} (η : H) (hη : (η : CoprodI G) * g' = g)
    (h0 : Vertex.mk 0 g ∈ D) (h1 : Vertex.mk 1 g ∈ D)
    (h0' : Vertex.mk 0 g' ∈ D) (h1' : Vertex.mk 1 g' ∈ D) : g = g' := by
  have e0 : Vertex.mk 0 g = Vertex.mk 0 g' :=
    hD.eq_of_mem_orbit _ h0 _ h0' ⟨η, by rw [← hη]; rfl⟩
  have e1 : Vertex.mk 1 g = Vertex.mk 1 g' :=
    hD.eq_of_mem_orbit _ h1 _ h1' ⟨η, by rw [← hη]; rfl⟩
  exact eq_of_mk_eq_mk (by decide) e0 e1

omit hD in

noncomputable def intEdge (c : {c : EdgeOrbits H // IsInternal D c}) : ((graph G).induce D).edgeSet :=
  ⟨s(⟨Vertex.mk 0 c.2.choose, c.2.choose_spec.2.1⟩, ⟨Vertex.mk 1 c.2.choose, c.2.choose_spec.2.2⟩), by
    rw [SimpleGraph.mem_edgeSet]
    exact adj_mk (by decide) _⟩

omit hD in
theorem intEdge_val (c : {c : EdgeOrbits H // IsInternal D c}) :
    ((intEdge c : ((graph G).induce D).edgeSet) : Sym2 D)
      = s(⟨Vertex.mk 0 c.2.choose, c.2.choose_spec.2.1⟩, ⟨Vertex.mk 1 c.2.choose, c.2.choose_spec.2.2⟩) :=
  rfl

theorem intEdge_hits {a b : D} (g : CoprodI G) (ha : Vertex.mk 0 g = a.1) (hb : Vertex.mk 1 g = b.1) :
    ∃ c : {c : EdgeOrbits H // IsInternal D c}, ((intEdge c : ((graph G).induce D).edgeSet) : Sym2 D) = s(a, b) := by
  have h0 : Vertex.mk 0 g ∈ D := by rw [ha]; exact a.2
  have h1 : Vertex.mk 1 g ∈ D := by rw [hb]; exact b.2
  have hint : IsInternal D (Quotient.mk _ g : EdgeOrbits H) := ⟨g, rfl, h0, h1⟩
  refine ⟨⟨_, hint⟩, ?_⟩
  have hspec := hint.choose_spec
  obtain ⟨η, hη⟩ := exists_smul_eq_of_mk_eq hspec.1
  have hcg : hint.choose = g := eq_of_internal hD η hη hspec.2.1 hspec.2.2 h0 h1
  have ea : (⟨Vertex.mk 0 hint.choose, hspec.2.1⟩ : D) = a := Subtype.ext (by
    show Vertex.mk 0 hint.choose = a.1
    rw [hcg]; exact ha)
  have eb : (⟨Vertex.mk 1 hint.choose, hspec.2.2⟩ : D) = b := Subtype.ext (by
    show Vertex.mk 1 hint.choose = b.1
    rw [hcg]; exact hb)
  rw [intEdge_val]
  exact congrArg₂ (fun u v => s(u, v)) ea eb

theorem intEdge_surjective : Function.Surjective (intEdge (H := H) (D := D)) := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with | h x y =>
  have hadj : (graph G).Adj x.1 y.1 := (SimpleGraph.mem_edgeSet _).mp he
  obtain ⟨hne, g, hgx, hgy⟩ := hadj
  have h2 : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rcases h2 x.1.1 with hx | hx <;> rcases h2 y.1.1 with hy | hy
  · exact absurd (hx.trans hy.symm) hne
  · rw [hx] at hgx; rw [hy] at hgy
    obtain ⟨c, hc⟩ := intEdge_hits hD g hgx hgy
    exact ⟨c, Subtype.ext hc⟩
  · rw [hx] at hgx; rw [hy] at hgy
    obtain ⟨c, hc⟩ := intEdge_hits hD g hgy hgx
    exact ⟨c, Subtype.ext (hc.trans Sym2.eq_swap)⟩
  · exact absurd (hx.trans hy.symm) hne

theorem card_D_le [H.FiniteIndex] {v₀ : Vertex G} (hv₀ : v₀ ∈ D) :
    Nat.card D ≤ Nat.card {c : EdgeOrbits H // IsInternal D c} + 1 := by
  haveI := finite_edgeOrbits H
  have h1 := (induce_connected hD hv₀).card_vert_le_card_edgeSet_add_one
  have h2 : Nat.card ((graph G).induce D).edgeSet ≤ Nat.card {c : EdgeOrbits H // IsInternal D c} := by
    first
    | exact Finite.card_le_of_surjective _ (intEdge_surjective hD)
    | exact Nat.card_le_card_of_surjective _ (intEdge_surjective hD)
  omega

theorem card_D_eq [H.FiniteIndex] :
    Nat.card D = Nat.card (ComponentOrbits H 0) + Nat.card (ComponentOrbits H 1) := by
  haveI := fun i => finite_componentOrbits H i
  have e1 : D ≃ orbitRel.Quotient H (Vertex G) :=
    Equiv.ofBijective (fun v => Quotient.mk'' v.1)
      ⟨fun v w h => Subtype.ext (hD.eq_of_mem_orbit _ v.2 _ w.2 (Quotient.exact' h)),
       fun c => by
        induction c using Quotient.inductionOn' with | h u =>
        obtain ⟨v, hvD, hv⟩ := hD.exists_mem_orbit u
        exact ⟨⟨v, hvD⟩, Quotient.sound' hv⟩⟩
  rw [Nat.card_congr (e1.trans (vertexOrbitEquivSigma H)), Nat.card_sigma, Fin.sum_univ_two]

end Count
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

theorem main (H : Subgroup (CoprodI G)) [H.FiniteIndex] (K : Type*) [Field K]
    (hK : ∀ i, (Nat.card (G i) : K) ≠ 0) :
    Module.finrank K (Additive H →+ K) + Nat.card (ComponentOrbits H 0) + Nat.card (ComponentOrbits H 1)
      ≤ H.index + 1 := by
  obtain ⟨D, hv₀, hD⟩ := exists_transversal H (Vertex.mk 0 1)
  have h1 := finrank_le_card_rep K hD hK hv₀
  have h2 := card_int_add_card_rep (H := H) D
  have h3 := card_D_le hD hv₀
  have h4 := card_D_eq hD
  omega

end OrbifoldBound
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

end GroupTheory
p2m_reactivate "P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory.BassSerre P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.GroupTheory"

theorem solution {G : Fin 2 → Type*} [∀ i, Group (G i)]
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex] (K : Type) [Field K]
    (hK : ∀ i, (Nat.card (G i) : K) ≠ 0) :
    Module.finrank K (Additive H →+ K)
      + Nat.card (MulAction.orbitRel.Quotient H
          (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := 0)).range))
      + Nat.card (MulAction.orbitRel.Quotient H
          (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := 1)).range))
      ≤ H.index + 1 :=
  GroupTheory.OrbifoldBound.main H K hK

#print axioms solution

end S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one
end P2MW
export P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one (solution)
