-- Prove2me | solution 1 for HyperCheeger.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T13:03:31.450214+00:00
-- url     : https://prove2.me/submissions/834bf044-af47-4e4e-859d-cbaf233e7d4c

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_conductance
import Definitions.Def_HyperCheeger_Hypergraph_nu2
import Definitions.Def_HyperCheeger_Hypergraph_aeGraph
import Theorems.Thm_HyperCheeger_theorem_3_1
import Theorems.Thm_HyperCheeger_lemma_3_3

section
set_option autoImplicit false

namespace HyperCheeger.Dev.Eq12

open HyperCheeger

/-- A chain of hyperedges of `G` from `x` to `y`, as in `Hypergraph.IsConnected`. -/
def Walk {V : Type} [DecidableEq V] (G : Hypergraph V) (x y : V) : Prop :=
  ∃ (ℓ : ℕ) (e : ℕ → Finset V), 1 ≤ ℓ ∧ (∀ i, 1 ≤ i → i ≤ ℓ → e i ∈ G.edges) ∧
    x ∈ e 1 ∧ y ∈ e ℓ ∧ ∀ i, 1 ≤ i → i < ℓ → (e i ∩ e (i + 1)).Nonempty

theorem walk_trans {V : Type} [DecidableEq V] (G : Hypergraph V) {x y z : V}
    (h1 : Walk G x y) (h2 : Walk G y z) : Walk G x z := by
  obtain ⟨ℓ, e, hℓ, he, hx, hy, hc⟩ := h1
  obtain ⟨m, f, hm, hf, hy', hz, hc'⟩ := h2
  refine ⟨ℓ + m, fun i => if i ≤ ℓ then e i else f (i - ℓ), by omega, ?_, ?_, ?_, ?_⟩
  · intro i hi1 hi2
    by_cases hi : i ≤ ℓ
    · simp only [hi, if_true]; exact he i hi1 hi
    · simp only [hi, if_false]; exact hf (i - ℓ) (by omega) (by omega)
  · simp only [show 1 ≤ ℓ from hℓ, if_true]; exact hx
  · simp only [show ¬ (ℓ + m ≤ ℓ) by omega, if_false, Nat.add_sub_cancel_left]; exact hz
  · intro i hi1 hi2
    by_cases hi : i < ℓ
    · simp only [show i ≤ ℓ by omega, show i + 1 ≤ ℓ by omega, if_true]
      exact hc i hi1 hi
    · by_cases hi' : i = ℓ
      · subst hi'
        simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false,
          show i + 1 - i = 1 by omega]
        exact ⟨y, Finset.mem_inter.mpr ⟨hy, hy'⟩⟩
      · simp only [show ¬ (i ≤ ℓ) by omega, show ¬ (i + 1 ≤ ℓ) by omega, if_false,
          show i + 1 - ℓ = (i - ℓ) + 1 by omega]
        exact hc' (i - ℓ) (by omega) (by omega)

/-- Any two vertices (equal or not) of a hyperedge of `H` are joined by a one-edge chain in the
AE graph. -/
theorem walk_of_mem {V : Type} [DecidableEq V] (H : Hypergraph V) {e : Finset V}
    (he : e ∈ H.edges) {x y : V} (hx : x ∈ e) (hy : y ∈ e) : Walk H.aeGraph x y := by
  -- find `z ∈ e` with `z ≠ x` (if `x = y`), else take `z = y`
  have hcard : 2 ≤ e.card := by
    have h1 : e.card ≠ 1 := H.card_ne_one e he
    have h0 : 0 < e.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  obtain ⟨z, hz, hzx, hzy⟩ : ∃ z ∈ e, z ≠ x ∧ (x ≠ y → z = y) := by
    by_cases hxy : x = y
    · obtain ⟨z, hz, hzx⟩ := Finset.exists_mem_ne hcard x
      exact ⟨z, hz, hzx, fun h => absurd hxy h⟩
    · exact ⟨y, hy, Ne.symm hxy, fun _ => rfl⟩
  have hedge : ({x, z} : Finset V) ∈ H.aeGraph.edges := by
    show ({x, z} : Finset V) ∈ H.edges.biUnion (Finset.powersetCard 2)
    refine Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hx
      · rw [Finset.mem_singleton.mp ht]; exact hz
    · exact Finset.card_pair (Ne.symm hzx)
  refine ⟨1, fun _ => {x, z}, le_refl 1, fun _ _ _ => hedge, by simp, ?_, ?_⟩
  · by_cases hxy : x = y
    · subst hxy; simp
    · rw [hzy hxy]; simp
  · intro i hi1 hi2; omega

theorem aeGraph_isConnected {V : Type} [DecidableEq V] (H : Hypergraph V)
    (hconn : H.IsConnected) : H.aeGraph.IsConnected := by
  intro u v
  obtain ⟨ℓ, e, hℓ, he, hu, hv, hc⟩ := hconn u v
  have key : ∀ k, 1 ≤ k → k ≤ ℓ → ∀ x ∈ e k, Walk H.aeGraph u x := by
    intro k hk1
    induction k with
    | zero => omega
    | succ k ih =>
      intro hk x hx
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · exact walk_of_mem H (he 1 le_rfl hℓ) hu hx
      · obtain ⟨p, hp⟩ := hc k hkpos (by omega)
        rw [Finset.mem_inter] at hp
        exact walk_trans H.aeGraph (ih hkpos (by omega) p hp.1)
          (walk_of_mem H (he (k + 1) hk1 hk) hp.2 hx)
  exact key ℓ hℓ le_rfl v hv

theorem nu2_aeGraph {V : Type} [Fintype V] [DecidableEq V] (H : Hypergraph V) :
    H.aeGraph.nu2 = H.nu2 := by
  unfold Hypergraph.nu2
  rw [(lemma_3_3 H).2.2.2]

end HyperCheeger.Dev.Eq12

namespace HyperCheeger

open HyperCheeger.Dev.Eq12 in
theorem chk_eq_12 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (H : Hypergraph V) (hconn : H.IsConnected) :
    H.nu2 / 2 ≤ H.aeGraph.conductance ∧ H.aeGraph.conductance ≤ Real.sqrt (2 * H.nu2) := by
  have h := theorem_3_1 hV H.aeGraph (lemma_3_3 H).1 (aeGraph_isConnected H hconn)
  rw [nu2_aeGraph] at h
  exact h

end HyperCheeger
end

theorem solution : type_of% @HyperCheeger.chk_eq_12 := @HyperCheeger.chk_eq_12
