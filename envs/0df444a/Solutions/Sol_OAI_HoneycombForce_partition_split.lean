-- Prove2me | solution 1 for OAI.HoneycombForce.partition_split
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:30:37.991358+00:00
-- url     : https://prove2.me/submissions/2cc4258a-b868-4b61-9c13-901870b2b246

-- Generated from openai/math@1581d4c lean/OAI/Probability/Honeycomb/FreeEnergy.lean:L504-L534
-- (upload_full_project.md Phase 4): solution for node OAI.HoneycombForce.partition_split. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_HoneycombFreeEnergy
import Definitions.Def_OAI_Probability_Honeycomb_FreeEnergy

-- ---- inline helpers from OAI.Probability.Honeycomb.FreeEnergy ----
namespace OAI

/-! Forced honeycomb walks and existence of their fixed-length free energy. -/

noncomputable section
open scoped ENNReal Topology
open Filter

namespace HoneycombForce

theorem mem_neighbors_iff (v w : Vertex) : w ∈ neighbors v ↔ Adj v w := by
  rcases v with ⟨i, j, s⟩
  rcases w with ⟨k, l, t⟩
  cases s <;> cases t <;>
    simp [neighbors, Adj, UpDownAdj, up, down, Vertex.mk.injEq] <;> omega

theorem mem_walkLists_iff (o : Vertex) (n : ℕ) (γ : List Vertex) :
    γ ∈ walkLists o n ↔
      γ.head? = some o ∧ γ.length = n + 1 ∧ γ.IsChain Adj := by
  induction n generalizing o γ with
  | zero =>
      cases γ with
      | nil => simp [walkLists]
      | cons v vs =>
          cases vs with
          | nil => simp [walkLists, eq_comm]
          | cons w ws => simp [walkLists]
  | succ n ih =>
      simp only [walkLists, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨v, hv, xs, hxs, rfl⟩
        obtain ⟨hh, hl, hc⟩ := (ih v xs).mp hxs
        cases xs with
        | nil => simp at hh
        | cons w ws =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst w
            exact ⟨rfl, by simpa using congrArg Nat.succ hl,
              List.isChain_cons_cons.mpr ⟨(mem_neighbors_iff o v).mp hv, hc⟩⟩
      · rintro ⟨hh, hl, hc⟩
        cases γ with
        | nil => simp at hh
        | cons v vs =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst v
            cases vs with
            | nil => simp at hl
            | cons w ws =>
                obtain ⟨how, hws⟩ := List.isChain_cons_cons.mp hc
                refine ⟨w, (mem_neighbors_iff o w).mpr how, w :: ws, ?_, rfl⟩
                apply (ih w (w :: ws)).mpr
                exact ⟨rfl, by simpa using Nat.succ.inj hl, hws⟩

theorem mem_saws_iff (o : Vertex) (n : ℕ) (γ : List Vertex) :
    γ ∈ saws o n ↔ γ.head? = some o ∧ γ.length = n + 1 ∧
      γ.IsChain Adj ∧ γ.Nodup := by
  simp only [saws, Finset.mem_filter, mem_walkLists_iff]
  tauto

theorem rho_pos : 0 < rho := by
  unfold rho
  positivity

theorem rho_nonneg : 0 ≤ rho := rho_pos.le

theorem splitWalk_injective (n : ℕ) : Function.Injective (splitWalk n) := by
  intro γ η h
  have hh := congrArg (fun p : (Σ _ : List Vertex, List Vertex) => p.1 ++ p.2.tail) h
  simpa [splitWalk, List.tail_drop, List.take_append_drop] using hh

theorem endpoint_take {o : Vertex} {γ : List Vertex} {n : ℕ} (hn : n < γ.length) :
    endpoint o (γ.take (n+1)) = γ[n] := by
  simp [endpoint, List.getLastD_eq_getLast?, List.getLast?_take, List.getElem?_eq_getElem hn]

theorem endpoint_drop {o p : Vertex} {γ : List Vertex} {n : ℕ} (hn : n < γ.length) :
    endpoint p (γ.drop n) = endpoint o γ := by
  have hγ : γ ≠ [] := by intro h; simp [h] at hn
  simp [endpoint, List.getLastD_eq_getLast?, List.getLast?_drop, hn.not_ge,
    List.getLast?_eq_some_getLast hγ]

theorem splitWalk_mem {o : Vertex} {n m : ℕ} {γ : List Vertex}
    (hγ : γ ∈ saws o (n+m)) :
    splitWalk n γ ∈ (saws o n).sigma (fun p => saws (endpoint o p) m) := by
  obtain ⟨hh, hl, hc, hnd⟩ := (mem_saws_iff _ _ _).mp hγ
  have hn : n < γ.length := by omega
  simp only [splitWalk, Finset.mem_sigma]
  constructor
  · apply (mem_saws_iff _ _ _).mpr
    refine ⟨?_, ?_, hc.take _, List.Pairwise.take hnd⟩
    · simpa [List.head?_take] using hh
    · simp only [List.length_take, hl]
      omega
  · apply (mem_saws_iff _ _ _).mpr
    refine ⟨?_, ?_, hc.drop _, List.Pairwise.drop hnd⟩
    · rw [endpoint_take hn]
      simp [List.getElem?_eq_getElem hn]
    · simp only [List.length_drop, hl]
      omega

theorem displacement_split {o : Vertex} {n m : ℕ} {γ : List Vertex}
    (hγ : γ ∈ saws o (n+m)) :
    displacement o γ = displacement o (γ.take (n+1)) +
      displacement (endpoint o (γ.take (n+1))) (γ.drop n) := by
  have hn : n < γ.length := by
    have hl := ((mem_saws_iff _ _ _).mp hγ).2.1
    omega
  unfold displacement
  rw [endpoint_drop hn]
  abel

end HoneycombForce

end

end OAI

-- ---- hoisted node ----
open OAI OAI.HoneycombForce
open scoped ENNReal Topology
open Filter

theorem solution (o : Vertex) (e : ℂ) (s : ℝ) (n m : ℕ) :
    partition o e s (n+m) ≤ ∑ p ∈ saws o n,
      (rho ^ n * Real.exp (s * projection e (displacement o p))) *
        partition (endpoint o p) e s m := by
  let W : (Σ _ : List Vertex, List Vertex) → ℝ := fun p =>
    (rho ^ n * Real.exp (s * projection e (displacement o p.1))) *
      (rho ^ m * Real.exp (s * projection e (displacement (endpoint o p.1) p.2)))
  calc
    partition o e s (n+m) = ∑ γ ∈ saws o (n+m), W (splitWalk n γ) := by
      apply Finset.sum_congr rfl
      intro γ hγ
      dsimp [W, splitWalk]
      rw [displacement_split hγ, pow_add]
      simp only [projection, mul_add, Complex.add_re, Real.exp_add]
      ring
    _ = ∑ p ∈ (saws o (n+m)).image (splitWalk n), W p := by
      exact (Finset.sum_image (fun _ _ _ _ h => splitWalk_injective n h)).symm
    _ ≤ ∑ p ∈ (saws o n).sigma (fun p => saws (endpoint o p) m), W p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
        exact splitWalk_mem hγ
      · intro p _ _
        exact mul_nonneg
          (mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le)
          (mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le)
    _ = _ := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro p _
      simp [W, partition, Finset.mul_sum]
