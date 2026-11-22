-- Prove2me | solution 1 for Monotonicity_Theorem.exception_list
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:42:54.854964+00:00
-- url     : https://prove2.me/submissions/b1bdc4a4-3cda-4efa-a64a-f8edfb76cd64

import Definitions.Def_Monotonicity_Theorem_Framework

open Monotonicity_Theorem

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {A : Set (Power R 1)} (hA : FiniteUnionOfPointsAndIntervals D A) :
    exists E : List R, forall x : Power R 1, A x ->
      Power.coord1 x ∈ E \/
      exists a b : Endpoint R, openInterval D a b x /\
        (forall y : Power R 1, openInterval D a b y -> A y) /\
        (forall v : R, a = Endpoint.finite v -> v ∈ E) /\
        (forall v : R, b = Endpoint.finite v -> v ∈ E) := by
  induction hA with
  | empty =>
    refine ⟨[], fun x hx => ?_⟩
    cases hx
  | point a0 =>
    refine ⟨[a0], fun x hx => ?_⟩
    have h : Power.coord1 x = a0 := hx
    exact Or.inl (by rw [h]; exact List.Mem.head _)
  | interval a0 b0 =>
    cases a0 with
    | negInf =>
      cases b0 with
      | negInf =>
        refine ⟨[], fun x hx => ?_⟩
        refine Or.inr ⟨Endpoint.negInf, Endpoint.negInf, hx, fun y hy => hy, ?_, ?_⟩
        · intro v hv
          cases hv
        · intro v hv
          cases hv
      | finite w =>
        refine ⟨[w], fun x hx => ?_⟩
        refine Or.inr ⟨Endpoint.negInf, Endpoint.finite w, hx, fun y hy => hy, ?_, ?_⟩
        · intro v hv
          cases hv
        · intro v hv
          cases hv
          exact List.Mem.head _
      | posInf =>
        refine ⟨[], fun x hx => ?_⟩
        refine Or.inr ⟨Endpoint.negInf, Endpoint.posInf, hx, fun y hy => hy, ?_, ?_⟩
        · intro v hv
          cases hv
        · intro v hv
          cases hv
    | finite w1 =>
      cases b0 with
      | negInf =>
        refine ⟨[w1], fun x hx => ?_⟩
        refine Or.inr ⟨Endpoint.finite w1, Endpoint.negInf, hx, fun y hy => hy, ?_, ?_⟩
        · intro v hv
          cases hv
          exact List.Mem.head _
        · intro v hv
          cases hv
      | finite w2 =>
        refine ⟨[w1, w2], fun x hx => ?_⟩
        refine Or.inr ⟨Endpoint.finite w1, Endpoint.finite w2, hx, fun y hy => hy, ?_, ?_⟩
        · intro v hv
          have e : w1 = v := by
            cases hv
            rfl
          rw [← e]
          exact List.Mem.head _
        · intro v hv
          have e : w2 = v := by
            cases hv
            rfl
          rw [← e]
          exact List.Mem.tail _ (List.Mem.head _)
      | posInf =>
        refine ⟨[w1], fun x hx => ?_⟩
        refine Or.inr ⟨Endpoint.finite w1, Endpoint.posInf, hx, fun y hy => hy, ?_, ?_⟩
        · intro v hv
          cases hv
          exact List.Mem.head _
        · intro v hv
          cases hv
    | posInf =>
      cases b0 with
      | negInf =>
        refine ⟨[], fun x hx => ?_⟩
        refine Or.inr ⟨Endpoint.posInf, Endpoint.negInf, hx, fun y hy => hy, ?_, ?_⟩
        · intro v hv
          cases hv
        · intro v hv
          cases hv
      | finite w =>
        refine ⟨[w], fun x hx => ?_⟩
        refine Or.inr ⟨Endpoint.posInf, Endpoint.finite w, hx, fun y hy => hy, ?_, ?_⟩
        · intro v hv
          cases hv
        · intro v hv
          cases hv
          exact List.Mem.head _
      | posInf =>
        refine ⟨[], fun x hx => ?_⟩
        refine Or.inr ⟨Endpoint.posInf, Endpoint.posInf, hx, fun y hy => hy, ?_, ?_⟩
        · intro v hv
          cases hv
        · intro v hv
          cases hv
  | union =>
    rename_i A B hA hB ihA ihB
    obtain ⟨EA, hEA⟩ := ihA
    obtain ⟨EB, hEB⟩ := ihB
    refine ⟨EA ++ EB, fun x hx => ?_⟩
    cases hx with
    | inl hxA =>
      obtain hAx := hEA x hxA
      cases hAx with
      | inl hmem =>
        exact Or.inl (List.mem_append.mpr (Or.inl hmem))
      | inr hmem2 =>
        obtain ⟨a, b, hmem, hsub, hL, hR⟩ := hmem2
        refine Or.inr ⟨a, b, hmem, fun y hy => Or.inl (hsub y hy), ?_, ?_⟩
        · intro v hv
          exact List.mem_append.mpr (Or.inl (hL v hv))
        · intro v hv
          exact List.mem_append.mpr (Or.inl (hR v hv))
    | inr hxB =>
      obtain hBx := hEB x hxB
      cases hBx with
      | inl hmem =>
        exact Or.inl (List.mem_append.mpr (Or.inr hmem))
      | inr hmem2 =>
        obtain ⟨a, b, hmem, hsub, hL, hR⟩ := hmem2
        refine Or.inr ⟨a, b, hmem, fun y hy => Or.inr (hsub y hy), ?_, ?_⟩
        · intro v hv
          exact List.mem_append.mpr (Or.inr (hL v hv))
        · intro v hv
          exact List.mem_append.mpr (Or.inr (hR v hv))
