-- Prove2me | solution 1 for Monotonicity_Theorem.uniform_pattern_window3
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T00:21:58.396809+00:00
-- url     : https://prove2.me/submissions/5f4f9371-4a20-4a58-9e2a-4eeb2a07348f

import Definitions.Def_Monotonicity_Theorem_Framework2
import Theorems.Thm_Monotonicity_Theorem_infinite_contains_interval_core2

open Monotonicity_Theorem

theorem Monotonicity_Theorem.exception_list {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {A : Set (Power R 1)} (hA : FiniteUnionOfPointsAndIntervals A) :
    ∃ E : List R, ∀ x : Power R 1, A x ->
      Power.coord1 x ∈ E ∨
      ∃ a b : Endpoint R, openInterval a b x ∧
        (∀ y : Power R 1, openInterval a b y → A y) ∧
        (∀ v : R, a = Endpoint.finite v → v ∈ E) ∧
        (∀ v : R, b = Endpoint.finite v → v ∈ E) := by
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

theorem Monotonicity_Theorem.exists_greatest_of_list {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (L : List R) (hNe : L ≠ []) :
    ∃ M : R, M ∈ L ∧ ∀ r : R, r ∈ L → (LT.lt r M ∨ r = M) := by
  induction L with
  | nil => exact absurd rfl hNe
  | cons h t ih =>
    cases t with
    | nil =>
      refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
      intro r hr
      simp at hr
      exact Or.inr hr
    | cons h2 t2 =>
      have hNet : h2 :: t2 ≠ [] := by simp
      obtain ⟨M, hM, hMax⟩ := ih hNet
      have hTri := lt_trichotomy h M
      cases hTri with
      | inl h1 =>
        have hlt := h1
        refine ⟨M, List.mem_cons.mpr (Or.inr hM), ?_⟩
        intro r hr
        cases List.mem_cons.mp hr with
        | inl he =>
          have hlt2 : LT.lt r M := by rw [he]; exact hlt
          exact Or.inl hlt2
        | inr hm => exact hMax r hm
      | inr h23 =>
        cases h23 with
        | inl h1 =>
          have heq := h1
          refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
          intro r hr
          cases List.mem_cons.mp hr with
          | inl he => exact Or.inr he
          | inr hm =>
            have hle := hMax r hm
            cases hle with
            | inl hltRM =>
              have hltRh : LT.lt r h := by rw [←heq] at hltRM; exact hltRM
              exact Or.inl hltRh
            | inr heqRM =>
              exact Or.inr (heqRM.trans heq.symm)
        | inr h1 =>
          have hlt := h1
          refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
          intro r hr
          cases List.mem_cons.mp hr with
          | inl he => exact Or.inr he
          | inr hm =>
            have hle := hMax r hm
            cases hle with
            | inl hltRM => exact Or.inl (lt_trans hltRM hlt)
            | inr heqRM =>
              have hltRh : LT.lt r h := by rw [heqRM]; exact hlt
              exact Or.inl hltRh


theorem Monotonicity_Theorem.exists_least_of_list {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (L : List R) (hNe : L ≠ []) :
    ∃ m : R, m ∈ L ∧ ∀ r : R, r ∈ L → (LT.lt m r ∨ m = r) := by
  induction L with
  | nil => contradiction
  | cons x B ih =>
    by_cases hB : B = []
    · subst hB
      refine ⟨x, List.Mem.head _, fun r hr => ?_⟩
      cases hr with
      | head => exact Or.inr rfl
      | tail _ h => cases h
    · have hBne : B ≠ [] := hB
      obtain ⟨mB, hmBin, hmBlower⟩ := ih hBne
      by_cases hlt : LT.lt x mB
      · refine ⟨x, List.Mem.head _, fun r hr => ?_⟩
        cases hr with
        | head => exact Or.inr rfl
        | tail _ hrB =>
          cases hmBlower r hrB with
          | inl h => exact Or.inl (lt_trans hlt h)
          | inr heq => exact Or.inl (by rw [← heq]; exact hlt)
      · refine ⟨mB, List.Mem.tail _ hmBin, fun r hr => ?_⟩
        cases hr with
        | head =>
          rcases lt_trichotomy x mB with h | heq | h
          · exact absurd h hlt
          · exact Or.inr heq.symm
          · exact Or.inl h
        | tail _ hrB => exact hmBlower r hrB

namespace Monotonicity_Theorem

theorem leftAux11 {R : Type} (x y : Power R 1) :
    Power.left (R := R) (n := 1) (m := 1) (Power.append x y) = x := by
  funext i
  simp [Power.left, Power.append, Fin.append_left]

theorem rightAux11 {R : Type} (x y : Power R 1) :
    Power.right (R := R) (n := 1) (m := 1) (Power.append x y) = y := by
  funext j
  exact Fin.append_right x y j

end Monotonicity_Theorem
theorem Monotonicity_Theorem.above_sign_definable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (J : Set (Power R 1)) (hJ : M.S 1 J) (c : R) :
    M.S 1 (fun y : Power R 1 => J y ∧ ∃ v : Power R 1,
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y v) ∧
      Lt1 (fun _ => c) v) := by
  have hOI : M.S 1 (openInterval (Endpoint.finite c) Endpoint.posInf) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hJw : M.S (1 + 1) (fun q : Power R (1 + 1) =>
      J (fun _ : Fin 1 => q (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))))) :=
    M.reindex_mem (fun _ : Fin 1 => Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))) hJ
  have hGc : M.S (1 + 1) (fun q : Power R (1 + 1) =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q j)) :=
    M.reindex_mem (fun j : Fin (1 + 1) => j) f.graph_mem
  have hOv : M.S (1 + 1) (fun q : Power R (1 + 1) =>
      (openInterval (Endpoint.finite c) Endpoint.posInf)
        (fun _ : Fin 1 => q (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))))) :=
    M.reindex_mem (fun _ : Fin 1 => Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))) hOI
  have hH : M.S 1 (fun y : Power R 1 => ∃ v : Power R 1,
      (fun q : Power R (1 + 1) => J (fun _ : Fin 1 => q (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v) ∧
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (fun j : Fin (1 + 1) => q j))
        (Power.append y v) ∧
      (fun q : Power R (1 + 1) => (openInterval (Endpoint.finite c) Endpoint.posInf)
        (fun _ : Fin 1 => q (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v)) :=
    M.existsLast_mem
      (M.inter_mem hJw (M.inter_mem hGc hOv))
  have heq : (fun y : Power R 1 => ∃ v : Power R 1,
      (fun q : Power R (1 + 1) => J (fun _ : Fin 1 => q (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v) ∧
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (fun j : Fin (1 + 1) => q j))
        (Power.append y v) ∧
      (fun q : Power R (1 + 1) => (openInterval (Endpoint.finite c) Endpoint.posInf)
        (fun _ : Fin 1 => q (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v))
      = (fun y : Power R 1 => J y ∧ ∃ v : Power R 1,
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y v) ∧
        Lt1 (fun _ => c) v) := by
    funext y
    apply propext
    constructor
    · intro ⟨v, hJy, hG, hO⟩
      dsimp only [] at hJy hG hO
      have eX : (fun _ : Fin 1 => (Power.append y v)
          (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)))) = y := by
        funext k
        have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
        rw [k0]
        exact Fin.append_left y v (⟨0, by omega⟩ : Fin 1)
      have eV : (fun _ : Fin 1 => (Power.append y v)
          (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))) = v := by
        funext k
        have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
        rw [k0]
        exact Fin.append_right y v (⟨0, by omega⟩ : Fin 1)
      have eG : (fun j : Fin (1 + 1) => (Power.append y v) j)
          = Power.append y v := rfl
      refine ⟨?_, v, ?_, ?_⟩
      · rw [eX] at hJy
        exact hJy
      · rw [eG] at hG
        exact hG
      · rw [eV] at hO
        have hOv' : Lt1 (fun _ => c) v := hO.left
        exact hOv'
    · intro ⟨hJy, v, hG, hO⟩
      refine ⟨v, ?_, ?_, ?_⟩
      · show J (fun _ : Fin 1 => (Power.append y v)
          (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))))
        have eX : (fun _ : Fin 1 => (Power.append y v)
            (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)))) = y := by
          funext k
          have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
          rw [k0]
          exact Fin.append_left y v (⟨0, by omega⟩ : Fin 1)
        rw [eX]
        exact hJy
      · show FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => (Power.append y v) j)
        have eG : (fun j : Fin (1 + 1) => (Power.append y v) j)
            = Power.append y v := rfl
        rw [eG]
        exact hG
      · show (openInterval (Endpoint.finite c) Endpoint.posInf)
          (fun _ : Fin 1 => (Power.append y v)
            (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))))
        have eV : (fun _ : Fin 1 => (Power.append y v)
            (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))) = v := by
          funext k
          have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
          rw [k0]
          exact Fin.append_right y v (⟨0, by omega⟩ : Fin 1)
        rw [eV]
        have hOv' : LT.lt c (v 0) := hO
        show Endpoint.lt (Endpoint.finite c) (Endpoint.finite (v 0)) ∧
          Endpoint.lt (Endpoint.finite (v 0)) Endpoint.posInf
        exact ⟨hOv', trivial⟩
  rw [heq] at hH
  exact hH

theorem Monotonicity_Theorem.below_sign_definable {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (J : Set (Power R 1)) (hJ : M.S 1 J) (c : R) :
    M.S 1 (fun y : Power R 1 => J y ∧ ∃ v : Power R 1,
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y v) ∧
      Lt1 v (fun _ => c)) := by
  have hOI : M.S 1 (openInterval Endpoint.negInf (Endpoint.finite c)) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hJw : M.S (1 + 1) (fun q : Power R (1 + 1) =>
      J (fun _ : Fin 1 => q (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))))) :=
    M.reindex_mem (fun _ : Fin 1 => Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))) hJ
  have hGc : M.S (1 + 1) (fun q : Power R (1 + 1) =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q j)) :=
    M.reindex_mem (fun j : Fin (1 + 1) => j) f.graph_mem
  have hOv : M.S (1 + 1) (fun q : Power R (1 + 1) =>
      (openInterval Endpoint.negInf (Endpoint.finite c))
        (fun _ : Fin 1 => q (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))))) :=
    M.reindex_mem (fun _ : Fin 1 => Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))) hOI
  have hH : M.S 1 (fun y : Power R 1 => ∃ v : Power R 1,
      (fun q : Power R (1 + 1) => J (fun _ : Fin 1 => q (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v) ∧
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (fun j : Fin (1 + 1) => q j))
        (Power.append y v) ∧
      (fun q : Power R (1 + 1) => (openInterval Endpoint.negInf (Endpoint.finite c))
        (fun _ : Fin 1 => q (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v)) :=
    M.existsLast_mem
      (M.inter_mem hJw (M.inter_mem hGc hOv))
  have heq : (fun y : Power R 1 => ∃ v : Power R 1,
      (fun q : Power R (1 + 1) => J (fun _ : Fin 1 => q (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v) ∧
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (fun j : Fin (1 + 1) => q j))
        (Power.append y v) ∧
      (fun q : Power R (1 + 1) => (openInterval Endpoint.negInf (Endpoint.finite c))
        (fun _ : Fin 1 => q (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v))
      = (fun y : Power R 1 => J y ∧ ∃ v : Power R 1,
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y v) ∧
        Lt1 v (fun _ => c)) := by
    funext y
    apply propext
    constructor
    · intro ⟨v, hJy, hG, hO⟩
      dsimp only [] at hJy hG hO
      have eX : (fun _ : Fin 1 => (Power.append y v)
          (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)))) = y := by
        funext k
        have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
        rw [k0]
        exact Fin.append_left y v (⟨0, by omega⟩ : Fin 1)
      have eV : (fun _ : Fin 1 => (Power.append y v)
          (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))) = v := by
        funext k
        have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
        rw [k0]
        exact Fin.append_right y v (⟨0, by omega⟩ : Fin 1)
      have eG : (fun j : Fin (1 + 1) => (Power.append y v) j)
          = Power.append y v := rfl
      refine ⟨?_, v, ?_, ?_⟩
      · rw [eX] at hJy
        exact hJy
      · rw [eG] at hG
        exact hG
      · rw [eV] at hO
        have hOv' : Lt1 v (fun _ => c) := hO.right
        exact hOv'
    · intro ⟨hJy, v, hG, hO⟩
      refine ⟨v, ?_, ?_, ?_⟩
      · show J (fun _ : Fin 1 => (Power.append y v)
          (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))))
        have eX : (fun _ : Fin 1 => (Power.append y v)
            (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)))) = y := by
          funext k
          have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
          rw [k0]
          exact Fin.append_left y v (⟨0, by omega⟩ : Fin 1)
        rw [eX]
        exact hJy
      · show FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => (Power.append y v) j)
        have eG : (fun j : Fin (1 + 1) => (Power.append y v) j)
            = Power.append y v := rfl
        rw [eG]
        exact hG
      · show (openInterval Endpoint.negInf (Endpoint.finite c))
          (fun _ : Fin 1 => (Power.append y v)
            (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))))
        have eV : (fun _ : Fin 1 => (Power.append y v)
            (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))) = v := by
          funext k
          have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
          rw [k0]
          exact Fin.append_right y v (⟨0, by omega⟩ : Fin 1)
        rw [eV]
        have hOv' : LT.lt (v 0) c := hO
        show Endpoint.lt Endpoint.negInf (Endpoint.finite (v 0)) ∧
          Endpoint.lt (Endpoint.finite (v 0)) (Endpoint.finite c)
        exact ⟨trivial, hOv'⟩
  rw [heq] at hH
  exact hH

namespace Monotonicity_Theorem

-- Left-endpoint side of piece transfer.
theorem alpha_side {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {α : Endpoint R} {M : R} {t0 s0 : R}
    (hαt : Endpoint.lt α (Endpoint.finite t0))
    (hleV : ∀ v : R, α = Endpoint.finite v → (LT.lt v M ∨ v = M))
    (hsM : LT.lt M s0) :
    Endpoint.lt α (Endpoint.finite s0) := by
  cases α with
  | negInf => exact trivial
  | finite v =>
    cases hleV v rfl with
    | inl h => exact lt_trans h hsM
    | inr heq =>
      rw [heq]
      exact hsM
  | posInf => exact False.elim hαt

end Monotonicity_Theorem
theorem Monotonicity_Theorem.left_adjacent_cut {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {A B : Set (Power R 1)}
    (hA : M.S 1 A) (hB : M.S 1 B)
    {c1 p : R} (hlt : LT.lt c1 p)
    (hcov : ∀ x : Power R 1,
      openInterval (Endpoint.finite c1) (Endpoint.finite p) x → A x ∨ B x) :
    ∃ c1' : R, LT.lt c1' p ∧ (LT.lt c1 c1' ∨ c1 = c1') ∧
      ((∀ x : Power R 1,
        openInterval (Endpoint.finite c1') (Endpoint.finite p) x → A x) ∨
       (∀ x : Power R 1,
        openInterval (Endpoint.finite c1') (Endpoint.finite p) x → B x)) := by
  classical
  obtain hFUIA := (M.ominimal A).mp hA
  obtain hFUIB := (M.ominimal B).mp hB
  obtain ⟨EA, hEA⟩ := Monotonicity_Theorem.exception_list hFUIA
  obtain ⟨EB, hEB⟩ := Monotonicity_Theorem.exception_list hFUIB
  set E : List R := (EA ++ EB).filter (fun c => decide (LT.lt c p)) with hEdef
  have hne : E ++ [c1] ≠ [] := by
    intro h
    have hm : c1 ∈ E ++ [c1] :=
      List.mem_append.mpr (Or.inr (List.Mem.head _))
    rw [h] at hm
    exact List.not_mem_nil hm
  obtain ⟨M, hMem, hMax⟩ :=
    Monotonicity_Theorem.exists_greatest_of_list (E ++ [c1]) hne
  have hle : ∀ r : R, r ∈ EA ++ EB → LT.lt r p → (LT.lt r M ∨ r = M) := by
    intro r hr hlt
    exact hMax _ (List.mem_append.mpr (Or.inl (List.mem_filter.mpr
      ⟨hr, by rw [decide_eq_true_eq]; exact hlt⟩)))
  have hMp : LT.lt M p := by
    cases List.mem_append.mp hMem with
    | inl hE =>
      rw [List.mem_filter] at hE
      exact of_decide_eq_true hE.right
    | inr hS =>
      cases hS with
      | head => exact hlt
      | tail _ h => cases h
  have hMc1 : LT.lt c1 M ∨ c1 = M :=
    hMax _ (List.mem_append.mpr (Or.inr (List.Mem.head _)))
  have hsub : ∀ x : Power R 1,
      openInterval (Endpoint.finite M) (Endpoint.finite p) x →
      openInterval (Endpoint.finite c1) (Endpoint.finite p) x := by
    intro x hx
    have hx1 : LT.lt M (Power.coord1 x) := hx.left
    have hx2 : LT.lt (Power.coord1 x) p := hx.right
    show Endpoint.lt (Endpoint.finite c1) (Endpoint.finite (x 0)) ∧
      Endpoint.lt (Endpoint.finite (x 0)) (Endpoint.finite p)
    constructor
    · cases hMc1 with
      | inl h => exact lt_trans h hx1
      | inr heq =>
        rw [heq]
        exact hx1
    · exact hx2
  by_cases hAex : ∃ x : Power R 1,
      openInterval (Endpoint.finite M) (Endpoint.finite p) x ∧ ¬ A x
  · by_cases hBex : ∃ y : Power R 1,
        openInterval (Endpoint.finite M) (Endpoint.finite p) y ∧ ¬ B y
    · obtain ⟨x, hxJ, hxNA⟩ := hAex
      obtain ⟨y, hyJ, hyNB⟩ := hBex
      have hxB : B x := by
        cases hcov x (hsub x hxJ) with
        | inl h => exact absurd h hxNA
        | inr h => exact h
      have hyA : A y := by
        cases hcov y (hsub y hyJ) with
        | inl h => exact h
        | inr h => exact absurd h hyNB
      have hxMx : LT.lt M (Power.coord1 x) := hxJ.left
      have hxp : LT.lt (Power.coord1 x) p := hxJ.right
      have hyM : LT.lt M (Power.coord1 y) := hyJ.left
      have hyp : LT.lt (Power.coord1 y) p := hyJ.right
      -- x's B-piece analysis toward y ∈ B
      have hyB : B y := by
        obtain hBx := hEB x hxB
        cases hBx with
        | inl hmem =>
          have hleM := hle _ (List.mem_append.mpr (Or.inr hmem)) hxp
          cases hleM with
          | inl h => exact False.elim (lt_irrefl M (lt_trans hxMx h))
          | inr heq =>
            rw [heq] at hxMx
            exact False.elim (lt_irrefl M hxMx)
        | inr hpiece =>
          obtain ⟨α, β, hxβ, hsubB, hLcond, hRcond⟩ := hpiece
          have hLE : ∀ v : R, α = Endpoint.finite v → (LT.lt v M ∨ v = M) := by
            intro v hv
            have hvt0 : LT.lt v (Power.coord1 x) := by
              have hleft : Endpoint.lt α (Endpoint.finite (x 0)) := hxβ.left
              rw [hv] at hleft
              exact hleft
            have hvp : LT.lt v p := lt_trans hvt0 hxp
            exact hle _ (List.mem_append.mpr (Or.inr (hLcond v hv))) hvp
          cases β with
          | negInf =>
            have hF : False := hxβ.right
            exact False.elim hF
          | posInf =>
            have hmem : openInterval α Endpoint.posInf y := by
              have hα : Endpoint.lt α (Endpoint.finite (y 0)) :=
                Monotonicity_Theorem.alpha_side hxβ.left hLE hyM
              exact ⟨hα, trivial⟩
            exact hsubB _ hmem
          | finite v =>
            rcases lt_trichotomy v p with hlt | heq | hlt
            · have hvE : v ∈ EB := hRcond v rfl
              have hleM := hle _ (List.mem_append.mpr (Or.inr hvE)) hlt
              have hxv : LT.lt (Power.coord1 x) v := hxβ.right
              cases hleM with
              | inl h =>
                exact False.elim (lt_irrefl M (lt_trans (lt_trans hxMx hxv) h))
              | inr heq2 =>
                rw [heq2] at hxv
                exact False.elim (lt_irrefl M (lt_trans hxMx hxv))
            · have hmem : openInterval α (Endpoint.finite v) y := by
                have hα : Endpoint.lt α (Endpoint.finite (y 0)) :=
                  Monotonicity_Theorem.alpha_side hxβ.left hLE hyM
                have hβ : Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite v) := by
                  rw [heq]
                  exact hyp
                exact ⟨hα, hβ⟩
              exact hsubB _ hmem
            · have hmem : openInterval α (Endpoint.finite v) y := by
                have hα : Endpoint.lt α (Endpoint.finite (y 0)) :=
                  Monotonicity_Theorem.alpha_side hxβ.left hLE hyM
                have hβ : Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite v) :=
                  lt_trans hyp hlt
                exact ⟨hα, hβ⟩
              exact hsubB _ hmem
      -- y's A-piece analysis toward False
      have hFalse : False := by
        obtain hAy := hEA y hyA
        cases hAy with
        | inl hmem =>
          have hleM := hle _ (List.mem_append.mpr (Or.inl hmem)) hyp
          cases hleM with
          | inl h => exact lt_irrefl M (lt_trans hyM h)
          | inr heq =>
            rw [heq] at hyM
            exact lt_irrefl M hyM
        | inr hpiece =>
          obtain ⟨α, β, hyβ, hsubA, hLcond, hRcond⟩ := hpiece
          have hLE : ∀ v : R, α = Endpoint.finite v → (LT.lt v M ∨ v = M) := by
            intro v hv
            have hvt0 : LT.lt v (Power.coord1 y) := by
              have hleft : Endpoint.lt α (Endpoint.finite (y 0)) := hyβ.left
              rw [hv] at hleft
              exact hleft
            have hvp : LT.lt v p := lt_trans hvt0 hyp
            exact hle _ (List.mem_append.mpr (Or.inl (hLcond v hv))) hvp
          cases β with
          | negInf =>
            have hF : False := hyβ.right
            exact hF
          | posInf =>
            have hmem : openInterval α Endpoint.posInf x := by
              have hα : Endpoint.lt α (Endpoint.finite (x 0)) :=
                Monotonicity_Theorem.alpha_side hyβ.left hLE hxMx
              exact ⟨hα, trivial⟩
            exact absurd (hsubA _ hmem) hxNA
          | finite v =>
            rcases lt_trichotomy v p with hlt | heq | hlt
            · have hvE : v ∈ EA := hRcond v rfl
              have hleM := hle _ (List.mem_append.mpr (Or.inl hvE)) hlt
              have hyv : LT.lt (Power.coord1 y) v := hyβ.right
              cases hleM with
              | inl h =>
                exact lt_irrefl M (lt_trans (lt_trans hyM hyv) h)
              | inr heq2 =>
                rw [heq2] at hyv
                exact lt_irrefl M (lt_trans hyM hyv)
            · have hmem : openInterval α (Endpoint.finite v) x := by
                have hα : Endpoint.lt α (Endpoint.finite (x 0)) :=
                  Monotonicity_Theorem.alpha_side hyβ.left hLE hxMx
                have hβ : Endpoint.lt (Endpoint.finite (x 0)) (Endpoint.finite v) := by
                  rw [heq]
                  exact hxp
                exact ⟨hα, hβ⟩
              exact absurd (hsubA _ hmem) hxNA
            · have hmem : openInterval α (Endpoint.finite v) x := by
                have hα : Endpoint.lt α (Endpoint.finite (x 0)) :=
                  Monotonicity_Theorem.alpha_side hyβ.left hLE hxMx
                have hβ : Endpoint.lt (Endpoint.finite (x 0)) (Endpoint.finite v) :=
                  lt_trans hxp hlt
                exact ⟨hα, hβ⟩
              exact absurd (hsubA _ hmem) hxNA
      exact False.elim hFalse
    · refine ⟨M, hMp, hMc1, Or.inr ?_⟩
      intro y hy
      by_contra hyNB
      exact hBex ⟨y, hy, hyNB⟩
  · refine ⟨M, hMp, hMc1, Or.inl ?_⟩
    intro x hx
    by_contra hxNA
    exact hAex ⟨x, hx, hxNA⟩

namespace Monotonicity_Theorem

-- Right-endpoint side of piece transfer.
theorem beta_side {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {β : Endpoint R} {m : R} {t0 s0 : R}
    (hβt : Endpoint.lt (Endpoint.finite t0) β)
    (hleV : ∀ v : R, β = Endpoint.finite v → (LT.lt m v ∨ m = v))
    (hsm : LT.lt s0 m) :
    Endpoint.lt (Endpoint.finite s0) β := by
  cases β with
  | negInf => exact False.elim hβt
  | finite v =>
    cases hleV v rfl with
    | inl h => exact lt_trans hsm h
    | inr heq =>
      rw [← heq]
      exact hsm
  | posInf => exact trivial

end Monotonicity_Theorem
theorem Monotonicity_Theorem.right_adjacent_cut {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {A B : Set (Power R 1)}
    (hA : M.S 1 A) (hB : M.S 1 B)
    {p c2 : R} (hlt : LT.lt p c2)
    (hcov : ∀ x : Power R 1,
      openInterval (Endpoint.finite p) (Endpoint.finite c2) x → A x ∨ B x) :
    ∃ m : R, LT.lt p m ∧ (LT.lt m c2 ∨ m = c2) ∧
      ((∀ x : Power R 1,
        openInterval (Endpoint.finite p) (Endpoint.finite m) x → A x) ∨
       (∀ x : Power R 1,
        openInterval (Endpoint.finite p) (Endpoint.finite m) x → B x)) := by
  classical
  obtain hFUIA := (M.ominimal A).mp hA
  obtain hFUIB := (M.ominimal B).mp hB
  obtain ⟨EA, hEA⟩ := Monotonicity_Theorem.exception_list hFUIA
  obtain ⟨EB, hEB⟩ := Monotonicity_Theorem.exception_list hFUIB
  set E : List R := (EA ++ EB).filter (fun c => decide (LT.lt p c)) with hEdef
  have hne : E ++ [c2] ≠ [] := by
    intro h
    have hm : c2 ∈ E ++ [c2] :=
      List.mem_append.mpr (Or.inr (List.Mem.head _))
    rw [h] at hm
    exact List.not_mem_nil hm
  obtain ⟨m, hMem, hMin⟩ :=
    Monotonicity_Theorem.exists_least_of_list (E ++ [c2]) hne
  have hle : ∀ r : R, r ∈ EA ++ EB → LT.lt p r → (LT.lt m r ∨ m = r) := by
    intro r hr hlt
    exact hMin _ (List.mem_append.mpr (Or.inl (List.mem_filter.mpr
      ⟨hr, by rw [decide_eq_true_eq]; exact hlt⟩)))
  have hMp : LT.lt p m := by
    cases List.mem_append.mp hMem with
    | inl hE =>
      rw [List.mem_filter] at hE
      exact of_decide_eq_true hE.right
    | inr hS =>
      cases hS with
      | head => exact hlt
      | tail _ h => cases h
  have hMc2 : LT.lt m c2 ∨ m = c2 :=
    hMin _ (List.mem_append.mpr (Or.inr (List.Mem.head _)))
  have hsub : ∀ x : Power R 1,
      openInterval (Endpoint.finite p) (Endpoint.finite m) x →
      openInterval (Endpoint.finite p) (Endpoint.finite c2) x := by
    intro x hx
    have hx1 : LT.lt p (Power.coord1 x) := hx.left
    have hx2 : LT.lt (Power.coord1 x) m := hx.right
    show Endpoint.lt (Endpoint.finite p) (Endpoint.finite (x 0)) ∧
      Endpoint.lt (Endpoint.finite (x 0)) (Endpoint.finite c2)
    constructor
    · exact hx1
    · cases hMc2 with
      | inl h => exact lt_trans hx2 h
      | inr heq =>
        rw [heq] at hx2
        exact hx2
  by_cases hAex : ∃ x : Power R 1,
      openInterval (Endpoint.finite p) (Endpoint.finite m) x ∧ ¬ A x
  · by_cases hBex : ∃ y : Power R 1,
        openInterval (Endpoint.finite p) (Endpoint.finite m) y ∧ ¬ B y
    · obtain ⟨x, hxJ, hxNA⟩ := hAex
      obtain ⟨y, hyJ, hyNB⟩ := hBex
      have hxB : B x := by
        cases hcov x (hsub x hxJ) with
        | inl h => exact absurd h hxNA
        | inr h => exact h
      have hyA : A y := by
        cases hcov y (hsub y hyJ) with
        | inl h => exact h
        | inr h => exact absurd h hyNB
      have hpx : LT.lt p (Power.coord1 x) := hxJ.left
      have hxm : LT.lt (Power.coord1 x) m := hxJ.right
      have hpy : LT.lt p (Power.coord1 y) := hyJ.left
      have hym : LT.lt (Power.coord1 y) m := hyJ.right
      -- x's B-piece analysis toward y ∈ B
      have hyB : B y := by
        obtain hBx := hEB x hxB
        cases hBx with
        | inl hmem =>
          have hleM := hle _ (List.mem_append.mpr (Or.inr hmem)) hpx
          cases hleM with
          | inl h => exact False.elim (lt_irrefl m (lt_trans h hxm))
          | inr heq =>
            rw [heq] at hxm
            exact False.elim (lt_irrefl _ hxm)
        | inr hpiece =>
          obtain ⟨α, β, hxβ, hsubB, hLcond, hRcond⟩ := hpiece
          have hleV : ∀ v : R, β = Endpoint.finite v → (LT.lt m v ∨ m = v) := by
            intro v hv
            have h1 : Endpoint.lt (Endpoint.finite (x 0)) (Endpoint.finite v) := by
              have h2 := hxβ.right
              rw [hv] at h2
              exact h2
            have hvt : LT.lt (Power.coord1 x) v := h1
            have hvp : LT.lt p v := lt_trans hpx hvt
            exact hle _ (List.mem_append.mpr (Or.inr (hRcond v hv))) hvp
          cases α with
          | posInf =>
            have hF : False := hxβ.left
            exact False.elim hF
          | negInf =>
            have hmem : openInterval Endpoint.negInf β y := by
              have hβ : Endpoint.lt (Endpoint.finite (y 0)) β :=
                Monotonicity_Theorem.beta_side hxβ.right hleV hym
              exact ⟨trivial, hβ⟩
            exact hsubB _ hmem
          | finite u =>
            rcases lt_trichotomy u p with hlt | heq | hlt
            · have hmem : openInterval (Endpoint.finite u) β y := by
                have hα : Endpoint.lt (Endpoint.finite u) (Endpoint.finite (y 0)) :=
                  lt_trans hlt hpy
                have hβ : Endpoint.lt (Endpoint.finite (y 0)) β :=
                  Monotonicity_Theorem.beta_side hxβ.right hleV hym
                exact ⟨hα, hβ⟩
              exact hsubB _ hmem
            · have hmem : openInterval (Endpoint.finite u) β y := by
                have hα : Endpoint.lt (Endpoint.finite u) (Endpoint.finite (y 0)) := by
                  rw [heq]
                  exact hpy
                have hβ : Endpoint.lt (Endpoint.finite (y 0)) β :=
                  Monotonicity_Theorem.beta_side hxβ.right hleV hym
                exact ⟨hα, hβ⟩
              exact hsubB _ hmem
            · have hvE : u ∈ EB := hLcond u rfl
              have hleM := hle _ (List.mem_append.mpr (Or.inr hvE)) hlt
              have hux : LT.lt u (Power.coord1 x) := hxβ.left
              cases hleM with
              | inl h =>
                exact False.elim (lt_irrefl _ (lt_trans (lt_trans hxm h) hux))
              | inr heq2 =>
                rw [← heq2] at hux
                exact False.elim (lt_irrefl _ (lt_trans hxm hux))
      -- y's A-piece analysis toward False
      have hFalse : False := by
        obtain hAy := hEA y hyA
        cases hAy with
        | inl hmem =>
          have hleM := hle _ (List.mem_append.mpr (Or.inl hmem)) hpy
          cases hleM with
          | inl h => exact lt_irrefl _ (lt_trans hym h)
          | inr heq =>
            rw [heq] at hym
            exact lt_irrefl _ hym
        | inr hpiece =>
          obtain ⟨α, β, hyβ, hsubA, hLcond, hRcond⟩ := hpiece
          have hleV : ∀ v : R, β = Endpoint.finite v → (LT.lt m v ∨ m = v) := by
            intro v hv
            have h1 : Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite v) := by
              have h2 := hyβ.right
              rw [hv] at h2
              exact h2
            have hvt : LT.lt (Power.coord1 y) v := h1
            have hvp : LT.lt p v := lt_trans hpy hvt
            exact hle _ (List.mem_append.mpr (Or.inl (hRcond v hv))) hvp
          cases α with
          | posInf =>
            have hF : False := hyβ.left
            exact hF
          | negInf =>
            have hmem : openInterval Endpoint.negInf β x := by
              have hβ : Endpoint.lt (Endpoint.finite (x 0)) β :=
                Monotonicity_Theorem.beta_side hyβ.right hleV hxm
              exact ⟨trivial, hβ⟩
            exact absurd (hsubA _ hmem) hxNA
          | finite u =>
            rcases lt_trichotomy u p with hlt | heq | hlt
            · have hmem : openInterval (Endpoint.finite u) β x := by
                have hα : Endpoint.lt (Endpoint.finite u) (Endpoint.finite (x 0)) :=
                  lt_trans hlt hpx
                have hβ : Endpoint.lt (Endpoint.finite (x 0)) β :=
                  Monotonicity_Theorem.beta_side hyβ.right hleV hxm
                exact ⟨hα, hβ⟩
              exact absurd (hsubA _ hmem) hxNA
            · have hmem : openInterval (Endpoint.finite u) β x := by
                have hα : Endpoint.lt (Endpoint.finite u) (Endpoint.finite (x 0)) := by
                  rw [heq]
                  exact hpx
                have hβ : Endpoint.lt (Endpoint.finite (x 0)) β :=
                  Monotonicity_Theorem.beta_side hyβ.right hleV hxm
                exact ⟨hα, hβ⟩
              exact absurd (hsubA _ hmem) hxNA
            · have hvE : u ∈ EA := hLcond u rfl
              have hleM := hle _ (List.mem_append.mpr (Or.inl hvE)) hlt
              have huy : LT.lt u (Power.coord1 y) := hyβ.left
              cases hleM with
              | inl h =>
                exact lt_irrefl _ (lt_trans (lt_trans hym h) huy)
              | inr heq2 =>
                rw [← heq2] at huy
                exact lt_irrefl _ (lt_trans hym huy)
      exact False.elim hFalse
    · refine ⟨m, hMp, hMc2, Or.inr ?_⟩
      intro y hy
      by_contra hyNB
      exact hBex ⟨y, hy, hyNB⟩
  · refine ⟨m, hMp, hMc2, Or.inl ?_⟩
    intro x hx
    by_contra hxNA
    exact hAex ⟨x, hx, hxNA⟩

namespace Monotonicity_Theorem

theorem covLeftAux {R : Type} (x y : Power R 1) :
    Power.left (R := R) (n := 1) (m := 1) (Power.append x y) = x := by
  funext i
  simp [Power.left, Power.append, Fin.append_left]

theorem covRightAux {R : Type} (x y : Power R 1) :
    Power.right (R := R) (n := 1) (m := 1) (Power.append x y) = y := by
  funext j
  exact Fin.append_right x y j

-- Read off v as the output tuple from a graph witness.
theorem covOutEq {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {a b : Endpoint R} {B : Set (Power R 1)}
    (M : OMinimalStructure R)
    (f : DefinableFunction M (openInterval a b) B)
    {y v : Power R 1} (hy : openInterval a b y)
    (hG : FunctionGraph (R := R) (m := 1) (n := 1)
      (A := openInterval a b) (B := B) f.toFun (Power.append y v)) :
    v = (f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval a b x})).1 := by
  obtain ⟨hx', hEq⟩ := hG
  have eL : Power.left (Power.append y v) = y := covLeftAux y v
  have eR : Power.right (Power.append y v) = v := covRightAux y v
  have hSub : (⟨Power.left (Power.append y v), hx'⟩
      : {x : Power R 1 // openInterval a b x})
      = (⟨y, hy⟩ : {x : Power R 1 // openInterval a b x}) := Subtype.ext eL
  rw [eR, hSub] at hEq
  exact hEq

end Monotonicity_Theorem
theorem Monotonicity_Theorem.pattern_at_interior_point {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {a b : Endpoint R} {B : Set (Power R 1)}
    (f : DefinableFunction M (openInterval a b) B)
    (hinj : ∀ x y (hx : openInterval a b x) (hy : openInterval a b y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y)
    {p : Power R 1} (hp : openInterval a b p) :
    (∃ c1 c2 : Power R 1, openInterval a b c1 ∧ openInterval a b c2 ∧
      Lt1 c1 p ∧ Lt1 p c2 ∧
      (∀ y (hy : openInterval a b y), Lt1 c1 y → Lt1 y p ->
        Lt1 (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1) ∧
      (∀ y (hy : openInterval a b y), Lt1 p y → Lt1 y c2 ->
        Lt1 (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1)) ∨
    (∃ c1 c2 : Power R 1, openInterval a b c1 ∧ openInterval a b c2 ∧
      Lt1 c1 p ∧ Lt1 p c2 ∧
      (∀ y (hy : openInterval a b y), Lt1 c1 y → Lt1 y p ->
        Lt1 (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1) ∧
      (∀ y (hy : openInterval a b y), Lt1 p y → Lt1 y c2 ->
        Lt1 (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1)) ∨
    (∃ c1 c2 : Power R 1, openInterval a b c1 ∧ openInterval a b c2 ∧
      Lt1 c1 p ∧ Lt1 p c2 ∧
      (∀ y (hy : openInterval a b y), Lt1 c1 y → Lt1 y p ->
        Lt1 (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1) ∧
      (∀ y (hy : openInterval a b y), Lt1 p y → Lt1 y c2 ->
        Lt1 (f.toFun (Subtype.mk p hp)).1 (f.toFun (Subtype.mk y hy)).1)) ∨
    (∃ c1 c2 : Power R 1, openInterval a b c1 ∧ openInterval a b c2 ∧
      Lt1 c1 p ∧ Lt1 p c2 ∧
      (∀ y (hy : openInterval a b y), Lt1 c1 y → Lt1 y p ->
        Lt1 (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1) ∧
      (∀ y (hy : openInterval a b y), Lt1 p y → Lt1 y c2 ->
        Lt1 (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk p hp)).1)) := by
  -- Step 0: witness coords on both sides.
  have hr1 : ∃ r1 : R, Endpoint.lt a (Endpoint.finite r1) ∧ LT.lt r1 (p 0) := by
    cases a with
    | negInf =>
      obtain ⟨r1, hr1⟩ := exists_lt (p 0)
      exact ⟨r1, trivial, hr1⟩
    | finite av =>
      have hav : LT.lt av (p 0) := hp.left
      obtain ⟨r1, hr1a, hr1p⟩ := exists_between hav
      exact ⟨r1, hr1a, hr1p⟩
    | posInf =>
      exact False.elim hp.left
  have hr2 : ∃ r2 : R, LT.lt (p 0) r2 ∧ Endpoint.lt (Endpoint.finite r2) b := by
    cases b with
    | negInf =>
      exact False.elim hp.right
    | finite bv =>
      have hpb : LT.lt (p 0) bv := hp.right
      obtain ⟨r2, hr2p, hr2b⟩ := exists_between hpb
      exact ⟨r2, hr2p, hr2b⟩
    | posInf =>
      obtain ⟨r2, hr2⟩ := exists_gt (p 0)
      exact ⟨r2, hr2, trivial⟩
  obtain ⟨r1, hr1a, hr1p⟩ := hr1
  obtain ⟨r2, hr2p, hr2b⟩ := hr2
  -- Windows and threshold.
  have hJl : M.S 1 (openInterval (Endpoint.finite r1) (Endpoint.finite (p 0))) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hJr : M.S 1 (openInterval (Endpoint.finite (p 0)) (Endpoint.finite r2)) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  set t : R := ((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1) 0 with htdef
  have hSpL := Monotonicity_Theorem.above_sign_definable M f
    (openInterval (Endpoint.finite r1) (Endpoint.finite (p 0))) hJl t
  have hSmL := Monotonicity_Theorem.below_sign_definable M f _ hJl t
  have hSpR := Monotonicity_Theorem.above_sign_definable M f _ hJr t
  have hSmR := Monotonicity_Theorem.below_sign_definable M f _ hJr t
  -- Windows lie in the domain.
  have hwinL : ∀ y : Power R 1,
      openInterval (Endpoint.finite r1) (Endpoint.finite (p 0)) y →
      openInterval a b y := by
    intro y hy
    have hy1 : LT.lt r1 (Power.coord1 y) := hy.left
    have hy2 : LT.lt (Power.coord1 y) (p 0) := hy.right
    have ha : Endpoint.lt a (Endpoint.finite (y 0)) := by
      cases a with
      | negInf => exact trivial
      | finite av =>
        have g0 : LT.lt av r1 := hr1a
        exact lt_trans g0 hy1
      | posInf => exact False.elim hr1a
    have hb : Endpoint.lt (Endpoint.finite (y 0)) b := by
      cases b with
      | negInf => exact False.elim hp.right
      | finite bv =>
        have g1 : LT.lt (p 0) bv := hp.right
        exact lt_trans hy2 g1
      | posInf => exact trivial
    exact ⟨ha, hb⟩
  have hwinR : ∀ y : Power R 1,
      openInterval (Endpoint.finite (p 0)) (Endpoint.finite r2) y →
      openInterval a b y := by
    intro y hy
    have hy1 : LT.lt (Power.coord1 y) r2 := hy.right
    have hy2 : LT.lt (p 0) (Power.coord1 y) := hy.left
    have ha : Endpoint.lt a (Endpoint.finite (y 0)) := by
      cases a with
      | negInf => exact trivial
      | finite av =>
        have g0 : LT.lt av (p 0) := hp.left
        exact lt_trans g0 hy2
      | posInf => exact False.elim hp.left
    have hb : Endpoint.lt (Endpoint.finite (y 0)) b := by
      cases b with
      | negInf => exact False.elim hp.right
      | finite bv =>
        have g1 : LT.lt r2 bv := hr2b
        exact lt_trans hy1 g1
      | posInf => exact trivial
    exact ⟨ha, hb⟩
  -- Covers by sign on each side.
  have hcovL : ∀ y : Power R 1,
      openInterval (Endpoint.finite r1) (Endpoint.finite (p 0)) y →
      ((fun y => openInterval (Endpoint.finite r1) (Endpoint.finite (p 0)) y ∧
        ∃ v : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1)
            (A := openInterval a b) (B := B) f.toFun (Power.append y v) ∧
          Lt1 (fun _ => t) v) y ∨
       (fun y => openInterval (Endpoint.finite r1) (Endpoint.finite (p 0)) y ∧
        ∃ v : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1)
            (A := openInterval a b) (B := B) f.toFun (Power.append y v) ∧
          Lt1 v (fun _ => t)) y) := by
    intro y hy
    have hyJ : openInterval a b y := hwinL y hy
    have hylt : LT.lt (Power.coord1 y) (p 0) := hy.right
    rcases lt_trichotomy (Power.coord1 ((f.toFun (⟨y, hyJ⟩
      : {x : Power R 1 // openInterval a b x})).1)) t with
      hlt | heq | hlt
    · refine Or.inr ⟨hy, (f.toFun (⟨y, hyJ⟩
        : {x : Power R 1 // openInterval a b x})).1, ?_, ?_⟩
      · have eL : Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1)) = y :=
          covLeftAux _ _
        have eR : Power.right (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1))
            = (f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x})).1 :=
          covRightAux _ _
        have hx' : openInterval a b
            (Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
              : {x : Power R 1 // openInterval a b x})).1))) := by
          rw [eL]
          exact hyJ
        have hSub : (⟨Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1)), hx'⟩
            : {x : Power R 1 // openInterval a b x})
            = (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x}) :=
          Subtype.ext eL
        refine ⟨hx', ?_⟩
        rw [eR, hSub]
      · have hO : Lt1
            ((f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x})).1)
            (fun _ => t) := hlt
        exact hO
    · have hteq : (f.toFun (⟨y, hyJ⟩
          : {x : Power R 1 // openInterval a b x})).1
          = (f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1 := by
        funext i
        have i0 : i = (0 : Fin 1) := Fin.ext (by omega)
        rw [i0]
        show (((f.toFun (⟨y, hyJ⟩
          : {x : Power R 1 // openInterval a b x})).1)) 0 = t
        exact heq
      have hSub : y = p :=
        hinj _ _ _ _ (Subtype.ext hteq)
      have hylt2 : LT.lt (Power.coord1 y) (p 0) := hy.right
      rw [hSub] at hylt2
      exact False.elim (lt_irrefl _ hylt2)
    · refine Or.inl ⟨hy, (f.toFun (⟨y, hyJ⟩
        : {x : Power R 1 // openInterval a b x})).1, ?_, ?_⟩
      · have eL : Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1)) = y :=
          covLeftAux _ _
        have eR : Power.right (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1))
            = (f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x})).1 :=
          covRightAux _ _
        have hx' : openInterval a b
            (Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
              : {x : Power R 1 // openInterval a b x})).1))) := by
          rw [eL]
          exact hyJ
        have hSub : (⟨Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1)), hx'⟩
            : {x : Power R 1 // openInterval a b x})
            = (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x}) :=
          Subtype.ext eL
        refine ⟨hx', ?_⟩
        rw [eR, hSub]
      · have hO : Lt1 (fun _ => t)
            ((f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x})).1) := hlt
        exact hO
  -- Cover on the right by sign.
  have hcovR : ∀ y : Power R 1,
      openInterval (Endpoint.finite (p 0)) (Endpoint.finite r2) y →
      ((fun y => openInterval (Endpoint.finite (p 0)) (Endpoint.finite r2) y ∧
        ∃ v : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1)
            (A := openInterval a b) (B := B) f.toFun (Power.append y v) ∧
          Lt1 (fun _ => t) v) y ∨
       (fun y => openInterval (Endpoint.finite (p 0)) (Endpoint.finite r2) y ∧
        ∃ v : Power R 1,
          FunctionGraph (R := R) (m := 1) (n := 1)
            (A := openInterval a b) (B := B) f.toFun (Power.append y v) ∧
          Lt1 v (fun _ => t)) y) := by
    intro y hy
    have hyJ : openInterval a b y := hwinR y hy
    rcases lt_trichotomy (Power.coord1 ((f.toFun (⟨y, hyJ⟩
      : {x : Power R 1 // openInterval a b x})).1)) t with
      hlt | heq | hlt
    · refine Or.inr ⟨hy, (f.toFun (⟨y, hyJ⟩
        : {x : Power R 1 // openInterval a b x})).1, ?_, ?_⟩
      · have eL : Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1)) = y :=
          covLeftAux _ _
        have eR : Power.right (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1))
            = (f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x})).1 :=
          covRightAux _ _
        have hx' : openInterval a b
            (Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
              : {x : Power R 1 // openInterval a b x})).1))) := by
          rw [eL]
          exact hyJ
        have hSub : (⟨Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1)), hx'⟩
            : {x : Power R 1 // openInterval a b x})
            = (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x}) :=
          Subtype.ext eL
        refine ⟨hx', ?_⟩
        rw [eR, hSub]
      · have hO : Lt1
            ((f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x})).1)
            (fun _ => t) := hlt
        exact hO
    · have hteq : (f.toFun (⟨y, hyJ⟩
          : {x : Power R 1 // openInterval a b x})).1
          = (f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1 := by
        funext i
        have i0 : i = (0 : Fin 1) := Fin.ext (by omega)
        rw [i0]
        show (((f.toFun (⟨y, hyJ⟩
          : {x : Power R 1 // openInterval a b x})).1)) 0 = t
        exact heq
      have hSub : y = p :=
        hinj _ _ _ _ (Subtype.ext hteq)
      have hylt2 : LT.lt (p 0) (Power.coord1 y) := hy.left
      rw [hSub] at hylt2
      exact False.elim (lt_irrefl _ hylt2)
    · refine Or.inl ⟨hy, (f.toFun (⟨y, hyJ⟩
        : {x : Power R 1 // openInterval a b x})).1, ?_, ?_⟩
      · have eL : Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1)) = y :=
          covLeftAux _ _
        have eR : Power.right (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1))
            = (f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x})).1 :=
          covRightAux _ _
        have hx' : openInterval a b
            (Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
              : {x : Power R 1 // openInterval a b x})).1))) := by
          rw [eL]
          exact hyJ
        have hSub : (⟨Power.left (Power.append y ((f.toFun (⟨y, hyJ⟩
            : {x : Power R 1 // openInterval a b x})).1)), hx'⟩
            : {x : Power R 1 // openInterval a b x})
            = (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x}) :=
          Subtype.ext eL
        refine ⟨hx', ?_⟩
        rw [eR, hSub]
      · have hO : Lt1 (fun _ => t)
            ((f.toFun (⟨y, hyJ⟩ : {x : Power R 1 // openInterval a b x})).1) := hlt
        exact hO
  -- Adjacency cuts on both sides.
  obtain ⟨Mc, hMp, hMbound, hPureL⟩ :=
    Monotonicity_Theorem.left_adjacent_cut M hSpL hSmL hr1p hcovL
  obtain ⟨Nc, hNp, hNbound, hPureR⟩ :=
    Monotonicity_Theorem.right_adjacent_cut M hSpR hSmR hr2p hcovR
  -- Cut points lie in the domain.
  have hMcJ : openInterval a b (fun _ => Mc) := by
    have hlow : Endpoint.lt a (Endpoint.finite Mc) := by
      cases a with
      | negInf => exact trivial
      | finite av =>
        have g0 : LT.lt av r1 := hr1a
        cases hMbound with
        | inl h => exact lt_trans g0 h
        | inr heq =>
          rw [← heq]
          exact g0
      | posInf => exact False.elim hr1a
    have hhigh : Endpoint.lt (Endpoint.finite Mc) b := by
      cases b with
      | negInf => exact False.elim hp.right
      | finite bv =>
        have g1 : LT.lt (p 0) bv := hp.right
        exact lt_trans hMp g1
      | posInf => exact trivial
    exact ⟨hlow, hhigh⟩
  have hNcJ : openInterval a b (fun _ => Nc) := by
    have hlow : Endpoint.lt a (Endpoint.finite Nc) := by
      cases a with
      | negInf => exact trivial
      | finite av =>
        have g0 : LT.lt av (p 0) := hp.left
        exact lt_trans g0 hNp
      | posInf => exact False.elim hp.left
    have hhigh : Endpoint.lt (Endpoint.finite Nc) b := by
      cases b with
      | negInf => exact False.elim hp.right
      | finite bv =>
        have g2 : LT.lt r2 bv := hr2b
        cases hNbound with
        | inl h => exact lt_trans h g2
        | inr heq =>
          rw [heq]
          exact g2
      | posInf => exact trivial
    exact ⟨hlow, hhigh⟩
  have hMcLt : Lt1 (fun _ => Mc) p := hMp
  have hNcLt : Lt1 p (fun _ => Nc) := hNp
  rcases hPureL with hPL | hPL
  · rcases hPureR with hPR | hPR
    · -- ++ : above on both sides
      refine Or.inl ⟨(fun _ => Mc), (fun _ => Nc), hMcJ, hNcJ, hMcLt, hNcLt, ?_, ?_⟩
      · intro y hy h1 h2
        have hwin : openInterval (Endpoint.finite Mc) (Endpoint.finite (p 0)) y := by
          show Endpoint.lt (Endpoint.finite Mc) (Endpoint.finite (y 0)) ∧
            Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite (p 0))
          constructor
          · have g : LT.lt Mc (Power.coord1 y) := h1
            exact g
          · have g : LT.lt (Power.coord1 y) (p 0) := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPL y hwin
        have hev := Monotonicity_Theorem.covOutEq M f hy hG
        have g1 : LT.lt t (v 0) := hOv
        show LT.lt (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
          (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
        rw [← hev]
        exact g1
      · intro y hy h1 h2
        have hwin : openInterval (Endpoint.finite (p 0)) (Endpoint.finite Nc) y := by
          show Endpoint.lt (Endpoint.finite (p 0)) (Endpoint.finite (y 0)) ∧
            Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite Nc)
          constructor
          · have g : LT.lt (Power.coord1 p) (Power.coord1 y) := h1
            exact g
          · have g : LT.lt (Power.coord1 y) Nc := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPR y hwin
        have hev := Monotonicity_Theorem.covOutEq M f hy hG
        have g1 : LT.lt t (v 0) := hOv
        show LT.lt (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
          (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
        rw [← hev]
        exact g1
    · -- +- : above left, below right
      refine Or.inr (Or.inl ⟨(fun _ => Mc), (fun _ => Nc), hMcJ, hNcJ, hMcLt, hNcLt, ?_, ?_⟩)
      · intro y hy h1 h2
        have hwin : openInterval (Endpoint.finite Mc) (Endpoint.finite (p 0)) y := by
          show Endpoint.lt (Endpoint.finite Mc) (Endpoint.finite (y 0)) ∧
            Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite (p 0))
          constructor
          · have g : LT.lt Mc (Power.coord1 y) := h1
            exact g
          · have g : LT.lt (Power.coord1 y) (p 0) := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPL y hwin
        have hev := Monotonicity_Theorem.covOutEq M f hy hG
        have g1 : LT.lt t (v 0) := hOv
        show LT.lt (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
          (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
        rw [← hev]
        exact g1
      · intro y hy h1 h2
        have hwin : openInterval (Endpoint.finite (p 0)) (Endpoint.finite Nc) y := by
          show Endpoint.lt (Endpoint.finite (p 0)) (Endpoint.finite (y 0)) ∧
            Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite Nc)
          constructor
          · have g : LT.lt (Power.coord1 p) (Power.coord1 y) := h1
            exact g
          · have g : LT.lt (Power.coord1 y) Nc := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPR y hwin
        have hev := Monotonicity_Theorem.covOutEq M f hy hG
        have g1 : LT.lt (v 0) t := hOv
        show LT.lt (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
          (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
        rw [← hev]
        exact g1
  · rcases hPureR with hPR | hPR
    · -- -+ : below left, above right
      refine Or.inr (Or.inr (Or.inl ⟨(fun _ => Mc), (fun _ => Nc), hMcJ, hNcJ, hMcLt, hNcLt, ?_, ?_⟩))
      · intro y hy h1 h2
        have hwin : openInterval (Endpoint.finite Mc) (Endpoint.finite (p 0)) y := by
          show Endpoint.lt (Endpoint.finite Mc) (Endpoint.finite (y 0)) ∧
            Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite (p 0))
          constructor
          · have g : LT.lt Mc (Power.coord1 y) := h1
            exact g
          · have g : LT.lt (Power.coord1 y) (p 0) := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPL y hwin
        have hev := Monotonicity_Theorem.covOutEq M f hy hG
        have g1 : LT.lt (v 0) t := hOv
        show LT.lt (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
          (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
        rw [← hev]
        exact g1
      · intro y hy h1 h2
        have hwin : openInterval (Endpoint.finite (p 0)) (Endpoint.finite Nc) y := by
          show Endpoint.lt (Endpoint.finite (p 0)) (Endpoint.finite (y 0)) ∧
            Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite Nc)
          constructor
          · have g : LT.lt (Power.coord1 p) (Power.coord1 y) := h1
            exact g
          · have g : LT.lt (Power.coord1 y) Nc := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPR y hwin
        have hev := Monotonicity_Theorem.covOutEq M f hy hG
        have g1 : LT.lt t (v 0) := hOv
        show LT.lt (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
          (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
        rw [← hev]
        exact g1
    · -- -- : below on both sides
      refine Or.inr (Or.inr (Or.inr ⟨(fun _ => Mc), (fun _ => Nc), hMcJ, hNcJ, hMcLt, hNcLt, ?_, ?_⟩))
      · intro y hy h1 h2
        have hwin : openInterval (Endpoint.finite Mc) (Endpoint.finite (p 0)) y := by
          show Endpoint.lt (Endpoint.finite Mc) (Endpoint.finite (y 0)) ∧
            Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite (p 0))
          constructor
          · have g : LT.lt Mc (Power.coord1 y) := h1
            exact g
          · have g : LT.lt (Power.coord1 y) (p 0) := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPL y hwin
        have hev := Monotonicity_Theorem.covOutEq M f hy hG
        have g1 : LT.lt (v 0) t := hOv
        show LT.lt (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
          (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
        rw [← hev]
        exact g1
      · intro y hy h1 h2
        have hwin : openInterval (Endpoint.finite (p 0)) (Endpoint.finite Nc) y := by
          show Endpoint.lt (Endpoint.finite (p 0)) (Endpoint.finite (y 0)) ∧
            Endpoint.lt (Endpoint.finite (y 0)) (Endpoint.finite Nc)
          constructor
          · have g : LT.lt (Power.coord1 p) (Power.coord1 y) := h1
            exact g
          · have g : LT.lt (Power.coord1 y) Nc := h2
            exact g
        obtain ⟨_, v, hG, hOv⟩ := hPR y hwin
        have hev := Monotonicity_Theorem.covOutEq M f hy hG
        have g1 : LT.lt (v 0) t := hOv
        show LT.lt (((f.toFun (⟨y, hy⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
          (((f.toFun (⟨p, hp⟩ : {x : Power R 1 // openInterval a b x})).1) 0)
        rw [← hev]
        exact g1

open Monotonicity_Theorem

namespace Monotonicity_Theorem


-- Shared index maps into arity 1 + (1 + (1 + (1 + 1))).
-- Positions (flattened): c = 0, x = 1, y = 2, w = 3, v = 4.
def huC0 : Fin 1 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun _ => ⟨0, by omega⟩

def huX1 : Fin 1 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun _ => ⟨1, by omega⟩

def huY2 : Fin 1 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun _ => ⟨2, by omega⟩

def huLt01 : Fin 2 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩

def huLt02 : Fin 2 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨0, by omega⟩ else ⟨2, by omega⟩

def huLt12 : Fin 2 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨1, by omega⟩ else ⟨2, by omega⟩

def huLt10 : Fin 2 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

def huLt21 : Fin 2 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨2, by omega⟩ else ⟨1, by omega⟩

def huLt20 : Fin 2 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨2, by omega⟩ else ⟨0, by omega⟩

def huGw : Fin (1 + 1) → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨2, by omega⟩ else ⟨3, by omega⟩

def huGx : Fin (1 + 1) → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨1, by omega⟩ else ⟨4, by omega⟩

def huBadAbove : Fin 2 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨3, by omega⟩ else ⟨4, by omega⟩

def huBadBelow : Fin 2 → Fin ((1 + 1) + (1 + (1 + 1))) :=
  fun j => if _ : j.val = 0 then ⟨4, by omega⟩ else ⟨3, by omega⟩

def huSwap : Fin (1 + 1) → Fin (1 + 1) :=
  fun j => if _ : j.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩

end Monotonicity_Theorem

open Monotonicity_Theorem


theorem huGreatest {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] : ∀ L : List R, L ≠ [] → ∃ M : R, M ∈ L ∧ ∀ r : R, r ∈ L → (LT.lt r M ∨ r = M) := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons h t ih =>
    intro hNe
    cases t with
    | nil =>
      refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
      intro r hr
      simp at hr
      exact Or.inr hr
    | cons h2 t2 =>
      have hNet : h2 :: t2 ≠ [] := by simp
      obtain ⟨M, hM, hMax⟩ := ih hNet
      have hTri := lt_trichotomy h M
      cases hTri with
      | inl h1 =>
        have hlt := h1
        refine ⟨M, List.mem_cons.mpr (Or.inr hM), ?_⟩
        intro r hr
        cases List.mem_cons.mp hr with
        | inl he =>
          have hlt2 : LT.lt r M := by rw [he]; exact hlt
          exact Or.inl hlt2
        | inr hm => exact hMax r hm
      | inr h23 =>
        cases h23 with
        | inl h1 =>
          have heq := h1
          refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
          intro r hr
          cases List.mem_cons.mp hr with
          | inl he => exact Or.inr he
          | inr hm =>
            have hle := hMax r hm
            cases hle with
            | inl hltRM =>
              have hltRh : LT.lt r h := by rw [←heq] at hltRM; exact hltRM
              exact Or.inl hltRh
            | inr heqRM =>
              exact Or.inr (heqRM.trans heq.symm)
        | inr h1 =>
          have hlt := h1
          refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
          intro r hr
          cases List.mem_cons.mp hr with
          | inl he => exact Or.inr he
          | inr hm =>
            have hle := hMax r hm
            cases hle with
            | inl hltRM => exact Or.inl (lt_trans hltRM hlt)
            | inr heqRM =>
              have hltRh : LT.lt r h := by rw [heqRM]; exact hlt
              exact Or.inl hltRh

theorem huOutside {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] {a0 b0 : Endpoint R} (hlt0 : Endpoint.lt a0 b0) (x0 : Power R 1) : ∀ L : List R, ∃ x : Power R 1, openInterval a0 b0 x ∧ Power.coord1 x ∉ L := by
  intro L
  cases a0 with
  | negInf =>
    cases b0 with
    | negInf => cases hlt0
    | finite r =>
      have hAux : ∀ (L : List R) (b : R),
          ∃ y : R, LT.lt y b ∧ y ∉ L := by
        intro L
        induction L with
        | nil =>
          intro b
          obtain ⟨y, hy⟩ := exists_lt b
          exact ⟨y, hy, by simp⟩
        | cons h t ih =>
          intro b
          haveI hDecH : Decidable (LT.lt h b) := Classical.propDecidable _
          by_cases hhb : LT.lt h b
          · obtain ⟨y, hyh, hyn⟩ := ih h
            have hyb : LT.lt y b := lt_trans hyh hhb
            refine ⟨y, hyb, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hcon : LT.lt h h := by rw [he] at hyh; exact hyh
              exact lt_irrefl _ hcon
            | inr hm2 => exact hyn hm2
          · obtain ⟨y, hyb, hyn⟩ := ih b
            refine ⟨y, hyb, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hY : LT.lt y b := hyb
              rw [he] at hY
              exact hhb hY
            | inr hm2 => exact hyn hm2
      obtain ⟨y, hyr, hyn⟩ := hAux L r
      refine ⟨fun _ => y, ?_, ?_⟩
      · show Endpoint.lt Endpoint.negInf (Endpoint.finite y) ∧
          Endpoint.lt (Endpoint.finite y) (Endpoint.finite r)
        exact ⟨trivial, hyr⟩
      · show y ∉ L
        exact hyn
    | posInf =>
      cases L with
      | nil =>
        refine ⟨fun _ => Power.coord1 x0, ?_, ?_⟩
        · show Endpoint.lt Endpoint.negInf (Endpoint.finite (Power.coord1 x0)) ∧
            Endpoint.lt (Endpoint.finite (Power.coord1 x0)) Endpoint.posInf
          exact ⟨trivial, trivial⟩
        · exact by simp
      | cons h t =>
        have hNet : h :: t ≠ [] := by simp
        obtain ⟨M, hM, hMax⟩ := huGreatest (h :: t) hNet
        obtain ⟨y, hy⟩ := exists_gt M
        refine ⟨fun _ => y, ?_, ?_⟩
        · show Endpoint.lt Endpoint.negInf (Endpoint.finite y) ∧
            Endpoint.lt (Endpoint.finite y) Endpoint.posInf
          exact ⟨trivial, trivial⟩
        · show y ∉ (h :: t)
          intro hm
          have hle := hMax y hm
          cases hle with
          | inl hltYM =>
            have hcon : LT.lt M M := lt_trans hy hltYM
            exact lt_irrefl _ hcon
          | inr heYM =>
            have hcon : LT.lt M M := by rw [heYM] at hy; exact hy
            exact lt_irrefl _ hcon
  | finite l =>
    cases b0 with
    | negInf => cases hlt0
    | finite r =>
      have hlr : LT.lt l r := hlt0
      have hAux : ∀ (L : List R) (lo hi : R), LT.lt lo hi ->
          ∃ y : R, LT.lt lo y ∧ LT.lt y hi ∧ y ∉ L := by
        intro L
        induction L with
        | nil =>
          intro lo hi hlt
          obtain ⟨y, hy1, hy2⟩ := exists_between hlt
          exact ⟨y, hy1, hy2, by simp⟩
        | cons h t ih =>
          intro lo hi hlt
          haveI hDecH : Decidable (LT.lt lo h ∧ LT.lt h hi) :=
            Classical.propDecidable _
          by_cases hmem : LT.lt lo h ∧ LT.lt h hi
          · obtain ⟨hlh, hhr⟩ := hmem
            obtain ⟨y, hy1, hy2, hyn⟩ := ih lo h hlh
            have hyr : LT.lt y hi := lt_trans hy2 hhr
            refine ⟨y, hy1, hyr, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hcon : LT.lt h h := by rw [he] at hy2; exact hy2
              exact lt_irrefl _ hcon
            | inr hm2 => exact hyn hm2
          · obtain ⟨y, hy1, hy2, hyn⟩ := ih lo hi hlt
            refine ⟨y, hy1, hy2, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hY : LT.lt lo y ∧ LT.lt y hi :=⟨hy1, hy2⟩
              rw [he] at hY
              exact hmem hY
            | inr hm2 => exact hyn hm2
      obtain ⟨y, hy1, hy2, hyn⟩ := hAux L l r hlr
      refine ⟨fun _ => y, ?_, ?_⟩
      · show Endpoint.lt (Endpoint.finite l) (Endpoint.finite y) ∧
          Endpoint.lt (Endpoint.finite y) (Endpoint.finite r)
        exact ⟨hy1, hy2⟩
      · show y ∉ L
        exact hyn
    | posInf =>
      have hAux : ∀ (L : List R) (lo : R),
          ∃ y : R, LT.lt lo y ∧ y ∉ L := by
        intro L
        induction L with
        | nil =>
          intro lo
          obtain ⟨y, hy⟩ := exists_gt lo
          exact ⟨y, hy, by simp⟩
        | cons h t ih =>
          intro lo
          haveI hDecH : Decidable (LT.lt lo h) := Classical.propDecidable _
          by_cases hlo : LT.lt lo h
          · obtain ⟨y, hyh, hyn⟩ := ih h
            have hyl : LT.lt lo y := lt_trans hlo hyh
            refine ⟨y, hyl, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hcon : LT.lt h h := by rw [he] at hyh; exact hyh
              exact lt_irrefl _ hcon
            | inr hm2 => exact hyn hm2
          · obtain ⟨y, hyl, hyn⟩ := ih lo
            refine ⟨y, hyl, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hY : LT.lt lo y := hyl
              rw [he] at hY
              exact hlo hY
            | inr hm2 => exact hyn hm2
      obtain ⟨y, hyl, hyn⟩ := hAux L l
      refine ⟨fun _ => y, ?_, ?_⟩
      · show Endpoint.lt (Endpoint.finite l) (Endpoint.finite y) ∧
          Endpoint.lt (Endpoint.finite y) Endpoint.posInf
        exact ⟨hyl, trivial⟩
      · show y ∉ L
        exact hyn
  | posInf =>
    cases b0 with
    | negInf => cases hlt0
    | finite r => cases hlt0
    | posInf => cases hlt0

theorem huMidL {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a b : Endpoint R) (x : Power R 1)
    (hx : openInterval a b x) :
    ∃ c : Power R 1, openInterval a b c ∧ Lt1 c x := by
  obtain ⟨hA, hB⟩ := hx
  cases a with
  | negInf =>
    obtain ⟨m, hm⟩ := exists_lt (Power.coord1 x)
    refine ⟨fun _ => m, ?_, ?_⟩
    · show Endpoint.lt Endpoint.negInf (Endpoint.finite m) ∧
        Endpoint.lt (Endpoint.finite m) b
      cases b with
      | negInf => cases hB
      | finite r =>
        have hxr : LT.lt (Power.coord1 x) r := hB
        exact ⟨trivial, lt_trans hm hxr⟩
      | posInf => exact ⟨trivial, trivial⟩
    · show Lt1 (fun _ => m) x
      exact hm
  | finite l =>
    have hlx : LT.lt l (Power.coord1 x) := hA
    obtain ⟨m, hm1, hm2⟩ := exists_between hlx
    refine ⟨fun _ => m, ?_, ?_⟩
    · show Endpoint.lt (Endpoint.finite l) (Endpoint.finite m) ∧
        Endpoint.lt (Endpoint.finite m) b
      cases b with
      | negInf => cases hB
      | finite r =>
        have hxr : LT.lt (Power.coord1 x) r := hB
        exact ⟨hm1, lt_trans hm2 hxr⟩
      | posInf => exact ⟨hm1, trivial⟩
    · show Lt1 (fun _ => m) x
      exact hm2
  | posInf => cases hA

theorem huMidR {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a b : Endpoint R) (x : Power R 1)
    (hx : openInterval a b x) :
    ∃ c : Power R 1, openInterval a b c ∧ Lt1 x c := by
  obtain ⟨hA, hB⟩ := hx
  cases b with
  | posInf =>
    obtain ⟨m, hm⟩ := exists_gt (Power.coord1 x)
    refine ⟨fun _ => m, ?_, ?_⟩
    · show Endpoint.lt a (Endpoint.finite m) ∧
        Endpoint.lt (Endpoint.finite m) Endpoint.posInf
      cases a with
      | negInf => exact ⟨trivial, trivial⟩
      | finite l =>
        have hlx : LT.lt l (Power.coord1 x) := hA
        exact ⟨lt_trans hlx hm, trivial⟩
      | posInf => cases hA
    · show Lt1 x (fun _ => m)
      exact hm
  | finite r =>
    have hxr : LT.lt (Power.coord1 x) r := hB
    obtain ⟨m, hm1, hm2⟩ := exists_between hxr
    refine ⟨fun _ => m, ?_, ?_⟩
    · show Endpoint.lt a (Endpoint.finite m) ∧
        Endpoint.lt (Endpoint.finite m) (Endpoint.finite r)
      cases a with
      | negInf => exact ⟨trivial, hm2⟩
      | finite l =>
        have hlx : LT.lt l (Power.coord1 x) := hA
        exact ⟨lt_trans hlx hm1, hm2⟩
      | posInf => cases hA
    · show Lt1 x (fun _ => m)
      exact hm1
  | negInf => cases hB

theorem huOutL {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a b : Endpoint R) (cc xc : R)
    (hX : Endpoint.lt a (Endpoint.finite xc) ∧ Endpoint.lt (Endpoint.finite xc) b)
    (hN : ¬(Endpoint.lt a (Endpoint.finite cc) ∧ Endpoint.lt (Endpoint.finite cc) b))
    (hCX : LT.lt cc xc) :
    ∀ yc : R, (Endpoint.lt a (Endpoint.finite yc) ∧ Endpoint.lt (Endpoint.finite yc) b) ->
      LT.lt cc yc := by
  intro yc hY
  have hTri := lt_trichotomy cc yc
  cases hTri with
  | inl h1 =>
    have hlt := h1
    exact hlt
  | inr h23 =>
    cases h23 with
    | inl h1 =>
      have heq := h1
      have hA : Endpoint.lt a (Endpoint.finite cc) := by rw [heq]; exact hY.1
      have hB : Endpoint.lt (Endpoint.finite cc) b := by rw [heq]; exact hY.2
      exact absurd ⟨hA, hB⟩ hN
    | inr h1 =>
      have hlt := h1
      have hA : Endpoint.lt a (Endpoint.finite cc) := by
        cases a with
        | negInf => trivial
        | finite l =>
          have hlyc : LT.lt l yc := hY.1
          exact lt_trans hlyc hlt
        | posInf => cases hY.1
      have hB : Endpoint.lt (Endpoint.finite cc) b := by
        cases b with
        | negInf => cases hY.2
        | finite r =>
          have hxr : LT.lt xc r := hX.2
          exact lt_trans hCX hxr
        | posInf => trivial
      exact absurd ⟨hA, hB⟩ hN

theorem huOutR {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a b : Endpoint R) (cc xc : R)
    (hX : Endpoint.lt a (Endpoint.finite xc) ∧ Endpoint.lt (Endpoint.finite xc) b)
    (hN : ¬(Endpoint.lt a (Endpoint.finite cc) ∧ Endpoint.lt (Endpoint.finite cc) b))
    (hCX : LT.lt xc cc) :
    ∀ yc : R, (Endpoint.lt a (Endpoint.finite yc) ∧ Endpoint.lt (Endpoint.finite yc) b) ->
      LT.lt yc cc := by
  intro yc hY
  have hTri := lt_trichotomy yc cc
  cases hTri with
  | inl h1 =>
    have hlt := h1
    exact hlt
  | inr h23 =>
    cases h23 with
    | inl h1 =>
      have heq := h1
      have hA : Endpoint.lt a (Endpoint.finite cc) := by rw [←heq]; exact hY.1
      have hB : Endpoint.lt (Endpoint.finite cc) b := by rw [←heq]; exact hY.2
      exact absurd ⟨hA, hB⟩ hN
    | inr h1 =>
      have hlt := h1
      have hA : Endpoint.lt a (Endpoint.finite cc) := by
        cases a with
        | negInf => trivial
        | finite l =>
          have hxc : LT.lt l xc := hX.1
          have hlc : LT.lt l cc := lt_trans hxc hCX
          exact hlc
        | posInf => cases hY.1
      have hB : Endpoint.lt (Endpoint.finite cc) b := by
        cases b with
        | negInf => cases hY.2
        | finite r =>
          have hyr : LT.lt yc r := hY.2
          have hcr : LT.lt cc r := lt_trans hlt hyr
          exact hcr
        | posInf => trivial
      exact absurd ⟨hA, hB⟩ hN

theorem solution {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hinj : forall (x : Power R 1), forall (y : Power R 1), forall (hx : I x), forall (hy : I y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y)
    {a0 b0 : Endpoint R} (hsub0 : (openInterval a0 b0).Subset I)
    (hlt0 : Endpoint.lt a0 b0) :
    exists (a : Endpoint R), exists (b : Endpoint R), Endpoint.lt a b /\
      (forall x, openInterval a b x -> openInterval a0 b0 x) /\
      ((forall (x : Power R 1), forall (hxI : I x), openInterval a b x ->
        exists (c1 : Power R 1), exists (c2 : Power R 1), openInterval a b c1 /\ openInterval a b c2 /\
        Lt1 c1 x /\ Lt1 x c2 /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 c1 y -> Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 x y -> Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)) \/
      (forall (x : Power R 1), forall (hxI : I x), openInterval a b x ->
        exists (c1 : Power R 1), exists (c2 : Power R 1), openInterval a b c1 /\ openInterval a b c2 /\
        Lt1 c1 x /\ Lt1 x c2 /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 c1 y -> Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 x y -> Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) \/
      (forall (x : Power R 1), forall (hxI : I x), openInterval a b x ->
        exists (c1 : Power R 1), exists (c2 : Power R 1), openInterval a b c1 /\ openInterval a b c2 /\
        Lt1 c1 x /\ Lt1 x c2 /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 c1 y -> Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 x y -> Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)) \/
      (forall (x : Power R 1), forall (hxI : I x), openInterval a b x ->
        exists (c1 : Power R 1), exists (c2 : Power R 1), openInterval a b c1 /\ openInterval a b c2 /\
        Lt1 c1 x /\ Lt1 x c2 /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 c1 y -> Lt1 y x ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) /\
        (forall (y : Power R 1), forall (hyI : I y), openInterval a b y -> Lt1 x y -> Lt1 y c2 ->
          Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1))) := by
  have hJ0 : M.S 1 (openInterval a0 b0) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a0 b0)
  have heqG : FunctionGraph (R := R) (m := 1) (n := 1)
          (A := openInterval a0 b0) (B := B)
          (fun p => f.toFun ⟨p.val, hsub0 p.property⟩)
        = {z : Power R (1 + 1) | openInterval a0 b0 (Power.left z)} ∩
          (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun) := by
      funext z
      apply propext
      constructor
      · intro ⟨hxJ, hEq⟩
        refine ⟨hxJ, hsub0 hxJ, ?_⟩
        exact hEq
      · intro ⟨hJ, hxI, hEq⟩
        refine ⟨hJ, ?_⟩
        exact hEq
  have hGraph : M.S (1 + 1)
      (FunctionGraph (R := R) (m := 1) (n := 1)
        (A := openInterval a0 b0) (B := B)
        (fun p => f.toFun ⟨p.val, hsub0 p.property⟩)) := by
    rw [heqG]
    have hJL : M.S (1 + 1)
        (fun z : Power R (1 + 1) => openInterval a0 b0 (Power.left z)) :=
      M.reindex_mem (fun _ : Fin 1 => (⟨0, by decide⟩ : Fin (1 + 1))) hJ0
    exact M.inter_mem hJL f.graph_mem
  let hfR : DefinableFunction M (openInterval a0 b0) B :=
    DefinableFunction.mk hJ0 f.codomain_mem
      (fun p => f.toFun ⟨p.val, hsub0 p.property⟩) hGraph
  have hinjR : ∀ x y (hx : openInterval a0 b0 x) (hy : openInterval a0 b0 y),
      hfR.toFun (Subtype.mk x hx) = hfR.toFun (Subtype.mk y hy) → x = y := by
    intro x y hx hy h
    exact hinj x y (hsub0 hx) (hsub0 hy) h
  have hPat : ∀ p : Power R 1, ∀ hp : openInterval a0 b0 p,
      (∃ c1 c2 : Power R 1, openInterval a0 b0 c1 ∧ openInterval a0 b0 c2 ∧
        Lt1 c1 p ∧ Lt1 p c2 ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 c1 y → Lt1 y p ->
          Lt1 (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1) ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 p y → Lt1 y c2 ->
          Lt1 (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1)) ∨
      (∃ c1 c2 : Power R 1, openInterval a0 b0 c1 ∧ openInterval a0 b0 c2 ∧
        Lt1 c1 p ∧ Lt1 p c2 ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 c1 y → Lt1 y p ->
          Lt1 (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1) ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 p y → Lt1 y c2 ->
          Lt1 (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1)) ∨
      (∃ c1 c2 : Power R 1, openInterval a0 b0 c1 ∧ openInterval a0 b0 c2 ∧
        Lt1 c1 p ∧ Lt1 p c2 ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 c1 y → Lt1 y p ->
          Lt1 (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1) ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 p y → Lt1 y c2 ->
          Lt1 (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1)) ∨
      (∃ c1 c2 : Power R 1, openInterval a0 b0 c1 ∧ openInterval a0 b0 c2 ∧
        Lt1 c1 p ∧ Lt1 p c2 ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 c1 y → Lt1 y p ->
          Lt1 (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1) ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 p y → Lt1 y c2 ->
          Lt1 (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1)) := by
    intro p hp
    exact Monotonicity_Theorem.pattern_at_interior_point M hfR hinjR hp
-- Left-above half: definable via failure matrix, projection,
-- complement closure, reintersection, projection.
  have hFLA : M.S ((1 + 1) + (1 + (1 + 1)))
      (fun q : Power R ((1 + 1) + (1 + (1 + 1))) =>
        openInterval a0 b0 (fun i : Fin 1 => q (huC0 i)) ∧
        openInterval a0 b0 (fun i : Fin 1 => q (huX1 i)) ∧
        openInterval a0 b0 (fun i : Fin 1 => q (huY2 i)) ∧
        LT.lt ((fun j : Fin 2 => q (huLt01 j)) 0)
          ((fun j : Fin 2 => q (huLt01 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (huLt02 j)) 0)
          ((fun j : Fin 2 => q (huLt02 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (huLt21 j)) 0)
          ((fun j : Fin 2 => q (huLt21 j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGw j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGx j)) ∧
        (LT.lt ((fun j : Fin 2 => q (huBadAbove j)) 0)
          ((fun j : Fin 2 => q (huBadAbove j)) 1) ∨
        q (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))))) :=
    M.inter_mem (M.reindex_mem huC0 hJ0)
      (M.inter_mem (M.reindex_mem huX1 hJ0)
        (M.inter_mem (M.reindex_mem huY2 hJ0)
          (M.inter_mem (M.reindex_mem huLt01 M.lt_mem)
            (M.inter_mem (M.reindex_mem huLt02 M.lt_mem)
              (M.inter_mem (M.reindex_mem huLt21 M.lt_mem)
                (M.inter_mem (M.reindex_mem huGw f.graph_mem)
                  (M.inter_mem (M.reindex_mem huGx f.graph_mem)
                    (M.union_mem (M.reindex_mem huBadAbove M.lt_mem)
                      (M.diagonal_mem (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                        (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) (by decide))))))))))
  have hP2LA : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ∃ t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
            ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
            ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
            ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.existsLast_mem hFLA
  have hC2LA : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
            ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
            ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
            ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.compl_mem hP2LA
  have hWLA : M.S (1 + 1)
      (fun q : Power R (1 + 1) =>
        openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
        openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
        LT.lt ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
              else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
              else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
        (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
          (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
            openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
            openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
            openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
              ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
              ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
              ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
            (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
              ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
            q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
            (Power.append q2 t)) q) :=
    M.inter_mem
      (M.reindex_mem (fun _ : Fin 1 => (⟨0, by decide⟩ : Fin (1 + 1))) hJ0)
      (M.inter_mem
        (M.reindex_mem (fun _ : Fin 1 => (⟨1, by decide⟩ : Fin (1 + 1))) hJ0)
        (M.inter_mem
          (M.reindex_mem (fun j : Fin 2 =>
            (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
              else (⟨1, by decide⟩ : Fin (1 + 1)))) M.lt_mem)
          hC2LA))
  have hHLAP : M.S (1 + 1)
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i))) :=
    M.reindex_mem huSwap hWLA
  have hHLA : M.S 1 (fun x : Power R 1 => ∃ c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) :=
    M.existsLast_mem hHLAP

  -- Left-below half.
  have hFLB : M.S ((1 + 1) + (1 + (1 + 1)))
      (fun q : Power R ((1 + 1) + (1 + (1 + 1))) =>
        openInterval a0 b0 (fun i : Fin 1 => q (huC0 i)) ∧
        openInterval a0 b0 (fun i : Fin 1 => q (huX1 i)) ∧
        openInterval a0 b0 (fun i : Fin 1 => q (huY2 i)) ∧
        LT.lt ((fun j : Fin 2 => q (huLt01 j)) 0)
          ((fun j : Fin 2 => q (huLt01 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (huLt02 j)) 0)
          ((fun j : Fin 2 => q (huLt02 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (huLt21 j)) 0)
          ((fun j : Fin 2 => q (huLt21 j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGw j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGx j)) ∧
        (LT.lt ((fun j : Fin 2 => q (huBadBelow j)) 0)
          ((fun j : Fin 2 => q (huBadBelow j)) 1) ∨
        q (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))))) :=
    M.inter_mem (M.reindex_mem huC0 hJ0)
      (M.inter_mem (M.reindex_mem huX1 hJ0)
        (M.inter_mem (M.reindex_mem huY2 hJ0)
          (M.inter_mem (M.reindex_mem huLt01 M.lt_mem)
            (M.inter_mem (M.reindex_mem huLt02 M.lt_mem)
              (M.inter_mem (M.reindex_mem huLt21 M.lt_mem)
                (M.inter_mem (M.reindex_mem huGw f.graph_mem)
                  (M.inter_mem (M.reindex_mem huGx f.graph_mem)
                    (M.union_mem (M.reindex_mem huBadBelow M.lt_mem)
                      (M.diagonal_mem (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                        (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) (by decide))))))))))
  have hP2LB : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ∃ t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
            ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
            ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
            ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.existsLast_mem hFLB
  have hC2LB : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
            ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
            ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
            ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.compl_mem hP2LB
  have hWLB : M.S (1 + 1)
      (fun q : Power R (1 + 1) =>
        openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
        openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
        LT.lt ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
              else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
              else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
        (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
          (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
            openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
            openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
            openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
              ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
              ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
              ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
            (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
              ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
            q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
            (Power.append q2 t)) q) :=
    M.inter_mem
      (M.reindex_mem (fun _ : Fin 1 => (⟨0, by decide⟩ : Fin (1 + 1))) hJ0)
      (M.inter_mem
        (M.reindex_mem (fun _ : Fin 1 => (⟨1, by decide⟩ : Fin (1 + 1))) hJ0)
        (M.inter_mem
          (M.reindex_mem (fun j : Fin 2 =>
            (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
              else (⟨1, by decide⟩ : Fin (1 + 1)))) M.lt_mem)
          hC2LB))
  have hHLBP : M.S (1 + 1)
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i))) :=
    M.reindex_mem huSwap hWLB
  have hHLB : M.S 1 (fun x : Power R 1 => ∃ c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) :=
    M.existsLast_mem hHLBP

  -- Right-above half.
  have hFRA : M.S ((1 + 1) + (1 + (1 + 1)))
      (fun q : Power R ((1 + 1) + (1 + (1 + 1))) =>
        openInterval a0 b0 (fun i : Fin 1 => q (huC0 i)) ∧
        openInterval a0 b0 (fun i : Fin 1 => q (huX1 i)) ∧
        openInterval a0 b0 (fun i : Fin 1 => q (huY2 i)) ∧
        LT.lt ((fun j : Fin 2 => q (huLt10 j)) 0)
          ((fun j : Fin 2 => q (huLt10 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (huLt12 j)) 0)
          ((fun j : Fin 2 => q (huLt12 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (huLt20 j)) 0)
          ((fun j : Fin 2 => q (huLt20 j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGw j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGx j)) ∧
        (LT.lt ((fun j : Fin 2 => q (huBadAbove j)) 0)
          ((fun j : Fin 2 => q (huBadAbove j)) 1) ∨
        q (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))))) :=
    M.inter_mem (M.reindex_mem huC0 hJ0)
      (M.inter_mem (M.reindex_mem huX1 hJ0)
        (M.inter_mem (M.reindex_mem huY2 hJ0)
          (M.inter_mem (M.reindex_mem huLt10 M.lt_mem)
            (M.inter_mem (M.reindex_mem huLt12 M.lt_mem)
              (M.inter_mem (M.reindex_mem huLt20 M.lt_mem)
                (M.inter_mem (M.reindex_mem huGw f.graph_mem)
                  (M.inter_mem (M.reindex_mem huGx f.graph_mem)
                    (M.union_mem (M.reindex_mem huBadAbove M.lt_mem)
                      (M.diagonal_mem (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                        (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) (by decide))))))))))
  have hP2RA : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ∃ t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
            ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
            ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
            ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.existsLast_mem hFRA
  have hC2RA : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
            ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
            ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
            ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.compl_mem hP2RA
  have hWRA : M.S (1 + 1)
      (fun q : Power R (1 + 1) =>
        openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
        openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
        LT.lt ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
        (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
          (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
            openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
            openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
            openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
              ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
              ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
              ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
            (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
              ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
            q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
            (Power.append q2 t)) q) :=
    M.inter_mem
      (M.reindex_mem (fun _ : Fin 1 => (⟨0, by decide⟩ : Fin (1 + 1))) hJ0)
      (M.inter_mem
        (M.reindex_mem (fun _ : Fin 1 => (⟨1, by decide⟩ : Fin (1 + 1))) hJ0)
        (M.inter_mem
          (M.reindex_mem (fun j : Fin 2 =>
            (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) M.lt_mem)
          hC2RA))
  have hHRAP : M.S (1 + 1)
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i))) :=
    M.reindex_mem huSwap hWRA
  have hHRA : M.S 1 (fun x : Power R 1 => ∃ c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) :=
    M.existsLast_mem hHRAP

  -- Right-below half.
  have hFRB : M.S ((1 + 1) + (1 + (1 + 1)))
      (fun q : Power R ((1 + 1) + (1 + (1 + 1))) =>
        openInterval a0 b0 (fun i : Fin 1 => q (huC0 i)) ∧
        openInterval a0 b0 (fun i : Fin 1 => q (huX1 i)) ∧
        openInterval a0 b0 (fun i : Fin 1 => q (huY2 i)) ∧
        LT.lt ((fun j : Fin 2 => q (huLt10 j)) 0)
          ((fun j : Fin 2 => q (huLt10 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (huLt12 j)) 0)
          ((fun j : Fin 2 => q (huLt12 j)) 1) ∧
        LT.lt ((fun j : Fin 2 => q (huLt20 j)) 0)
          ((fun j : Fin 2 => q (huLt20 j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGw j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGx j)) ∧
        (LT.lt ((fun j : Fin 2 => q (huBadBelow j)) 0)
          ((fun j : Fin 2 => q (huBadBelow j)) 1) ∨
        q (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))))) :=
    M.inter_mem (M.reindex_mem huC0 hJ0)
      (M.inter_mem (M.reindex_mem huX1 hJ0)
        (M.inter_mem (M.reindex_mem huY2 hJ0)
          (M.inter_mem (M.reindex_mem huLt10 M.lt_mem)
            (M.inter_mem (M.reindex_mem huLt12 M.lt_mem)
              (M.inter_mem (M.reindex_mem huLt20 M.lt_mem)
                (M.inter_mem (M.reindex_mem huGw f.graph_mem)
                  (M.inter_mem (M.reindex_mem huGx f.graph_mem)
                    (M.union_mem (M.reindex_mem huBadBelow M.lt_mem)
                      (M.diagonal_mem (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                        (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) (by decide))))))))))
  have hP2RB : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ∃ t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
            ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
            ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
            ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.existsLast_mem hFRB
  have hC2RB : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
            ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
            ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
          LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
            ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.compl_mem hP2RB
  have hWRB : M.S (1 + 1)
      (fun q : Power R (1 + 1) =>
        openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
        openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
        LT.lt ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
        (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
          (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
            openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
            openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
            openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
              ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
              ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
            LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
              ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
            (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
              ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
            q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
            (Power.append q2 t)) q) :=
    M.inter_mem
      (M.reindex_mem (fun _ : Fin 1 => (⟨0, by decide⟩ : Fin (1 + 1))) hJ0)
      (M.inter_mem
        (M.reindex_mem (fun _ : Fin 1 => (⟨1, by decide⟩ : Fin (1 + 1))) hJ0)
        (M.inter_mem
          (M.reindex_mem (fun j : Fin 2 =>
            (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) M.lt_mem)
          hC2RB))
  have hHRBP : M.S (1 + 1)
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i))) :=
    M.reindex_mem huSwap hWRB
  have hHRB : M.S 1 (fun x : Power R 1 => ∃ c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) :=
    M.existsLast_mem hHRBP

  -- Intersections (the four uniform pattern sets).
  have hH1 : M.S 1 (setInter
      (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
      (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))) :=
    M.inter_mem hHLA hHRA
  have hHH2 : M.S 1 (setInter
      (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
      (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))) :=
    M.inter_mem hHLA hHRB
  have hHH3 : M.S 1 (setInter
      (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
      (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))) :=
    M.inter_mem hHLB hHRA
  have hHH4 : M.S 1 (setInter
      (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
      (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))) :=
    M.inter_mem hHLB hHRB
  -- Covering, above-above case: pattern witnesses land in HLA and HRA.
  have hCovPP : ∀ p : Power R 1, ∀ hp : openInterval a0 b0 p,
      (∃ c1 c2 : Power R 1, openInterval a0 b0 c1 ∧ openInterval a0 b0 c2 ∧
        Lt1 c1 p ∧ Lt1 p c2 ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 c1 y → Lt1 y p ->
          Lt1 (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1) ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 p y → Lt1 y c2 ->
          Lt1 (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1)) ->
      ((fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c)) p) := by
    intro p hp hPP
    obtain ⟨c1, c2, hJc1, hJc2, hLT1, hLT2, hL, hR⟩ := hPP
    refine ⟨c1, ?_, ?_, ?_, ?_⟩
    · -- J0c-part via funext bridge.
      have e : (fun _ : Fin 1 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          ((⟨0, by decide⟩ : Fin (1 + 1)))) = c1 := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      rw [e]
      exact hJc1
    · -- J0x-part via funext bridge.
      have e : (fun _ : Fin 1 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          ((⟨1, by decide⟩ : Fin (1 + 1)))) = p := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      rw [e]
      exact hp
    · -- Lt-part by closed ascription.
      have g : LT.lt ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
            else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
            else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) := hLT1
      exact g
    · -- Failure part by contrapositive.
      intro hF
      obtain ⟨t, hYy, h1, h2, hGw, hGx, hBad⟩ := hF
      obtain ⟨hLt21, hGW, hGX, hBAD⟩ := hBad
      have hGWc := hGW
      have hGXc := hGX
      let yT : Power R 1 := (fun _ : Fin 1 => t ((⟨0, by decide⟩ : Fin (1 + (1 + 1)))))
      let wT : Power R 1 := (fun _ : Fin 1 => t ((⟨1, by decide⟩ : Fin (1 + (1 + 1)))))
      let vT : Power R 1 := (fun _ : Fin 1 => t ((⟨2, by decide⟩ : Fin (1 + (1 + 1)))))
      have hYyT : openInterval a0 b0 yT := h2
      have e1 : Lt1 c1 yT := hGx
      have e2 : Lt1 yT p := hLt21
      have hAbove : Lt1 (hfR.toFun (Subtype.mk p hp)).1
          (hfR.toFun (Subtype.mk yT hYyT)).1 := hL yT hYyT e1 e2
      obtain ⟨hxW0, hEqW0⟩ := hGW
      obtain ⟨hxV0, hEqV0⟩ := hGX
      have eGW : (fun j : Fin (1 + 1) => (Power.append
          (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGw j))
          = Power.append yT wT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGw j
              = (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGw j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = yT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append yT wT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left yT wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append yT wT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGw j
              = (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGw j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = wT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append yT wT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right yT wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append yT wT) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => (Power.append
          (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGx j))
          = Power.append p vT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGx j
              = (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGx j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = p ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append p vT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left p vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append p vT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGx j
              = (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGx j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = vT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append p vT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right p vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append p vT) j := by rw [hj1]
      have hGW' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append yT wT) := by
        rw [← eGW]
        exact hGWc
      have hGX' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append p vT) := by
        rw [← eGX]
        exact hGXc
      obtain ⟨hxW, hEqW⟩ := hGW'
      obtain ⟨hxV, hEqV⟩ := hGX'
      have hLW : Power.left (Power.append yT wT) = yT := by
        funext i
        exact Fin.append_left yT wT i
      have hRW : Power.right (Power.append yT wT) = wT := by
        funext i
        exact Fin.append_right yT wT i
      have hLV : Power.left (Power.append p vT) = p := by
        funext i
        exact Fin.append_left p vT i
      have hRV : Power.right (Power.append p vT) = vT := by
        funext i
        exact Fin.append_right p vT i
      have hArgW : (⟨Power.left (Power.append yT wT), hxW⟩ : {x : Power R 1 // I x})
          = ⟨yT, hsub0 hYyT⟩ := Subtype.ext hLW
      have hArgV : (⟨Power.left (Power.append p vT), hxV⟩ : {x : Power R 1 // I x})
          = ⟨p, hsub0 hp⟩ := Subtype.ext hLV
      have eW : (hfR.toFun (Subtype.mk yT hYyT)).1 = wT := by
        have h1 : (f.toFun ⟨Power.left (Power.append yT wT), hxW⟩).1
            = (hfR.toFun ⟨yT, hYyT⟩).1 := by
          rw [hArgW]
        rw [← hRW]
        rw [← h1]
        exact hEqW.symm
      have eV : (hfR.toFun (Subtype.mk p hp)).1 = vT := by
        have h1 : (f.toFun ⟨Power.left (Power.append p vT), hxV⟩).1
            = (hfR.toFun ⟨p, hp⟩).1 := by
          rw [hArgV]
        rw [← hRV]
        rw [← h1]
        exact hEqV.symm
      rw [eV, eW] at hAbove
      have g2 : LT.lt (Power.coord1 vT) (Power.coord1 wT) := hAbove
      cases hBAD with
      | inl hIn =>
        have g1 : LT.lt (Power.coord1 wT) (Power.coord1 vT) := hIn
        exact lt_irrefl _ (lt_trans g1 g2)
      | inr hEqB =>
        have e : Power.coord1 wT = Power.coord1 vT := hEqB
        have g3 : LT.lt (Power.coord1 vT) (Power.coord1 vT) := e ▸ g2
        exact lt_irrefl _ g3
  -- Covering, left-above case: pattern witnesses land in HLA.
  have hCovLA : ∀ p : Power R 1, ∀ hp : openInterval a0 b0 p,
      (∃ c1 : Power R 1, openInterval a0 b0 c1 ∧
        Lt1 c1 p ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 c1 y → Lt1 y p ->
          Lt1 (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1)) ->
      ((fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c)) p) := by
    intro p hp hPP
    obtain ⟨c1, hJc1, hLT1, hL⟩ := hPP
    refine ⟨c1, ?_, ?_, ?_, ?_⟩
    · -- J0c-part via funext bridge.
      have e : (fun _ : Fin 1 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          ((⟨0, by decide⟩ : Fin (1 + 1)))) = c1 := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      rw [e]
      exact hJc1
    · -- J0x-part via funext bridge.
      have e : (fun _ : Fin 1 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          ((⟨1, by decide⟩ : Fin (1 + 1)))) = p := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      rw [e]
      exact hp
    · -- Lt-part by closed ascription.
      have g : LT.lt ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
            else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
            else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) := hLT1
      exact g
    · -- Failure part by contrapositive.
      intro hF
      obtain ⟨t, hYy, h1, h2, hGw, hGx, hBad⟩ := hF
      obtain ⟨hLt21, hGW, hGX, hBAD⟩ := hBad
      have hGWc := hGW
      have hGXc := hGX
      let yT : Power R 1 := (fun _ : Fin 1 => t ((⟨0, by decide⟩ : Fin (1 + (1 + 1)))))
      let wT : Power R 1 := (fun _ : Fin 1 => t ((⟨1, by decide⟩ : Fin (1 + (1 + 1)))))
      let vT : Power R 1 := (fun _ : Fin 1 => t ((⟨2, by decide⟩ : Fin (1 + (1 + 1)))))
      have hYyT : openInterval a0 b0 yT := h2
      have e1 : Lt1 c1 yT := hGx
      have e2 : Lt1 yT p := hLt21
      have hAbove : Lt1 (hfR.toFun (Subtype.mk p hp)).1
          (hfR.toFun (Subtype.mk yT hYyT)).1 := hL yT hYyT e1 e2
      obtain ⟨hxW0, hEqW0⟩ := hGW
      obtain ⟨hxV0, hEqV0⟩ := hGX
      have eGW : (fun j : Fin (1 + 1) => (Power.append
          (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGw j))
          = Power.append yT wT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGw j
              = (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGw j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = yT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append yT wT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left yT wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append yT wT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGw j
              = (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGw j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = wT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append yT wT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right yT wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append yT wT) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => (Power.append
          (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGx j))
          = Power.append p vT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGx j
              = (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGx j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = p ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append p vT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left p vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append p vT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGx j
              = (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGx j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = vT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append p vT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right p vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append p vT) j := by rw [hj1]
      have hGW' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append yT wT) := by
        rw [← eGW]
        exact hGWc
      have hGX' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append p vT) := by
        rw [← eGX]
        exact hGXc
      obtain ⟨hxW, hEqW⟩ := hGW'
      obtain ⟨hxV, hEqV⟩ := hGX'
      have hLW : Power.left (Power.append yT wT) = yT := by
        funext i
        exact Fin.append_left yT wT i
      have hRW : Power.right (Power.append yT wT) = wT := by
        funext i
        exact Fin.append_right yT wT i
      have hLV : Power.left (Power.append p vT) = p := by
        funext i
        exact Fin.append_left p vT i
      have hRV : Power.right (Power.append p vT) = vT := by
        funext i
        exact Fin.append_right p vT i
      have hArgW : (⟨Power.left (Power.append yT wT), hxW⟩ : {x : Power R 1 // I x})
          = ⟨yT, hsub0 hYyT⟩ := Subtype.ext hLW
      have hArgV : (⟨Power.left (Power.append p vT), hxV⟩ : {x : Power R 1 // I x})
          = ⟨p, hsub0 hp⟩ := Subtype.ext hLV
      have eW : (hfR.toFun (Subtype.mk yT hYyT)).1 = wT := by
        have h1 : (f.toFun ⟨Power.left (Power.append yT wT), hxW⟩).1
            = (hfR.toFun ⟨yT, hYyT⟩).1 := by
          rw [hArgW]
        rw [← hRW]
        rw [← h1]
        exact hEqW.symm
      have eV : (hfR.toFun (Subtype.mk p hp)).1 = vT := by
        have h1 : (f.toFun ⟨Power.left (Power.append p vT), hxV⟩).1
            = (hfR.toFun ⟨p, hp⟩).1 := by
          rw [hArgV]
        rw [← hRV]
        rw [← h1]
        exact hEqV.symm
      rw [eV, eW] at hAbove
      have g2 : LT.lt (Power.coord1 vT) (Power.coord1 wT) := hAbove
      cases hBAD with
      | inl hIn =>
        have g1 : LT.lt (Power.coord1 wT) (Power.coord1 vT) := hIn
        exact lt_irrefl _ (lt_trans g1 g2)
      | inr hEqB =>
        have e : Power.coord1 wT = Power.coord1 vT := hEqB
        have g3 : LT.lt (Power.coord1 vT) (Power.coord1 vT) := e ▸ g2
        exact lt_irrefl _ g3

  -- Covering, right-above case: pattern witnesses land in HRA.
  have hCovRA : ∀ p : Power R 1, ∀ hp : openInterval a0 b0 p,
      (∃ c2 : Power R 1, openInterval a0 b0 c2 ∧
        Lt1 p c2 ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 p y → Lt1 y c2 ->
          Lt1 (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1)) ->
      ((fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c)) p) := by
    intro p hp hPP
    obtain ⟨c2, hJc2, hLT2, hR⟩ := hPP
    refine ⟨c2, ?_, ?_, ?_, ?_⟩
    · -- J0c-part via funext bridge.
      have e : (fun _ : Fin 1 => (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i))
          ((⟨0, by decide⟩ : Fin (1 + 1)))) = c2 := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      rw [e]
      exact hJc2
    · -- J0x-part via funext bridge.
      have e : (fun _ : Fin 1 => (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i))
          ((⟨1, by decide⟩ : Fin (1 + 1)))) = p := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      rw [e]
      exact hp
    · -- Lt-part by closed ascription.
      have g : LT.lt ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i))
          (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
            else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i))
          (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
            else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) := hLT2
      exact g
    · -- Failure part by contrapositive.
      intro hF
      obtain ⟨t, hYy, h1, h2, hGw, hGx, hBad⟩ := hF
      obtain ⟨hLt20, hGW, hGX, hBAD⟩ := hBad
      have hGWc := hGW
      have hGXc := hGX
      let yT : Power R 1 := (fun _ : Fin 1 => t ((⟨0, by decide⟩ : Fin (1 + (1 + 1)))))
      let wT : Power R 1 := (fun _ : Fin 1 => t ((⟨1, by decide⟩ : Fin (1 + (1 + 1)))))
      let vT : Power R 1 := (fun _ : Fin 1 => t ((⟨2, by decide⟩ : Fin (1 + (1 + 1)))))
      have hYyT : openInterval a0 b0 yT := h2
      have e1 : Lt1 p yT := hGx
      have e2 : Lt1 yT c2 := hLt20
      have hAbove : Lt1 (hfR.toFun (Subtype.mk p hp)).1
          (hfR.toFun (Subtype.mk yT hYyT)).1 := hR yT hYyT e1 e2
      obtain ⟨hxW0, hEqW0⟩ := hGW
      obtain ⟨hxV0, hEqV0⟩ := hGX
      have eGW : (fun j : Fin (1 + 1) => (Power.append
          (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGw j))
          = Power.append yT wT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGw j
              = (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGw j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t)
                (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = yT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append yT wT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left yT wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append yT wT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGw j
              = (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGw j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t)
                (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = wT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append yT wT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right yT wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append yT wT) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => (Power.append
          (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGx j))
          = Power.append p vT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGx j
              = (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGx j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t)
                (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = p ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append p vT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left p vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append p vT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGx j
              = (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGx j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t)
                (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = vT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append p vT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right p vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append p vT) j := by rw [hj1]
      have hGW' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append yT wT) := by
        rw [← eGW]
        exact hGWc
      have hGX' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append p vT) := by
        rw [← eGX]
        exact hGXc
      obtain ⟨hxW, hEqW⟩ := hGW'
      obtain ⟨hxV, hEqV⟩ := hGX'
      have hLW : Power.left (Power.append yT wT) = yT := by
        funext i
        exact Fin.append_left yT wT i
      have hRW : Power.right (Power.append yT wT) = wT := by
        funext i
        exact Fin.append_right yT wT i
      have hLV : Power.left (Power.append p vT) = p := by
        funext i
        exact Fin.append_left p vT i
      have hRV : Power.right (Power.append p vT) = vT := by
        funext i
        exact Fin.append_right p vT i
      have hArgW : (⟨Power.left (Power.append yT wT), hxW⟩ : {x : Power R 1 // I x})
          = ⟨yT, hsub0 hYyT⟩ := Subtype.ext hLW
      have hArgV : (⟨Power.left (Power.append p vT), hxV⟩ : {x : Power R 1 // I x})
          = ⟨p, hsub0 hp⟩ := Subtype.ext hLV
      have eW : (hfR.toFun (Subtype.mk yT hYyT)).1 = wT := by
        have h1 : (f.toFun ⟨Power.left (Power.append yT wT), hxW⟩).1
            = (hfR.toFun ⟨yT, hYyT⟩).1 := by
          rw [hArgW]
        rw [← hRW]
        rw [← h1]
        exact hEqW.symm
      have eV : (hfR.toFun (Subtype.mk p hp)).1 = vT := by
        have h1 : (f.toFun ⟨Power.left (Power.append p vT), hxV⟩).1
            = (hfR.toFun ⟨p, hp⟩).1 := by
          rw [hArgV]
        rw [← hRV]
        rw [← h1]
        exact hEqV.symm
      rw [eV, eW] at hAbove
      have g2 : LT.lt (Power.coord1 vT) (Power.coord1 wT) := hAbove
      cases hBAD with
      | inl hIn =>
        have g1 : LT.lt (Power.coord1 wT) (Power.coord1 vT) := hIn
        exact lt_irrefl _ (lt_trans g1 g2)
      | inr hEqB =>
        have e : Power.coord1 wT = Power.coord1 vT := hEqB
        have g3 : LT.lt (Power.coord1 vT) (Power.coord1 vT) := e ▸ g2
        exact lt_irrefl _ g3

  -- Covering, left-below case: pattern witnesses land in HLB.
  have hCovLB : ∀ p : Power R 1, ∀ hp : openInterval a0 b0 p,
      (∃ c1 : Power R 1, openInterval a0 b0 c1 ∧
        Lt1 c1 p ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 c1 y → Lt1 y p ->
          Lt1 (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1)) ->
      ((fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c)) p) := by
    intro p hp hPP
    obtain ⟨c1, hJc1, hLT1, hL⟩ := hPP
    refine ⟨c1, ?_, ?_, ?_, ?_⟩
    · -- J0c-part via funext bridge.
      have e : (fun _ : Fin 1 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          ((⟨0, by decide⟩ : Fin (1 + 1)))) = c1 := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      rw [e]
      exact hJc1
    · -- J0x-part via funext bridge.
      have e : (fun _ : Fin 1 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          ((⟨1, by decide⟩ : Fin (1 + 1)))) = p := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      rw [e]
      exact hp
    · -- Lt-part by closed ascription.
      have g : LT.lt ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
            else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
          (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
            else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) := hLT1
      exact g
    · -- Failure part by contrapositive.
      intro hF
      obtain ⟨t, hYy, h1, h2, hGw, hGx, hBad⟩ := hF
      obtain ⟨hLt21, hGW, hGX, hBAD⟩ := hBad
      have hGWc := hGW
      have hGXc := hGX
      let yT : Power R 1 := (fun _ : Fin 1 => t ((⟨0, by decide⟩ : Fin (1 + (1 + 1)))))
      let wT : Power R 1 := (fun _ : Fin 1 => t ((⟨1, by decide⟩ : Fin (1 + (1 + 1)))))
      let vT : Power R 1 := (fun _ : Fin 1 => t ((⟨2, by decide⟩ : Fin (1 + (1 + 1)))))
      have hYyT : openInterval a0 b0 yT := h2
      have e1 : Lt1 c1 yT := hGx
      have e2 : Lt1 yT p := hLt21
      have hBelow : Lt1 (hfR.toFun (Subtype.mk yT hYyT)).1
          (hfR.toFun (Subtype.mk p hp)).1 := hL yT hYyT e1 e2
      obtain ⟨hxW0, hEqW0⟩ := hGW
      obtain ⟨hxV0, hEqV0⟩ := hGX
      have eGW : (fun j : Fin (1 + 1) => (Power.append
          (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGw j))
          = Power.append yT wT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGw j
              = (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGw j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = yT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append yT wT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left yT wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append yT wT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGw j
              = (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGw j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = wT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append yT wT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right yT wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append yT wT) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => (Power.append
          (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGx j))
          = Power.append p vT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGx j
              = (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGx j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = p ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append p vT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left p vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append p vT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGx j
              = (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t) (huGx j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i)) t)
                (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = vT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append p vT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right p vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append p vT) j := by rw [hj1]
      have hGW' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append yT wT) := by
        rw [← eGW]
        exact hGWc
      have hGX' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append p vT) := by
        rw [← eGX]
        exact hGXc
      obtain ⟨hxW, hEqW⟩ := hGW'
      obtain ⟨hxV, hEqV⟩ := hGX'
      have hLW : Power.left (Power.append yT wT) = yT := by
        funext i
        exact Fin.append_left yT wT i
      have hRW : Power.right (Power.append yT wT) = wT := by
        funext i
        exact Fin.append_right yT wT i
      have hLV : Power.left (Power.append p vT) = p := by
        funext i
        exact Fin.append_left p vT i
      have hRV : Power.right (Power.append p vT) = vT := by
        funext i
        exact Fin.append_right p vT i
      have hArgW : (⟨Power.left (Power.append yT wT), hxW⟩ : {x : Power R 1 // I x})
          = ⟨yT, hsub0 hYyT⟩ := Subtype.ext hLW
      have hArgV : (⟨Power.left (Power.append p vT), hxV⟩ : {x : Power R 1 // I x})
          = ⟨p, hsub0 hp⟩ := Subtype.ext hLV
      have eW : (hfR.toFun (Subtype.mk yT hYyT)).1 = wT := by
        have h1 : (f.toFun ⟨Power.left (Power.append yT wT), hxW⟩).1
            = (hfR.toFun ⟨yT, hYyT⟩).1 := by
          rw [hArgW]
        rw [← hRW]
        rw [← h1]
        exact hEqW.symm
      have eV : (hfR.toFun (Subtype.mk p hp)).1 = vT := by
        have h1 : (f.toFun ⟨Power.left (Power.append p vT), hxV⟩).1
            = (hfR.toFun ⟨p, hp⟩).1 := by
          rw [hArgV]
        rw [← hRV]
        rw [← h1]
        exact hEqV.symm
      rw [eV, eW] at hBelow
      have g2 : LT.lt (Power.coord1 wT) (Power.coord1 vT) := hBelow
      cases hBAD with
      | inl hIn =>
        have g1 : LT.lt (Power.coord1 vT) (Power.coord1 wT) := hIn
        exact lt_irrefl _ (lt_trans g2 g1)
      | inr hEqB =>
        have e : Power.coord1 wT = Power.coord1 vT := hEqB
        have g3 : LT.lt (Power.coord1 vT) (Power.coord1 vT) := e ▸ g2
        exact lt_irrefl _ g3

  -- Covering, right-below case: pattern witnesses land in HRB.
  have hCovRB : ∀ p : Power R 1, ∀ hp : openInterval a0 b0 p,
      (∃ c2 : Power R 1, openInterval a0 b0 c2 ∧
        Lt1 p c2 ∧
        (∀ y (hy : openInterval a0 b0 y), Lt1 p y → Lt1 y c2 ->
          Lt1 (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1)) ->
      ((fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c)) p) := by
    intro p hp hPP
    obtain ⟨c2, hJc2, hLT2, hR⟩ := hPP
    refine ⟨c2, ?_, ?_, ?_, ?_⟩
    · -- J0c-part via funext bridge.
      have e : (fun _ : Fin 1 => (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i))
          ((⟨0, by decide⟩ : Fin (1 + 1)))) = c2 := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      rw [e]
      exact hJc2
    · -- J0x-part via funext bridge.
      have e : (fun _ : Fin 1 => (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i))
          ((⟨1, by decide⟩ : Fin (1 + 1)))) = p := by
        funext i
        have hiv : i.val < 1 := i.isLt
        have hi0 : i.val = 0 := by omega
        have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
        rw [hi]
        rfl
      rw [e]
      exact hp
    · -- Lt-part by closed ascription.
      have g : LT.lt ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i))
          (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
            else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i))
          (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
            else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) := hLT2
      exact g
    · -- Failure part by contrapositive.
      intro hF
      obtain ⟨t, hYy, h1, h2, hGw, hGx, hBad⟩ := hF
      obtain ⟨hLt20, hGW, hGX, hBAD⟩ := hBad
      have hGWc := hGW
      have hGXc := hGX
      let yT : Power R 1 := (fun _ : Fin 1 => t ((⟨0, by decide⟩ : Fin (1 + (1 + 1)))))
      let wT : Power R 1 := (fun _ : Fin 1 => t ((⟨1, by decide⟩ : Fin (1 + (1 + 1)))))
      let vT : Power R 1 := (fun _ : Fin 1 => t ((⟨2, by decide⟩ : Fin (1 + (1 + 1)))))
      have hYyT : openInterval a0 b0 yT := h2
      have e1 : Lt1 p yT := hGx
      have e2 : Lt1 yT c2 := hLt20
      have hBelow : Lt1 (hfR.toFun (Subtype.mk yT hYyT)).1
          (hfR.toFun (Subtype.mk p hp)).1 := hR yT hYyT e1 e2
      obtain ⟨hxW0, hEqW0⟩ := hGW
      obtain ⟨hxV0, hEqV0⟩ := hGX
      have eGW : (fun j : Fin (1 + 1) => (Power.append
          (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGw j))
          = Power.append yT wT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGw j
              = (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGw j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t)
                (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = yT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append yT wT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left yT wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append yT wT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGw j
              = (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGw j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t)
                (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = wT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append yT wT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right yT wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append yT wT) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => (Power.append
          (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGx j))
          = Power.append p vT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGx j
              = (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGx j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t)
                (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = p ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append p vT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left p vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append p vT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGx j
              = (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t) (huGx j)
              = (Power.append
                (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i)) t)
                (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = vT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append p vT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right p vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append p vT) j := by rw [hj1]
      have hGW' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append yT wT) := by
        rw [← eGW]
        exact hGWc
      have hGX' : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append p vT) := by
        rw [← eGX]
        exact hGXc
      obtain ⟨hxW, hEqW⟩ := hGW'
      obtain ⟨hxV, hEqV⟩ := hGX'
      have hLW : Power.left (Power.append yT wT) = yT := by
        funext i
        exact Fin.append_left yT wT i
      have hRW : Power.right (Power.append yT wT) = wT := by
        funext i
        exact Fin.append_right yT wT i
      have hLV : Power.left (Power.append p vT) = p := by
        funext i
        exact Fin.append_left p vT i
      have hRV : Power.right (Power.append p vT) = vT := by
        funext i
        exact Fin.append_right p vT i
      have hArgW : (⟨Power.left (Power.append yT wT), hxW⟩ : {x : Power R 1 // I x})
          = ⟨yT, hsub0 hYyT⟩ := Subtype.ext hLW
      have hArgV : (⟨Power.left (Power.append p vT), hxV⟩ : {x : Power R 1 // I x})
          = ⟨p, hsub0 hp⟩ := Subtype.ext hLV
      have eW : (hfR.toFun (Subtype.mk yT hYyT)).1 = wT := by
        have h1 : (f.toFun ⟨Power.left (Power.append yT wT), hxW⟩).1
            = (hfR.toFun ⟨yT, hYyT⟩).1 := by
          rw [hArgW]
        rw [← hRW]
        rw [← h1]
        exact hEqW.symm
      have eV : (hfR.toFun (Subtype.mk p hp)).1 = vT := by
        have h1 : (f.toFun ⟨Power.left (Power.append p vT), hxV⟩).1
            = (hfR.toFun ⟨p, hp⟩).1 := by
          rw [hArgV]
        rw [← hRV]
        rw [← h1]
        exact hEqV.symm
      rw [eV, eW] at hBelow
      have g2 : LT.lt (Power.coord1 wT) (Power.coord1 vT) := hBelow
      cases hBAD with
      | inl hIn =>
        have g1 : LT.lt (Power.coord1 vT) (Power.coord1 wT) := hIn
        exact lt_irrefl _ (lt_trans g2 g1)
      | inr hEqB =>
        have e : Power.coord1 wT = Power.coord1 vT := hEqB
        have g3 : LT.lt (Power.coord1 vT) (Power.coord1 vT) := e ▸ g2
        exact lt_irrefl _ g3
  -- Uniform covering sets (intersections of half-sets).
  let S1 : Set (Power R 1) := setInter
    (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
    (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
  let S2 : Set (Power R 1) := setInter
    (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
    (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
  let S3 : Set (Power R 1) := setInter
    (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
    (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
  let S4 : Set (Power R 1) := setInter
    (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
    (fun x : Power R 1 => ∃ c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            LT.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
  have hS1 : M.S 1 S1 := hH1
  have hS2 : M.S 1 S2 := hHH2
  have hS3 : M.S 1 S3 := hHH3
  have hS4 : M.S 1 S4 := hHH4
  -- Every pattern point lands in one of the four intersections.
  have hCover : ∀ p : Power R 1, ∀ hp : openInterval a0 b0 p,
      S1 p ∨ S2 p ∨ S3 p ∨ S4 p := by
    intro p hp
    have hB := hPat p hp
    cases hB with
    | inl hB1 =>
      obtain ⟨c1, c2, hJc1, hJc2, hLT1, hLT2, hL, hR⟩ := hB1
      exact Or.inl ⟨hCovLA p hp ⟨c1, hJc1, hLT1, hL⟩, hCovRA p hp ⟨c2, hJc2, hLT2, hR⟩⟩
    | inr hRest =>
      cases hRest with
      | inl hB2 =>
        obtain ⟨c1, c2, hJc1, hJc2, hLT1, hLT2, hL, hR⟩ := hB2
        exact Or.inr (Or.inl ⟨hCovLA p hp ⟨c1, hJc1, hLT1, hL⟩, hCovRB p hp ⟨c2, hJc2, hLT2, hR⟩⟩)
      | inr hRest2 =>
        cases hRest2 with
        | inl hB3 =>
          obtain ⟨c1, c2, hJc1, hJc2, hLT1, hLT2, hL, hR⟩ := hB3
          exact Or.inr (Or.inr (Or.inl ⟨hCovLB p hp ⟨c1, hJc1, hLT1, hL⟩, hCovRA p hp ⟨c2, hJc2, hLT2, hR⟩⟩))
        | inr hB4 =>
          obtain ⟨c1, c2, hJc1, hJc2, hLT1, hLT2, hL, hR⟩ := hB4
          exact Or.inr (Or.inr (Or.inr ⟨hCovLB p hp ⟨c1, hJc1, hLT1, hL⟩, hCovRB p hp ⟨c2, hJc2, hLT2, hR⟩⟩))
  have hS1J0 : ∀ x : Power R 1, S1 x → openInterval a0 b0 x := by
    intro x hx
    obtain ⟨hLmem, hRmem⟩ := hx
    obtain ⟨c, hJc, hJx, hLT, hNeg⟩ := hLmem
    have hJx0 : openInterval a0 b0 x := hJx
    exact hJx0
  have hS2J0 : ∀ x : Power R 1, S2 x → openInterval a0 b0 x := by
    intro x hx
    obtain ⟨hLmem, hRmem⟩ := hx
    obtain ⟨c, hJc, hJx, hLT, hNeg⟩ := hLmem
    have hJx0 : openInterval a0 b0 x := hJx
    exact hJx0
  have hS3J0 : ∀ x : Power R 1, S3 x → openInterval a0 b0 x := by
    intro x hx
    obtain ⟨hLmem, hRmem⟩ := hx
    obtain ⟨c, hJc, hJx, hLT, hNeg⟩ := hLmem
    have hJx0 : openInterval a0 b0 x := hJx
    exact hJx0
  have hS4J0 : ∀ x : Power R 1, S4 x → openInterval a0 b0 x := by
    intro x hx
    obtain ⟨hLmem, hRmem⟩ := hx
    obtain ⟨c, hJc, hJx, hLT, hNeg⟩ := hLmem
    have hJx0 : openInterval a0 b0 x := hJx
    exact hJx0
  -- Decidability for the domain-emptiness split.
  have hValleyL : ∀ (a b : Endpoint R),
      (∀ y : Power R 1, openInterval a b y → openInterval a0 b0 y) ->
      ∀ x : Power R 1, ∀ hxI : I x, ∀ hxab : openInterval a b x,
  (fun x : Power R 1 => ∃ c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) x ->
      ∃ c1 : Power R 1, openInterval a b c1 ∧ Lt1 c1 x ∧
      ∀ y : Power R 1, ∀ hyI : I y, ∀ hyab : openInterval a b y,
      Lt1 c1 y → Lt1 y x ->
      Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
    intro a b hJY x hxI hxab hHALFx
    obtain ⟨c, hjc, hjx, hltCX, hneg⟩ := hHALFx
    have hJc0 : openInterval a0 b0 c := hjc
    have hccx : Lt1 c x := hltCX
    have hxab0 := hxab
    obtain ⟨hAxc, hBxc⟩ := hxab
    have hCore : ∀ y : Power R 1, ∀ hyI : I y,
        ∀ hyab : openInterval a b y,
        Lt1 c y → Lt1 y x → Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
      intro y hyI hyab h1 h2
      have hyJ : openInterval a0 b0 y := hJY y hyab
      let wT : Power R 1 := (f.toFun (Subtype.mk y hyI)).1
      let vT : Power R 1 := (f.toFun (Subtype.mk x hxI)).1
      have hGWt : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y wT) := by
        have hLW : Power.left (Power.append y wT) = y := by
          funext i
          exact Fin.append_left y wT i
        have hRW : Power.right (Power.append y wT) = wT := by
          funext i
          exact Fin.append_right y wT i
        have hx0 : I (Power.left (Power.append y wT)) := by
          rw [hLW]
          exact hyI
        refine ⟨hx0, ?_⟩
        have hArg : (⟨Power.left (Power.append y wT), hx0⟩ : {x : Power R 1 // I x})
            = ⟨y, hyI⟩ := Subtype.ext hLW
        rw [hRW, hArg]
      have hGVt : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x vT) := by
        have hLW : Power.left (Power.append x vT) = x := by
          funext i
          exact Fin.append_left x vT i
        have hRW : Power.right (Power.append x vT) = vT := by
          funext i
          exact Fin.append_right x vT i
        have hx0 : I (Power.left (Power.append x vT)) := by
          rw [hLW]
          exact hxI
        refine ⟨hx0, ?_⟩
        have hArg : (⟨Power.left (Power.append x vT), hx0⟩ : {x : Power R 1 // I x})
            = ⟨x, hxI⟩ := Subtype.ext hLW
        rw [hRW, hArg]
      let qv : Power R (1 + 1) :=
        (fun i : Fin (1 + 1) => (Power.append x c) (huSwap i))
      let tW : Power R (1 + (1 + 1)) := Power.append y (Power.append wT vT)
      let q5v : Power R ((1 + 1) + (1 + (1 + 1))) := Power.append qv tW
      have eGW : (fun j : Fin (1 + 1) => q5v (huGw j))
          = Power.append y wT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGw j
              = (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc q5v (huGw j)
              = q5v (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y wT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left y wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y wT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGw j
              = (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc q5v (huGw j)
              = q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = wT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y wT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right y wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y wT) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => q5v (huGx j))
          = Power.append x vT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGx j
              = (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc q5v (huGx j)
              = q5v (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = x ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x vT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left x vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x vT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGx j
              = (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc q5v (huGx j)
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = vT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x vT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right x vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x vT) j := by rw [hj1]
      have gJc : openInterval a0 b0 (fun i : Fin 1 => q5v (huC0 i)) := hjc
      have gJx : openInterval a0 b0 (fun i : Fin 1 => q5v (huX1 i)) := hjx
      have gJy : openInterval a0 b0 (fun i : Fin 1 => q5v (huY2 i)) := hyJ
      have g0 : LT.lt ((fun j : Fin 2 => q5v (huLt01 j)) 0)
          ((fun j : Fin 2 => q5v (huLt01 j)) 1) := hccx
      have g1 : LT.lt ((fun j : Fin 2 => q5v (huLt02 j)) 0)
          ((fun j : Fin 2 => q5v (huLt02 j)) 1) := h1
      have g2 : LT.lt ((fun j : Fin 2 => q5v (huLt21 j)) 0)
          ((fun j : Fin 2 => q5v (huLt21 j)) 1) := h2
      have gGW : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGw j)) := by
        rw [eGW]
        exact hGWt
      have gGX : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGx j)) := by
        rw [eGX]
        exact hGVt
      have hnb : ¬(LT.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0) ((fun j : Fin 2 => q5v (huBadAbove j)) 1) ∨ q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun hbad => hneg ⟨tW, gJc, gJx, gJy, g0, g1, g2, gGW, gGX, hbad⟩
      have hnA : ¬LT.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0)
          ((fun j : Fin 2 => q5v (huBadAbove j)) 1) :=
        fun h => hnb (Or.inl h)
      have hnE : ¬(q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun h => hnb (Or.inr h)
      have hTri := lt_trichotomy (Power.coord1 wT) (Power.coord1 vT)
      cases hTri with
      | inl h =>
        have hlt := h
        have hQQ : LT.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5v (huBadAbove j)) 1) := hlt
        exact absurd hQQ hnA
      | inr h23 =>
        cases h23 with
        | inl h =>
          have heq := h
          have hQQ : q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := heq
          exact absurd hQQ hnE
        | inr h =>
          have hlt := h
          exact hlt
    haveI hDecW : Decidable (openInterval a b c) := Classical.propDecidable _
    by_cases hcW : openInterval a b c
    · refine ⟨c, hcW, hccx, ?_⟩
      intro y hyI hyab h1 h2
      exact hCore y hyI hyab h1 h2
    · have hcW0 : ¬(Endpoint.lt a (Endpoint.finite (Power.coord1 c)) ∧
        Endpoint.lt (Endpoint.finite (Power.coord1 c)) b) := hcW
      have hccxC : LT.lt (Power.coord1 c) (Power.coord1 x) := hccx
      have hOut : ∀ yc : R, (Endpoint.lt a (Endpoint.finite yc) ∧
          Endpoint.lt (Endpoint.finite yc) b) → LT.lt (Power.coord1 c) yc :=
        huOutL a b (Power.coord1 c) (Power.coord1 x)
          ⟨hAxc, hBxc⟩ hcW0 hccxC
      obtain ⟨c0, hc0W, hc0x⟩ := huMidL a b x hxab0
      refine ⟨c0, hc0W, hc0x, ?_⟩
      intro y hyI hyab h1 h2
      have hyab0 := hyab
      obtain ⟨hAy, hBy⟩ := hyab
      have h1c : Lt1 c y := hOut _ ⟨hAy, hBy⟩
      exact hCore y hyI hyab0 h1c h2

  have hValleyR : ∀ (a b : Endpoint R),
      (∀ y : Power R 1, openInterval a b y → openInterval a0 b0 y) ->
      ∀ x : Power R 1, ∀ hxI : I x, ∀ hxab : openInterval a b x,
  (fun x : Power R 1 => ∃ c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) x ->
      ∃ c1 : Power R 1, openInterval a b c1 ∧ Lt1 x c1 ∧
      ∀ y : Power R 1, ∀ hyI : I y, ∀ hyab : openInterval a b y,
      Lt1 x y → Lt1 y c1 ->
      Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
    intro a b hJY x hxI hxab hHALFx
    obtain ⟨c, hjc, hjx, hltCX, hneg⟩ := hHALFx
    have hJc0 : openInterval a0 b0 c := hjc
    have hccx : Lt1 x c := hltCX
    have hxab0 := hxab
    obtain ⟨hAxc, hBxc⟩ := hxab
    have hCore : ∀ y : Power R 1, ∀ hyI : I y,
        ∀ hyab : openInterval a b y,
        Lt1 x y → Lt1 y c → Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
      intro y hyI hyab h1 h2
      have hyJ : openInterval a0 b0 y := hJY y hyab
      let wT : Power R 1 := (f.toFun (Subtype.mk y hyI)).1
      let vT : Power R 1 := (f.toFun (Subtype.mk x hxI)).1
      have hGWt : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y wT) := by
        have hLW : Power.left (Power.append y wT) = y := by
          funext i
          exact Fin.append_left y wT i
        have hRW : Power.right (Power.append y wT) = wT := by
          funext i
          exact Fin.append_right y wT i
        have hx0 : I (Power.left (Power.append y wT)) := by
          rw [hLW]
          exact hyI
        refine ⟨hx0, ?_⟩
        have hArg : (⟨Power.left (Power.append y wT), hx0⟩ : {x : Power R 1 // I x})
            = ⟨y, hyI⟩ := Subtype.ext hLW
        rw [hRW, hArg]
      have hGVt : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x vT) := by
        have hLW : Power.left (Power.append x vT) = x := by
          funext i
          exact Fin.append_left x vT i
        have hRW : Power.right (Power.append x vT) = vT := by
          funext i
          exact Fin.append_right x vT i
        have hx0 : I (Power.left (Power.append x vT)) := by
          rw [hLW]
          exact hxI
        refine ⟨hx0, ?_⟩
        have hArg : (⟨Power.left (Power.append x vT), hx0⟩ : {x : Power R 1 // I x})
            = ⟨x, hxI⟩ := Subtype.ext hLW
        rw [hRW, hArg]
      let qv : Power R (1 + 1) :=
        (fun i : Fin (1 + 1) => (Power.append x c) (huSwap i))
      let tW : Power R (1 + (1 + 1)) := Power.append y (Power.append wT vT)
      let q5v : Power R ((1 + 1) + (1 + (1 + 1))) := Power.append qv tW
      have eGW : (fun j : Fin (1 + 1) => q5v (huGw j))
          = Power.append y wT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGw j
              = (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc q5v (huGw j)
              = q5v (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y wT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left y wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y wT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGw j
              = (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc q5v (huGw j)
              = q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = wT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y wT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right y wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y wT) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => q5v (huGx j))
          = Power.append x vT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGx j
              = (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc q5v (huGx j)
              = q5v (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = x ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x vT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left x vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x vT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGx j
              = (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc q5v (huGx j)
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = vT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x vT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right x vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x vT) j := by rw [hj1]
      have gJc : openInterval a0 b0 (fun i : Fin 1 => q5v (huC0 i)) := hjc
      have gJx : openInterval a0 b0 (fun i : Fin 1 => q5v (huX1 i)) := hjx
      have gJy : openInterval a0 b0 (fun i : Fin 1 => q5v (huY2 i)) := hyJ
      have g0 : LT.lt ((fun j : Fin 2 => q5v (huLt10 j)) 0)
          ((fun j : Fin 2 => q5v (huLt10 j)) 1) := hccx
      have g1 : LT.lt ((fun j : Fin 2 => q5v (huLt12 j)) 0)
          ((fun j : Fin 2 => q5v (huLt12 j)) 1) := h1
      have g2 : LT.lt ((fun j : Fin 2 => q5v (huLt20 j)) 0)
          ((fun j : Fin 2 => q5v (huLt20 j)) 1) := h2
      have gGW : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGw j)) := by
        rw [eGW]
        exact hGWt
      have gGX : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGx j)) := by
        rw [eGX]
        exact hGVt
      have hnb : ¬(LT.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0) ((fun j : Fin 2 => q5v (huBadAbove j)) 1) ∨ q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun hbad => hneg ⟨tW, gJc, gJx, gJy, g0, g1, g2, gGW, gGX, hbad⟩
      have hnA : ¬LT.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0)
          ((fun j : Fin 2 => q5v (huBadAbove j)) 1) :=
        fun h => hnb (Or.inl h)
      have hnE : ¬(q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun h => hnb (Or.inr h)
      have hTri := lt_trichotomy (Power.coord1 wT) (Power.coord1 vT)
      cases hTri with
      | inl h =>
        have hlt := h
        have hQQ : LT.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5v (huBadAbove j)) 1) := hlt
        exact absurd hQQ hnA
      | inr h23 =>
        cases h23 with
        | inl h =>
          have heq := h
          have hQQ : q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := heq
          exact absurd hQQ hnE
        | inr h =>
          have hlt := h
          exact hlt
    haveI hDecW : Decidable (openInterval a b c) := Classical.propDecidable _
    by_cases hcW : openInterval a b c
    · refine ⟨c, hcW, hccx, ?_⟩
      intro y hyI hyab h1 h2
      exact hCore y hyI hyab h1 h2
    · have hcW0 : ¬(Endpoint.lt a (Endpoint.finite (Power.coord1 c)) ∧
        Endpoint.lt (Endpoint.finite (Power.coord1 c)) b) := hcW
      have hccxC : LT.lt (Power.coord1 x) (Power.coord1 c) := hccx
      have hOut : ∀ yc : R, (Endpoint.lt a (Endpoint.finite yc) ∧
          Endpoint.lt (Endpoint.finite yc) b) → LT.lt yc (Power.coord1 c) :=
        huOutR a b (Power.coord1 c) (Power.coord1 x)
          ⟨hAxc, hBxc⟩ hcW0 hccxC
      obtain ⟨c0, hc0W, hc0x⟩ := huMidR a b x hxab0
      refine ⟨c0, hc0W, hc0x, ?_⟩
      intro y hyI hyab h1 h2
      have hyab0 := hyab
      obtain ⟨hAy, hBy⟩ := hyab
      have h2c : Lt1 y c := hOut _ ⟨hAy, hBy⟩
      exact hCore y hyI hyab0 h1 h2c

  have hPeakL : ∀ (a b : Endpoint R),
      (∀ y : Power R 1, openInterval a b y → openInterval a0 b0 y) ->
      ∀ x : Power R 1, ∀ hxI : I x, ∀ hxab : openInterval a b x,
  (fun x : Power R 1 => ∃ c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) x ->
      ∃ c1 : Power R 1, openInterval a b c1 ∧ Lt1 c1 x ∧
      ∀ y : Power R 1, ∀ hyI : I y, ∀ hyab : openInterval a b y,
      Lt1 c1 y → Lt1 y x ->
      Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1 := by
    intro a b hJY x hxI hxab hHALFx
    obtain ⟨c, hjc, hjx, hltCX, hneg⟩ := hHALFx
    have hJc0 : openInterval a0 b0 c := hjc
    have hccx : Lt1 c x := hltCX
    have hxab0 := hxab
    obtain ⟨hAxc, hBxc⟩ := hxab
    have hCore : ∀ y : Power R 1, ∀ hyI : I y,
        ∀ hyab : openInterval a b y,
        Lt1 c y → Lt1 y x → Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1 := by
      intro y hyI hyab h1 h2
      have hyJ : openInterval a0 b0 y := hJY y hyab
      let wT : Power R 1 := (f.toFun (Subtype.mk y hyI)).1
      let vT : Power R 1 := (f.toFun (Subtype.mk x hxI)).1
      have hGWt : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y wT) := by
        have hLW : Power.left (Power.append y wT) = y := by
          funext i
          exact Fin.append_left y wT i
        have hRW : Power.right (Power.append y wT) = wT := by
          funext i
          exact Fin.append_right y wT i
        have hx0 : I (Power.left (Power.append y wT)) := by
          rw [hLW]
          exact hyI
        refine ⟨hx0, ?_⟩
        have hArg : (⟨Power.left (Power.append y wT), hx0⟩ : {x : Power R 1 // I x})
            = ⟨y, hyI⟩ := Subtype.ext hLW
        rw [hRW, hArg]
      have hGVt : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x vT) := by
        have hLW : Power.left (Power.append x vT) = x := by
          funext i
          exact Fin.append_left x vT i
        have hRW : Power.right (Power.append x vT) = vT := by
          funext i
          exact Fin.append_right x vT i
        have hx0 : I (Power.left (Power.append x vT)) := by
          rw [hLW]
          exact hxI
        refine ⟨hx0, ?_⟩
        have hArg : (⟨Power.left (Power.append x vT), hx0⟩ : {x : Power R 1 // I x})
            = ⟨x, hxI⟩ := Subtype.ext hLW
        rw [hRW, hArg]
      let qv : Power R (1 + 1) :=
        (fun i : Fin (1 + 1) => (Power.append x c) (huSwap i))
      let tW : Power R (1 + (1 + 1)) := Power.append y (Power.append wT vT)
      let q5v : Power R ((1 + 1) + (1 + (1 + 1))) := Power.append qv tW
      have eGW : (fun j : Fin (1 + 1) => q5v (huGw j))
          = Power.append y wT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGw j
              = (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc q5v (huGw j)
              = q5v (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y wT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left y wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y wT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGw j
              = (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc q5v (huGw j)
              = q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = wT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y wT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right y wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y wT) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => q5v (huGx j))
          = Power.append x vT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGx j
              = (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc q5v (huGx j)
              = q5v (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = x ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x vT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left x vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x vT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGx j
              = (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc q5v (huGx j)
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = vT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x vT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right x vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x vT) j := by rw [hj1]
      have gJc : openInterval a0 b0 (fun i : Fin 1 => q5v (huC0 i)) := hjc
      have gJx : openInterval a0 b0 (fun i : Fin 1 => q5v (huX1 i)) := hjx
      have gJy : openInterval a0 b0 (fun i : Fin 1 => q5v (huY2 i)) := hyJ
      have g0 : LT.lt ((fun j : Fin 2 => q5v (huLt01 j)) 0)
          ((fun j : Fin 2 => q5v (huLt01 j)) 1) := hccx
      have g1 : LT.lt ((fun j : Fin 2 => q5v (huLt02 j)) 0)
          ((fun j : Fin 2 => q5v (huLt02 j)) 1) := h1
      have g2 : LT.lt ((fun j : Fin 2 => q5v (huLt21 j)) 0)
          ((fun j : Fin 2 => q5v (huLt21 j)) 1) := h2
      have gGW : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGw j)) := by
        rw [eGW]
        exact hGWt
      have gGX : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGx j)) := by
        rw [eGX]
        exact hGVt
      have hnb : ¬(LT.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0) ((fun j : Fin 2 => q5v (huBadBelow j)) 1) ∨ q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun hbad => hneg ⟨tW, gJc, gJx, gJy, g0, g1, g2, gGW, gGX, hbad⟩
      have hnA : ¬LT.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0)
          ((fun j : Fin 2 => q5v (huBadBelow j)) 1) :=
        fun h => hnb (Or.inl h)
      have hnE : ¬(q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun h => hnb (Or.inr h)
      have hTri := lt_trichotomy (Power.coord1 vT) (Power.coord1 wT)
      cases hTri with
      | inl h =>
        have hlt := h
        have hQQ : LT.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5v (huBadBelow j)) 1) := hlt
        exact absurd hQQ hnA
      | inr h23 =>
        cases h23 with
        | inl h =>
          have heq := h
          have hQQ : q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := heq.symm
          exact absurd hQQ hnE
        | inr h =>
          have hlt := h
          exact hlt
    haveI hDecW : Decidable (openInterval a b c) := Classical.propDecidable _
    by_cases hcW : openInterval a b c
    · refine ⟨c, hcW, hccx, ?_⟩
      intro y hyI hyab h1 h2
      exact hCore y hyI hyab h1 h2
    · have hcW0 : ¬(Endpoint.lt a (Endpoint.finite (Power.coord1 c)) ∧
        Endpoint.lt (Endpoint.finite (Power.coord1 c)) b) := hcW
      have hccxC : LT.lt (Power.coord1 c) (Power.coord1 x) := hccx
      have hOut : ∀ yc : R, (Endpoint.lt a (Endpoint.finite yc) ∧
          Endpoint.lt (Endpoint.finite yc) b) → LT.lt (Power.coord1 c) yc :=
        huOutL a b (Power.coord1 c) (Power.coord1 x)
          ⟨hAxc, hBxc⟩ hcW0 hccxC
      obtain ⟨c0, hc0W, hc0x⟩ := huMidL a b x hxab0
      refine ⟨c0, hc0W, hc0x, ?_⟩
      intro y hyI hyab h1 h2
      have hyab0 := hyab
      obtain ⟨hAy, hBy⟩ := hyab
      have h1c : Lt1 c y := hOut _ ⟨hAy, hBy⟩
      exact hCore y hyI hyab0 h1c h2

  have hPeakR : ∀ (a b : Endpoint R),
      (∀ y : Power R 1, openInterval a b y → openInterval a0 b0 y) ->
      ∀ x : Power R 1, ∀ hxI : I x, ∀ hxab : openInterval a b x,
  (fun x : Power R 1 => ∃ c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          LT.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ ∃ t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              LT.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (LT.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) x ->
      ∃ c1 : Power R 1, openInterval a b c1 ∧ Lt1 x c1 ∧
      ∀ y : Power R 1, ∀ hyI : I y, ∀ hyab : openInterval a b y,
      Lt1 x y → Lt1 y c1 ->
      Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1 := by
    intro a b hJY x hxI hxab hHALFx
    obtain ⟨c, hjc, hjx, hltCX, hneg⟩ := hHALFx
    have hJc0 : openInterval a0 b0 c := hjc
    have hccx : Lt1 x c := hltCX
    have hxab0 := hxab
    obtain ⟨hAxc, hBxc⟩ := hxab
    have hCore : ∀ y : Power R 1, ∀ hyI : I y,
        ∀ hyab : openInterval a b y,
        Lt1 x y → Lt1 y c → Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1 := by
      intro y hyI hyab h1 h2
      have hyJ : openInterval a0 b0 y := hJY y hyab
      let wT : Power R 1 := (f.toFun (Subtype.mk y hyI)).1
      let vT : Power R 1 := (f.toFun (Subtype.mk x hxI)).1
      have hGWt : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y wT) := by
        have hLW : Power.left (Power.append y wT) = y := by
          funext i
          exact Fin.append_left y wT i
        have hRW : Power.right (Power.append y wT) = wT := by
          funext i
          exact Fin.append_right y wT i
        have hx0 : I (Power.left (Power.append y wT)) := by
          rw [hLW]
          exact hyI
        refine ⟨hx0, ?_⟩
        have hArg : (⟨Power.left (Power.append y wT), hx0⟩ : {x : Power R 1 // I x})
            = ⟨y, hyI⟩ := Subtype.ext hLW
        rw [hRW, hArg]
      have hGVt : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append x vT) := by
        have hLW : Power.left (Power.append x vT) = x := by
          funext i
          exact Fin.append_left x vT i
        have hRW : Power.right (Power.append x vT) = vT := by
          funext i
          exact Fin.append_right x vT i
        have hx0 : I (Power.left (Power.append x vT)) := by
          rw [hLW]
          exact hxI
        refine ⟨hx0, ?_⟩
        have hArg : (⟨Power.left (Power.append x vT), hx0⟩ : {x : Power R 1 // I x})
            = ⟨x, hxI⟩ := Subtype.ext hLW
        rw [hRW, hArg]
      let qv : Power R (1 + 1) :=
        (fun i : Fin (1 + 1) => (Power.append x c) (huSwap i))
      let tW : Power R (1 + (1 + 1)) := Power.append y (Power.append wT vT)
      let q5v : Power R ((1 + 1) + (1 + (1 + 1))) := Power.append qv tW
      have eGW : (fun j : Fin (1 + 1) => q5v (huGw j))
          = Power.append y wT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGw j
              = (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc q5v (huGw j)
              = q5v (⟨2, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = y ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y wT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left y wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y wT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGw j
              = (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGw, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc q5v (huGw j)
              = q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = wT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append y wT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right y wT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append y wT) j := by rw [hj1]
      have eGX : (fun j : Fin (1 + 1) => q5v (huGx j))
          = Power.append x vT := by
        funext j
        by_cases hj : j.val = 0
        · have e : huGx j
              = (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj0 : j = Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext hj
          calc q5v (huGx j)
              = q5v (⟨1, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = x ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x vT)
                (Fin.castAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_left x vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x vT) j := by rw [hj0]
        · have jv : j.val = 1 := by omega
          have e : huGx j
              = (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by
            simp [huGx, hj]
          have hj1 : j = Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1)) := Fin.ext jv
          calc q5v (huGx j)
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := by rw [e]
            _ = vT ((⟨0, by decide⟩ : Fin 1)) := rfl
            _ = (Power.append x vT)
                (Fin.natAdd 1 ((⟨0, by decide⟩ : Fin 1))) :=
                (Fin.append_right x vT (⟨0, by decide⟩ : Fin 1)).symm
            _ = (Power.append x vT) j := by rw [hj1]
      have gJc : openInterval a0 b0 (fun i : Fin 1 => q5v (huC0 i)) := hjc
      have gJx : openInterval a0 b0 (fun i : Fin 1 => q5v (huX1 i)) := hjx
      have gJy : openInterval a0 b0 (fun i : Fin 1 => q5v (huY2 i)) := hyJ
      have g0 : LT.lt ((fun j : Fin 2 => q5v (huLt10 j)) 0)
          ((fun j : Fin 2 => q5v (huLt10 j)) 1) := hccx
      have g1 : LT.lt ((fun j : Fin 2 => q5v (huLt12 j)) 0)
          ((fun j : Fin 2 => q5v (huLt12 j)) 1) := h1
      have g2 : LT.lt ((fun j : Fin 2 => q5v (huLt20 j)) 0)
          ((fun j : Fin 2 => q5v (huLt20 j)) 1) := h2
      have gGW : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGw j)) := by
        rw [eGW]
        exact hGWt
      have gGX : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGx j)) := by
        rw [eGX]
        exact hGVt
      have hnb : ¬(LT.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0) ((fun j : Fin 2 => q5v (huBadBelow j)) 1) ∨ q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun hbad => hneg ⟨tW, gJc, gJx, gJy, g0, g1, g2, gGW, gGX, hbad⟩
      have hnA : ¬LT.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0)
          ((fun j : Fin 2 => q5v (huBadBelow j)) 1) :=
        fun h => hnb (Or.inl h)
      have hnE : ¬(q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun h => hnb (Or.inr h)
      have hTri := lt_trichotomy (Power.coord1 vT) (Power.coord1 wT)
      cases hTri with
      | inl h =>
        have hlt := h
        have hQQ : LT.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5v (huBadBelow j)) 1) := hlt
        exact absurd hQQ hnA
      | inr h23 =>
        cases h23 with
        | inl h =>
          have heq := h
          have hQQ : q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := heq.symm
          exact absurd hQQ hnE
        | inr h =>
          have hlt := h
          exact hlt
    haveI hDecW : Decidable (openInterval a b c) := Classical.propDecidable _
    by_cases hcW : openInterval a b c
    · refine ⟨c, hcW, hccx, ?_⟩
      intro y hyI hyab h1 h2
      exact hCore y hyI hyab h1 h2
    · have hcW0 : ¬(Endpoint.lt a (Endpoint.finite (Power.coord1 c)) ∧
        Endpoint.lt (Endpoint.finite (Power.coord1 c)) b) := hcW
      have hccxC : LT.lt (Power.coord1 x) (Power.coord1 c) := hccx
      have hOut : ∀ yc : R, (Endpoint.lt a (Endpoint.finite yc) ∧
          Endpoint.lt (Endpoint.finite yc) b) → LT.lt yc (Power.coord1 c) :=
        huOutR a b (Power.coord1 c) (Power.coord1 x)
          ⟨hAxc, hBxc⟩ hcW0 hccxC
      obtain ⟨c0, hc0W, hc0x⟩ := huMidR a b x hxab0
      refine ⟨c0, hc0W, hc0x, ?_⟩
      intro y hyI hyab h1 h2
      have hyab0 := hyab
      obtain ⟨hAy, hBy⟩ := hyab
      have h2c : Lt1 y c := hOut _ ⟨hAy, hBy⟩
      exact hCore y hyI hyab0 h1 h2c

  haveI hDecE : Decidable (∃ _ : Power R 1, True) := Classical.propDecidable _
  by_cases hE : ∃ _ : Power R 1, True
  · -- Nonempty domain: the infinitude argument goes through.
    obtain ⟨x0, _⟩ := hE
    have hGreatest : ∀ L : List R, L ≠ [] → ∃ M : R, M ∈ L ∧ ∀ r : R, r ∈ L → (LT.lt r M ∨ r = M) := huGreatest
    have hOutside : ∀ L : List R, ∃ x : Power R 1, openInterval a0 b0 x ∧ Power.coord1 x ∉ L := huOutside hlt0 x0
    have hUFin : ∀ A B : Set (Power R 1), Set.Finite A → Set.Finite B →
        Set.Finite (A ∪ B) :=
      fun A B hA hB => hA.union hB
    have hInf1 : Set.Infinite S1 ∨ Set.Infinite S2 ∨ Set.Infinite S3 ∨ Set.Infinite S4 :=
      Classical.byContradiction (fun hCon => by
        have e1 : ¬Set.Infinite S1 :=
          fun h => hCon (Or.inl h)
        have e234 : ¬(Set.Infinite S2 ∨ Set.Infinite S3 ∨ Set.Infinite S4) :=
          fun h => hCon (Or.inr h)
        have e2 : ¬Set.Infinite S2 :=
          fun h => e234 (Or.inl h)
        have e34 : ¬(Set.Infinite S3 ∨ Set.Infinite S4) :=
          fun h => e234 (Or.inr h)
        have e3 : ¬Set.Infinite S3 :=
          fun h => e34 (Or.inl h)
        have e4 : ¬Set.Infinite S4 :=
          fun h => e34 (Or.inr h)
        have hF1 : Set.Finite S1 := Classical.byContradiction (fun h => e1 h)
        have hF2 : Set.Finite S2 := Classical.byContradiction (fun h => e2 h)
        have hF3 : Set.Finite S3 := Classical.byContradiction (fun h => e3 h)
        have hF4 : Set.Finite S4 := Classical.byContradiction (fun h => e4 h)
        have hU : Set.Finite (((S1 ∪ S2)) ∪ ((S3 ∪ S4))) :=
          hUFin _ _ (hUFin _ _ hF1 hF2) (hUFin _ _ hF3 hF4)
        have hU' : Set.Finite (((S1 ∪ S2)) ∪ ((S3 ∪ S4))) := hU
        set Lc : List R := hU'.toFinset.image Power.coord1 |>.toList with hLcdef
        have hLc : ∀ x : Power R 1, (((S1 ∪ S2)) ∪ ((S3 ∪ S4))) x →
            Power.coord1 x ∈ Lc := by
          intro x hx
          rw [hLcdef]
          exact Finset.mem_toList.mpr
            (Finset.mem_image.mpr ⟨x, hU'.mem_toFinset.mpr hx, rfl⟩)
        obtain ⟨x, hxJ, hxo⟩ := hOutside Lc
        have hmem := hCover x hxJ
        have hUx : (((S1 ∪ S2)) ∪ ((S3 ∪ S4))) x := by
          cases hmem with
          | inl h1 => exact Or.inl (Or.inl h1)
          | inr h234 =>
            cases h234 with
            | inl h2 => exact Or.inl (Or.inr h2)
            | inr h34 =>
              cases h34 with
              | inl h3 => exact Or.inr (Or.inl h3)
              | inr h4 => exact Or.inr (Or.inr h4)
        have hLcx := hLc x hUx
        exact hxo hLcx)
    cases hInf1 with
    | inl hI1 =>
      obtain ⟨a, b, hab, hsub⟩ :=
        Monotonicity_Theorem.infinite_contains_interval_core2 S1 ((M.ominimal S1).mp hS1) hI1
      have hJY : ∀ y : Power R 1, openInterval a b y → openInterval a0 b0 y :=
        fun y hy => hS1J0 y (hsub y hy)
      refine ⟨a, b, hab, ?_, Or.inl ?_⟩
      · intro z hz
        exact hJY z hz
      · intro x hxI hxab
        have hxS : S1 x := hsub x hxab
        obtain ⟨hLAx, hRAx⟩ := hxS
        obtain ⟨c1, hc1W, hc1x, hleft⟩ := hValleyL a b hJY x hxI hxab hLAx
        obtain ⟨c2, hc2W, hc2x, hright⟩ := hValleyR a b hJY x hxI hxab hRAx
        exact ⟨c1, c2, hc1W, hc2W, hc1x, hc2x, hleft, hright⟩
    | inr hRest =>
      cases hRest with
      | inl hI2 =>
        obtain ⟨a, b, hab, hsub⟩ :=
          Monotonicity_Theorem.infinite_contains_interval_core2 S2 ((M.ominimal S2).mp hS2) hI2
        have hJY : ∀ y : Power R 1, openInterval a b y → openInterval a0 b0 y :=
          fun y hy => hS2J0 y (hsub y hy)
        refine ⟨a, b, hab, ?_, Or.inr (Or.inl ?_)⟩
        · intro z hz
          exact hJY z hz
        · intro x hxI hxab
          have hxS : S2 x := hsub x hxab
          obtain ⟨hLAx, hRBx⟩ := hxS
          obtain ⟨c1, hc1W, hc1x, hleft⟩ := hValleyL a b hJY x hxI hxab hLAx
          obtain ⟨c2, hc2W, hc2x, hright⟩ := hPeakR a b hJY x hxI hxab hRBx
          exact ⟨c1, c2, hc1W, hc2W, hc1x, hc2x, hleft, hright⟩
      | inr hRest2 =>
        cases hRest2 with
        | inl hI3 =>
          obtain ⟨a, b, hab, hsub⟩ :=
            Monotonicity_Theorem.infinite_contains_interval_core2 S3 ((M.ominimal S3).mp hS3) hI3
          have hJY : ∀ y : Power R 1, openInterval a b y → openInterval a0 b0 y :=
            fun y hy => hS3J0 y (hsub y hy)
          refine ⟨a, b, hab, ?_, Or.inr (Or.inr (Or.inl ?_))⟩
          · intro z hz
            exact hJY z hz
          · intro x hxI hxab
            have hxS : S3 x := hsub x hxab
            obtain ⟨hLBx, hRAx⟩ := hxS
            obtain ⟨c1, hc1W, hc1x, hleft⟩ := hPeakL a b hJY x hxI hxab hLBx
            obtain ⟨c2, hc2W, hc2x, hright⟩ := hValleyR a b hJY x hxI hxab hRAx
            exact ⟨c1, c2, hc1W, hc2W, hc1x, hc2x, hleft, hright⟩
        | inr hI4 =>
          obtain ⟨a, b, hab, hsub⟩ :=
            Monotonicity_Theorem.infinite_contains_interval_core2 S4 ((M.ominimal S4).mp hS4) hI4
          have hJY : ∀ y : Power R 1, openInterval a b y → openInterval a0 b0 y :=
            fun y hy => hS4J0 y (hsub y hy)
          refine ⟨a, b, hab, ?_, Or.inr (Or.inr (Or.inr ?_))⟩
          · intro z hz
            exact hJY z hz
          · intro x hxI hxab
            have hxS : S4 x := hsub x hxab
            obtain ⟨hLBx, hRBx⟩ := hxS
            obtain ⟨c1, hc1W, hc1x, hleft⟩ := hPeakL a b hJY x hxI hxab hLBx
            obtain ⟨c2, hc2W, hc2x, hright⟩ := hPeakR a b hJY x hxI hxab hRBx
            exact ⟨c1, c2, hc1W, hc2W, hc1x, hc2x, hleft, hright⟩
  · -- Empty domain: everything is vacuous.
    refine ⟨Endpoint.negInf, Endpoint.posInf, ?_, ?_, ?_⟩
    · trivial
    · intro x hx
      have hnx : ∃ y : Power R 1, True := ⟨x, trivial⟩
      exact (hE hnx).elim
    · refine Or.inl ?_
      intro x hxI hxab
      have hnx : ∃ y : Power R 1, True := ⟨x, trivial⟩
      exact (hE hnx).elim
