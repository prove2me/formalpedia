-- Prove2me | solution 1 for Monotonicity_Theorem.uniform_pattern_window
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T20:02:25.276799+00:00
-- url     : https://prove2.me/submissions/eee3e381-4f9e-48fc-8b67-f122a7e94d4c

import Definitions.Def_Monotonicity_Theorem_Framework
import Theorems.Thm_Monotonicity_Theorem_pattern_at_interior_point
import Theorems.Thm_Monotonicity_Theorem_infinite_contains_interval_core

open Monotonicity_Theorem

namespace Monotonicity_Theorem

theorem huGraphVal {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (y w : Power R 1) (hyI : I y)
    (hG : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
      (Power.append y w)) :
    w = (f.toFun (Subtype.mk y hyI)).1 := by
  obtain ⟨hxy, hEq⟩ := hG
  have eL : Power.left (Power.append y w) = y := by
    funext i
    simp [Power.left, Power.append, Fin.append_left]
  have eR : Power.right (Power.append y w) = w := by
    funext j
    exact Fin.append_right y w j
  calc w = Power.right (Power.append y w) := eR.symm
    _ = (f.toFun (Subtype.mk (Power.left (Power.append y w)) hxy)).1 := hEq
    _ = (f.toFun (Subtype.mk y hyI)).1 := by
      have eSub : (Subtype.mk (Power.left (Power.append y w)) hxy : {x // I x})
          = Subtype.mk y hyI := Subtype.ext eL
      rw [eSub]

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


theorem huGreatest {R : Type} (D : DenseLinearOrderNoEndpoints R) : forall L : List R, L ≠ [] -> exists M : R, M ∈ L /\ forall r : R, r ∈ L -> (D.lt r M \/ r = M) := by
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
      have hTri := D.trichotomy h M
      cases hTri with
      | inl h1 =>
        obtain ⟨hlt, _, _⟩ := h1
        refine ⟨M, List.mem_cons.mpr (Or.inr hM), ?_⟩
        intro r hr
        cases List.mem_cons.mp hr with
        | inl he =>
          have hlt2 : D.lt r M := by rw [he]; exact hlt
          exact Or.inl hlt2
        | inr hm => exact hMax r hm
      | inr h23 =>
        cases h23 with
        | inl h1 =>
          obtain ⟨heq, _, _⟩ := h1
          refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
          intro r hr
          cases List.mem_cons.mp hr with
          | inl he => exact Or.inr he
          | inr hm =>
            have hle := hMax r hm
            cases hle with
            | inl hltRM =>
              have hltRh : D.lt r h := by rw [←heq] at hltRM; exact hltRM
              exact Or.inl hltRh
            | inr heqRM =>
              exact Or.inr (heqRM.trans heq.symm)
        | inr h1 =>
          obtain ⟨hlt, _, _⟩ := h1
          refine ⟨h, List.mem_cons.mpr (Or.inl rfl), ?_⟩
          intro r hr
          cases List.mem_cons.mp hr with
          | inl he => exact Or.inr he
          | inr hm =>
            have hle := hMax r hm
            cases hle with
            | inl hltRM => exact Or.inl (D.trans hltRM hlt)
            | inr heqRM =>
              have hltRh : D.lt r h := by rw [heqRM]; exact hlt
              exact Or.inl hltRh

theorem huOutside {R : Type} (D : DenseLinearOrderNoEndpoints R) {a0 b0 : Endpoint R} (hlt0 : Endpoint.lt D a0 b0) (x0 : Power R 1) : forall L : List R, exists x : Power R 1, openInterval D a0 b0 x /\ Power.coord1 x ∉ L := by
  intro L
  cases a0 with
  | negInf =>
    cases b0 with
    | negInf => cases hlt0
    | finite r =>
      have hAux : forall (L : List R) (b : R),
          exists y : R, D.lt y b /\ y ∉ L := by
        intro L
        induction L with
        | nil =>
          intro b
          obtain ⟨y, hy⟩ := D.no_left_endpoint b
          exact ⟨y, hy, by simp⟩
        | cons h t ih =>
          intro b
          haveI hDecH : Decidable (D.lt h b) := Classical.propDecidable _
          by_cases hhb : D.lt h b
          · obtain ⟨y, hyh, hyn⟩ := ih h
            have hyb : D.lt y b := D.trans hyh hhb
            refine ⟨y, hyb, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hcon : D.lt h h := by rw [he] at hyh; exact hyh
              exact D.irrefl _ hcon
            | inr hm2 => exact hyn hm2
          · obtain ⟨y, hyb, hyn⟩ := ih b
            refine ⟨y, hyb, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hY : D.lt y b := hyb
              rw [he] at hY
              exact hhb hY
            | inr hm2 => exact hyn hm2
      obtain ⟨y, hyr, hyn⟩ := hAux L r
      refine ⟨fun _ => y, ?_, ?_⟩
      · show Endpoint.lt D Endpoint.negInf (Endpoint.finite y) /\
          Endpoint.lt D (Endpoint.finite y) (Endpoint.finite r)
        exact ⟨trivial, hyr⟩
      · show y ∉ L
        exact hyn
    | posInf =>
      cases L with
      | nil =>
        refine ⟨fun _ => Power.coord1 x0, ?_, ?_⟩
        · show Endpoint.lt D Endpoint.negInf (Endpoint.finite (Power.coord1 x0)) /\
            Endpoint.lt D (Endpoint.finite (Power.coord1 x0)) Endpoint.posInf
          exact ⟨trivial, trivial⟩
        · exact by simp
      | cons h t =>
        have hNet : h :: t ≠ [] := by simp
        obtain ⟨M, hM, hMax⟩ := huGreatest D (h :: t) hNet
        obtain ⟨y, hy⟩ := D.no_right_endpoint M
        refine ⟨fun _ => y, ?_, ?_⟩
        · show Endpoint.lt D Endpoint.negInf (Endpoint.finite y) /\
            Endpoint.lt D (Endpoint.finite y) Endpoint.posInf
          exact ⟨trivial, trivial⟩
        · show y ∉ (h :: t)
          intro hm
          have hle := hMax y hm
          cases hle with
          | inl hltYM =>
            have hcon : D.lt M M := D.trans hy hltYM
            exact D.irrefl _ hcon
          | inr heYM =>
            have hcon : D.lt M M := by rw [heYM] at hy; exact hy
            exact D.irrefl _ hcon
  | finite l =>
    cases b0 with
    | negInf => cases hlt0
    | finite r =>
      have hlr : D.lt l r := hlt0
      have hAux : forall (L : List R) (lo hi : R), D.lt lo hi ->
          exists y : R, D.lt lo y /\ D.lt y hi /\ y ∉ L := by
        intro L
        induction L with
        | nil =>
          intro lo hi hlt
          obtain ⟨y, hy1, hy2⟩ := D.dense hlt
          exact ⟨y, hy1, hy2, by simp⟩
        | cons h t ih =>
          intro lo hi hlt
          haveI hDecH : Decidable (D.lt lo h /\ D.lt h hi) :=
            Classical.propDecidable _
          by_cases hmem : D.lt lo h /\ D.lt h hi
          · obtain ⟨hlh, hhr⟩ := hmem
            obtain ⟨y, hy1, hy2, hyn⟩ := ih lo h hlh
            have hyr : D.lt y hi := D.trans hy2 hhr
            refine ⟨y, hy1, hyr, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hcon : D.lt h h := by rw [he] at hy2; exact hy2
              exact D.irrefl _ hcon
            | inr hm2 => exact hyn hm2
          · obtain ⟨y, hy1, hy2, hyn⟩ := ih lo hi hlt
            refine ⟨y, hy1, hy2, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hY : D.lt lo y /\ D.lt y hi :=⟨hy1, hy2⟩
              rw [he] at hY
              exact hmem hY
            | inr hm2 => exact hyn hm2
      obtain ⟨y, hy1, hy2, hyn⟩ := hAux L l r hlr
      refine ⟨fun _ => y, ?_, ?_⟩
      · show Endpoint.lt D (Endpoint.finite l) (Endpoint.finite y) /\
          Endpoint.lt D (Endpoint.finite y) (Endpoint.finite r)
        exact ⟨hy1, hy2⟩
      · show y ∉ L
        exact hyn
    | posInf =>
      have hAux : forall (L : List R) (lo : R),
          exists y : R, D.lt lo y /\ y ∉ L := by
        intro L
        induction L with
        | nil =>
          intro lo
          obtain ⟨y, hy⟩ := D.no_right_endpoint lo
          exact ⟨y, hy, by simp⟩
        | cons h t ih =>
          intro lo
          haveI hDecH : Decidable (D.lt lo h) := Classical.propDecidable _
          by_cases hlo : D.lt lo h
          · obtain ⟨y, hyh, hyn⟩ := ih h
            have hyl : D.lt lo y := D.trans hlo hyh
            refine ⟨y, hyl, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hcon : D.lt h h := by rw [he] at hyh; exact hyh
              exact D.irrefl _ hcon
            | inr hm2 => exact hyn hm2
          · obtain ⟨y, hyl, hyn⟩ := ih lo
            refine ⟨y, hyl, ?_⟩
            intro hm
            cases List.mem_cons.mp hm with
            | inl he =>
              have hY : D.lt lo y := hyl
              rw [he] at hY
              exact hlo hY
            | inr hm2 => exact hyn hm2
      obtain ⟨y, hyl, hyn⟩ := hAux L l
      refine ⟨fun _ => y, ?_, ?_⟩
      · show Endpoint.lt D (Endpoint.finite l) (Endpoint.finite y) /\
          Endpoint.lt D (Endpoint.finite y) Endpoint.posInf
        exact ⟨hyl, trivial⟩
      · show y ∉ L
        exact hyn
  | posInf =>
    cases b0 with
    | negInf => cases hlt0
    | finite r => cases hlt0
    | posInf => cases hlt0

theorem huMidL {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (a b : Endpoint R) (x : Power R 1)
    (hx : openInterval D a b x) :
    exists c : Power R 1, openInterval D a b c /\ Lt1 D c x := by
  obtain ⟨hA, hB⟩ := hx
  cases a with
  | negInf =>
    obtain ⟨m, hm⟩ := D.no_left_endpoint (Power.coord1 x)
    refine ⟨fun _ => m, ?_, ?_⟩
    · show Endpoint.lt D Endpoint.negInf (Endpoint.finite m) /\
        Endpoint.lt D (Endpoint.finite m) b
      cases b with
      | negInf => cases hB
      | finite r =>
        have hxr : D.lt (Power.coord1 x) r := hB
        exact ⟨trivial, D.trans hm hxr⟩
      | posInf => exact ⟨trivial, trivial⟩
    · show Lt1 D (fun _ => m) x
      exact hm
  | finite l =>
    have hlx : D.lt l (Power.coord1 x) := hA
    obtain ⟨m, hm1, hm2⟩ := D.dense hlx
    refine ⟨fun _ => m, ?_, ?_⟩
    · show Endpoint.lt D (Endpoint.finite l) (Endpoint.finite m) /\
        Endpoint.lt D (Endpoint.finite m) b
      cases b with
      | negInf => cases hB
      | finite r =>
        have hxr : D.lt (Power.coord1 x) r := hB
        exact ⟨hm1, D.trans hm2 hxr⟩
      | posInf => exact ⟨hm1, trivial⟩
    · show Lt1 D (fun _ => m) x
      exact hm2
  | posInf => cases hA

theorem huMidR {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (a b : Endpoint R) (x : Power R 1)
    (hx : openInterval D a b x) :
    exists c : Power R 1, openInterval D a b c /\ Lt1 D x c := by
  obtain ⟨hA, hB⟩ := hx
  cases b with
  | posInf =>
    obtain ⟨m, hm⟩ := D.no_right_endpoint (Power.coord1 x)
    refine ⟨fun _ => m, ?_, ?_⟩
    · show Endpoint.lt D a (Endpoint.finite m) /\
        Endpoint.lt D (Endpoint.finite m) Endpoint.posInf
      cases a with
      | negInf => exact ⟨trivial, trivial⟩
      | finite l =>
        have hlx : D.lt l (Power.coord1 x) := hA
        exact ⟨D.trans hlx hm, trivial⟩
      | posInf => cases hA
    · show Lt1 D x (fun _ => m)
      exact hm
  | finite r =>
    have hxr : D.lt (Power.coord1 x) r := hB
    obtain ⟨m, hm1, hm2⟩ := D.dense hxr
    refine ⟨fun _ => m, ?_, ?_⟩
    · show Endpoint.lt D a (Endpoint.finite m) /\
        Endpoint.lt D (Endpoint.finite m) (Endpoint.finite r)
      cases a with
      | negInf => exact ⟨trivial, hm2⟩
      | finite l =>
        have hlx : D.lt l (Power.coord1 x) := hA
        exact ⟨D.trans hlx hm1, hm2⟩
      | posInf => cases hA
    · show Lt1 D x (fun _ => m)
      exact hm1
  | negInf => cases hB

theorem huOutL {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (a b : Endpoint R) (cc xc : R)
    (hX : Endpoint.lt D a (Endpoint.finite xc) /\ Endpoint.lt D (Endpoint.finite xc) b)
    (hN : ¬(Endpoint.lt D a (Endpoint.finite cc) /\ Endpoint.lt D (Endpoint.finite cc) b))
    (hCX : D.lt cc xc) :
    forall yc : R, (Endpoint.lt D a (Endpoint.finite yc) /\ Endpoint.lt D (Endpoint.finite yc) b) ->
      D.lt cc yc := by
  intro yc hY
  have hTri := D.trichotomy cc yc
  cases hTri with
  | inl h1 =>
    obtain ⟨hlt, _, _⟩ := h1
    exact hlt
  | inr h23 =>
    cases h23 with
    | inl h1 =>
      obtain ⟨heq, _, _⟩ := h1
      have hA : Endpoint.lt D a (Endpoint.finite cc) := by rw [heq]; exact hY.1
      have hB : Endpoint.lt D (Endpoint.finite cc) b := by rw [heq]; exact hY.2
      exact absurd ⟨hA, hB⟩ hN
    | inr h1 =>
      obtain ⟨hlt, _, _⟩ := h1
      have hA : Endpoint.lt D a (Endpoint.finite cc) := by
        cases a with
        | negInf => trivial
        | finite l =>
          have hlyc : D.lt l yc := hY.1
          exact D.trans hlyc hlt
        | posInf => cases hY.1
      have hB : Endpoint.lt D (Endpoint.finite cc) b := by
        cases b with
        | negInf => cases hY.2
        | finite r =>
          have hxr : D.lt xc r := hX.2
          exact D.trans hCX hxr
        | posInf => trivial
      exact absurd ⟨hA, hB⟩ hN

theorem huOutR {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (a b : Endpoint R) (cc xc : R)
    (hX : Endpoint.lt D a (Endpoint.finite xc) /\ Endpoint.lt D (Endpoint.finite xc) b)
    (hN : ¬(Endpoint.lt D a (Endpoint.finite cc) /\ Endpoint.lt D (Endpoint.finite cc) b))
    (hCX : D.lt xc cc) :
    forall yc : R, (Endpoint.lt D a (Endpoint.finite yc) /\ Endpoint.lt D (Endpoint.finite yc) b) ->
      D.lt yc cc := by
  intro yc hY
  have hTri := D.trichotomy yc cc
  cases hTri with
  | inl h1 =>
    obtain ⟨hlt, _, _⟩ := h1
    exact hlt
  | inr h23 =>
    cases h23 with
    | inl h1 =>
      obtain ⟨heq, _, _⟩ := h1
      have hA : Endpoint.lt D a (Endpoint.finite cc) := by rw [←heq]; exact hY.1
      have hB : Endpoint.lt D (Endpoint.finite cc) b := by rw [←heq]; exact hY.2
      exact absurd ⟨hA, hB⟩ hN
    | inr h1 =>
      obtain ⟨hlt, _, _⟩ := h1
      have hA : Endpoint.lt D a (Endpoint.finite cc) := by
        cases a with
        | negInf => trivial
        | finite l =>
          have hxc : D.lt l xc := hX.1
          have hlc : D.lt l cc := D.trans hxc hCX
          exact hlc
        | posInf => cases hY.1
      have hB : Endpoint.lt D (Endpoint.finite cc) b := by
        cases b with
        | negInf => cases hY.2
        | finite r =>
          have hyr : D.lt yc r := hY.2
          have hcr : D.lt cc r := D.trans hlt hyr
          exact hcr
        | posInf => trivial
      exact absurd ⟨hA, hB⟩ hN

theorem huCompl1 {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) :
    forall A : Set (Power R 1), M.S 1 A -> M.S 1 (fun x : Power R 1 => ¬ A x) := by
  intro A hA
  have hFU := (M.ominimal A).mp hA
  induction hFU with
  | empty =>
    have hU : M.S 1 (openInterval D Endpoint.negInf Endpoint.posInf) :=
      (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf Endpoint.posInf)
    have heq : (fun x : Power R 1 => ¬ (fun _ : Power R 1 => False) x)
        = openInterval D Endpoint.negInf Endpoint.posInf := by
      funext x
      apply propext
      constructor
      · intro _
        exact ⟨trivial, trivial⟩
      · intro hU hF
        exact hF.elim
    rw [heq]
    exact hU
  | point a =>
    have hL : M.S 1 (openInterval D Endpoint.negInf (Endpoint.finite a)) :=
      (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf (Endpoint.finite a))
    have hR : M.S 1 (openInterval D (Endpoint.finite a) Endpoint.posInf) :=
      (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval (Endpoint.finite a) Endpoint.posInf)
    have heq : (fun x : Power R 1 => ¬pointSet a x)
        = setUnion (openInterval D Endpoint.negInf (Endpoint.finite a))
          (openInterval D (Endpoint.finite a) Endpoint.posInf) := by
      funext x
      apply propext
      constructor
      · intro h
        have hTri := D.trichotomy (x 0) a
        cases hTri with
        | inl h1 =>
          obtain ⟨hlt, _, _⟩ := h1
          exact Or.inl ⟨trivial, hlt⟩
        | inr h23 =>
          cases h23 with
          | inl h1 =>
            obtain ⟨heq2, _, _⟩ := h1
            exact (h heq2).elim
          | inr h1 =>
            obtain ⟨hlt, _, _⟩ := h1
            exact Or.inr ⟨hlt, trivial⟩
      · intro h
        cases h with
        | inl h1 =>
          intro he
          have heq3 : x 0 = a := he
          obtain ⟨_, hlt⟩ := h1
          have hcon : D.lt a a := by rw [heq3] at hlt; exact hlt
          exact D.irrefl _ hcon
        | inr h1 =>
          intro he
          have heq3 : x 0 = a := he
          obtain ⟨hlt, _⟩ := h1
          have hcon : D.lt a a := by rw [heq3] at hlt; exact hlt
          exact D.irrefl _ hcon
    rw [heq]
    exact M.union_mem hL hR
  | interval a b =>
    cases a with
    | negInf =>
      cases b with
      | negInf =>
        have hU : M.S 1 (openInterval D Endpoint.negInf Endpoint.posInf) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf Endpoint.posInf)
        have hEmpty : forall x : Power R 1, openInterval D Endpoint.negInf Endpoint.negInf x -> False := by
          intro x hx
          obtain ⟨_, h2⟩ := hx
          cases h2
        have heq : (fun x : Power R 1 => ¬openInterval D Endpoint.negInf Endpoint.negInf x)
            = openInterval D Endpoint.negInf Endpoint.posInf := by
          funext x
          apply propext
          constructor
          · intro _
            exact ⟨trivial, trivial⟩
          · intro _ hE
            exact (hEmpty x hE).elim
        rw [heq]
        exact hU
      | finite r =>
        have hPt : M.S 1 (pointSet r) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point r)
        have hR : M.S 1 (openInterval D (Endpoint.finite r) Endpoint.posInf) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval (Endpoint.finite r) Endpoint.posInf)
        have heq : (fun x : Power R 1 => ¬openInterval D Endpoint.negInf (Endpoint.finite r) x)
            = setUnion (pointSet r) (openInterval D (Endpoint.finite r) Endpoint.posInf) := by
          funext x
          apply propext
          constructor
          · intro h
            have hTri := D.trichotomy (x 0) r
            cases hTri with
            | inl h1 =>
              obtain ⟨hlt, _, _⟩ := h1
              exact (h ⟨trivial, hlt⟩).elim
            | inr h23 =>
              cases h23 with
              | inl h1 =>
                obtain ⟨heq2, _, _⟩ := h1
                exact Or.inl heq2
              | inr h1 =>
                obtain ⟨hlt, _, _⟩ := h1
                exact Or.inr ⟨hlt, trivial⟩
          · intro h
            cases h with
            | inl h1 =>
              intro he
              have heq3 : x 0 = r := h1
              obtain ⟨_, hlt⟩ := he
              have hcon : D.lt r r := by rw [heq3] at hlt; exact hlt
              exact D.irrefl _ hcon
            | inr h1 =>
              intro he
              obtain ⟨hltR, _⟩ := h1
              obtain ⟨_, hlt⟩ := he
              have hcon : D.lt (x 0) (x 0) := D.trans hlt hltR
              exact D.irrefl _ hcon
        rw [heq]
        exact M.union_mem hPt hR
      | posInf =>
        have heq : (fun x : Power R 1 => ¬openInterval D Endpoint.negInf Endpoint.posInf x)
            = setEmpty := by
          funext x
          apply propext
          constructor
          · intro h
            exact h ⟨trivial, trivial⟩
          · intro h
            exact False.elim h
        rw [heq]
        exact M.empty_mem 1
    | finite l =>
      cases b with
      | negInf =>
        have hU : M.S 1 (openInterval D Endpoint.negInf Endpoint.posInf) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf Endpoint.posInf)
        have hEmpty : forall x : Power R 1, openInterval D (Endpoint.finite l) Endpoint.negInf x -> False := by
          intro x hx
          obtain ⟨_, h2⟩ := hx
          cases h2
        have heq : (fun x : Power R 1 => ¬openInterval D (Endpoint.finite l) Endpoint.negInf x)
            = openInterval D Endpoint.negInf Endpoint.posInf := by
          funext x
          apply propext
          constructor
          · intro _
            exact ⟨trivial, trivial⟩
          · intro _ hE
            exact (hEmpty x hE).elim
        rw [heq]
        exact hU
      | finite r =>
        have hL : M.S 1 (openInterval D Endpoint.negInf (Endpoint.finite l)) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf (Endpoint.finite l))
        have hP1 : M.S 1 (pointSet l) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point l)
        have hP2 : M.S 1 (pointSet r) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point r)
        have hR : M.S 1 (openInterval D (Endpoint.finite r) Endpoint.posInf) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval (Endpoint.finite r) Endpoint.posInf)
        have heq : (fun x : Power R 1 => ¬openInterval D (Endpoint.finite l) (Endpoint.finite r) x)
            = setUnion (openInterval D Endpoint.negInf (Endpoint.finite l))
              (setUnion (pointSet l) (setUnion (pointSet r)
                (openInterval D (Endpoint.finite r) Endpoint.posInf))) := by
          funext x
          apply propext
          constructor
          · intro h
            have hT1 := D.trichotomy (x 0) l
            cases hT1 with
            | inl h1 =>
              obtain ⟨hlt, _, _⟩ := h1
              exact Or.inl ⟨trivial, hlt⟩
            | inr h23 =>
              cases h23 with
              | inl h1 =>
                obtain ⟨heq2, _, _⟩ := h1
                exact Or.inr (Or.inl heq2)
              | inr h1 =>
                obtain ⟨hlt, _, _⟩ := h1
                have hT2 := D.trichotomy (x 0) r
                cases hT2 with
                | inl h2 =>
                  obtain ⟨hlt2, _, _⟩ := h2
                  have hA : Endpoint.lt D (Endpoint.finite l) (Endpoint.finite (x 0)) := hlt
                  have hB : Endpoint.lt D (Endpoint.finite (x 0)) (Endpoint.finite r) := hlt2
                  exact (h ⟨hA, hB⟩).elim
                | inr h34 =>
                  cases h34 with
                  | inl h2 =>
                    obtain ⟨heq3, _, _⟩ := h2
                    exact Or.inr (Or.inr (Or.inl heq3))
                  | inr h2 =>
                    obtain ⟨hlt2, _, _⟩ := h2
                    exact Or.inr (Or.inr (Or.inr ⟨hlt2, trivial⟩))
          · intro h
            intro hAB
            obtain ⟨hA, hB⟩ := hAB
            have hAx : D.lt l (x 0) := hA
            have hBx : D.lt (x 0) r := hB
            cases h with
            | inl hL =>
              obtain ⟨_, hLL⟩ := hL
              have hLLx : D.lt (x 0) l := hLL
              have hcon : D.lt (x 0) (x 0) := D.trans hLLx hAx
              exact D.irrefl _ hcon
            | inr h234 =>
              cases h234 with
              | inl hP =>
                have he : x 0 = l := hP
                have hcon : D.lt l l := by rw [he] at hAx; exact hAx
                exact D.irrefl _ hcon
              | inr h34 =>
                cases h34 with
                | inl hP =>
                  have he : x 0 = r := hP
                  have hcon : D.lt r r := by rw [he] at hBx; exact hBx
                  exact D.irrefl _ hcon
                | inr hR =>
                  obtain ⟨hRR, _⟩ := hR
                  have hRRx : D.lt r (x 0) := hRR
                  have hcon : D.lt (x 0) (x 0) := D.trans hBx hRRx
                  exact D.irrefl _ hcon
        rw [heq]
        exact M.union_mem hL (M.union_mem hP1 (M.union_mem hP2 hR))
      | posInf =>
        have hL : M.S 1 (openInterval D Endpoint.negInf (Endpoint.finite l)) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf (Endpoint.finite l))
        have hP : M.S 1 (pointSet l) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.point l)
        have heq : (fun x : Power R 1 => ¬openInterval D (Endpoint.finite l) Endpoint.posInf x)
            = setUnion (openInterval D Endpoint.negInf (Endpoint.finite l)) (pointSet l) := by
          funext x
          apply propext
          constructor
          · intro h
            have hT1 := D.trichotomy (x 0) l
            cases hT1 with
            | inl h1 =>
              obtain ⟨hlt, _, _⟩ := h1
              exact Or.inl ⟨trivial, hlt⟩
            | inr h23 =>
              cases h23 with
              | inl h1 =>
                obtain ⟨heq2, _, _⟩ := h1
                exact Or.inr heq2
              | inr h1 =>
                obtain ⟨hlt, _, _⟩ := h1
                exact (h ⟨hlt, trivial⟩).elim
          · intro h
            intro hAB
            obtain ⟨hA, hB⟩ := hAB
            have hAx : D.lt l (x 0) := hA
            cases h with
            | inl hL =>
              obtain ⟨_, hLL⟩ := hL
              have hLLx : D.lt (x 0) l := hLL
              have hcon : D.lt (x 0) (x 0) := D.trans hLLx hAx
              exact D.irrefl _ hcon
            | inr hP =>
              have he : x 0 = l := hP
              have hcon : D.lt l l := by rw [he] at hAx; exact hAx
              exact D.irrefl _ hcon
        rw [heq]
        exact M.union_mem hL hP
    | posInf =>
      cases b with
      | negInf =>
        have hU : M.S 1 (openInterval D Endpoint.negInf Endpoint.posInf) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf Endpoint.posInf)
        have hEmpty : forall x : Power R 1, openInterval D Endpoint.posInf Endpoint.negInf x -> False := by
          intro x hx
          obtain ⟨h1, _⟩ := hx
          cases h1
        have heq : (fun x : Power R 1 => ¬openInterval D Endpoint.posInf Endpoint.negInf x)
            = openInterval D Endpoint.negInf Endpoint.posInf := by
          funext x
          apply propext
          constructor
          · intro _
            exact ⟨trivial, trivial⟩
          · intro _ hE
            exact (hEmpty x hE).elim
        rw [heq]
        exact hU
      | finite r =>
        have hU : M.S 1 (openInterval D Endpoint.negInf Endpoint.posInf) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf Endpoint.posInf)
        have hEmpty : forall x : Power R 1, openInterval D Endpoint.posInf (Endpoint.finite r) x -> False := by
          intro x hx
          obtain ⟨h1, _⟩ := hx
          cases h1
        have heq : (fun x : Power R 1 => ¬openInterval D Endpoint.posInf (Endpoint.finite r) x)
            = openInterval D Endpoint.negInf Endpoint.posInf := by
          funext x
          apply propext
          constructor
          · intro _
            exact ⟨trivial, trivial⟩
          · intro _ hE
            exact (hEmpty x hE).elim
        rw [heq]
        exact hU
      | posInf =>
        have hU : M.S 1 (openInterval D Endpoint.negInf Endpoint.posInf) :=
          (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval Endpoint.negInf Endpoint.posInf)
        have hEmpty : forall x : Power R 1, openInterval D Endpoint.posInf Endpoint.posInf x -> False := by
          intro x hx
          obtain ⟨h1, _⟩ := hx
          cases h1
        have heq : (fun x : Power R 1 => ¬openInterval D Endpoint.posInf Endpoint.posInf x)
            = openInterval D Endpoint.negInf Endpoint.posInf := by
          funext x
          apply propext
          constructor
          · intro _
            exact ⟨trivial, trivial⟩
          · intro _ hE
            exact (hEmpty x hE).elim
        rw [heq]
        exact hU
  | union h1 h2 ih1 ih2 =>
    rename_i SA SB
    have heq : (fun x : Power R 1 => ¬(fun x : Power R 1 => SA x \/ SB x) x)
        = setInter (fun x : Power R 1 => ¬SA x) (fun x : Power R 1 => ¬SB x) := by
      funext x
      apply propext
      constructor
      · intro h
        refine ⟨by intro hA; exact h (Or.inl hA), by intro hB; exact h (Or.inr hB)⟩
      · intro h hAB
        obtain ⟨hnA, hnB⟩ := h
        cases hAB with
        | inl hA => exact hnA hA
        | inr hB => exact hnB hB
    rw [heq]
    exact M.inter_mem (ih1 ((M.ominimal _).mpr h1)) (ih2 ((M.ominimal _).mpr h2))

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hinj : forall x y (hx : I x) (hy : I y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) -> x = y)
    {a0 b0 : Endpoint R} (hsub0 : (openInterval D a0 b0).Subset I)
    (hlt0 : Endpoint.lt D a0 b0) :
    exists a b : Endpoint R, Endpoint.lt D a b /\
      (forall x, openInterval D a b x -> openInterval D a0 b0 x) /\
      ((forall x (hxI : I x), openInterval D a b x ->
        exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
        Lt1 D c1 x /\ Lt1 D x c2 /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D c1 y -> Lt1 D y x ->
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D x y -> Lt1 D y c2 ->
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)) \/
      (forall x (hxI : I x), openInterval D a b x ->
        exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
        Lt1 D c1 x /\ Lt1 D x c2 /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D c1 y -> Lt1 D y x ->
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D x y -> Lt1 D y c2 ->
          Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) \/
      (forall x (hxI : I x), openInterval D a b x ->
        exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
        Lt1 D c1 x /\ Lt1 D x c2 /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D c1 y -> Lt1 D y x ->
          Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D x y -> Lt1 D y c2 ->
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)) \/
      (forall x (hxI : I x), openInterval D a b x ->
        exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
        Lt1 D c1 x /\ Lt1 D x c2 /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D c1 y -> Lt1 D y x ->
          Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D x y -> Lt1 D y c2 ->
          Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1))) := by
  have hJ0 : M.S 1 (openInterval D a0 b0) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval a0 b0)
  have heqG : FunctionGraph (R := R) (m := 1) (n := 1)
          (A := openInterval D a0 b0) (B := B)
          (fun p => f.toFun ⟨p.val, hsub0 p.property⟩)
        = setInter (fun z : Power R (1 + 1) => openInterval D a0 b0 (Power.left z))
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
        (A := openInterval D a0 b0) (B := B)
        (fun p => f.toFun ⟨p.val, hsub0 p.property⟩)) := by
    rw [heqG]
    have hJL : M.S (1 + 1)
        (fun z : Power R (1 + 1) => openInterval D a0 b0 (Power.left z)) :=
      M.reindex_mem (fun _ : Fin 1 => (⟨0, by decide⟩ : Fin (1 + 1))) hJ0
    exact M.inter_mem hJL f.graph_mem
  let hfR : DefinableFunction M (openInterval D a0 b0) B :=
    DefinableFunction.mk hJ0 f.codomain_mem
      (fun p => f.toFun ⟨p.val, hsub0 p.property⟩) hGraph
  have hinjR : forall x y (hx : openInterval D a0 b0 x) (hy : openInterval D a0 b0 y),
      hfR.toFun (Subtype.mk x hx) = hfR.toFun (Subtype.mk y hy) -> x = y := by
    intro x y hx hy h
    exact hinj x y (hsub0 hx) (hsub0 hy) h
  have hPat : forall p : Power R 1, forall hp : openInterval D a0 b0 p,
      (exists c1 c2 : Power R 1, openInterval D a0 b0 c1 /\ openInterval D a0 b0 c2 /\
        Lt1 D c1 p /\ Lt1 D p c2 /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D c1 y -> Lt1 D y p ->
          Lt1 D (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1) /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D p y -> Lt1 D y c2 ->
          Lt1 D (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1)) \/
      (exists c1 c2 : Power R 1, openInterval D a0 b0 c1 /\ openInterval D a0 b0 c2 /\
        Lt1 D c1 p /\ Lt1 D p c2 /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D c1 y -> Lt1 D y p ->
          Lt1 D (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1) /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D p y -> Lt1 D y c2 ->
          Lt1 D (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1)) \/
      (exists c1 c2 : Power R 1, openInterval D a0 b0 c1 /\ openInterval D a0 b0 c2 /\
        Lt1 D c1 p /\ Lt1 D p c2 /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D c1 y -> Lt1 D y p ->
          Lt1 D (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1) /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D p y -> Lt1 D y c2 ->
          Lt1 D (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1)) \/
      (exists c1 c2 : Power R 1, openInterval D a0 b0 c1 /\ openInterval D a0 b0 c2 /\
        Lt1 D c1 p /\ Lt1 D p c2 /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D c1 y -> Lt1 D y p ->
          Lt1 D (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1) /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D p y -> Lt1 D y c2 ->
          Lt1 D (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1)) := by
    intro p hp
    exact Monotonicity_Theorem.pattern_at_interior_point D M hfR hinjR hp
  -- Left-above half: definable via failure matrix, projection, axiom
  -- complement, reintersection, projection.
  have hFLA : M.S ((1 + 1) + (1 + (1 + 1)))
      (fun q : Power R ((1 + 1) + (1 + (1 + 1))) =>
        openInterval D a0 b0 (fun i : Fin 1 => q (huC0 i)) ∧
        openInterval D a0 b0 (fun i : Fin 1 => q (huX1 i)) ∧
        openInterval D a0 b0 (fun i : Fin 1 => q (huY2 i)) ∧
        D.lt ((fun j : Fin 2 => q (huLt01 j)) 0)
          ((fun j : Fin 2 => q (huLt01 j)) 1) ∧
        D.lt ((fun j : Fin 2 => q (huLt02 j)) 0)
          ((fun j : Fin 2 => q (huLt02 j)) 1) ∧
        D.lt ((fun j : Fin 2 => q (huLt21 j)) 0)
          ((fun j : Fin 2 => q (huLt21 j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGw j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGx j)) ∧
        (D.lt ((fun j : Fin 2 => q (huBadAbove j)) 0)
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
      (fun q : Power R (1 + 1) => exists t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
            ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
            ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
            ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.existsLast_mem hFLA
  have hC2LA : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
            ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
            ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
            ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.compl_mem hP2LA
  have hWLA : M.S (1 + 1)
      (fun q : Power R (1 + 1) =>
        openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
        openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
        D.lt ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
              else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
              else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
        (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
          (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
              ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
              ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
              ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
            (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
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
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i))) :=
    M.reindex_mem huSwap hWLA
  have hHLA : M.S 1 (fun x : Power R 1 => exists c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
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
        openInterval D a0 b0 (fun i : Fin 1 => q (huC0 i)) ∧
        openInterval D a0 b0 (fun i : Fin 1 => q (huX1 i)) ∧
        openInterval D a0 b0 (fun i : Fin 1 => q (huY2 i)) ∧
        D.lt ((fun j : Fin 2 => q (huLt01 j)) 0)
          ((fun j : Fin 2 => q (huLt01 j)) 1) ∧
        D.lt ((fun j : Fin 2 => q (huLt02 j)) 0)
          ((fun j : Fin 2 => q (huLt02 j)) 1) ∧
        D.lt ((fun j : Fin 2 => q (huLt21 j)) 0)
          ((fun j : Fin 2 => q (huLt21 j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGw j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGx j)) ∧
        (D.lt ((fun j : Fin 2 => q (huBadBelow j)) 0)
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
      (fun q : Power R (1 + 1) => exists t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
            ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
            ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
            ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.existsLast_mem hFLB
  have hC2LB : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
            ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
            ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
            ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.compl_mem hP2LB
  have hWLB : M.S (1 + 1)
      (fun q : Power R (1 + 1) =>
        openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
        openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
        D.lt ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
              else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
              else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
        (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
          (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
              ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
              ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
              ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
            (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
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
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i))) :=
    M.reindex_mem huSwap hWLB
  have hHLB : M.S 1 (fun x : Power R 1 => exists c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
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
        openInterval D a0 b0 (fun i : Fin 1 => q (huC0 i)) ∧
        openInterval D a0 b0 (fun i : Fin 1 => q (huX1 i)) ∧
        openInterval D a0 b0 (fun i : Fin 1 => q (huY2 i)) ∧
        D.lt ((fun j : Fin 2 => q (huLt10 j)) 0)
          ((fun j : Fin 2 => q (huLt10 j)) 1) ∧
        D.lt ((fun j : Fin 2 => q (huLt12 j)) 0)
          ((fun j : Fin 2 => q (huLt12 j)) 1) ∧
        D.lt ((fun j : Fin 2 => q (huLt20 j)) 0)
          ((fun j : Fin 2 => q (huLt20 j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGw j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGx j)) ∧
        (D.lt ((fun j : Fin 2 => q (huBadAbove j)) 0)
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
      (fun q : Power R (1 + 1) => exists t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
            ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
            ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
            ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.existsLast_mem hFRA
  have hC2RA : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
            ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
            ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
            ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.compl_mem hP2RA
  have hWRA : M.S (1 + 1)
      (fun q : Power R (1 + 1) =>
        openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
        openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
        D.lt ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
        (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
          (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
              ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
              ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
              ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
            (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
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
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i))) :=
    M.reindex_mem huSwap hWRA
  have hHRA : M.S 1 (fun x : Power R 1 => exists c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
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
        openInterval D a0 b0 (fun i : Fin 1 => q (huC0 i)) ∧
        openInterval D a0 b0 (fun i : Fin 1 => q (huX1 i)) ∧
        openInterval D a0 b0 (fun i : Fin 1 => q (huY2 i)) ∧
        D.lt ((fun j : Fin 2 => q (huLt10 j)) 0)
          ((fun j : Fin 2 => q (huLt10 j)) 1) ∧
        D.lt ((fun j : Fin 2 => q (huLt12 j)) 0)
          ((fun j : Fin 2 => q (huLt12 j)) 1) ∧
        D.lt ((fun j : Fin 2 => q (huLt20 j)) 0)
          ((fun j : Fin 2 => q (huLt20 j)) 1) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGw j)) ∧
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q (huGx j)) ∧
        (D.lt ((fun j : Fin 2 => q (huBadBelow j)) 0)
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
      (fun q : Power R (1 + 1) => exists t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
            ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
            ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
            ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.existsLast_mem hFRB
  have hC2RB : M.S (1 + 1)
      (fun q : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
        (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
          openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
            ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
            ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
          D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
            ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
          FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
            (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
          (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
          q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
            = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
          (Power.append q t)) :=
    M.compl_mem hP2RB
  have hWRB : M.S (1 + 1)
      (fun q : Power R (1 + 1) =>
        openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
        openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
        D.lt ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
          ((fun j : Fin 2 => q
            (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
        (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
          (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
            openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
              ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
              ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
            D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
              ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
            FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
              (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
            (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
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
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i))) :=
    M.reindex_mem huSwap hWRB
  have hHRB : M.S 1 (fun x : Power R 1 => exists c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) :=
    M.existsLast_mem hHRBP

  -- Intersections (the four uniform pattern sets).
  have hH1 : M.S 1 (setInter
      (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
      (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))) :=
    M.inter_mem hHLA hHRA
  have hHH2 : M.S 1 (setInter
      (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
      (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))) :=
    M.inter_mem hHLA hHRB
  have hHH3 : M.S 1 (setInter
      (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
      (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))) :=
    M.inter_mem hHLB hHRA
  have hHH4 : M.S 1 (setInter
      (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
      (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)
          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))) :=
    M.inter_mem hHLB hHRB
  -- Covering, above-above case: pattern witnesses land in HLA and HRA.
  have hCovPP : forall p : Power R 1, forall hp : openInterval D a0 b0 p,
      (exists c1 c2 : Power R 1, openInterval D a0 b0 c1 /\ openInterval D a0 b0 c2 /\
        Lt1 D c1 p /\ Lt1 D p c2 /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D c1 y -> Lt1 D y p ->
          Lt1 D (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1) /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D p y -> Lt1 D y c2 ->
          Lt1 D (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1)) ->
      ((fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
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
      have g : D.lt ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
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
      have hYyT : openInterval D a0 b0 yT := h2
      have e1 : Lt1 D c1 yT := hGx
      have e2 : Lt1 D yT p := hLt21
      have hAbove : Lt1 D (hfR.toFun (Subtype.mk p hp)).1
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
      have g2 : D.lt (Power.coord1 vT) (Power.coord1 wT) := hAbove
      cases hBAD with
      | inl hIn =>
        have g1 : D.lt (Power.coord1 wT) (Power.coord1 vT) := hIn
        exact D.irrefl _ (D.trans g1 g2)
      | inr hEqB =>
        have e : Power.coord1 wT = Power.coord1 vT := hEqB
        have g3 : D.lt (Power.coord1 vT) (Power.coord1 vT) := e ▸ g2
        exact D.irrefl _ g3
  -- Covering, left-above case: pattern witnesses land in HLA.
  have hCovLA : forall p : Power R 1, forall hp : openInterval D a0 b0 p,
      (exists c1 : Power R 1, openInterval D a0 b0 c1 /\
        Lt1 D c1 p /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D c1 y -> Lt1 D y p ->
          Lt1 D (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1)) ->
      ((fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
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
      have g : D.lt ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
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
      have hYyT : openInterval D a0 b0 yT := h2
      have e1 : Lt1 D c1 yT := hGx
      have e2 : Lt1 D yT p := hLt21
      have hAbove : Lt1 D (hfR.toFun (Subtype.mk p hp)).1
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
      have g2 : D.lt (Power.coord1 vT) (Power.coord1 wT) := hAbove
      cases hBAD with
      | inl hIn =>
        have g1 : D.lt (Power.coord1 wT) (Power.coord1 vT) := hIn
        exact D.irrefl _ (D.trans g1 g2)
      | inr hEqB =>
        have e : Power.coord1 wT = Power.coord1 vT := hEqB
        have g3 : D.lt (Power.coord1 vT) (Power.coord1 vT) := e ▸ g2
        exact D.irrefl _ g3

  -- Covering, right-above case: pattern witnesses land in HRA.
  have hCovRA : forall p : Power R 1, forall hp : openInterval D a0 b0 p,
      (exists c2 : Power R 1, openInterval D a0 b0 c2 /\
        Lt1 D p c2 /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D p y -> Lt1 D y c2 ->
          Lt1 D (hfR.toFun (Subtype.mk p hp)).1 (hfR.toFun (Subtype.mk y hy)).1)) ->
      ((fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
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
      have g : D.lt ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i))
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
      have hYyT : openInterval D a0 b0 yT := h2
      have e1 : Lt1 D p yT := hGx
      have e2 : Lt1 D yT c2 := hLt20
      have hAbove : Lt1 D (hfR.toFun (Subtype.mk p hp)).1
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
      have g2 : D.lt (Power.coord1 vT) (Power.coord1 wT) := hAbove
      cases hBAD with
      | inl hIn =>
        have g1 : D.lt (Power.coord1 wT) (Power.coord1 vT) := hIn
        exact D.irrefl _ (D.trans g1 g2)
      | inr hEqB =>
        have e : Power.coord1 wT = Power.coord1 vT := hEqB
        have g3 : D.lt (Power.coord1 vT) (Power.coord1 vT) := e ▸ g2
        exact D.irrefl _ g3

  -- Covering, left-below case: pattern witnesses land in HLB.
  have hCovLB : forall p : Power R 1, forall hp : openInterval D a0 b0 p,
      (exists c1 : Power R 1, openInterval D a0 b0 c1 /\
        Lt1 D c1 p /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D c1 y -> Lt1 D y p ->
          Lt1 D (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1)) ->
      ((fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
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
      have g : D.lt ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c1) (huSwap i))
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
      have hYyT : openInterval D a0 b0 yT := h2
      have e1 : Lt1 D c1 yT := hGx
      have e2 : Lt1 D yT p := hLt21
      have hBelow : Lt1 D (hfR.toFun (Subtype.mk yT hYyT)).1
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
      have g2 : D.lt (Power.coord1 wT) (Power.coord1 vT) := hBelow
      cases hBAD with
      | inl hIn =>
        have g1 : D.lt (Power.coord1 vT) (Power.coord1 wT) := hIn
        exact D.irrefl _ (D.trans g2 g1)
      | inr hEqB =>
        have e : Power.coord1 wT = Power.coord1 vT := hEqB
        have g3 : D.lt (Power.coord1 vT) (Power.coord1 vT) := e ▸ g2
        exact D.irrefl _ g3

  -- Covering, right-below case: pattern witnesses land in HRB.
  have hCovRB : forall p : Power R 1, forall hp : openInterval D a0 b0 p,
      (exists c2 : Power R 1, openInterval D a0 b0 c2 /\
        Lt1 D p c2 /\
        (forall y (hy : openInterval D a0 b0 y), Lt1 D p y -> Lt1 D y c2 ->
          Lt1 D (hfR.toFun (Subtype.mk y hy)).1 (hfR.toFun (Subtype.mk p hp)).1)) ->
      ((fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1))
                  else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
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
      have g : D.lt ((fun j : Fin 2 => (fun i : Fin (1 + 1) => (Power.append p c2) (huSwap i))
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
      have hYyT : openInterval D a0 b0 yT := h2
      have e1 : Lt1 D p yT := hGx
      have e2 : Lt1 D yT c2 := hLt20
      have hBelow : Lt1 D (hfR.toFun (Subtype.mk yT hYyT)).1
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
      have g2 : D.lt (Power.coord1 wT) (Power.coord1 vT) := hBelow
      cases hBAD with
      | inl hIn =>
        have g1 : D.lt (Power.coord1 vT) (Power.coord1 wT) := hIn
        exact D.irrefl _ (D.trans g2 g1)
      | inr hEqB =>
        have e : Power.coord1 wT = Power.coord1 vT := hEqB
        have g3 : D.lt (Power.coord1 vT) (Power.coord1 vT) := e ▸ g2
        exact D.irrefl _ g3
  -- Uniform covering sets (intersections of half-sets).
  let S1 : Set (Power R 1) := setInter
    (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
    (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
  let S2 : Set (Power R 1) := setInter
    (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
    (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
  let S3 : Set (Power R 1) := setInter
    (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
    (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                  ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
  let S4 : Set (Power R 1) := setInter
    (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                  else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                  ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
                q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                  = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
                (Power.append q2 t)) q)

          (fun i : Fin (1 + 1) => qs (huSwap i)))
          (Power.append x c))
    (fun x : Power R 1 => exists c : Power R 1,
        (fun qs : Power R (1 + 1) =>
          (fun q : Power R (1 + 1) =>
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
            openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
            D.lt ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
              ((fun j : Fin 2 => q
                (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
            (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
              (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
                openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
                D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                  ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
                FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                  (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
                (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
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
  have hCover : forall p : Power R 1, forall hp : openInterval D a0 b0 p,
      S1 p \/ S2 p \/ S3 p \/ S4 p := by
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
  have hS1J0 : forall x : Power R 1, S1 x -> openInterval D a0 b0 x := by
    intro x hx
    obtain ⟨hLmem, hRmem⟩ := hx
    obtain ⟨c, hJc, hJx, hLT, hNeg⟩ := hLmem
    have hJx0 : openInterval D a0 b0 x := hJx
    exact hJx0
  have hS2J0 : forall x : Power R 1, S2 x -> openInterval D a0 b0 x := by
    intro x hx
    obtain ⟨hLmem, hRmem⟩ := hx
    obtain ⟨c, hJc, hJx, hLT, hNeg⟩ := hLmem
    have hJx0 : openInterval D a0 b0 x := hJx
    exact hJx0
  have hS3J0 : forall x : Power R 1, S3 x -> openInterval D a0 b0 x := by
    intro x hx
    obtain ⟨hLmem, hRmem⟩ := hx
    obtain ⟨c, hJc, hJx, hLT, hNeg⟩ := hLmem
    have hJx0 : openInterval D a0 b0 x := hJx
    exact hJx0
  have hS4J0 : forall x : Power R 1, S4 x -> openInterval D a0 b0 x := by
    intro x hx
    obtain ⟨hLmem, hRmem⟩ := hx
    obtain ⟨c, hJc, hJx, hLT, hNeg⟩ := hLmem
    have hJx0 : openInterval D a0 b0 x := hJx
    exact hJx0
  -- Decidability for the domain-emptiness split.
  have hValleyL : forall (a b : Endpoint R),
      (forall y : Power R 1, openInterval D a b y -> openInterval D a0 b0 y) ->
      forall x : Power R 1, forall hxI : I x, forall hxab : openInterval D a b x,
  (fun x : Power R 1 => exists c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) x ->
      exists c1 : Power R 1, openInterval D a b c1 /\ Lt1 D c1 x /\
      forall y : Power R 1, forall hyI : I y, forall hyab : openInterval D a b y,
      Lt1 D c1 y -> Lt1 D y x ->
      Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
    intro a b hJY x hxI hxab hHALFx
    obtain ⟨c, hjc, hjx, hltCX, hneg⟩ := hHALFx
    have hJc0 : openInterval D a0 b0 c := hjc
    have hccx : Lt1 D c x := hltCX
    have hxab0 := hxab
    obtain ⟨hAxc, hBxc⟩ := hxab
    have hCore : forall y : Power R 1, forall hyI : I y,
        forall hyab : openInterval D a b y,
        Lt1 D c y -> Lt1 D y x -> Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
      intro y hyI hyab h1 h2
      have hyJ : openInterval D a0 b0 y := hJY y hyab
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
      have gJc : openInterval D a0 b0 (fun i : Fin 1 => q5v (huC0 i)) := hjc
      have gJx : openInterval D a0 b0 (fun i : Fin 1 => q5v (huX1 i)) := hjx
      have gJy : openInterval D a0 b0 (fun i : Fin 1 => q5v (huY2 i)) := hyJ
      have g0 : D.lt ((fun j : Fin 2 => q5v (huLt01 j)) 0)
          ((fun j : Fin 2 => q5v (huLt01 j)) 1) := hccx
      have g1 : D.lt ((fun j : Fin 2 => q5v (huLt02 j)) 0)
          ((fun j : Fin 2 => q5v (huLt02 j)) 1) := h1
      have g2 : D.lt ((fun j : Fin 2 => q5v (huLt21 j)) 0)
          ((fun j : Fin 2 => q5v (huLt21 j)) 1) := h2
      have gGW : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGw j)) := by
        rw [eGW]
        exact hGWt
      have gGX : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGx j)) := by
        rw [eGX]
        exact hGVt
      have hnb : ¬(D.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0) ((fun j : Fin 2 => q5v (huBadAbove j)) 1) \/ q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun hbad => hneg ⟨tW, gJc, gJx, gJy, g0, g1, g2, gGW, gGX, hbad⟩
      have hnA : ¬D.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0)
          ((fun j : Fin 2 => q5v (huBadAbove j)) 1) :=
        fun h => hnb (Or.inl h)
      have hnE : ¬(q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun h => hnb (Or.inr h)
      have hTri := D.trichotomy (Power.coord1 wT) (Power.coord1 vT)
      cases hTri with
      | inl h =>
        obtain ⟨hlt, _, _⟩ := h
        have hQQ : D.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5v (huBadAbove j)) 1) := hlt
        exact absurd hQQ hnA
      | inr h23 =>
        cases h23 with
        | inl h =>
          obtain ⟨heq, _, _⟩ := h
          have hQQ : q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := heq
          exact absurd hQQ hnE
        | inr h =>
          obtain ⟨hlt, _, _⟩ := h
          exact hlt
    haveI hDecW : Decidable (openInterval D a b c) := Classical.propDecidable _
    by_cases hcW : openInterval D a b c
    · refine ⟨c, hcW, hccx, ?_⟩
      intro y hyI hyab h1 h2
      exact hCore y hyI hyab h1 h2
    · have hcW0 : ¬(Endpoint.lt D a (Endpoint.finite (Power.coord1 c)) /\
        Endpoint.lt D (Endpoint.finite (Power.coord1 c)) b) := hcW
      have hccxC : D.lt (Power.coord1 c) (Power.coord1 x) := hccx
      have hOut : forall yc : R, (Endpoint.lt D a (Endpoint.finite yc) /\
          Endpoint.lt D (Endpoint.finite yc) b) -> D.lt (Power.coord1 c) yc :=
        huOutL D a b (Power.coord1 c) (Power.coord1 x)
          ⟨hAxc, hBxc⟩ hcW0 hccxC
      obtain ⟨c0, hc0W, hc0x⟩ := huMidL D a b x hxab0
      refine ⟨c0, hc0W, hc0x, ?_⟩
      intro y hyI hyab h1 h2
      have hyab0 := hyab
      obtain ⟨hAy, hBy⟩ := hyab
      have h1c : Lt1 D c y := hOut _ ⟨hAy, hBy⟩
      exact hCore y hyI hyab0 h1c h2

  have hValleyR : forall (a b : Endpoint R),
      (forall y : Power R 1, openInterval D a b y -> openInterval D a0 b0 y) ->
      forall x : Power R 1, forall hxI : I x, forall hxab : openInterval D a b x,
  (fun x : Power R 1 => exists c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadAbove j)) 0)
                ((fun j : Fin 2 => q5 (huBadAbove j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) x ->
      exists c1 : Power R 1, openInterval D a b c1 /\ Lt1 D x c1 /\
      forall y : Power R 1, forall hyI : I y, forall hyab : openInterval D a b y,
      Lt1 D x y -> Lt1 D y c1 ->
      Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
    intro a b hJY x hxI hxab hHALFx
    obtain ⟨c, hjc, hjx, hltCX, hneg⟩ := hHALFx
    have hJc0 : openInterval D a0 b0 c := hjc
    have hccx : Lt1 D x c := hltCX
    have hxab0 := hxab
    obtain ⟨hAxc, hBxc⟩ := hxab
    have hCore : forall y : Power R 1, forall hyI : I y,
        forall hyab : openInterval D a b y,
        Lt1 D x y -> Lt1 D y c -> Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1 := by
      intro y hyI hyab h1 h2
      have hyJ : openInterval D a0 b0 y := hJY y hyab
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
      have gJc : openInterval D a0 b0 (fun i : Fin 1 => q5v (huC0 i)) := hjc
      have gJx : openInterval D a0 b0 (fun i : Fin 1 => q5v (huX1 i)) := hjx
      have gJy : openInterval D a0 b0 (fun i : Fin 1 => q5v (huY2 i)) := hyJ
      have g0 : D.lt ((fun j : Fin 2 => q5v (huLt10 j)) 0)
          ((fun j : Fin 2 => q5v (huLt10 j)) 1) := hccx
      have g1 : D.lt ((fun j : Fin 2 => q5v (huLt12 j)) 0)
          ((fun j : Fin 2 => q5v (huLt12 j)) 1) := h1
      have g2 : D.lt ((fun j : Fin 2 => q5v (huLt20 j)) 0)
          ((fun j : Fin 2 => q5v (huLt20 j)) 1) := h2
      have gGW : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGw j)) := by
        rw [eGW]
        exact hGWt
      have gGX : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGx j)) := by
        rw [eGX]
        exact hGVt
      have hnb : ¬(D.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0) ((fun j : Fin 2 => q5v (huBadAbove j)) 1) \/ q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun hbad => hneg ⟨tW, gJc, gJx, gJy, g0, g1, g2, gGW, gGX, hbad⟩
      have hnA : ¬D.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0)
          ((fun j : Fin 2 => q5v (huBadAbove j)) 1) :=
        fun h => hnb (Or.inl h)
      have hnE : ¬(q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun h => hnb (Or.inr h)
      have hTri := D.trichotomy (Power.coord1 wT) (Power.coord1 vT)
      cases hTri with
      | inl h =>
        obtain ⟨hlt, _, _⟩ := h
        have hQQ : D.lt ((fun j : Fin 2 => q5v (huBadAbove j)) 0)
            ((fun j : Fin 2 => q5v (huBadAbove j)) 1) := hlt
        exact absurd hQQ hnA
      | inr h23 =>
        cases h23 with
        | inl h =>
          obtain ⟨heq, _, _⟩ := h
          have hQQ : q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := heq
          exact absurd hQQ hnE
        | inr h =>
          obtain ⟨hlt, _, _⟩ := h
          exact hlt
    haveI hDecW : Decidable (openInterval D a b c) := Classical.propDecidable _
    by_cases hcW : openInterval D a b c
    · refine ⟨c, hcW, hccx, ?_⟩
      intro y hyI hyab h1 h2
      exact hCore y hyI hyab h1 h2
    · have hcW0 : ¬(Endpoint.lt D a (Endpoint.finite (Power.coord1 c)) /\
        Endpoint.lt D (Endpoint.finite (Power.coord1 c)) b) := hcW
      have hccxC : D.lt (Power.coord1 x) (Power.coord1 c) := hccx
      have hOut : forall yc : R, (Endpoint.lt D a (Endpoint.finite yc) /\
          Endpoint.lt D (Endpoint.finite yc) b) -> D.lt yc (Power.coord1 c) :=
        huOutR D a b (Power.coord1 c) (Power.coord1 x)
          ⟨hAxc, hBxc⟩ hcW0 hccxC
      obtain ⟨c0, hc0W, hc0x⟩ := huMidR D a b x hxab0
      refine ⟨c0, hc0W, hc0x, ?_⟩
      intro y hyI hyab h1 h2
      have hyab0 := hyab
      obtain ⟨hAy, hBy⟩ := hyab
      have h2c : Lt1 D y c := hOut _ ⟨hAy, hBy⟩
      exact hCore y hyI hyab0 h1 h2c

  have hPeakL : forall (a b : Endpoint R),
      (forall y : Power R 1, openInterval D a b y -> openInterval D a0 b0 y) ->
      forall x : Power R 1, forall hxI : I x, forall hxab : openInterval D a b x,
  (fun x : Power R 1 => exists c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨0, by decide⟩ : Fin (1 + 1))
                else (⟨1, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt01 j)) 0)
                ((fun j : Fin 2 => q5 (huLt01 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt02 j)) 0)
                ((fun j : Fin 2 => q5 (huLt02 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt21 j)) 0)
                ((fun j : Fin 2 => q5 (huLt21 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) x ->
      exists c1 : Power R 1, openInterval D a b c1 /\ Lt1 D c1 x /\
      forall y : Power R 1, forall hyI : I y, forall hyab : openInterval D a b y,
      Lt1 D c1 y -> Lt1 D y x ->
      Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1 := by
    intro a b hJY x hxI hxab hHALFx
    obtain ⟨c, hjc, hjx, hltCX, hneg⟩ := hHALFx
    have hJc0 : openInterval D a0 b0 c := hjc
    have hccx : Lt1 D c x := hltCX
    have hxab0 := hxab
    obtain ⟨hAxc, hBxc⟩ := hxab
    have hCore : forall y : Power R 1, forall hyI : I y,
        forall hyab : openInterval D a b y,
        Lt1 D c y -> Lt1 D y x -> Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1 := by
      intro y hyI hyab h1 h2
      have hyJ : openInterval D a0 b0 y := hJY y hyab
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
      have gJc : openInterval D a0 b0 (fun i : Fin 1 => q5v (huC0 i)) := hjc
      have gJx : openInterval D a0 b0 (fun i : Fin 1 => q5v (huX1 i)) := hjx
      have gJy : openInterval D a0 b0 (fun i : Fin 1 => q5v (huY2 i)) := hyJ
      have g0 : D.lt ((fun j : Fin 2 => q5v (huLt01 j)) 0)
          ((fun j : Fin 2 => q5v (huLt01 j)) 1) := hccx
      have g1 : D.lt ((fun j : Fin 2 => q5v (huLt02 j)) 0)
          ((fun j : Fin 2 => q5v (huLt02 j)) 1) := h1
      have g2 : D.lt ((fun j : Fin 2 => q5v (huLt21 j)) 0)
          ((fun j : Fin 2 => q5v (huLt21 j)) 1) := h2
      have gGW : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGw j)) := by
        rw [eGW]
        exact hGWt
      have gGX : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGx j)) := by
        rw [eGX]
        exact hGVt
      have hnb : ¬(D.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0) ((fun j : Fin 2 => q5v (huBadBelow j)) 1) \/ q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun hbad => hneg ⟨tW, gJc, gJx, gJy, g0, g1, g2, gGW, gGX, hbad⟩
      have hnA : ¬D.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0)
          ((fun j : Fin 2 => q5v (huBadBelow j)) 1) :=
        fun h => hnb (Or.inl h)
      have hnE : ¬(q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun h => hnb (Or.inr h)
      have hTri := D.trichotomy (Power.coord1 vT) (Power.coord1 wT)
      cases hTri with
      | inl h =>
        obtain ⟨hlt, _, _⟩ := h
        have hQQ : D.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5v (huBadBelow j)) 1) := hlt
        exact absurd hQQ hnA
      | inr h23 =>
        cases h23 with
        | inl h =>
          obtain ⟨heq, _, _⟩ := h
          have hQQ : q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := heq.symm
          exact absurd hQQ hnE
        | inr h =>
          obtain ⟨hlt, _, _⟩ := h
          exact hlt
    haveI hDecW : Decidable (openInterval D a b c) := Classical.propDecidable _
    by_cases hcW : openInterval D a b c
    · refine ⟨c, hcW, hccx, ?_⟩
      intro y hyI hyab h1 h2
      exact hCore y hyI hyab h1 h2
    · have hcW0 : ¬(Endpoint.lt D a (Endpoint.finite (Power.coord1 c)) /\
        Endpoint.lt D (Endpoint.finite (Power.coord1 c)) b) := hcW
      have hccxC : D.lt (Power.coord1 c) (Power.coord1 x) := hccx
      have hOut : forall yc : R, (Endpoint.lt D a (Endpoint.finite yc) /\
          Endpoint.lt D (Endpoint.finite yc) b) -> D.lt (Power.coord1 c) yc :=
        huOutL D a b (Power.coord1 c) (Power.coord1 x)
          ⟨hAxc, hBxc⟩ hcW0 hccxC
      obtain ⟨c0, hc0W, hc0x⟩ := huMidL D a b x hxab0
      refine ⟨c0, hc0W, hc0x, ?_⟩
      intro y hyI hyab h1 h2
      have hyab0 := hyab
      obtain ⟨hAy, hBy⟩ := hyab
      have h1c : Lt1 D c y := hOut _ ⟨hAy, hBy⟩
      exact hCore y hyI hyab0 h1c h2

  have hPeakR : forall (a b : Endpoint R),
      (forall y : Power R 1, openInterval D a b y -> openInterval D a0 b0 y) ->
      forall x : Power R 1, forall hxI : I x, forall hxab : openInterval D a b x,
  (fun x : Power R 1 => exists c : Power R 1,
      (fun qs : Power R (1 + 1) =>
        (fun q : Power R (1 + 1) =>
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨0, by decide⟩ : Fin (1 + 1))) ∧
          openInterval D a0 b0 (fun _ : Fin 1 => q (⟨1, by decide⟩ : Fin (1 + 1))) ∧
          D.lt ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 0)
            ((fun j : Fin 2 => q
              (if _ : j.val = 0 then (⟨1, by decide⟩ : Fin (1 + 1)) else (⟨0, by decide⟩ : Fin (1 + 1)))) 1) ∧
          (fun q2 : Power R (1 + 1) => ¬ exists t : Power R (1 + (1 + 1)),
            (fun q5 : Power R ((1 + 1) + (1 + (1 + 1))) =>
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huC0 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huX1 i)) ∧
              openInterval D a0 b0 (fun i : Fin 1 => q5 (huY2 i)) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt10 j)) 0)
                ((fun j : Fin 2 => q5 (huLt10 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt12 j)) 0)
                ((fun j : Fin 2 => q5 (huLt12 j)) 1) ∧
              D.lt ((fun j : Fin 2 => q5 (huLt20 j)) 0)
                ((fun j : Fin 2 => q5 (huLt20 j)) 1) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGw j)) ∧
              FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
                (fun j : Fin (1 + 1) => q5 (huGx j)) ∧
              (D.lt ((fun j : Fin 2 => q5 (huBadBelow j)) 0)
                ((fun j : Fin 2 => q5 (huBadBelow j)) 1) ∨
              q5 (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
                = q5 (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))))
              (Power.append q2 t)) q)
        
        (fun i : Fin (1 + 1) => qs (huSwap i)))
        (Power.append x c)) x ->
      exists c1 : Power R 1, openInterval D a b c1 /\ Lt1 D x c1 /\
      forall y : Power R 1, forall hyI : I y, forall hyab : openInterval D a b y,
      Lt1 D x y -> Lt1 D y c1 ->
      Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1 := by
    intro a b hJY x hxI hxab hHALFx
    obtain ⟨c, hjc, hjx, hltCX, hneg⟩ := hHALFx
    have hJc0 : openInterval D a0 b0 c := hjc
    have hccx : Lt1 D x c := hltCX
    have hxab0 := hxab
    obtain ⟨hAxc, hBxc⟩ := hxab
    have hCore : forall y : Power R 1, forall hyI : I y,
        forall hyab : openInterval D a b y,
        Lt1 D x y -> Lt1 D y c -> Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1 := by
      intro y hyI hyab h1 h2
      have hyJ : openInterval D a0 b0 y := hJY y hyab
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
      have gJc : openInterval D a0 b0 (fun i : Fin 1 => q5v (huC0 i)) := hjc
      have gJx : openInterval D a0 b0 (fun i : Fin 1 => q5v (huX1 i)) := hjx
      have gJy : openInterval D a0 b0 (fun i : Fin 1 => q5v (huY2 i)) := hyJ
      have g0 : D.lt ((fun j : Fin 2 => q5v (huLt10 j)) 0)
          ((fun j : Fin 2 => q5v (huLt10 j)) 1) := hccx
      have g1 : D.lt ((fun j : Fin 2 => q5v (huLt12 j)) 0)
          ((fun j : Fin 2 => q5v (huLt12 j)) 1) := h1
      have g2 : D.lt ((fun j : Fin 2 => q5v (huLt20 j)) 0)
          ((fun j : Fin 2 => q5v (huLt20 j)) 1) := h2
      have gGW : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGw j)) := by
        rw [eGW]
        exact hGWt
      have gGX : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) => q5v (huGx j)) := by
        rw [eGX]
        exact hGVt
      have hnb : ¬(D.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0) ((fun j : Fin 2 => q5v (huBadBelow j)) 1) \/ q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun hbad => hneg ⟨tW, gJc, gJx, gJy, g0, g1, g2, gGW, gGX, hbad⟩
      have hnA : ¬D.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0)
          ((fun j : Fin 2 => q5v (huBadBelow j)) 1) :=
        fun h => hnb (Or.inl h)
      have hnE : ¬(q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
          = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))) :=
        fun h => hnb (Or.inr h)
      have hTri := D.trichotomy (Power.coord1 vT) (Power.coord1 wT)
      cases hTri with
      | inl h =>
        obtain ⟨hlt, _, _⟩ := h
        have hQQ : D.lt ((fun j : Fin 2 => q5v (huBadBelow j)) 0)
            ((fun j : Fin 2 => q5v (huBadBelow j)) 1) := hlt
        exact absurd hQQ hnA
      | inr h23 =>
        cases h23 with
        | inl h =>
          obtain ⟨heq, _, _⟩ := h
          have hQQ : q5v (⟨3, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1))))
              = q5v (⟨4, by decide⟩ : Fin ((1 + 1) + (1 + (1 + 1)))) := heq.symm
          exact absurd hQQ hnE
        | inr h =>
          obtain ⟨hlt, _, _⟩ := h
          exact hlt
    haveI hDecW : Decidable (openInterval D a b c) := Classical.propDecidable _
    by_cases hcW : openInterval D a b c
    · refine ⟨c, hcW, hccx, ?_⟩
      intro y hyI hyab h1 h2
      exact hCore y hyI hyab h1 h2
    · have hcW0 : ¬(Endpoint.lt D a (Endpoint.finite (Power.coord1 c)) /\
        Endpoint.lt D (Endpoint.finite (Power.coord1 c)) b) := hcW
      have hccxC : D.lt (Power.coord1 x) (Power.coord1 c) := hccx
      have hOut : forall yc : R, (Endpoint.lt D a (Endpoint.finite yc) /\
          Endpoint.lt D (Endpoint.finite yc) b) -> D.lt yc (Power.coord1 c) :=
        huOutR D a b (Power.coord1 c) (Power.coord1 x)
          ⟨hAxc, hBxc⟩ hcW0 hccxC
      obtain ⟨c0, hc0W, hc0x⟩ := huMidR D a b x hxab0
      refine ⟨c0, hc0W, hc0x, ?_⟩
      intro y hyI hyab h1 h2
      have hyab0 := hyab
      obtain ⟨hAy, hBy⟩ := hyab
      have h2c : Lt1 D y c := hOut _ ⟨hAy, hBy⟩
      exact hCore y hyI hyab0 h1 h2c

  haveI hDecE : Decidable (Exists (fun _ : Power R 1 => True)) := Classical.propDecidable _
  by_cases hE : Exists (fun _ : Power R 1 => True)
  · -- Nonempty domain: the infinitude argument goes through.
    obtain ⟨x0, _⟩ := hE
    have hGreatest : forall L : List R, L ≠ [] -> exists M : R, M ∈ L /\ forall r : R, r ∈ L -> (D.lt r M \/ r = M) := huGreatest D
    have hOutside : forall L : List R, exists x : Power R 1, openInterval D a0 b0 x /\ Power.coord1 x ∉ L := huOutside D hlt0 x0
    have hUFin : forall A B : Set (Power R 1), IsFinite1 A -> IsFinite1 B ->
        IsFinite1 (setUnion A B) := by
      intro A B hA hB
      obtain ⟨L1, hL1⟩ := hA
      obtain ⟨L2, hL2⟩ := hB
      refine ⟨L1 ++ L2, fun x => ⟨?_, ?_⟩⟩
      · intro hx
        have hx2 : A x \/ B x := hx
        cases hx2 with
        | inl ha => exact List.mem_append.mpr (Or.inl ((hL1 x).mp ha))
        | inr hb => exact List.mem_append.mpr (Or.inr ((hL2 x).mp hb))
      · intro hm
        cases List.mem_append.mp hm with
        | inl h1 => exact Or.inl ((hL1 x).mpr h1)
        | inr h2 => exact Or.inr ((hL2 x).mpr h2)
    have hInf1 : IsInfinite1 S1 \/ IsInfinite1 S2 \/ IsInfinite1 S3 \/ IsInfinite1 S4 :=
      Classical.byContradiction (fun hCon => by
        have e1 : ¬IsInfinite1 S1 :=
          fun h => hCon (Or.inl h)
        have e234 : ¬(IsInfinite1 S2 \/ IsInfinite1 S3 \/ IsInfinite1 S4) :=
          fun h => hCon (Or.inr h)
        have e2 : ¬IsInfinite1 S2 :=
          fun h => e234 (Or.inl h)
        have e34 : ¬(IsInfinite1 S3 \/ IsInfinite1 S4) :=
          fun h => e234 (Or.inr h)
        have e3 : ¬IsInfinite1 S3 :=
          fun h => e34 (Or.inl h)
        have e4 : ¬IsInfinite1 S4 :=
          fun h => e34 (Or.inr h)
        have hF1 : IsFinite1 S1 := Classical.byContradiction (fun h => e1 h)
        have hF2 : IsFinite1 S2 := Classical.byContradiction (fun h => e2 h)
        have hF3 : IsFinite1 S3 := Classical.byContradiction (fun h => e3 h)
        have hF4 : IsFinite1 S4 := Classical.byContradiction (fun h => e4 h)
        have hU : IsFinite1 (setUnion (setUnion S1 S2) (setUnion S3 S4)) :=
          hUFin _ _ (hUFin _ _ hF1 hF2) (hUFin _ _ hF3 hF4)
        obtain ⟨Lc, hLc⟩ := hU
        obtain ⟨x, hxJ, hxo⟩ := hOutside Lc
        have hmem := hCover x hxJ
        have hUx : setUnion (setUnion S1 S2) (setUnion S3 S4) x := by
          cases hmem with
          | inl h1 => exact Or.inl (Or.inl h1)
          | inr h234 =>
            cases h234 with
            | inl h2 => exact Or.inl (Or.inr h2)
            | inr h34 =>
              cases h34 with
              | inl h3 => exact Or.inr (Or.inl h3)
              | inr h4 => exact Or.inr (Or.inr h4)
        have hLcx := (hLc x).mp hUx
        exact hxo hLcx)
    cases hInf1 with
    | inl hI1 =>
      obtain ⟨a, b, hab, hsub⟩ :=
        Monotonicity_Theorem.infinite_contains_interval_core D S1 ((M.ominimal S1).mp hS1) hI1
      have hJY : forall y : Power R 1, openInterval D a b y -> openInterval D a0 b0 y :=
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
          Monotonicity_Theorem.infinite_contains_interval_core D S2 ((M.ominimal S2).mp hS2) hI2
        have hJY : forall y : Power R 1, openInterval D a b y -> openInterval D a0 b0 y :=
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
            Monotonicity_Theorem.infinite_contains_interval_core D S3 ((M.ominimal S3).mp hS3) hI3
          have hJY : forall y : Power R 1, openInterval D a b y -> openInterval D a0 b0 y :=
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
            Monotonicity_Theorem.infinite_contains_interval_core D S4 ((M.ominimal S4).mp hS4) hI4
          have hJY : forall y : Power R 1, openInterval D a b y -> openInterval D a0 b0 y :=
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
