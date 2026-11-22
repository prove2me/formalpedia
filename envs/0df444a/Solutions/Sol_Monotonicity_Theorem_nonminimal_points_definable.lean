-- Prove2me | solution 1 for Monotonicity_Theorem.nonminimal_points_definable
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:06:50.600008+00:00
-- url     : https://prove2.me/submissions/54a00140-9b9f-428a-b4b8-8e8bb1489a58

import Definitions.Def_Monotonicity_Theorem_Framework

open Monotonicity_Theorem

namespace Monotonicity_Theorem

theorem leftGenAux {R : Type} {n m : Nat} (x : Power R n) (y : Power R m) :
    Power.left (R := R) (n := n) (m := m) (Power.append x y) = x := by
  funext i
  simp [Power.left, Power.append, Fin.append_left]

theorem rightGenAux {R : Type} {n m : Nat} (x : Power R n) (y : Power R m) :
    Power.right (R := R) (n := n) (m := m) (Power.append x y) = y := by
  funext j
  exact Fin.append_right x y j

-- Index maps into arity 1 + 2. Branches are constructor applications.
def sigIx : Fin 1 → Fin (1 + 2) :=
  fun _ => Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))

def sigIw : Fin 1 → Fin (1 + 2) :=
  fun _ => Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))

def sigLt : Fin 2 → Fin (1 + 2) :=
  fun j => if _ : j.val = 0 then Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))
    else Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))

def sigGw : Fin (1 + 1) → Fin (1 + 2) :=
  fun j => if _ : j.val = 0 then Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))
    else Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))

def sigGx : Fin (1 + 1) → Fin (1 + 2) :=
  fun j => if _ : j.val = 0 then Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))
    else Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))

-- Append-form pair equalities.
theorem pairX {R : Type} (x w y : Power R 1) :
    (fun i : Fin 1 => (Power.append x (Power.append w y)) (sigIx i)) = x := by
  funext k
  have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
  rw [k0]
  simp only [sigIx]
  exact Fin.append_left x (Power.append w y) (⟨0, by omega⟩ : Fin 1)

theorem pairW {R : Type} (x w y : Power R 1) :
    (fun i : Fin 1 => (Power.append x (Power.append w y)) (sigIw i)) = w := by
  funext k
  have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
  rw [k0]
  simp only [sigIw]
  have s1 : (Power.append x (Power.append w y))
      (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2)))
      = (Power.append w y) ((⟨0, by omega⟩ : Fin 2)) :=
    Fin.append_right x (Power.append w y) (⟨0, by omega⟩ : Fin 2)
  have s2 : (Power.append w y) ((⟨0, by omega⟩ : Fin 2))
      = w ((⟨0, by omega⟩ : Fin 1)) :=
    Fin.append_left w y (⟨0, by omega⟩ : Fin 1)
  exact s1.trans s2

theorem pairGw {R : Type} (x w y : Power R 1) :
    (fun j : Fin (1 + 1) => (Power.append x (Power.append w y)) (sigGw j))
      = Power.append w y := by
  funext j
  by_cases hj : j.val = 0
  · have e : sigGw j = Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2)) := by
      simp [sigGw, hj]
    have hj0 : j = Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)) := Fin.ext hj
    calc (Power.append x (Power.append w y)) (sigGw j)
        = (Power.append x (Power.append w y))
          (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))) := by rw [e]
      _ = (Power.append w y) ((⟨0, by omega⟩ : Fin 2)) :=
          Fin.append_right x (Power.append w y) (⟨0, by omega⟩ : Fin 2)
      _ = w ((⟨0, by omega⟩ : Fin 1)) :=
          Fin.append_left w y (⟨0, by omega⟩ : Fin 1)
      _ = (Power.append w y) (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))) :=
          (Fin.append_left w y (⟨0, by omega⟩ : Fin 1)).symm
      _ = (Power.append w y) j := by rw [hj0]
  · have jv : j.val = 1 := by omega
    have e : sigGw j = Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2)) := by
      simp [sigGw, hj]
    have hj1 : j = Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)) := Fin.ext jv
    have eb : ((⟨1, by omega⟩ : Fin 2))
        = Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)) := by rfl
    calc (Power.append x (Power.append w y)) (sigGw j)
        = (Power.append x (Power.append w y))
          (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))) := by rw [e]
      _ = (Power.append w y) ((⟨1, by omega⟩ : Fin 2)) :=
          Fin.append_right x (Power.append w y) (⟨1, by omega⟩ : Fin 2)
      _ = (Power.append w y) (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))) := by
          rw [eb]
      _ = y ((⟨0, by omega⟩ : Fin 1)) :=
          Fin.append_right w y (⟨0, by omega⟩ : Fin 1)
      _ = (Power.append w y) j := by
          rw [hj1]
          exact Fin.append_right w y (⟨0, by omega⟩ : Fin 1)

theorem pairGx {R : Type} (x w y : Power R 1) :
    (fun j : Fin (1 + 1) => (Power.append x (Power.append w y)) (sigGx j))
      = Power.append x y := by
  funext j
  by_cases hj : j.val = 0
  · have e : sigGx j = Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1)) := by
      simp [sigGx, hj]
    have hj0 : j = Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)) := Fin.ext hj
    calc (Power.append x (Power.append w y)) (sigGx j)
        = (Power.append x (Power.append w y))
          (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))) := by rw [e]
      _ = x ((⟨0, by omega⟩ : Fin 1)) :=
          Fin.append_left x (Power.append w y) (⟨0, by omega⟩ : Fin 1)
      _ = (Power.append x y) (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))) :=
          (Fin.append_left x y (⟨0, by omega⟩ : Fin 1)).symm
      _ = (Power.append x y) j := by rw [hj0]
  · have jv : j.val = 1 := by omega
    have e : sigGx j = Fin.natAdd 1 (1 : Fin 2) := by
      simp [sigGx, hj]
    have hj1 : j = Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)) := Fin.ext jv
    have eb : ((1 : Fin 2))
        = Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)) := by rfl
    calc (Power.append x (Power.append w y)) (sigGx j)
        = (Power.append x (Power.append w y))
          (Fin.natAdd 1 (1 : Fin 2)) := by rw [e]
      _ = (Power.append w y) ((1 : Fin 2)) :=
          Fin.append_right x (Power.append w y) (1 : Fin 2)
      _ = (Power.append w y) (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))) := by
          rw [eb]
      _ = y ((⟨0, by omega⟩ : Fin 1)) :=
          Fin.append_right w y (⟨0, by omega⟩ : Fin 1)
      _ = (Power.append x y) j := by
          rw [hj1]
          exact Fin.append_right x y (⟨0, by omega⟩ : Fin 1)

theorem pairLt0 {R : Type} (x w y : Power R 1) :
    (fun j : Fin 2 => (Power.append x (Power.append w y)) (sigLt j)) 0
      = w ((⟨0, by omega⟩ : Fin 1)) := by
  have e : sigLt ((⟨0, by omega⟩ : Fin 2))
      = Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2)) := by
    simp [sigLt]
  calc (fun j : Fin 2 => (Power.append x (Power.append w y)) (sigLt j)) 0
      = (Power.append x (Power.append w y)) (sigLt ((⟨0, by omega⟩ : Fin 2))) := rfl
    _ = (Power.append x (Power.append w y))
        (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))) := by rw [e]
    _ = (Power.append w y) ((⟨0, by omega⟩ : Fin 2)) :=
        Fin.append_right x (Power.append w y) (⟨0, by omega⟩ : Fin 2)
    _ = w ((⟨0, by omega⟩ : Fin 1)) :=
        Fin.append_left w y (⟨0, by omega⟩ : Fin 1)

theorem pairLt1 {R : Type} (x w y : Power R 1) :
    (fun j : Fin 2 => (Power.append x (Power.append w y)) (sigLt j)) 1
      = x ((⟨0, by omega⟩ : Fin 1)) := by
  have e : sigLt ((⟨1, by omega⟩ : Fin 2))
      = Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1)) := by
    simp [sigLt]
  calc (fun j : Fin 2 => (Power.append x (Power.append w y)) (sigLt j)) 1
      = (Power.append x (Power.append w y)) (sigLt ((⟨1, by omega⟩ : Fin 2))) := rfl
    _ = (Power.append x (Power.append w y))
        (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))) := by rw [e]
    _ = x ((⟨0, by omega⟩ : Fin 1)) :=
        Fin.append_left x (Power.append w y) (⟨0, by omega⟩ : Fin 1)

-- Forward-direction tuple equalities for general middle blocks.
theorem qIw {R : Type} (x : Power R 1) (q12 : Power R 2) :
    (fun i : Fin 1 => (Power.append x q12) (sigIw i))
      = (fun _ : Fin 1 => (Power.append x q12)
        (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2)))) := by
  funext k
  simp only [sigIw]

theorem qIx {R : Type} (x : Power R 1) (q12 : Power R 2) :
    (fun i : Fin 1 => (Power.append x q12) (sigIx i))
      = (fun _ : Fin 1 => (Power.append x q12)
        (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1)))) := by
  funext k
  simp only [sigIx]

theorem qGw {R : Type} (x : Power R 1) (q12 : Power R 2)
    (w Y : Power R 1)
    (hw : w = (fun _ : Fin 1 => (Power.append x q12)
      (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2)))))
    (hY : Y = (fun _ : Fin 1 => (Power.append x q12)
      (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))))) :
    (fun j : Fin (1 + 1) => (Power.append x q12) (sigGw j))
      = Power.append w Y := by
  funext j
  by_cases hj : j.val = 0
  · have e : sigGw j = Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2)) := by
      simp [sigGw, hj]
    have hj0 : j = Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)) := Fin.ext hj
    calc (Power.append x q12) (sigGw j)
        = (Power.append x q12) (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))) := by
          rw [e]
      _ = w ((⟨0, by omega⟩ : Fin 1)) := by
          rw [hw]
      _ = (Power.append w Y) (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))) :=
          (Fin.append_left w Y (⟨0, by omega⟩ : Fin 1)).symm
      _ = (Power.append w Y) j := by rw [hj0]
  · have jv : j.val = 1 := by omega
    have e : sigGw j = Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2)) := by
      simp [sigGw, hj]
    have hj1 : j = Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)) := Fin.ext jv
    calc (Power.append x q12) (sigGw j)
        = (Power.append x q12) (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))) := by
          rw [e]
      _ = Y ((⟨0, by omega⟩ : Fin 1)) := by
          rw [hY]
      _ = (Power.append w Y) (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))) :=
          (Fin.append_right w Y (⟨0, by omega⟩ : Fin 1)).symm
      _ = (Power.append w Y) j := by rw [hj1]

theorem qGx {R : Type} (x : Power R 1) (q12 : Power R 2)
    (X Y : Power R 1)
    (hX : X = (fun _ : Fin 1 => (Power.append x q12)
      (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1)))))
    (hY : Y = (fun _ : Fin 1 => (Power.append x q12)
      (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))))) :
    (fun j : Fin (1 + 1) => (Power.append x q12) (sigGx j))
      = Power.append X Y := by
  funext j
  by_cases hj : j.val = 0
  · have e : sigGx j = Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1)) := by
      simp [sigGx, hj]
    have hj0 : j = Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)) := Fin.ext hj
    calc (Power.append x q12) (sigGx j)
        = (Power.append x q12) (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))) := by
          rw [e]
      _ = X ((⟨0, by omega⟩ : Fin 1)) := by
          rw [hX]
      _ = (Power.append X Y) (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))) :=
          (Fin.append_left X Y (⟨0, by omega⟩ : Fin 1)).symm
      _ = (Power.append X Y) j := by rw [hj0]
  · have jv : j.val = 1 := by omega
    have e : sigGx j = Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2)) := by
      simp [sigGx, hj]
    have hj1 : j = Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)) := Fin.ext jv
    calc (Power.append x q12) (sigGx j)
        = (Power.append x q12) (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))) := by
          rw [e]
      _ = Y ((⟨0, by omega⟩ : Fin 1)) := by
          rw [hY]
      _ = (Power.append X Y) (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))) :=
          (Fin.append_right X Y (⟨0, by omega⟩ : Fin 1)).symm
      _ = (Power.append X Y) j := by rw [hj1]

theorem qLt0 {R : Type} (x : Power R 1) (q12 : Power R 2) :
    (fun j : Fin 2 => (Power.append x q12) (sigLt j)) 0
      = (Power.append x q12) (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))) := by
  have e : sigLt ((0 : Fin 2)) = Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2)) := by
    simp [sigLt]
  calc (fun j : Fin 2 => (Power.append x q12) (sigLt j)) 0
      = (Power.append x q12) (sigLt ((0 : Fin 2))) := rfl
    _ = (Power.append x q12) (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))) := by
        rw [e]

theorem qLt1 {R : Type} (x : Power R 1) (q12 : Power R 2) :
    (fun j : Fin 2 => (Power.append x q12) (sigLt j)) 1
      = (Power.append x q12) (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))) := by
  have e : sigLt ((1 : Fin 2)) = Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1)) := by
    simp [sigLt]
  calc (fun j : Fin 2 => (Power.append x q12) (sigLt j)) 1
      = (Power.append x q12) (sigLt ((1 : Fin 2))) := rfl
    _ = (Power.append x q12) (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))) := by
        rw [e]

end Monotonicity_Theorem

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (fun x : Power R 1 => exists w : Power R 1, I w /\ Lt1 D w x /\
      exists hxw : I w, exists hxx : I x,
        (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk x hxx)).1) := by
  have hIw : M.S (1 + 2) (fun q : Power R (1 + 2) =>
      I (fun i : Fin 1 => q (sigIw i))) :=
    M.reindex_mem sigIw f.domain_mem
  have hIx : M.S (1 + 2) (fun q : Power R (1 + 2) =>
      I (fun i : Fin 1 => q (sigIx i))) :=
    M.reindex_mem sigIx f.domain_mem
  have hLt : M.S (1 + 2) (fun q : Power R (1 + 2) =>
      D.lt ((fun j : Fin 2 => q (sigLt j)) 0)
        ((fun j : Fin 2 => q (sigLt j)) 1)) :=
    M.reindex_mem sigLt M.lt_mem
  have hGw : M.S (1 + 2) (fun q : Power R (1 + 2) =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (sigGw j))) :=
    M.reindex_mem sigGw f.graph_mem
  have hGx : M.S (1 + 2) (fun q : Power R (1 + 2) =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q (sigGx j))) :=
    M.reindex_mem sigGx f.graph_mem
  have hBad0 : M.S 1 (fun x : Power R 1 => exists q12 : Power R 2,
      (fun q : Power R (1 + 2) => I (fun i : Fin 1 => q (sigIw i))) (Power.append x q12) /\
      (fun q : Power R (1 + 2) => I (fun i : Fin 1 => q (sigIx i))) (Power.append x q12) /\
      D.lt ((fun j : Fin 2 => (Power.append x q12) (sigLt j)) 0)
        ((fun j : Fin 2 => (Power.append x q12) (sigLt j)) 1) /\
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => (Power.append x q12) (sigGw j)) /\
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => (Power.append x q12) (sigGx j))) :=
    M.existsLast_mem
      (M.inter_mem hIw (M.inter_mem hIx (M.inter_mem hLt (M.inter_mem hGw hGx))))
  have heq : (fun x : Power R 1 => exists q12 : Power R 2,
      (fun q : Power R (1 + 2) => I (fun i : Fin 1 => q (sigIw i))) (Power.append x q12) /\
      (fun q : Power R (1 + 2) => I (fun i : Fin 1 => q (sigIx i))) (Power.append x q12) /\
      D.lt ((fun j : Fin 2 => (Power.append x q12) (sigLt j)) 0)
        ((fun j : Fin 2 => (Power.append x q12) (sigLt j)) 1) /\
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => (Power.append x q12) (sigGw j)) /\
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => (Power.append x q12) (sigGx j)))
      = (fun x : Power R 1 => exists w : Power R 1, I w /\ Lt1 D w x /\
        exists hxw : I w, exists hxx : I x,
          (f.toFun (Subtype.mk w hxw)).1 = (f.toFun (Subtype.mk x hxx)).1) := by
    funext x
    apply propext
    constructor
    · intro ⟨q12, hIw, hIx, hLt, hGw, hGx⟩
      change I (fun i : Fin 1 => (Power.append x q12) (sigIw i)) at hIw
      change I (fun i : Fin 1 => (Power.append x q12) (sigIx i)) at hIx
      change D.lt ((fun j : Fin 2 => (Power.append x q12) (sigLt j)) 0)
        ((fun j : Fin 2 => (Power.append x q12) (sigLt j)) 1) at hLt
      change FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => (Power.append x q12) (sigGw j)) at hGw
      change FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => (Power.append x q12) (sigGx j)) at hGx
      have eXx : (fun _ : Fin 1 => (Power.append x q12)
          (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1)))) = x := by
        funext k
        have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
        rw [k0]
        exact Fin.append_left x q12 (⟨0, by omega⟩ : Fin 1)
      refine ⟨(fun _ : Fin 1 => (Power.append x q12)
        (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2)))), ?_, ?_, ?_, ?_, ?_⟩
      · rw [← qIw x q12]
        exact hIw
      · rw [qLt0 x q12, qLt1 x q12] at hLt
        rw [← eXx]
        show D.lt ((Power.append x q12) (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))))
          ((Power.append x q12) (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))))
        exact hLt
      · rw [← qIw x q12]
        exact hIw
      · rw [qIx x q12] at hIx
        rw [eXx] at hIx
        exact hIx
      · rw [qGw x q12 _ _ rfl rfl] at hGw
        rw [qGx x q12 _ _ rfl rfl] at hGx
        obtain ⟨hx0, e0⟩ := hGw
        obtain ⟨hx1, e1⟩ := hGx
        have eR : Power.right (Power.append
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))))
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))))) =
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2)))) :=
          rightGenAux _ _
        have eL : Power.left (Power.append
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))))
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))))) =
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2)))) :=
          leftGenAux _ _
        have eLx : Power.left (Power.append
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))))
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))))) =
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1)))) :=
          leftGenAux _ _
        have hSub : (⟨Power.left (Power.append
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2))))
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))))), hx0⟩
              : {x : Power R 1 // I x})
            = (⟨(fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 2)))), hIw⟩
              : {x : Power R 1 // I x}) := Subtype.ext eL
        rw [eR, hSub] at e0
        have eRx : Power.right (Power.append
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))))
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))))) =
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2)))) :=
          rightGenAux _ _
        have hIxX : I (fun _ : Fin 1 => (Power.append x q12)
            (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1)))) := by
          rw [← qIx x q12]
          exact hIx
        have hIx5 : I x := by
          rw [← eXx]
          exact hIxX
        have hSub2 : (⟨Power.left (Power.append
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.castAdd 2 ((⟨0, by omega⟩ : Fin 1))))
            (fun _ : Fin 1 => (Power.append x q12)
              (Fin.natAdd 1 ((⟨1, by omega⟩ : Fin 2))))), hx1⟩
              : {x : Power R 1 // I x})
            = (⟨x, hIx5⟩ : {x : Power R 1 // I x}) :=
          Subtype.ext (eLx.trans eXx)
        rw [eRx, hSub2] at e1
        exact e0.symm.trans e1
    · intro ⟨w, hwI, hlt, hxw, hxx, heqout⟩
      refine ⟨Power.append w ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1),
        ?_, ?_, ?_, ?_, ?_⟩
      · show I (fun i : Fin 1 =>
          (Power.append x (Power.append w ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)))
            (sigIw i))
        rw [pairW x w _]
        exact hwI
      · show I (fun i : Fin 1 =>
          (Power.append x (Power.append w ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)))
            (sigIx i))
        rw [pairX x w _]
        exact hxx
      · show D.lt ((fun j : Fin 2 =>
          (Power.append x (Power.append w ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)))
            (sigLt j)) 0)
          ((fun j : Fin 2 =>
          (Power.append x (Power.append w ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)))
            (sigLt j)) 1)
        rw [pairLt0 x w _, pairLt1 x w _]
        exact hlt
      · show FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) =>
          (Power.append x (Power.append w ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)))
            (sigGw j))
        rw [pairGw x w _]
        have eL : Power.left (Power.append w
            ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)) = w :=
          leftGenAux _ _
        have hWit : I (Power.left (Power.append w
            ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1))) := by
          rw [eL]
          exact hxw
        have hSub2 : (⟨w, hxw⟩ : {x : Power R 1 // I x})
            = (⟨Power.left (Power.append w
              ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)), hWit⟩
              : {x : Power R 1 // I x}) := Subtype.ext eL.symm
        have hEqW : Power.right (Power.append w
            ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1))
            = ((f.toFun (⟨Power.left (Power.append w
              ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)), hWit⟩
              : {x : Power R 1 // I x})).1 : Power R 1) := by
          rw [rightGenAux, ← hSub2]
        exact ⟨hWit, hEqW⟩
      · show FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun j : Fin (1 + 1) =>
          (Power.append x (Power.append w ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)))
            (sigGx j))
        rw [pairGx x w _]
        have eLx : Power.left (Power.append x
            ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)) = x :=
          leftGenAux _ _
        have hWitX : I (Power.left (Power.append x
            ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1))) := by
          rw [eLx]
          exact hxx
        have hSubX : (⟨x, hxx⟩ : {x : Power R 1 // I x})
            = (⟨Power.left (Power.append x
              ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)), hWitX⟩
              : {x : Power R 1 // I x}) := Subtype.ext eLx.symm
        have hEqX : Power.right (Power.append x
            ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1))
            = ((f.toFun (⟨Power.left (Power.append x
              ((f.toFun (⟨w, hxw⟩ : {x : Power R 1 // I x})).1)), hWitX⟩
              : {x : Power R 1 // I x})).1 : Power R 1) := by
          rw [rightGenAux, ← hSubX]
          exact heqout
        exact ⟨hWitX, hEqX⟩
  rw [heq] at hBad0
  exact hBad0
