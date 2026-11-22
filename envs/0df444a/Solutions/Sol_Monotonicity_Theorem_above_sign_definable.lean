-- Prove2me | solution 1 for Monotonicity_Theorem.above_sign_definable
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:44:03.019053+00:00
-- url     : https://prove2.me/submissions/40c959f7-38b2-48cf-99be-e8af5265a0d1

import Definitions.Def_Monotonicity_Theorem_Framework

open Monotonicity_Theorem

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

open Monotonicity_Theorem

theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (J : Set (Power R 1)) (hJ : M.S 1 J) (c : R) :
    M.S 1 (fun y : Power R 1 => J y ∧ exists v : Power R 1,
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (Power.append y v) /\
      Lt1 D (fun _ => c) v) := by
  have hOI : M.S 1 (openInterval D (Endpoint.finite c) Endpoint.posInf) :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hJw : M.S (1 + 1) (fun q : Power R (1 + 1) =>
      J (fun _ : Fin 1 => q (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))))) :=
    M.reindex_mem (fun _ : Fin 1 => Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1))) hJ
  have hGc : M.S (1 + 1) (fun q : Power R (1 + 1) =>
      FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
        (fun j : Fin (1 + 1) => q j)) :=
    M.reindex_mem (fun j : Fin (1 + 1) => j) f.graph_mem
  have hOv : M.S (1 + 1) (fun q : Power R (1 + 1) =>
      (openInterval D (Endpoint.finite c) Endpoint.posInf)
        (fun _ : Fin 1 => q (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))))) :=
    M.reindex_mem (fun _ : Fin 1 => Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))) hOI
  have hH : M.S 1 (fun y : Power R 1 => exists v : Power R 1,
      (fun q : Power R (1 + 1) => J (fun _ : Fin 1 => q (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v) /\
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (fun j : Fin (1 + 1) => q j))
        (Power.append y v) /\
      (fun q : Power R (1 + 1) => (openInterval D (Endpoint.finite c) Endpoint.posInf)
        (fun _ : Fin 1 => q (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v)) :=
    M.existsLast_mem
      (M.inter_mem hJw (M.inter_mem hGc hOv))
  have heq : (fun y : Power R 1 => exists v : Power R 1,
      (fun q : Power R (1 + 1) => J (fun _ : Fin 1 => q (Fin.castAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v) /\
      (fun q : Power R (1 + 1) => FunctionGraph (R := R) (m := 1) (n := 1)
        (A := I) (B := B) f.toFun (fun j : Fin (1 + 1) => q j))
        (Power.append y v) /\
      (fun q : Power R (1 + 1) => (openInterval D (Endpoint.finite c) Endpoint.posInf)
        (fun _ : Fin 1 => q (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))))
        (Power.append y v))
      = (fun y : Power R 1 => J y ∧ exists v : Power R 1,
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (Power.append y v) /\
        Lt1 D (fun _ => c) v) := by
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
        have hOv' : Lt1 D (fun _ => c) v := hO.left
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
      · show (openInterval D (Endpoint.finite c) Endpoint.posInf)
          (fun _ : Fin 1 => (Power.append y v)
            (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1))))
        have eV : (fun _ : Fin 1 => (Power.append y v)
            (Fin.natAdd 1 ((⟨0, by omega⟩ : Fin 1)))) = v := by
          funext k
          have k0 : k = ((⟨0, by omega⟩ : Fin 1)) := Fin.ext (by omega)
          rw [k0]
          exact Fin.append_right y v (⟨0, by omega⟩ : Fin 1)
        rw [eV]
        have hOv' : D.lt c (v 0) := hO
        show Endpoint.lt D (Endpoint.finite c) (Endpoint.finite (v 0)) ∧
          Endpoint.lt D (Endpoint.finite (v 0)) Endpoint.posInf
        exact ⟨hOv', trivial⟩
  rw [heq] at hH
  exact hH
