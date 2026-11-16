-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.redM_mul
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:57:14.6922+00:00
-- url     : https://prove2.me/submissions/c96f92cf-80a2-4255-a481-a4e179899dc3

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

open IntMul.Kappa.R6.Bit
open AModelFac
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem toGood_val {N : ℕ} {r : ℚ} (h : Nat.Coprime r.den N) :
    ((toGood N r : goodSub N) : ℚ) = r := by
  simp [toGood, dif_pos h]

private def toG (N : ℕ) (A : Matrix n n ℚ) : Matrix n n (goodSub N) := A.map (toGood N)

private theorem toG_val {N : ℕ} {A : Matrix n n ℚ}
    (hA : ∀ i j, Nat.Coprime (A i j).den N) :
    (goodSub N).subtype.mapMatrix (toG N A) = A := by
  ext i j
  simp [toG, toGood_val (hA i j)]

private theorem goodM_mul {N : ℕ} {A B : Matrix n n ℚ}
    (hA : ∀ i j, Nat.Coprime (A i j).den N)
    (hB : ∀ i j, Nat.Coprime (B i j).den N) :
    ∀ i j, Nat.Coprime ((A * B) i j).den N := by
  intro i j
  have : (A * B) i j ∈ goodSub N := by
    rw [Matrix.mul_apply]
    exact (goodSub N).sum_mem fun k _ => (goodSub N).mul_mem (hA i k) (hB k j)
  exact this

private theorem toG_mul {N : ℕ} {A B : Matrix n n ℚ}
    (hA : ∀ i j, Nat.Coprime (A i j).den N)
    (hB : ∀ i j, Nat.Coprime (B i j).den N) :
    toG N (A * B) = toG N A * toG N B := by
  apply Matrix.map_injective (f := ((↑) : goodSub N → ℚ)) Subtype.val_injective
  change (goodSub N).subtype.mapMatrix (toG N (A * B)) =
    (goodSub N).subtype.mapMatrix (toG N A * toG N B)
  rw [map_mul, toG_val hA, toG_val hB, toG_val (goodM_mul hA hB)]

private theorem redMap_eq (N : ℕ) (A : Matrix n n ℚ) :
    A.map (redQ N) = (redHom N).mapMatrix (toG N A) := by
  ext i j
  rfl

private theorem redMap_mul {N : ℕ} {A B : Matrix n n ℚ}
    (hA : ∀ i j, Nat.Coprime (A i j).den N)
    (hB : ∀ i j, Nat.Coprime (B i j).den N) :
    (A * B).map (redQ N) = A.map (redQ N) * B.map (redQ N) := by
  rw [redMap_eq, redMap_eq, redMap_eq, toG_mul hA hB, map_mul]

theorem solution {m N : ℕ} (A B : QMat2 m)
    (hA : ∀ i j, Nat.Coprime (A i j).den N)
    (hB : ∀ i j, Nat.Coprime (B i j).den N) :
    redM N (A * B) = redM N A * redM N B := by
  simpa [redM] using redMap_mul (n := Fin (m + m)) hA hB
