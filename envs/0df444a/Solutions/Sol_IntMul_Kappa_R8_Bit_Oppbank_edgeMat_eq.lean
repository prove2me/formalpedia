-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.edgeMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:17:18.221453+00:00
-- url     : https://prove2.me/submissions/ee6b2431-baa2-437a-a727-6c3d79baa955

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Matrix
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.EOKO
open AModel AModelFac

variable {l n p : Type*} [Fintype l] [Fintype n] [Fintype p] [DecidableEq n]
variable {m : ℕ}

def toG (N : ℕ) (A : Matrix n n ℚ) : Matrix n n (goodSub N) := A.map (toGood N)

lemma redHom_apply (N : ℕ) (r : goodSub N) : redHom N r = redFun N r := rfl

lemma toGood_val {N : ℕ} {r : ℚ} (h : Nat.Coprime r.den N) : (toGood N r : ℚ) = r := by
  rw [toGood, dif_pos h]

lemma redQ_eq {N : ℕ} {r : ℚ} (h : Nat.Coprime r.den N) : redQ N r = redFun N r := by
  simp only [redQ, toGood, dif_pos h, redHom_apply]

lemma redQ_intCast (N : ℕ) (z : ℤ) : redQ N z = z := by
  have hc : Nat.Coprime ((z : ℚ).den) N := by simp
  rw [redQ_eq hc]
  simpa using redFun_spec hc z 1 (by simp)

lemma redQ_zero (N : ℕ) : redQ N 0 = 0 := by simpa using redQ_intCast N 0

theorem goodM_mul {N : ℕ} {A : Matrix l n ℚ} {B : Matrix n p ℚ}
    (hA : GoodM N A) (hB : GoodM N B) : GoodM N (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (goodSub N).sum_mem fun k _ => (goodSub N).mul_mem (hA i k) (hB k j)

theorem toG_val_mat {N : ℕ} {A : Matrix n n ℚ} (hA : GoodM N A) :
    (goodSub N).subtype.mapMatrix (toG N A) = A := by
  ext i j; simp [toG, toGood_val (hA i j)]

theorem toG_mul {N : ℕ} {A B : Matrix n n ℚ} (hA : GoodM N A) (hB : GoodM N B) :
    toG N (A * B) = toG N A * toG N B := by
  refine Matrix.map_injective (f := ((↑) : goodSub N → ℚ)) Subtype.val_injective ?_
  have hAB : GoodM N (A * B) := goodM_mul hA hB
  calc
    (goodSub N).subtype.mapMatrix (toG N (A * B)) = A * B := toG_val_mat hAB
    _ = (goodSub N).subtype.mapMatrix (toG N A) *
          (goodSub N).subtype.mapMatrix (toG N B) := by
            rw [toG_val_mat hA, toG_val_mat hB]
    _ = (goodSub N).subtype.mapMatrix (toG N A * toG N B) := by
            rw [← map_mul]

theorem redMap_eq (N : ℕ) (A : Matrix n n ℚ) :
    A.map (redQ N) = (redHom N).mapMatrix (toG N A) := by
  ext i j; rfl

theorem redMap_mul {N : ℕ} {A B : Matrix n n ℚ} (hA : GoodM N A) (hB : GoodM N B) :
    (A * B).map (redQ N) = A.map (redQ N) * B.map (redQ N) := by
  rw [redMap_eq, redMap_eq, redMap_eq, toG_mul hA hB, map_mul]

theorem redMap_perm (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    (σ.permMatrix ℚ).map (redQ N) = σ.permMatrix (ZMod N) := by
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  split_ifs
  · simpa using redQ_intCast N 1
  · exact redQ_zero N

theorem goodM_perm (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) :
    GoodM N (σ.permMatrix ℚ) := by
  intro i j
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem solution {N : ℕ} {e : Edge m} {q : Matrix (Fin m) (Fin m) ℚ}
    (he : EdgeQ e q) (h1 : GoodM N e.E₁) (h2 : GoodM N e.E₂) :
    edgeMat N e = redM N (pswQ q) := by
  obtain ⟨-, -, -, -, -, hq⟩ := he
  rw [edgeMat, ← hq]
  simp only [redM]
  rw [redMap_mul (goodM_mul h1 (goodM_perm N _)) h2, redMap_mul h1 (goodM_perm N _),
    redMap_perm]
