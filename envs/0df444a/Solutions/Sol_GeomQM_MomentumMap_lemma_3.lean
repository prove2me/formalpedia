-- Prove2me | solution 1 for GeomQM.MomentumMap.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:56:02.967277+00:00
-- url     : https://prove2.me/submissions/fb9d9488-f4cb-475e-a9c2-b6b1f8e50082

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

open Matrix

namespace Aux_GQM3
open GeomQM.MomentumMap

lemma star_half : star (1 / 2 : ℂ) = 1 / 2 := by
  rw [Complex.star_def, map_div₀, map_one, map_ofNat]

lemma lie_herm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (lieO A B).IsHermitian := by
  unfold IsHermitian lieO
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hA.eq, hB.eq,
    Complex.star_def, Complex.conj_I]
  module

lemma lie_lin {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    lieO (r • A + B) C = r • lieO A C + lieO B C := by
  simp only [lieO, RCLike.real_smul_eq_coe_smul (K := ℂ), Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  module

lemma lie_anti {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : lieO A B = -lieO B A := by
  unfold lieO; module

lemma lie_jacobi {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ) :
    lieO A (lieO B C) + lieO B (lieO C A) + lieO C (lieO A B) = 0 := by
  simp only [lieO, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_assoc]
  module

lemma jor_herm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (jordan A B).IsHermitian := by
  unfold IsHermitian jordan
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hA.eq, hB.eq,
    star_half, add_comm]

lemma jor_lin {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    jordan (r • A + B) C = r • jordan A C + jordan B C := by
  simp only [jordan, RCLike.real_smul_eq_coe_smul (K := ℂ), Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  module

lemma jor_comm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : jordan A B = jordan B A := by
  unfold jordan; rw [add_comm]

lemma jor_id {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    jordan (jordan A B) (jordan A A) = jordan A (jordan B (jordan A A)) := by
  simp only [jordan, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_assoc]
  module

lemma lie_leib {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ) :
    lieO A (jordan B C) = jordan (lieO A B) C + jordan B (lieO A C) := by
  simp only [lieO, jordan, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.sub_mul, Matrix.mul_sub, ← Matrix.mul_assoc]
  module

lemma assoc {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ) :
    jordan (jordan A B) C - jordan A (jordan B C) = (1 / 4 : ℝ) • lieO (lieO A C) B := by
  simp only [lieO, jordan, RCLike.real_smul_eq_coe_smul (K := ℂ), Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    ← Matrix.mul_assoc, smul_sub, smul_add, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [hI]
  push_cast
  module

end Aux_GQM3

open GeomQM.MomentumMap in
theorem solution (n : ℕ) (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (lieO A B).IsHermitian ∧
    (∀ r : ℝ, lieO (r • A + B) C = r • lieO A C + lieO B C) ∧
    lieO A B = -lieO B A ∧
    lieO A (lieO B C) + lieO B (lieO C A) + lieO C (lieO A B) = 0 ∧
    (jordan A B).IsHermitian ∧
    (∀ r : ℝ, jordan (r • A + B) C = r • jordan A C + jordan B C) ∧
    jordan A B = jordan B A ∧
    jordan (jordan A B) (jordan A A) = jordan A (jordan B (jordan A A)) ∧
    lieO A (jordan B C) = jordan (lieO A B) C + jordan B (lieO A C) ∧
    jordan (jordan A B) C - jordan A (jordan B C) =
      (1 / 4 : ℝ) • lieO (lieO A C) B :=
  ⟨Aux_GQM3.lie_herm hA hB, fun r => Aux_GQM3.lie_lin A B C r, Aux_GQM3.lie_anti A B,
    Aux_GQM3.lie_jacobi A B C, Aux_GQM3.jor_herm hA hB, fun r => Aux_GQM3.jor_lin A B C r,
    Aux_GQM3.jor_comm A B, Aux_GQM3.jor_id A B, Aux_GQM3.lie_leib A B C, Aux_GQM3.assoc A B C⟩
