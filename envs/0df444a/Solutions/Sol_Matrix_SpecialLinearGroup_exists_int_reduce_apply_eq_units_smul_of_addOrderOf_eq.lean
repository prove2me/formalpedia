-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2c6c08b0-b893-50ac-a2a0-01b6d8940b50

import Mathlib
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (m : ℕ) [NeZero m] (w : ZMod m × ZMod m) (hw : addOrderOf w = m) (a : (ZMod m)ˣ) :
    ∃ γ : SL(2, ℤ),
      ((γ 0 0 : ℤ) : ZMod m) * w.1 + ((γ 0 1 : ℤ) : ZMod m) * w.2 = (a : ZMod m) * w.1 ∧
      ((γ 1 0 : ℤ) : ZMod m) * w.1 + ((γ 1 1 : ℤ) : ZMod m) * w.2 = (a : ZMod m) * w.2 := by
  classical
  obtain ⟨hrow, -, -⟩ := CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff m ⊥

  obtain ⟨δ, hδ1, hδ2⟩ := hrow w hw
  have hau : addOrderOf (a : ZMod m) = m := by
    have h1 := ZMod.addOrderOf_coe (a : ZMod m).val (NeZero.ne m)
    rw [ZMod.natCast_zmod_val] at h1
    rw [h1, Nat.Coprime.gcd_eq_one (ZMod.val_coe_unit_coprime a).symm, Nat.div_one]
  have ha : addOrderOf (((0 : ZMod m), (a : ZMod m)) : ZMod m × ZMod m) = m := by
    rw [Prod.addOrderOf, addOrderOf_zero, hau, Nat.lcm_one_left]
  obtain ⟨D, hD1, hD2⟩ := hrow ((0 : ZMod m), (a : ZMod m)) ha

  let φ : SL(2, ℤ) →* SL(2, ZMod m) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod m))
  have hφ : ∀ (g : SL(2, ℤ)) (i j : Fin 2), (φ g : Matrix (Fin 2) (Fin 2) (ZMod m)) i j = ((g i j : ℤ) : ZMod m) :=
    fun g i j => rfl
  let E : Fin 2 → ZMod m := ![0, 1]
  let Wv : Fin 2 → ZMod m := ![w.1, w.2]
  have hE : ∀ (g : SL(2, ℤ)), Matrix.vecMul E (φ g : Matrix (Fin 2) (Fin 2) (ZMod m)) =
      ![((g 1 0 : ℤ) : ZMod m), ((g 1 1 : ℤ) : ZMod m)] := by
    intro g
    ext j
    fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, E, hφ]
  have hEδ : Matrix.vecMul E (φ δ : Matrix (Fin 2) (Fin 2) (ZMod m)) = Wv := by
    rw [hE, hδ1, hδ2]
  have hED : Matrix.vecMul E (φ D : Matrix (Fin 2) (Fin 2) (ZMod m)) = (a : ZMod m) • E := by
    rw [hE, hD1, hD2]
    ext j
    fin_cases j <;> simp [E]

  let γ' : SL(2, ℤ) := δ⁻¹ * D * δ
  have hcancel : (φ δ : Matrix (Fin 2) (Fin 2) (ZMod m)) * (φ δ⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod m)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hW : Matrix.vecMul Wv (φ γ' : Matrix (Fin 2) (Fin 2) (ZMod m)) = (a : ZMod m) • Wv := by
    have : (φ γ' : Matrix (Fin 2) (Fin 2) (ZMod m)) =
        (φ δ⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod m)) * (φ D : Matrix (Fin 2) (Fin 2) (ZMod m)) *
          (φ δ : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
      simp only [γ', map_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [this, ← hEδ, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hcancel,
      Matrix.one_mul, ← Matrix.vecMul_vecMul, hED, Matrix.smul_vecMul]

  refine ⟨Matrix.SpecialLinearGroup.transpose γ', ?_, ?_⟩
  · have h0 := congrFun hW 0
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Wv, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hφ] at h0
    simp only [Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_apply]
    linear_combination h0
  · have h1 := congrFun hW 1
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Wv, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hφ] at h1
    simp only [Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_apply]
    linear_combination h1

end S_Matrix_SpecialLinearGroup_exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq (solution)
