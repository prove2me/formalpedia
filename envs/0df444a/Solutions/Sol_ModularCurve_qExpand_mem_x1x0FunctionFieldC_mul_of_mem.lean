-- Prove2me | solution 1 for ModularCurve.qExpand_mem_x1x0FunctionFieldC_mul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/941f28c1-b886-5d27-a0d4-bdef5f2031f7

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_mem_x1x0FunctionFieldC_mul_of_mem
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve IntermediateField
open scoped MatrixGroups

namespace QExpX1X0

open CongruenceSubgroup

theorem gamma1_mul_le (M p : ℕ) : Gamma1 (M * p) ≤ Gamma1 M ⊓ Gamma0 (M * p) := by
  intro A hA
  have hA' := hA
  rw [Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h00
      rwa [map_intCast, map_one] at this
    · have := congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h11
      rwa [map_intCast, map_one] at this
    · have := congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h10
      rwa [map_intCast, map_zero] at this
  · rw [Gamma0_mem]
    exact h10

theorem T_mem (M q : ℕ) : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 q := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem, ModularGroup.coe_T]
    simp
  · rw [Gamma0_mem, ModularGroup.coe_T]
    simp

theorem entry (N t p : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N ⊓ Gamma0 (N * t * p)) :
    ∃ γ₁ ∈ Gamma1 N ⊓ Gamma0 (N * t),
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (p : ℤ) * γ 0 1 ∧ (p : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  obtain ⟨m, hm⟩ := h0
  rw [Gamma1_mem] at h1
  obtain ⟨ha, hd, -⟩ := h1
  have hc : γ 1 0 = (p : ℤ) * (((N * t : ℕ) : ℤ) * m) := by rw [hm]; push_cast; ring
  have hdet : Matrix.det !![γ 0 0, (p : ℤ) * γ 0 1; ((N * t : ℕ) : ℤ) * m, γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    calc γ 0 0 * γ 1 1 - (p : ℤ) * γ 0 1 * (((N * t : ℕ) : ℤ) * m)
        = γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 := by rw [hc]; ring
      _ = 1 := h
  refine ⟨⟨_, hdet⟩, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · show (((!![γ 0 0, (p : ℤ) * γ 0 1; ((N * t : ℕ) : ℤ) * m, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) = 1
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      exact ha
    · show (((!![γ 0 0, (p : ℤ) * γ 0 1; ((N * t : ℕ) : ℤ) * m, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = 1
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact hd
    · show (((!![γ 0 0, (p : ℤ) * γ 0 1; ((N * t : ℕ) : ℤ) * m, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
      rw [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]
  · rw [Gamma0_mem]
    show (((!![γ 0 0, (p : ℤ) * γ 0 1; ((N * t : ℕ) : ℤ) * m, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod (N * t)) = 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  · show (!![γ 0 0, (p : ℤ) * γ 0 1; ((N * t : ℕ) : ℤ) * m, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = γ 0 0
    simp
  · show (!![γ 0 0, (p : ℤ) * γ 0 1; ((N * t : ℕ) : ℤ) * m, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = (p : ℤ) * γ 0 1
    simp
  · show (p : ℤ) * (!![γ 0 0, (p : ℤ) * γ 0 1; ((N * t : ℕ) : ℤ) * m, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = γ 1 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    exact hc.symm
  · show (!![γ 0 0, (p : ℤ) * γ 0 1; ((N * t : ℕ) : ℤ) * m, γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = γ 1 1
    simp

end QExpX1X0

open QExpX1X0 CongruenceSubgroup in
theorem solution
    (N t p : ℕ) [NeZero N] [NeZero t] [Fact p.Prime]
    {y : LaurentSeries ℚ} (hy : y ∈ x1x0FunctionFieldC ℚ N (N * t)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    qExpand ℚ p y ∈ x1x0FunctionFieldC ℚ N (N * t * p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (N * t) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne t)⟩
  haveI : (Gamma1 N ⊓ Gamma0 (N * t)).FiniteIndex := Subgroup.finiteIndex_of_le (gamma1_mul_le N t)
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ
    (Γ := Gamma1 N ⊓ Gamma0 (N * t)) (Γ' := Gamma1 N ⊓ Gamma0 (N * t * p))
    (T_mem N (N * t)) p (fun γ hγ => entry N t p γ hγ)
  change y ∈ qExpFunctionFieldC ℚ (Gamma1 N ⊓ Gamma0 (N * t)) at hy
  change qExpand ℚ p y ∈ qExpFunctionFieldC ℚ (Gamma1 N ⊓ Gamma0 (N * t * p))
  rw [qExpFunctionFieldC] at hy ⊢
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 N ⊓ Gamma0 (N * t)))).map
      (qExpandAlgHomC ℚ p) ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 N ⊓ Gamma0 (N * t * p))) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy, rfl⟩

end S_ModularCurve_qExpand_mem_x1x0FunctionFieldC_mul_of_mem
end P2MW
export P2MW.S_ModularCurve_qExpand_mem_x1x0FunctionFieldC_mul_of_mem (solution)
