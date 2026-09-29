-- Prove2me | solution 1 for ModularCurve.coe_atkinLehnerInvolutionFull_modularUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/14e1f3ce-e04f-506c-a152-797c234956d4

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries_of_neZero
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open ModularCurve

private theorem memFullMul (d Q : ℕ) [NeZero d] [NeZero Q] {x : LaurentSeries ℚ}
    (hx : x ∈ modularFunctionField Q) : x ∈ modularFunctionFieldFull (d * Q) :=
  full_degeneracy_le (dvd_mul_left Q d) (modularFunctionField_le_full Q hx)

private theorem memFull (Q : ℕ) [NeZero Q] {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionField Q) :
    x ∈ modularFunctionFieldFull Q :=
  modularFunctionField_le_full Q hx

private theorem unitMemField (Q : ℕ) [NeZero Q] : modularUnitSeries Q ∈ modularFunctionField Q := by
  have h := modularUnitSeries_mem_modularFunctionFieldFull Q
  rw [(functionFieldGeneration_iff_full_eq Q).1 (functionFieldGeneration Q)] at h
  exact h

private theorem alJq {d Q : ℕ} [NeZero Q]
    (hAL : IsAtkinLehnerAutFull d Q (atkinLehnerInvolutionFull d Q))
    (h : jq ∈ modularFunctionFieldFull (d * Q)) :
    ((atkinLehnerInvolutionFull d Q ⟨jq, h⟩ : modularFunctionFieldFull (d * Q)) : LaurentSeries ℚ)
      = qExpand ℚ Q jq := by
  have h1 := (hAL 1 inferInstance (one_dvd d)).1
  have hel : (⟨jq, h⟩ : modularFunctionFieldFull (d * Q))
      = ⟨qExpand ℚ 1 jq, jqd_mem_full (d * Q) (Dvd.dvd.mul_right (one_dvd d) Q)⟩ :=
    Subtype.ext (qExpand_one_apply jq).symm
  rw [hel]
  exact (congrArg Subtype.val h1).trans (qExpand_congr (one_mul Q) jq)

private theorem alJqQ {d Q : ℕ} [NeZero Q]
    (hAL : IsAtkinLehnerAutFull d Q (atkinLehnerInvolutionFull d Q))
    (h : qExpand ℚ Q jq ∈ modularFunctionFieldFull (d * Q)) :
    ((atkinLehnerInvolutionFull d Q ⟨qExpand ℚ Q jq, h⟩ : modularFunctionFieldFull (d * Q)) :
        LaurentSeries ℚ)
      = jq := by
  have h2 := (hAL 1 inferInstance (one_dvd d)).2
  have hel : (⟨qExpand ℚ Q jq, h⟩ : modularFunctionFieldFull (d * Q))
      = ⟨qExpand ℚ (1 * Q) jq, jqd_mem_full (d * Q) (Nat.mul_dvd_mul_right (one_dvd d) Q)⟩ :=
    Subtype.ext (qExpand_congr (one_mul Q).symm jq)
  rw [hel]
  exact (congrArg Subtype.val h2).trans (qExpand_one_apply jq)

private theorem frickeGenuine (Q : ℕ) [NeZero Q] : IsFrickeAutFull Q (frickeInvolutionFull Q) :=
  isFrickeAutFull_frickeInvolutionFull Q (exists_isFrickeAutFull_of_neZero Q)

private theorem frickeJq (Q : ℕ) [NeZero Q] (h : jq ∈ modularFunctionFieldFull Q) :
    ((frickeInvolutionFull Q ⟨jq, h⟩ : modularFunctionFieldFull Q) : LaurentSeries ℚ)
      = qExpand ℚ Q jq := by
  have h1 := frickeGenuine Q 1 Q (one_mul Q) inferInstance inferInstance
  have hel : (⟨jq, h⟩ : modularFunctionFieldFull Q)
      = ⟨qExpand ℚ 1 jq, jqd_mem_full Q (Dvd.intro Q (one_mul Q))⟩ :=
    Subtype.ext (qExpand_one_apply jq).symm
  rw [hel]
  exact congrArg Subtype.val h1

private theorem frickeJqQ (Q : ℕ) [NeZero Q] (h : qExpand ℚ Q jq ∈ modularFunctionFieldFull Q) :
    ((frickeInvolutionFull Q ⟨qExpand ℚ Q jq, h⟩ : modularFunctionFieldFull Q) : LaurentSeries ℚ)
      = jq := by
  have h2 := frickeGenuine Q Q 1 (mul_one Q) inferInstance inferInstance
  exact (congrArg Subtype.val h2).trans (qExpand_one_apply jq)

private theorem alEqFricke {d Q : ℕ} [NeZero d] [NeZero Q]
    (hσ : ∃ σ : modularFunctionFieldFull (d * Q) ≃ₐ[ℚ] modularFunctionFieldFull (d * Q),
        IsAtkinLehnerAutFull d Q σ)
    (x : LaurentSeries ℚ) (hx : x ∈ modularFunctionField Q) :
    ((atkinLehnerInvolutionFull d Q ⟨x, memFullMul d Q hx⟩ : modularFunctionFieldFull (d * Q)) :
        LaurentSeries ℚ)
      = ((frickeInvolutionFull Q ⟨x, memFull Q hx⟩ : modularFunctionFieldFull Q) :
          LaurentSeries ℚ) := by
  have hAL : IsAtkinLehnerAutFull d Q (atkinLehnerInvolutionFull d Q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull d Q hσ
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      rcases hy with rfl | rfl
      · rw [alJq hAL, frickeJq]
      · rw [alJqQ hAL, frickeJqQ]
  | algebraMap r =>
      have e1 : (⟨algebraMap ℚ (LaurentSeries ℚ) r,
            memFullMul d Q ((modularFunctionField Q).algebraMap_mem r)⟩ :
            modularFunctionFieldFull (d * Q))
          = algebraMap ℚ (modularFunctionFieldFull (d * Q)) r := Subtype.ext (by simp)
      have e2 : (⟨algebraMap ℚ (LaurentSeries ℚ) r,
            memFull Q ((modularFunctionField Q).algebraMap_mem r)⟩ :
            modularFunctionFieldFull Q)
          = algebraMap ℚ (modularFunctionFieldFull Q) r := Subtype.ext (by simp)
      rw [e1, e2, AlgEquiv.commutes, AlgEquiv.commutes]
      simp
  | add x y hx hy ihx ihy =>
      have e1 : (⟨x + y, memFullMul d Q (add_mem hx hy)⟩ : modularFunctionFieldFull (d * Q))
          = ⟨x, memFullMul d Q hx⟩ + ⟨y, memFullMul d Q hy⟩ := rfl
      have e2 : (⟨x + y, memFull Q (add_mem hx hy)⟩ : modularFunctionFieldFull Q)
          = ⟨x, memFull Q hx⟩ + ⟨y, memFull Q hy⟩ := rfl
      rw [e1, e2, map_add, map_add]
      push_cast
      rw [ihx, ihy]
  | inv x hx ihx =>
      have e1 : (⟨x⁻¹, memFullMul d Q (inv_mem hx)⟩ : modularFunctionFieldFull (d * Q))
          = (⟨x, memFullMul d Q hx⟩ : modularFunctionFieldFull (d * Q))⁻¹ := rfl
      have e2 : (⟨x⁻¹, memFull Q (inv_mem hx)⟩ : modularFunctionFieldFull Q)
          = (⟨x, memFull Q hx⟩ : modularFunctionFieldFull Q)⁻¹ := rfl
      rw [e1, e2, map_inv₀, map_inv₀]
      push_cast
      rw [ihx]
  | mul x y hx hy ihx ihy =>
      have e1 : (⟨x * y, memFullMul d Q (mul_mem hx hy)⟩ : modularFunctionFieldFull (d * Q))
          = ⟨x, memFullMul d Q hx⟩ * ⟨y, memFullMul d Q hy⟩ := rfl
      have e2 : (⟨x * y, memFull Q (mul_mem hx hy)⟩ : modularFunctionFieldFull Q)
          = ⟨x, memFull Q hx⟩ * ⟨y, memFull Q hy⟩ := rfl
      rw [e1, e2, map_mul, map_mul]
      push_cast
      rw [ihx, ihy]

theorem solution (d Q : ℕ) [NeZero d] [NeZero Q]
    (hσ : ∃ σ : ModularCurve.modularFunctionFieldFull (d * Q) ≃ₐ[ℚ]
        ModularCurve.modularFunctionFieldFull (d * Q), ModularCurve.IsAtkinLehnerAutFull d Q σ)
    (hmem : ModularCurve.modularUnitSeries Q ∈ ModularCurve.modularFunctionFieldFull (d * Q)) :
    ((ModularCurve.atkinLehnerInvolutionFull d Q ⟨ModularCurve.modularUnitSeries Q, hmem⟩ :
        ModularCurve.modularFunctionFieldFull (d * Q)) : LaurentSeries ℚ)
      = (Q : ℚ) ^ 12 • (ModularCurve.modularUnitSeries Q)⁻¹ := by
  have hx : modularUnitSeries Q ∈ modularFunctionField Q := unitMemField Q
  have h := alEqFricke hσ (modularUnitSeries Q) hx
  rcases Classical.em Q.Prime with hQ | -
  · haveI : Fact Q.Prime := ⟨hQ⟩
    exact h.trans (coe_frickeInvolutionFull_modularUnitSeries Q (memFull Q hx))
  · exact h.trans (ModularCurve.coe_frickeInvolutionFull_modularUnitSeries_of_neZero Q (memFull Q hx))

end S_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries
end P2MW
export P2MW.S_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries (solution)
