-- Prove2me | solution 1 for NetworkVolatility.Robust.theorem_1_part_3_steps_1_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:08:35.301879+00:00
-- url     : https://prove2.me/submissions/0f03f6c4-1af1-431c-b4fe-28d148304db6

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

open Matrix

theorem solution {n : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hW : W.IsSymm) (hWt : Wt.IsSymm) (hL : IsUnit (1 - α • W)) (hLt : IsUnit (1 - α • Wt))
    (f : Fin n → ℝ) :
    (0 < f ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f) →
      let f' := (Real.sqrt (f ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f)))⁻¹ • f
      f' ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f') = 1 ∧
      |(f' ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f') - f' ⬝ᵥ ((1 - α • Wt)⁻¹ *ᵥ f')) /
          f' ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f')| =
        |(f ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f) - f ⬝ᵥ ((1 - α • Wt)⁻¹ *ᵥ f)) /
          f ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f)|) ∧
    (let L := 1 - α • W
     let M := 1 - L * (1 - α • Wt)⁻¹
     f ⬝ᵥ (L⁻¹ *ᵥ f) - f ⬝ᵥ ((1 - α • Wt)⁻¹ *ᵥ f) = f ⬝ᵥ ((L⁻¹ * M) *ᵥ f) ∧
       (L⁻¹ * M).IsSymm ∧ (L⁻¹).IsSymm) := by
  refine ⟨fun hq => ?_, ?_⟩
  · intro f'
    set q := f ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f) with hqdef
    set q' := f ⬝ᵥ ((1 - α • Wt)⁻¹ *ᵥ f) with hq'def
    set c := (Real.sqrt q)⁻¹ with hc
    have hc2 : c * c * q = 1 := by
      rw [hc, ← mul_inv, Real.mul_self_sqrt hq.le, inv_mul_cancel₀ hq.ne']
    have e1 : f' ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f') = c * c * q := by
      show (c • f) ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ (c • f)) = _
      rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hqdef]
      ring
    have e2 : f' ⬝ᵥ ((1 - α • Wt)⁻¹ *ᵥ f') = c * c * q' := by
      show (c • f) ⬝ᵥ ((1 - α • Wt)⁻¹ *ᵥ (c • f)) = _
      rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hq'def]
      ring
    refine ⟨by rw [e1, hc2], ?_⟩
    rw [e1, e2]
    congr 1
    have hcc : c * c ≠ 0 := by
      intro h; rw [h, zero_mul] at hc2; exact zero_ne_one hc2
    have hc0 : c ≠ 0 := fun h => hcc (by rw [h, zero_mul])
    field_simp
  · intro L M
    have hdet : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det _).mp hL
    have hLinv : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hdet
    have hLM : L⁻¹ * M = L⁻¹ - (1 - α • Wt)⁻¹ := by
      show L⁻¹ * (1 - L * (1 - α • Wt)⁻¹) = _
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hLinv, Matrix.one_mul]
    have hLs : L.IsSymm := isSymm_one.sub (hW.smul α)
    have hLts : (1 - α • Wt).IsSymm := isSymm_one.sub (hWt.smul α)
    refine ⟨?_, ?_, hLs.inv⟩
    · rw [hLM, sub_mulVec, dotProduct_sub]
    · rw [hLM]; exact hLs.inv.sub hLts.inv
