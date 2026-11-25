-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.quot_maj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:37.947944+00:00
-- url     : https://prove2.me/submissions/16ab2d89-0ab7-4937-9d49-34655f98f5fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G H : Matrix n n ℂ} {V w : Matrix (Fin 1) n ℂ} {B : Matrix m n ℂ} {S : Matrix n m ℂ}
    (hG : Gᴴ = G) (h0 : G.det ≠ 0) (hH : H.PosDef) (hm : H * G⁻¹ * H = G)
    (hw : V * G * wᴴ = 1) (hV : V * G * Vᴴ = 0) (hB : B * G * Vᴴ = 0)
    (hS : S * B = 1 - G * wᴴ * V - G * Vᴴ * w) (hd : (B * G * Bᴴ).det ≠ 0) :
    ∃ L : Matrix m (Fin 1) ℂ, ((B - L * V) * H * (B - L * V)ᴴ).PosDef ∧
      (B - L * V) * H * (B - L * V)ᴴ * (B * G * Bᴴ)⁻¹ * ((B - L * V) * H * (B - L * V)ᴴ) =
        B * G * Bᴴ := by
  have inj : ∀ {k : Type} [Fintype k] [DecidableEq k] (A : Matrix k n ℂ) (R : Matrix n k ℂ),
      A * R = 1 → Function.Injective A.vecMul := fun A R h x y e => by
    have := congrArg (fun z => z ᵥ* R) e
    simpa [vecMul_vecMul, h] using this
  have hh : (V * H * Vᴴ).PosDef :=
    hH.mul_mul_conjTranspose_same (inj V (G * wᴴ) (by rw [← Matrix.mul_assoc, hw]))
  have hu : IsUnit (V * H * Vᴴ).det := hh.det_pos.ne'.isUnit
  refine ⟨B * H * Vᴴ * (V * H * Vᴴ)⁻¹, ?_⟩
  generalize hL : B * H * Vᴴ * (V * H * Vᴴ)⁻¹ = L
  have e1 : (B - L * V) * H * Vᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc L, Matrix.mul_assoc L, ← hL,
      nonsing_inv_mul_cancel_right _ _ hu, sub_self]
  have e2 : (B - L * V) * G * Vᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc L, Matrix.mul_assoc L, hB, hV]; simp
  have hB' : V * G * Bᴴ = 0 := by
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using congrArg conjTranspose hB
  have e3 : (B - L * V) * G * (B - L * V)ᴴ = B * G * Bᴴ := by
    rw [conjTranspose_sub, conjTranspose_mul, Matrix.mul_sub, ← Matrix.mul_assoc, e2,
      Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc L, Matrix.mul_assoc L, hB']
    simp
  have e4 : S * (B - L * V) = 1 - (G * wᴴ + S * L) * V - G * Vᴴ * w := by
    rw [Matrix.mul_sub, hS, Matrix.add_mul, Matrix.mul_assoc S]; abel
  generalize B - L * V = P at e1 e2 e3 e4
  refine ⟨hH.mul_mul_conjTranspose_same (inj P (G * Pᴴ * (B * G * Bᴴ)⁻¹) ?_), ?_⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e3, mul_nonsing_inv _ hd.isUnit]
  obtain ⟨Y, hY⟩ : ∃ Y, Y = P * H * G⁻¹ := ⟨_, rfl⟩
  have y1 : Y * G = P * H := by rw [hY, nonsing_inv_mul_cancel_right _ _ h0.isUnit]
  have y2 : Y * H = P * G := by
    rw [hY]; conv_rhs => rw [← hm]
    simp only [Matrix.mul_assoc]
  have y3 : Y * S * P = Y - Y * (G * wᴴ + S * L) * V := by
    rw [Matrix.mul_assoc, e4, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc Y (G * Vᴴ),
      ← Matrix.mul_assoc Y G, y1, e1, Matrix.mul_assoc]
    simp
  have y4 : Y * (G * wᴴ + S * L) = 0 := by
    have := congrArg (fun Z => Z * H * Vᴴ * (V * H * Vᴴ)⁻¹) y3
    simp only [Matrix.sub_mul] at this
    rw [y2, e2, Matrix.mul_assoc _ P, Matrix.mul_assoc _ (P * H), e1, Matrix.mul_assoc _ V,
      Matrix.mul_assoc _ (V * H), mul_nonsing_inv_cancel_right _ _ hu] at this
    simpa using this
  rw [y4, Matrix.zero_mul, sub_zero] at y3
  have y5 : P * H * Pᴴ = Y * S * (B * G * Bᴴ) := by
    rw [← e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, y3, y1]
  nth_rewrite 1 [y5]
  rw [mul_nonsing_inv_cancel_right _ _ hd.isUnit, ← Matrix.mul_assoc, ← Matrix.mul_assoc, y3, y2, e3]
end GlobalTheory.SW.ShortStep
