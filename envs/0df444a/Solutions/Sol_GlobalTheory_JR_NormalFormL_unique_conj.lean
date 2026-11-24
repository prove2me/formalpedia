-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.unique_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:53.604652+00:00
-- url     : https://prove2.me/submissions/995bbea8-1c43-42c2-abb9-532e5984e067

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_GlobalTheory_JR_NormalFormL_mul_Bm
import Theorems.Thm_GlobalTheory_JR_NormalFormL_vecMul_Bm
import Theorems.Thm_GlobalTheory_JR_NormalFormL_det_Bm_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (Y Y₁ : Gl r k) (hΔ : Delta (inv Y) ≠ 0) (hI : inv Y₁ = inv Y) :
    ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  have hB : IsUnit (Bm Y) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_Bm_ne Y hΔ))
  have hB₁ : IsUnit (Bm Y₁) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_Bm_ne Y₁ (hI ▸ hΔ)))
  set u := hB.unit with hu
  set u₁ := hB₁.unit with hu₁
  have eu : (u : Matrix (Fin r) (Fin r) k) = Bm Y := hB.unit_spec
  have eu₁ : (u₁ : Matrix (Fin r) (Fin r) k) = Bm Y₁ := hB₁.unit_spec
  refine ⟨u₁ * u⁻¹, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨A, b, c, l⟩ := Y
    obtain ⟨A₁, b₁, c₁, l₁⟩ := Y₁
    have hAB := mul_Bm (A, b, c, l)
    have hAB₁ := mul_Bm (A₁, b₁, c₁, l₁)
    have hc := vecMul_Bm (A, b, c, l)
    have hc₁ := vecMul_Bm (A₁, b₁, c₁, l₁)
    rw [hI] at hAB₁ hc₁
    rw [← eu] at hAB hc
    rw [← eu₁] at hAB₁ hc₁
    have hl : l₁ = l := congrArg (fun a : Inv r k => a.2.2) hI
    simp only [act, _root_.mul_inv_rev, inv_inv, Units.val_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, hl.symm⟩
    · calc (u₁ : Matrix (Fin r) (Fin r) k) * ↑u⁻¹ * A * (↑u * ↑u₁⁻¹)
            = ↑u₁ * (↑u⁻¹ * (A * ↑u)) * ↑u₁⁻¹ := by simp only [mul_assoc]
          _ = ↑u₁ * companion (inv (A, b, c, l)).1 * ↑u₁⁻¹ := by
            rw [hAB, Units.inv_mul_cancel_left]
          _ = A₁ := by rw [← hAB₁, Units.mul_inv_cancel_right]
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; funext i; exact i.elim0
      have e0 : ∀ (B : Matrix (Fin r) (Fin r) k) (Z : Gl r k), B = Bm Z →
          B *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = Z.2.1 := by
        intro B Z hBZ; subst hBZ; funext i; simp [mulVec_single, Bm]
      have hb : (u : Matrix (Fin r) (Fin r) k) *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = b :=
        e0 _ (A, b, c, l) eu
      have hb₁ : (u₁ : Matrix (Fin r) (Fin r) k) *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = b₁ :=
        e0 _ (A₁, b₁, c₁, l₁) eu₁
      rw [← hb, mulVec_mulVec, mul_assoc, Units.inv_mul, mul_one, hb₁]
    · have hc' : c ᵥ* (u : Matrix (Fin r) (Fin r) k) = c₁ ᵥ* (u₁ : Matrix (Fin r) (Fin r) k) :=
        hc.trans hc₁.symm
      rw [← vecMul_vecMul, hc', vecMul_vecMul, Units.mul_inv, vecMul_one]
  · rw [Units.val_mul, mul_assoc, eu.symm, Units.inv_mul, mul_one, eu₁]
  · rintro g ⟨_, hg⟩
    apply Units.ext
    rw [Units.val_mul, eu₁, ← hg, ← eu, mul_assoc, Units.mul_inv, mul_one]
end GlobalTheory.JR.NormalFormL
