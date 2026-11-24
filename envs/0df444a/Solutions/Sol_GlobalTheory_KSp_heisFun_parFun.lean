-- Prove2me | solution 1 for GlobalTheory.KSp.heisFun_parFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:29:57.54435+00:00
-- url     : https://prove2.me/submissions/516bb2f7-e4b6-4c1e-8099-0e3de66df233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelParabolicOperatorsHeisenbergCompat
import Theorems.Thm_GlobalTheory_SplitUnitary_form_add_left
import Theorems.Thm_GlobalTheory_SplitUnitary_form_add_right
import Theorems.Thm_GlobalTheory_SplitUnitary_form_left_left
import Theorems.Thm_GlobalTheory_SplitUnitary_form_mul
import Theorems.Thm_GlobalTheory_SplitUnitary_form_right_right
import Theorems.Thm_GlobalTheory_SplitUnitary_form_swap
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ), heisFun c ψ Q w (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c p) (heisFun c ψ Q (w * mat c p) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ _ _ _ χ _ _ p hp w φ
  have hc : ∀ z, c (c z) = z := hE.invol
  have hp0 : (mat c p).toBlocks₂₁ = 0 := hp
  set A := (mat c p).toBlocks₁₁ with hA
  set B := (mat c p).toBlocks₁₂ with hB
  set D := (mat c p).toBlocks₂₂ with hD
  have key : ∀ x y : Matrix α ν E, fromCols x y * mat c p = fromCols (x * A) (x * B + y * D) := by
    intro x y
    conv_lhs => rw [← fromBlocks_toBlocks (mat c p)]
    rw [fromCols_mul_fromBlocks, hp0]
    simp [hA, hB, hD]
  have spl : ∀ u v : Matrix α ν E, fromCols u v = fromCols u 0 + fromCols 0 v := fun u v => by
    ext i (j | j) <;> simp
  have e1 : ∀ x x' : Matrix α ν E, fromCols (x + x') (0 : Matrix α ν E) = fromCols x 0 + fromCols x' 0 := fun x x' => by
    ext i (j | j) <;> simp
  have e2 : ∀ y y' : Matrix α ν E, fromCols (0 : Matrix α ν E) (y + y') = fromCols 0 y + fromCols 0 y' := fun x x' => by
    ext i (j | j) <;> simp

  have h1 : ∀ x y : Matrix α ν E, form c Q (fromCols (x * A) 0) (fromCols 0 (y * D)) = form c Q (fromCols x 0) (fromCols 0 y) := by
    intro x y
    have h := form_mul c Q p (fromCols x 0) (fromCols 0 y)
    change form c Q (fromCols x 0 * mat c p) (fromCols 0 y * mat c p) = _ at h
    rw [key, key] at h
    simp only [Matrix.zero_mul, add_zero, zero_add] at h
    rw [spl (x * A) (x * B), form_add_left, form_right_right, add_zero] at h
    exact h

  have h2 : ∀ x x' : Matrix α ν E, form c Q (fromCols (x' * A) 0) (fromCols 0 (x * B)) = form c Q (fromCols (x * A) 0) (fromCols 0 (x' * B)) := by
    intro x x'
    have h := form_mul c Q p (fromCols x' 0) (fromCols x 0)
    change form c Q (fromCols x' 0 * mat c p) (fromCols x 0 * mat c p) = _ at h
    rw [key, key] at h
    simp only [Matrix.zero_mul, add_zero, zero_add] at h
    rw [spl (x' * A) (x' * B), spl (x * A) (x * B), form_add_left, form_add_right, form_add_right,
      form_left_left, form_left_left, form_right_right, form_swap c hc hQ (fromCols (x * A) 0) (fromCols 0 (x' * B))] at h
    linear_combination h
  have hw : w * mat c p = fromCols (w.toCols₁ * A) (w.toCols₁ * B + w.toCols₂ * D) := by
    conv_lhs => rw [← fromCols_toCols w]
    exact key _ _
  funext x
  simp only [heisFun, parFun, pr, hw, toCols₁_fromCols, toCols₂_fromCols]
  rw [← hA, ← hB]
  have key2 : ∀ (a b c d : F) (s t : ℂ), a + b = c + d → ψ a * (s * (ψ b * t)) = s * (ψ c * (ψ d * t)) := by
    intro a b c d s t h
    rw [show ψ a * (s * (ψ b * t)) = s * (ψ (a + b) * t) by rw [AddChar.map_add_eq_mul]; ring, h,
      AddChar.map_add_eq_mul]
    ring
  rw [Matrix.add_mul x w.toCols₁ A, Matrix.add_mul x w.toCols₁ B]
  simp only [e1, e2, form_add_left, form_add_right, h1]
  rw [h2 x w.toCols₁]
  apply key2
  ring
end GlobalTheory.KSp
