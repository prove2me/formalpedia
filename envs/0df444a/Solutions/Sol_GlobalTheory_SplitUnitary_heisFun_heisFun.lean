-- Prove2me | solution 1 for GlobalTheory.SplitUnitary.heisFun_heisFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:14:45.43669+00:00
-- url     : https://prove2.me/submissions/ccd92adc-3d9d-413b-ab09-a080be9050fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Theorems.Thm_GlobalTheory_SplitUnitary_form_add_left
import Theorems.Thm_GlobalTheory_SplitUnitary_form_add_right
import Theorems.Thm_GlobalTheory_SplitUnitary_form_swap
import Theorems.Thm_GlobalTheory_SplitUnitary_form_left_left
import Theorems.Thm_GlobalTheory_SplitUnitary_form_right_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
namespace GlobalTheory.SplitUnitary
theorem _root_.solution [CharZero F] (hc : ∀ z, c (c z) = z) (ψ : AddChar F ℂ) {Q : Matrix α α E} (hQ : IsHerm c Q)
    (w w' : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) :
    heisFun c ψ Q w (heisFun c ψ Q w' φ) = ψ (2⁻¹ * form c Q w w') • heisFun c ψ Q (w + w') φ := by
  have e1 : ∀ x x' : Matrix α ν E, fromCols (x + x') (0 : Matrix α ν E) = fromCols x 0 + fromCols x' 0 := fun x x' => by
    ext i (j | j) <;> simp
  have e2 : ∀ y y' : Matrix α ν E, fromCols (0 : Matrix α ν E) (y + y') = fromCols 0 y + fromCols 0 y' := fun x x' => by
    ext i (j | j) <;> simp
  have e3 : ∀ u : Matrix α (ν ⊕ ν) E, u = fromCols u.toCols₁ 0 + fromCols 0 u.toCols₂ := fun u => by
    ext i (j | j) <;> simp
  have e4 : form c Q w w' = form c Q (fromCols w.toCols₁ 0) (fromCols 0 w'.toCols₂) -
      form c Q (fromCols w'.toCols₁ 0) (fromCols 0 w.toCols₂) := by
    conv_lhs => rw [e3 w, e3 w']
    rw [form_add_left, form_add_right, form_add_right, form_left_left, form_right_right,
      form_swap c hc hQ (fromCols w'.toCols₁ 0)]
    ring
  funext x
  rw [Pi.smul_apply, heisFun, heisFun, heisFun, show (w + w').toCols₁ = w.toCols₁ + w'.toCols₁ from rfl,
    show (w + w').toCols₂ = w.toCols₂ + w'.toCols₂ from rfl, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x, e4]
  congr 2
  simp only [e1, e2, form_add_left, form_add_right]
  ring
end GlobalTheory.SplitUnitary
