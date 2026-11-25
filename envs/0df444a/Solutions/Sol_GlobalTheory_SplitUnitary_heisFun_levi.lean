-- Prove2me | solution 1 for GlobalTheory.SplitUnitary.heisFun_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:13:25.086848+00:00
-- url     : https://prove2.me/submissions/20688f6a-4e43-4632-b53a-883d5820794d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Theorems.Thm_GlobalTheory_SplitUnitary_levi_val
import Theorems.Thm_GlobalTheory_SplitUnitary_form_mul

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
omit [DecidableEq α]
namespace GlobalTheory.SplitUnitary
theorem _root_.solution (hc : ∀ z, c (c z) = z) (ψ : AddChar F ℂ) (Q : Matrix α α E) (a : GL ν E) (w : Matrix α (ν ⊕ ν) E)
    (φ : Matrix α ν E → ℂ) :
    heisFun c ψ Q w (fun x => φ (x * (a : Matrix ν ν E))) =
      fun x => heisFun c ψ Q (w * ((levi c hc a : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) φ (x * (a : Matrix ν ν E)) := by
  have e : ∀ x y : Matrix α ν E, fromCols x y * ((levi c hc a : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) =
      fromCols (x * (a : Matrix ν ν E)) (y * (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ) := fun x y => by
    rw [levi_val, fromCols_mul_fromBlocks]; simp
  have f : ∀ x y : Matrix α ν E, form c Q (fromCols (x * (a : Matrix ν ν E)) 0)
      (fromCols 0 (y * (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ)) = form c Q (fromCols x 0) (fromCols 0 y) := fun x y => by
    rw [← form_mul c Q (levi c hc a) (fromCols x 0), e, e, Matrix.zero_mul, Matrix.zero_mul]
  funext x
  conv_rhs => rw [← fromCols_toCols w, e]
  simp only [heisFun, toCols₁_fromCols, toCols₂_fromCols, f, Matrix.add_mul]
end GlobalTheory.SplitUnitary
