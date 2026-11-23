-- Prove2me | solution 1 for GlobalTheory.Published.ComplexMultiplicationJSt.finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:19.074564+00:00
-- url     : https://prove2.me/submissions/360b85e9-ca8a-4585-800f-162fdd8b2b58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
open NumberField
open scoped nonZeroDivisors IntermediateField
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
namespace GlobalTheory.Published
namespace _root_.GlobalTheory.Published.ComplexMultiplicationJSt
theorem _root_.solution
    (h : _root_.GlobalTheory.Published.ComplexMultiplicationJSt) [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) {H : IntermediateField K ℂ} (hH : _root_.GlobalTheory.Published.IsHilbertClassField H) :
    Module.finrank K H = classNumber K := by
  obtain ⟨H₀, art, hH₀, -, -, -⟩ := h K h2
  obtain rfl : H = H₀ := le_antisymm (hH₀.2 H hH.1) (hH.2 H₀ hH₀.1)
  haveI := hH.1.1
  haveI := hH.1.2.1
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr art.toEquiv, classNumber,
    Nat.card_eq_fintype_card]
end _root_.GlobalTheory.Published.ComplexMultiplicationJSt
end GlobalTheory.Published
