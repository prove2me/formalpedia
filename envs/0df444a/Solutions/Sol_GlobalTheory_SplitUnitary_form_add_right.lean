-- Prove2me | solution 1 for GlobalTheory.SplitUnitary.form_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:50.064311+00:00
-- url     : https://prove2.me/submissions/9a5a729b-7d45-4655-8779-643ae7b57dbc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary

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
theorem _root_.solution (Q : Matrix α α E) (w w₁ w₂ : Matrix α (ν ⊕ ν) E) :
    form c Q w (w₁ + w₂) = form c Q w w₁ + form c Q w w₂ := by
  simp only [form, hTens, Matrix.add_apply, Finset.sum_add_distrib, map_add, mul_add]
end GlobalTheory.SplitUnitary
