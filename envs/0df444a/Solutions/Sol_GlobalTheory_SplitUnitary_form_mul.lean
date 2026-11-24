-- Prove2me | solution 1 for GlobalTheory.SplitUnitary.form_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:16:04.279798+00:00
-- url     : https://prove2.me/submissions/99bb9d9f-9324-4a0d-b918-53b05a8508eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Theorems.Thm_GlobalTheory_SplitUnitary_hTens_eq

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
theorem _root_.solution (Q : Matrix α α E) (g : UG c (stdJ ν E)) (w w' : Matrix α (ν ⊕ ν) E) :
    form c Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (w' * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) =
      form c Q w w' := by
  have h := (mem_UG_iff c _).mp g.2
  rw [form, form, hTens_eq, hTens_eq, Matrix.map_mul (f := c), transpose_mul]
  conv_rhs => rw [← h]
  simp only [Matrix.mul_assoc]
end GlobalTheory.SplitUnitary
