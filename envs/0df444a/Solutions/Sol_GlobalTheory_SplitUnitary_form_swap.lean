-- Prove2me | solution 1 for GlobalTheory.SplitUnitary.form_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:02:42.051894+00:00
-- url     : https://prove2.me/submissions/db3ffbed-43d9-49b4-b735-d22093a270bd

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
namespace GlobalTheory.SplitUnitary
theorem _root_.solution (hc : ∀ z, c (c z) = z) {Q : Matrix α α E} (hQ : IsHerm c Q) (w w' : Matrix α (ν ⊕ ν) E) :
    form c Q w' w = -form c Q w w' := by
  have hJ : ∀ j l, c (stdJ ν E j l) = -stdJ ν E l j := by
    rintro (j | j) (l | l) <;> simp [stdJ, one_apply, eq_comm]
  have h : hTens c Q (stdJ ν E) w' w = -c (hTens c Q (stdJ ν E) w w') := by
    simp only [hTens, map_sum, map_mul, hc, hJ, hQ.1, ← Finset.sum_neg_distrib]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    exact Fintype.sum_equiv ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by simp only [Equiv.coe_fn_mk]; ring
  have ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z
  rw [form, form, h, map_neg, ht, mul_neg]
end GlobalTheory.SplitUnitary
