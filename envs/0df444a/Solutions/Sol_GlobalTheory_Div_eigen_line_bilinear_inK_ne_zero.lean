-- Prove2me | solution 1 for GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:21.414873+00:00
-- url     : https://prove2.me/submissions/1e7b7528-1ea0-4b12-a7e6-abf931a17b9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.eigen_line_bilinear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.Div.eigen_line_bilinear
theorem _root_.solution (hfree : Module.Free O H) {h : H} (hh : h ≠ 0) : inK (O := O) K H h ≠ 0 := by
  have hloc : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).2 (TensorProduct.isBaseChange O H K)
  intro h0
  have h0' : TensorProduct.mk O K H 1 h = 0 := h0
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) _).1 h0'
  rw [Submonoid.smul_def] at ht
  exact hh ((smul_eq_zero.1 ht).resolve_left (nonZeroDivisors.ne_zero t.2))
end GlobalTheory.Div.eigen_line_bilinear
