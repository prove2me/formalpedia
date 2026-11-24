-- Prove2me | solution 1 for GlobalTheory.ChartRing.eq_evalAdic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:50.546005+00:00
-- url     : https://prove2.me/submissions/ab179fbe-d016-4ec7-9517-33698c489f95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_X
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_C
import Theorems.Thm_GlobalTheory_ChartRing_algHom_ext_of_isHausdorff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ChartRing.evalAdic_X
attribute [local simp] GlobalTheory.ChartRing.evalAdic_C

set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable (J : Ideal S) [IsAdicComplete J S] {s : S} (hs : s ∈ J)
namespace GlobalTheory.ChartRing
theorem _root_.solution (φ : A⟦X⟧ →ₐ[A] S) (h : φ X = s) : φ = evalAdic A J hs :=
  algHom_ext_of_isHausdorff J (h ▸ hs) (by simp [h])
end GlobalTheory.ChartRing
