-- Prove2me | solution 1 for GlobalTheory.Published.latticeCurve_j_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:40:04.40586+00:00
-- url     : https://prove2.me/submissions/5c7b9c51-2281-4a33-b32a-8e0292133134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
import Theorems.Thm_GlobalTheory_Published_latticeCurve_j_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
namespace GlobalTheory.Published
theorem _root_.solution {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    (latticeCurve L).j = (latticeCurve L').j := by
  have hG : ∀ n, L.G n = L'.G n := by
    intro n
    unfold PeriodPair.G
    rw [h]
  rw [latticeCurve_j_eq, latticeCurve_j_eq]
  simp only [PeriodPair.g₂, PeriodPair.g₃, hG]
end GlobalTheory.Published
