-- Prove2me | solution 1 for GlobalTheory.Published.IsIntegersLattice.j_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:19.234531+00:00
-- url     : https://prove2.me/submissions/b6534256-cadd-4a74-a703-055bbcceadfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
import Theorems.Thm_GlobalTheory_Published_latticeCurve_j_congr

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
namespace IsIntegersLattice
theorem _root_.solution {p : ℕ} {L L' : PeriodPair} (h : IsIntegersLattice p L)
    (h' : IsIntegersLattice p L') : (latticeCurve L).j = (latticeCurve L').j := by
  apply latticeCurve_j_congr
  ext z
  rw [h z, h' z]
end IsIntegersLattice
end GlobalTheory.Published
