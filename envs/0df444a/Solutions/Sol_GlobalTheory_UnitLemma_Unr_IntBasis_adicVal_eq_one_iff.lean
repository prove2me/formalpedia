-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.IntBasis.adicVal_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:47.777295+00:00
-- url     : https://prove2.me/submissions/4a2b2016-a4d0-483e-9f79-375517c4dee9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.IntBasis
open IsLocalRing
variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}
namespace GlobalTheory.UnitLemma.Unr.IntBasis
theorem _root_.solution (K : UQ) (a : K.O) : adicVal K (algebraMap K.O K.E a) = 1 ↔ IsUnit a := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  simp [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
end GlobalTheory.UnitLemma.Unr.IntBasis
