-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.IntBasis.adicVal_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:43.882804+00:00
-- url     : https://prove2.me/submissions/d63dad54-bbf1-41b8-92f3-2c871a2cf6da

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
theorem _root_.solution (K : UQ) (x : K.E) : adicVal K x ≤ 1 ↔ ∃ a : K.O, algebraMap K.O K.E a = x :=
  ⟨IsDiscreteValuationRing.exists_lift_of_le_one, by
    rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩
end GlobalTheory.UnitLemma.Unr.IntBasis
