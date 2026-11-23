-- Prove2me | solution 1 for GlobalTheory.PairingBound.ord_alg_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:42.215104+00:00
-- url     : https://prove2.me/submissions/a01d9aac-0103-4228-b088-6a6141105689

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBound

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
open GlobalTheory GlobalTheory.PairingBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]
namespace GlobalTheory.PairingBound
theorem _root_.solution (x : O) (hx : x ≠ 0) : 0 ≤ ord_vw O (algebraMap O K x) := by
  have hx' : algebraMap O K x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hx
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K x) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hx'
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K x) ≤ 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact HeightOneSpectrum.intValuation_le_one _ x
  unfold ord_vw
  rw [← WithZero.exp_log h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  linarith
end GlobalTheory.PairingBound
