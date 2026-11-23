-- Prove2me | solution 1 for GlobalTheory.PairingBound.ord_l_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:42.904806+00:00
-- url     : https://prove2.me/submissions/711d8b2d-11ea-4105-9d8f-dd6f5db8680f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBound
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.PairingBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]
namespace GlobalTheory.PairingBound
theorem _root_.solution (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) : 0 < ord_vw O (l : K) := by
  have h0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap O K)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (Nat.cast_ne_zero.2 hl)
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) < 1 := by
    rw [← map_natCast (algebraMap O K), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) ≠ 0 := by simpa using h0
  unfold ord_vw
  rw [← WithZero.exp_log h2, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  linarith
end GlobalTheory.PairingBound
