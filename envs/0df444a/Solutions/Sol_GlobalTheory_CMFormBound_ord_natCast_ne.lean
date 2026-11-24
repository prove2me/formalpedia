-- Prove2me | solution 1 for GlobalTheory.CMFormBound.ord_natCast_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:03:58.948804+00:00
-- url     : https://prove2.me/submissions/336dbdbd-1bef-4626-9bef-1a988d8494e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
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
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]
namespace GlobalTheory.CMFormBound
theorem _root_.solution [CharZero O] (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) : ord_vw O (l : K) ≠ 0 := by
  have h0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap O K)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (Nat.cast_ne_zero.2 hl)
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) < 1 := by
    rw [← map_natCast (algebraMap O K), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) ≠ 0 := by simpa using h0
  unfold ord_vw
  intro h4
  have := WithZero.exp_log h2
  rw [neg_eq_zero.1 h4, WithZero.exp_zero] at this
  exact h1.ne this.symm
end GlobalTheory.CMFormBound
