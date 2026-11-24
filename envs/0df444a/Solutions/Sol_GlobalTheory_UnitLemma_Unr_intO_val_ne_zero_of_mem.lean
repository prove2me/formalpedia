-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.intO_val_ne_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:46.413501+00:00
-- url     : https://prove2.me/submissions/fe8bd285-c7df-4c62-93c1-ec76c5da8bc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial IsLocalRing
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (K : UQ) (a : K.O) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal K.O) :
    val K.O (algebraMap K.O K.E a) ≠ 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) < 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 ha
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha0
  unfold val
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  omega
end GlobalTheory.UnitLemma.Unr
