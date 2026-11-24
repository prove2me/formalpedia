-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.SplitPair.exists_int_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:24.792798+00:00
-- url     : https://prove2.me/submissions/ba76b1d7-052e-4c15-a71c-cbf92320714e

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeCharUnramifiedInverseSplitPair
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_ball_mem_nhds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler.SplitPair
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ b : 𝓞 E, Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap E P).mem_nhds (OrderUnits.ball_mem_nhds P 1 z)
  have hk' : Valued.v (algebraMap E (P.adicCompletion E) k - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hk
  have hval : ∀ x : E, Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x
  have h1 : P.valuation E k ≤ 1 := by
    have h2 : WithZero.exp (-((1 : ℕ) : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have := Valuation.map_add_le _ (hk'.trans h2) hz
    rwa [sub_add_cancel, hval] at this
  obtain ⟨b, hb⟩ := P.exists_valuation_sub_lt_of_integer h1 (Units.mk0 (WithZero.exp (-((1 : ℕ) : ℤ))) WithZero.exp_ne_zero)
  refine ⟨b, ?_⟩
  rw [← hval, map_sub] at hb
  have := Valuation.map_add_le _ hb.le hk'
  rw [sub_add_sub_cancel] at this
  exact this
end GlobalTheory.CMVal.Euler.SplitPair
