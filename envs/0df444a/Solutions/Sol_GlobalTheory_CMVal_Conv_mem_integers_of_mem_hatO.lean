-- Prove2me | solution 1 for GlobalTheory.CMVal.Conv.mem_integers_of_mem_hatO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:02.72926+00:00
-- url     : https://prove2.me/submissions/7bf0cf1a-cef3-463b-babf-4d76ee857f3b

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntegersOfMemHatO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Conv
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Conv
theorem _root_.solution {c : Ideal (OF E)} {y : Af E} (hy : y ∈ hatO c) (v : HeightOneSpectrum (𝓞 E)) :
    y v ∈ v.adicCompletionIntegers E := by
  have hc : IsClosed {y : Af E | y v ∈ v.adicCompletionIntegers E} :=
    (Valued.isClosed_valuationSubring (v.adicCompletion E)).preimage (RestrictedProduct.continuous_eval v)
  refine closure_minimal (t := {y : Af E | y v ∈ v.adicCompletionIntegers E}) ?_ hc hy
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  have : algebraMap (OF E) E a + algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by
    rw [map_add]; rfl
  rw [this]
  refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one _)
end GlobalTheory.CMVal.Conv
