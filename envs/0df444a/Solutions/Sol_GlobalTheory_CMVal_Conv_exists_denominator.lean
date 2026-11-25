-- Prove2me | solution 1 for GlobalTheory.CMVal.Conv.exists_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:27.172836+00:00
-- url     : https://prove2.me/submissions/23041e37-c496-4cdc-92b8-61b1cd5514bc

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntegersOfMemHatO
import Theorems.Thm_GlobalTheory_CMVal_Conv_mem_integers_of_mem_hatO
import Theorems.Thm_PI_AdCpctDenWork_exists_nat_adele


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
theorem _root_.solution (c : Ideal (OF E)) (y : (Af E)ˣ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ lattice c y, ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = n * x := by
  obtain ⟨n, hn, hy⟩ := PI.AdCpctDenWork.exists_nat_adele (y : Af E)
  refine ⟨n, hn, fun x hx => ?_⟩
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_
  have h1 := mul_mem (hy v) (mem_integers_of_mem_hatO hx v)
  have h2 : ((n : Af E) * (y : Af E)) * (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) = algebraMap E (Af E) (n * x) := by
    rw [map_mul, map_natCast]
    linear_combination ((n : Af E) * algebraMap E (Af E) x) * y.mul_inv
  have h3 : (algebraMap E (Af E) (n * x)) v ∈ v.adicCompletionIntegers E := by
    rw [← h2]; exact h1
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)
end GlobalTheory.CMVal.Conv
