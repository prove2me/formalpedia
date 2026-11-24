-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.exists_nsmul_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:45:06.585857+00:00
-- url     : https://prove2.me/submissions/fbb02f1c-1d80-414d-8730-e02e61b2df82

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_algebraMap_eq_pairA
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_ker_mem_nhds
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_exists_nsmul_adele


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ N : ℕ, 0 < N ∧ ∀ r : 𝓞 F, ψ (pairA F (algebraMap F _ ((N : F) * r)) 0) = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (ker_mem_nhds hψ.1 hψ.2.1)
  refine ⟨N, hN, fun r => ?_⟩
  have h1 : ψ (pairA F 0 (N • algebraMap F (Af F) r)) = 1 :=
    h _ fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v r
  have h2 := hψ.2.2.1 ((N : F) * r)
  rw [nsmul_eq_mul, ← map_natCast (algebraMap F (Af F)), ← map_mul] at h1
  rwa [algebraMap_eq_pairA, AddChar.map_add_eq_mul, h1, mul_one] at h2
end GlobalTheory.CompanionTheory.AdeleCharLocal
