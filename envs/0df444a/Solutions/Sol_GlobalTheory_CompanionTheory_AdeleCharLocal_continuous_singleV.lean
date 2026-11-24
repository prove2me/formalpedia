-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.continuous_singleV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:26:45.990784+00:00
-- url     : https://prove2.me/submissions/05166432-fcee-4418-9236-cea9f7a65177

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]
open Classical
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf
end GlobalTheory.CompanionTheory.AdeleCharLocal
