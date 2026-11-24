-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:38:45.45572+00:00
-- url     : https://prove2.me/submissions/972a18d3-b968-474b-9de5-b80ef1d201ee

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_inf
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_continuous_singleV
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_fin

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
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), Continuous (psiV F ψ v) ∧ ∃ y, psiV F ψ v y ≠ 1) ∧ Continuous (psiInf F ψ) ∧ ∀ (w : InfinitePlace F), ∃ x : Ainf F, (∀ w', w' ≠ w → x w' = 0) ∧ psiInf F ψ x ≠ 1 := by
  intro F _ _ ψ hψ
  exact ⟨fun v => ⟨hψ.1.comp (continuous_const.prodMk (continuous_singleV v)), exists_fin hψ v⟩,
    hψ.1.comp (continuous_id.prodMk continuous_const), fun w => exists_inf hψ w⟩
end GlobalTheory.CompanionTheory.AdeleCharLocal
