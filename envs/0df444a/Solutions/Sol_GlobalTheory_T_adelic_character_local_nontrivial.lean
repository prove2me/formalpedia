-- Prove2me | solution 1 for GlobalTheory.T.adelic_character_local_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:02:49.110831+00:00
-- url     : https://prove2.me/submissions/0329439e-77da-492d-8843-1587e20d8219

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_AdelicCharacterLocalNontrivial
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_char_nontrivial_at_every_place


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), Continuous (psiV F ψ v) ∧ ∃ y, psiV F ψ v y ≠ 1) ∧ Continuous (psiInf F ψ) ∧ ∀ (w : InfinitePlace F), ∃ x : Ainf F, (∀ w', w' ≠ w → x w' = 0) ∧ psiInf F ψ x ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place | exact GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place | (intros; apply GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place <;> assumption)
end _root_.GlobalTheory.T
