-- Prove2me | solution 1 for GlobalTheory.T.archimedean_fundamental_domain_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:02:47.45483+00:00
-- url     : https://prove2.me/submissions/3405285f-649d-4ef5-83b2-1ad5b83557af

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegers
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegersStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_exists_bounded_infDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ li : Measure (Ainf F), IsStdInf li → ∃ D K₀ : Set (Ainf F), MeasurableSet D ∧ IsCompact K₀ ∧ D ⊆ K₀ ∧ li D = 1 ∧ ∀ y : Ainf F, ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ D := by
  first | exact @GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain | exact GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain | (intros; apply GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain <;> assumption)
end _root_.GlobalTheory.T
