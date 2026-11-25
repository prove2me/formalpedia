-- Prove2me | solution 1 for GlobalTheory.T.isInertAt_of_unique_unramified_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:23.349164+00:00
-- url     : https://prove2.me/submissions/6faa5742-fe9a-4f83-97d0-280ccae25d82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsInertAtOfUniqueUnramifiedPrime
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsInertAtOfUniqueUnramifiedPrimeStatement
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SelfDualGenus_isInertAt_of_unique_unramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ (x : E)⁻¹ ∉ semiLoc v)) → (∃ x : 𝓞 (maximalRealSubfield E), ∃ y : 𝓞 E, (y : E) = algebraMap (maximalRealSubfield E) E (x : maximalRealSubfield E) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) → IsInertAt (maximalRealSubfield E) E v P := by
  first | exact @GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified | exact GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified | (intros; apply GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified <;> assumption)
end _root_.GlobalTheory.T
