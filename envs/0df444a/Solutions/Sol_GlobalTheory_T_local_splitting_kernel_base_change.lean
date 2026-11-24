-- Prove2me | solution 1 for GlobalTheory.T.local_splitting_kernel_base_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:18:21.984734+00:00
-- url     : https://prove2.me/submissions/034386ac-2342-474c-b14a-eedfc5730f44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalSplittingKernelBaseChange
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalSplittingKernelBaseChangeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RegularLocal_regular_of_regular_at_maximal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P), (∀ (p : Ideal R) [p.IsMaximal], ∃ r : Localization.AtPrime p ⊗[R] P →ₗ[Localization.AtPrime p] Localization.AtPrime p ⊗[R] Q, d.baseChange (Localization.AtPrime p) ∘ₗ r ∘ₗ d.baseChange (Localization.AtPrime p) = d.baseChange (Localization.AtPrime p)) → ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by
  first | exact @GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal | exact GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal | (intros; apply GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal <;> assumption)
end _root_.GlobalTheory.T
