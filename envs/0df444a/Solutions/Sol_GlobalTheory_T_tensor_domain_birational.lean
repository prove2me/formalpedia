-- Prove2me | solution 1 for GlobalTheory.T.tensor_domain_birational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:07:22.307891+00:00
-- url     : https://prove2.me/submissions/c11fc541-b5b4-4af7-86a4-3e3663ca79d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorDomainBirational
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TensorDomainBirationalStatement
import Theorems.Thm_GlobalTheory_flat_baseChange_birational_isDomain_and_includeRight_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B R : Type) [CommRing A] [CommRing B] [IsDomain B] [CommRing R] [IsDomain R] [Algebra A B] [Algebra A R] [Module.Flat A R], Function.Injective (algebraMap A B) → (∀ b : B, ∃ a s : A, algebraMap A B s ≠ 0 ∧ algebraMap A B s * b = algebraMap A B a) → IsDomain (TensorProduct A B R) ∧ Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by
  first | exact @GlobalTheory.flat_baseChange_birational_isDomain_and_includeRight_injective | exact GlobalTheory.flat_baseChange_birational_isDomain_and_includeRight_injective | (intros; apply GlobalTheory.flat_baseChange_birational_isDomain_and_includeRight_injective <;> assumption)
end _root_.GlobalTheory.T
