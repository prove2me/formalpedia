-- Prove2me | solution 1 for GlobalTheory.T.exists_cyclotomic_splitting_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:20:59.4852+00:00
-- url     : https://prove2.me/submissions/e34d7637-a624-4a5e-9b92-2cdd3e16f3ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCyclotomicSplittingExtension
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCyclotomicSplittingExtensionStatement
import Theorems.Thm_GlobalTheory_splitExt_intClosure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (f : Polynomial (FractionRing A)), f ≠ 0 → ∀ q : ℕ, q ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : Algebra A A') (σ : FractionRing A →+* FractionRing A'), Module.Finite A A' ∧ Function.Injective (algebraMap A A') ∧ IsIntegrallyClosed A' ∧ (∃ ζ : A', IsPrimitiveRoot ζ q) ∧ (f.map σ).Splits ∧ σ.comp (algebraMap A (FractionRing A)) = (algebraMap A' (FractionRing A')).comp (algebraMap A A') := by
  first | exact @GlobalTheory.splitExt_intClosure | exact GlobalTheory.splitExt_intClosure | (intros; apply GlobalTheory.splitExt_intClosure <;> assumption)
end _root_.GlobalTheory.T
