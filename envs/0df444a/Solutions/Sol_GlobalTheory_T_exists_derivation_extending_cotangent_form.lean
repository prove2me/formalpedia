-- Prove2me | solution 1 for GlobalTheory.T.exists_derivation_extending_cotangent_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:21:14.078247+00:00
-- url     : https://prove2.me/submissions/a0831c74-7eda-471d-b214-4c446c699b5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationExtendingCotangentForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationExtendingCotangentFormStatement
import Theorems.Thm_GlobalTheory_ConormalDer_exists_derivation_extending


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by
  first | exact @GlobalTheory.ConormalDer.exists_derivation_extending | exact GlobalTheory.ConormalDer.exists_derivation_extending | (intros; apply GlobalTheory.ConormalDer.exists_derivation_extending <;> assumption)
end _root_.GlobalTheory.T
