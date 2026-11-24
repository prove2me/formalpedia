-- Prove2me | solution 1 for GlobalTheory.T.exists_injective_norm_le_one_of_finite_padicInt_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:06.766657+00:00
-- url     : https://prove2.me/submissions/1dce1a92-aa8d-442e-89d6-f4f8e753ca68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOneOfFinitePadicIntDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOneOfFinitePadicIntDomainStatement
import Theorems.Thm_GlobalTheory_PadicEmb_exists_embedding


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
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D], (p : D) ≠ 0 → ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d, ‖φ d‖ ≤ 1 := by
  first | exact @GlobalTheory.PadicEmb.exists_embedding | exact GlobalTheory.PadicEmb.exists_embedding | (intros; apply GlobalTheory.PadicEmb.exists_embedding <;> assumption)
end _root_.GlobalTheory.T
