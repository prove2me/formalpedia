-- Prove2me | solution 1 for GlobalTheory.T.finiteType_invariants_finite_group_and_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:22:00.950422+00:00
-- url     : https://prove2.me/submissions/986bf3d0-4b34-4c84-aba6-2bebd3a5f088

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteTypeInvariantsFiniteGroupAndFinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteTypeInvariantsFiniteGroupAndFiniteStatement
import Theorems.Thm_GlobalTheory_finiteType_invariants_and_finite


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C'] (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C'), (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' := by
  first | exact @GlobalTheory.finiteType_invariants_and_finite | exact GlobalTheory.finiteType_invariants_and_finite | (intros; apply GlobalTheory.finiteType_invariants_and_finite <;> assumption)
end _root_.GlobalTheory.T
