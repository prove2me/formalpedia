-- Prove2me | solution 1 for GlobalTheory.T.finite_image_of_trivial_on_inf_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:22.567804+00:00
-- url     : https://prove2.me/submissions/fa6a52b0-46e1-4d1c-9b5b-d4473782b4bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImageFiniteOfTrivialOnInfFiniteIndex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImageFiniteOfTrivialOnInfFiniteIndexStatement
import Theorems.Thm_GlobalTheory_image_finite_of_trivial_on_inf_finiteIndex


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
theorem _root_.solution : ∀ (G Q : Type) [Group G] [Group Q] (ρ : G →* Q) (J H : Subgroup G), H.FiniteIndex → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set G)).Finite := by
  first | exact @GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex | exact GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex | (intros; apply GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex <;> assumption)
end _root_.GlobalTheory.T
