-- Prove2me | solution 1 for GlobalTheory.Doubling.flatOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:53.542031+00:00
-- url     : https://prove2.me/submissions/af232ec6-69b7-491b-91a4-fc7dd91d6944

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
open scoped NNReal
open MeasureTheory
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A) (ν : Aˣ →* ℝ≥0) (K : Subgroup G)
variable {e mat ν K}
namespace GlobalTheory.Doubling
theorem _root_.solution (Φ : G → ℂ) (s₀ s : ℂ) (g : G) :
    flatOf e mat ν K Φ s₀ s g = Φ g * npow (hgtOf e mat ν K g) (s - s₀) := rfl
end GlobalTheory.Doubling
