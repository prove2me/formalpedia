-- Prove2me | solution 1 for GlobalTheory.Doubling.IwasawaOf.hgtOf_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:39:10.133129+00:00
-- url     : https://prove2.me/submissions/716624d0-8c13-49ef-a2b7-9f7fb5aae8df

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_iwAbs_mul


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
namespace IwasawaOf
theorem _root_.solution (h : IwasawaOf e mat ν K) (p : siegelOf e mat) {k : G} (hk : k ∈ K) :
    hgtOf e mat ν K (p * k) = ν (aOf e mat p) := IsIwasawa.iwAbs_mul h p hk
end IwasawaOf
end GlobalTheory.Doubling
