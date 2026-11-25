-- Prove2me | solution 1 for GlobalTheory.Doubling.iwasawaOf_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:42:13.068808+00:00
-- url     : https://prove2.me/submissions/77251509-6905-44cf-8e86-a94840fc4a20

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_isClosed_siegelOf
import Theorems.Thm_GlobalTheory_Doubling_continuous_aOf
import Theorems.Thm_GlobalTheory_Doubling_isIwasawa_of_isCompact


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
variable [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [TopologicalSpace G] [IsTopologicalGroup G]
omit [IsTopologicalGroup G]
namespace GlobalTheory.Doubling
theorem _root_.solution (hm : Continuous mat) (hν : Continuous ν) (hK : IsCompact (K : Set G))
    (h : ∀ g : G, ∃ p : siegelOf e mat, ∃ k ∈ K, g = p * k) : IwasawaOf e mat ν K :=
  isIwasawa_of_isCompact (isClosed_siegelOf hm) (hν.comp (continuous_aOf hm)) hK h
end GlobalTheory.Doubling
