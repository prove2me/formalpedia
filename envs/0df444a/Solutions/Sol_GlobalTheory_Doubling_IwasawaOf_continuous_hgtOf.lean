-- Prove2me | solution 1 for GlobalTheory.Doubling.IwasawaOf.continuous_hgtOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:06:26.192801+00:00
-- url     : https://prove2.me/submissions/e227a58f-ed12-40d1-924f-d0f093cda2b4

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_isClosed_siegelOf
import Theorems.Thm_GlobalTheory_Doubling_continuous_aOf
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_continuous_iwAbs


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
namespace GlobalTheory.Doubling
namespace IwasawaOf
theorem _root_.solution (h : IwasawaOf e mat ν K) (hm : Continuous mat) (hν : Continuous ν)
    (hK : IsCompact (K : Set G)) : Continuous (hgtOf e mat ν K) :=
  IsIwasawa.continuous_iwAbs h (isClosed_siegelOf hm) (hν.comp (continuous_aOf hm)) hK
end IwasawaOf
end GlobalTheory.Doubling
