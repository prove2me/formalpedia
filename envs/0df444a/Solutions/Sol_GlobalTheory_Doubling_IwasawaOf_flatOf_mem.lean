-- Prove2me | solution 1 for GlobalTheory.Doubling.IwasawaOf.flatOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:13.589831+00:00
-- url     : https://prove2.me/submissions/23ccfa6f-d6e4-46a3-9363-ec2b495605bd

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_isClosed_siegelOf
import Theorems.Thm_GlobalTheory_Doubling_continuous_aOf
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_flatSec_mem


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
    (hK : IsCompact (K : Set G)) {μ : Aˣ →* Circle} {s₀ : ℂ} {Φ : G → ℂ} (hΦ : Φ ∈ degPSOf e mat ν K μ s₀) (s : ℂ) :
    flatOf e mat ν K Φ s₀ s ∈ degPSOf e mat ν K μ s :=
  IsIwasawa.flatSec_mem h (isClosed_siegelOf hm) (hν.comp (continuous_aOf hm)) hK hΦ s
end IwasawaOf
end GlobalTheory.Doubling
