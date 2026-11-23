-- Prove2me | solution 1 for GlobalTheory.Tw.measurable_comp_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:35.932504+00:00
-- url     : https://prove2.me/submissions/5ceee015-b98f-4a94-ba4d-26b66dd057e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
import Theorems.Thm_GlobalTheory_Tw_apply_out_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {G : Type} [Group G] [MeasurableSpace G]
namespace GlobalTheory.Tw
theorem _root_.solution {T : Subgroup G} {α : Type} [MeasurableSpace α] {F : G → α} (hm : Measurable F)
    (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : Measurable fun c : RCoset T => F (Quotient.out c) := by
  refine measurable_from_quotient.2 ?_
  have : (fun c : RCoset T => F (Quotient.out c)) ∘ Quotient.mk'' = F := funext (apply_out_mk hF)
  rwa [this]
end GlobalTheory.Tw
