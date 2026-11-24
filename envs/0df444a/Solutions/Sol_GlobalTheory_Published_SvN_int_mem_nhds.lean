-- Prove2me | solution 1 for GlobalTheory.Published.SvN.int_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:40:00.668388+00:00
-- url     : https://prove2.me/submissions/a503dfd9-e26a-4b75-bbf6-571f10789aa0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.Published.SvN
theorem _root_.solution : (𝒪[F] : Set F) ∈ 𝓝 (0 : F) :=
  (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.2 ⟨1, one_ne_zero, fun _ hx => le_of_lt (α := ValueGroupWithZero F) hx⟩
end GlobalTheory.Published.SvN
