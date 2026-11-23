-- Prove2me | solution 1 for GlobalTheory.WeilM.nonarch_field
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:14.007527+00:00
-- url     : https://prove2.me/submissions/985ee306-3f37-4ae1-81c9-b63e9f70a5af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormPowTwoPowSubOneGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise
open GlobalTheory GlobalTheory.WeilM
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.WeilM
theorem _root_.solution : NonarchimedeanAddGroup F where
  is_nonarchimedean U hU := by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hU
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩, SplitWeil.neg_mem_cball⟩,
      SplitWeil.isOpen_cball s⟩, hs⟩
end GlobalTheory.WeilM
