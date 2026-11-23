-- Prove2me | solution 1 for GlobalTheory.WeilM.diag_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:46.690643+00:00
-- url     : https://prove2.me/submissions/bc774d88-185d-4895-b2fb-3512f68d60a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


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
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}
namespace GlobalTheory.WeilM
theorem _root_.solution [Fintype κ] {φ : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) :
    (fun x : κ → F => φ (Sum.elim x x)) ∈ SB (κ → F) := by
  have := SplitWeil.t2Space F
  have hc : Continuous fun x : κ → F => (Sum.elim x x : κ ⊕ κ → F) :=
    continuous_pi (by rintro (k | k) <;> exact continuous_apply k)
  have hc' : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  refine ⟨hφ.1.comp_continuous hc, HasCompactSupport.intro (hφ.2.image hc') fun x hx => ?_⟩
  by_contra h
  exact hx ⟨Sum.elim x x, subset_tsupport _ h, rfl⟩
end GlobalTheory.WeilM
