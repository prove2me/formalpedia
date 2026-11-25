-- Prove2me | solution 1 for GlobalTheory.StepData.cosetInd_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:10.041979+00:00
-- url     : https://prove2.me/submissions/817d231a-1a6d-4367-81e3-efe66f76f330

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n n' : Type*}
variable [ValuativeRel k]
variable [Fintype n] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ε : k)
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k]
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.StepData
theorem _root_.solution (c : kˣ) (yb : (n → k) ⧸ box n c) : cosetInd (box n c) yb ∈ SB (n → k) := by
  have := t2Space k
  obtain ⟨y₀, rfl⟩ := Submodule.Quotient.mk_surjective _ yb
  have e : {y : n → k | Submodule.Quotient.mk (p := box n c) y = Submodule.Quotient.mk y₀} =
      (Homeomorph.subRight y₀) ⁻¹' (Set.pi Set.univ fun _ => cball c) := by
    ext y; simp [Submodule.Quotient.eq, mem_box, cball]
  have ho : IsOpen (Set.pi Set.univ fun _ : n => cball c) := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball c
  have hc : IsCompact (Set.pi Set.univ fun _ : n => cball c) := isCompact_univ_pi fun _ => isCompact_cball c
  have hc' := (Homeomorph.subRight y₀).isCompact_preimage.2 hc
  unfold cosetInd
  rw [e]
  exact ⟨(LocallyConstant.charFn ℂ ⟨hc'.isClosed, ho.preimage (Homeomorph.continuous _)⟩).isLocallyConstant,
    HasCompactSupport.intro hc' fun x hx => Set.indicator_of_notMem hx _⟩
end GlobalTheory.StepData
