-- Prove2me | solution 1 for GlobalTheory.Proof.TwistSupportPeriodicLevels.intM_of_parPhi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:39.070723+00:00
-- url     : https://prove2.me/submissions/1a8fc1e7-7ed1-4709-b12c-a131d6cecca0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Theorems.Thm_GlobalTheory_StepData_MaxM_intM
import Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_intM_of_mem_KO
import Theorems.Thm_GlobalTheory_StepData_parPhi_ne_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.TwistSupportPeriodicLevels
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r s s' : Type} [Fintype r] [DecidableEq r]
namespace GlobalTheory.Proof.TwistSupportPeriodicLevels
theorem _root_.solution (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} (hx : parPhi δ x ≠ 0) : IntM x := by
  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  rw [← Matrix.fromBlocks_toBlocks x, intM_fromBlocks]
  refine ⟨?_, h12, h21.intM, h22⟩
  rw [← e]
  exact intM_of_mem_KO hg
end GlobalTheory.Proof.TwistSupportPeriodicLevels
