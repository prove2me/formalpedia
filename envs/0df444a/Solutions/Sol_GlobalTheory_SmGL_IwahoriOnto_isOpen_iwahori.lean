-- Prove2me | solution 1 for GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:16.748882+00:00
-- url     : https://prove2.me/submissions/32796dd3-c84d-4230-8a0c-5e0228f50276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IwahoriOnto
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
namespace GlobalTheory.SmGL.IwahoriOnto
theorem _root_.solution : IsOpen (iwahori k n : Set (GL n k)) := by
  have e : (iwahori k n : Set (GL n k)) = (KO k n : Set (GL n k)) ∩ ⋂ i, ⋂ j, ⋂ _ : j < i,
      (fun g : GL n k => g.val i j) ⁻¹' {x | valuation k x < 1} := by
    ext g; simp only [SetLike.mem_coe, mem_iwahori, Set.mem_inter_iff, Set.mem_iInter]; rfl
  rw [e]
  refine SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => IsOpen.preimage ?_ ?_)
  · exact Units.continuous_val.matrix_elem i j
  · simpa using (valuation k).isOpen_ball 1
end GlobalTheory.SmGL.IwahoriOnto
