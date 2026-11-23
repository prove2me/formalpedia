-- Prove2me | solution 1 for GlobalTheory.CharForm.cosetInd_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:45.511472+00:00
-- url     : https://prove2.me/submissions/44ad9ae7-28f5-4122-90b0-eb90c153ed7d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEqMulApplyZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
noncomputable section
open scoped Classical Topology
open GlobalTheory GlobalTheory.CharForm
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
namespace GlobalTheory.CharForm
theorem _root_.solution (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X)) (q : X ⧸ U) :
    cosetInd U q ∈ SB X := by
  haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo
  refine ⟨?_, ?_⟩
  · exact (IsLocallyConstant.of_discrete (fun q' : X ⧸ U => if q' = q then (1 : ℂ) else 0)).comp_continuous
      QuotientAddGroup.continuous_mk
  · have hK : IsCompact ((fun u => q.out + u) '' (U : Set X)) := hUc.image (continuous_const.add continuous_id)
    have hKc : IsClosed ((fun u => q.out + u) '' (U : Set X)) :=
      (Homeomorph.addLeft q.out).isClosedMap _ (AddSubgroup.isClosed_of_isOpen U hUo)
    refine HasCompactSupport.intro' hK hKc fun x hx => ?_
    simp only [cosetInd, ite_eq_right_iff, one_ne_zero, imp_false]
    intro hxq
    apply hx
    refine ⟨-q.out + x, ?_, by simp⟩
    rw [← QuotientAddGroup.out_eq' q] at hxq
    exact QuotientAddGroup.eq.mp hxq.symm
end GlobalTheory.CharForm
