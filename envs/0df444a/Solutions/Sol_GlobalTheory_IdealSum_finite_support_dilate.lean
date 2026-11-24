-- Prove2me | solution 1 for GlobalTheory.IdealSum.finite_support_dilate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:37:16.765613+00:00
-- url     : https://prove2.me/submissions/05e6c097-235e-48b4-b24f-798d30cca978

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LatticeSumDilateHaarAsymptoticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealSumPeriodicDilate
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.IdealSum
namespace GlobalTheory.IdealSum
theorem _root_.solution (K : Type) [Field K] [NumberField K] (f : mixedSpace K → ℂ)
    (hf : HasCompactSupport f) (t : ℝ) (ht : 0 < t) :
    {α : 𝓞 K | f (t • mixedEmbedding K (α : K)) ≠ 0}.Finite := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : mixedSpace K)).1
    hf.isCompact.isBounded
  let I := FractionalIdeal.mk0 K (1 : (Ideal (𝓞 K))⁰)
  have hd : DiscreteTopology (idealLattice K I).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (idealLattice K I))
  have hfin : (Metric.closedBall (0 : mixedSpace K) (r / t) ∩
      (idealLattice K I : Set (mixedSpace K))).Finite :=
    Metric.finite_isBounded_inter_isClosed
      (isDiscrete_iff_discreteTopology.2 hd)
      Metric.isBounded_closedBall
      (AddSubgroup.isClosed_of_discrete (H := (idealLattice K I).toAddSubgroup))
  have hinj : Function.Injective fun α : 𝓞 K => mixedEmbedding K (α : K) :=
    (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective
  refine (hfin.preimage hinj.injOn).subset fun α hα => ⟨?_, ?_⟩
  · have := hr (subset_tsupport f hα)
    rw [mem_closedBall_zero_iff, _root_.norm_smul, Real.norm_of_nonneg ht.le] at this
    rw [mem_closedBall_zero_iff, le_div_iff₀ ht, mul_comm]
    exact this
  · refine (mem_idealLattice K I).2 ⟨(α : K), ?_, rfl⟩
    simp [I]
end GlobalTheory.IdealSum
