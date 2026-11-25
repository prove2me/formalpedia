-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.orthonormal_avgVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:11:47.929101+00:00
-- url     : https://prove2.me/submissions/053e61a2-4218-4ae5-a402-bcd3f80df83c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_measureReal_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal
noncomputable section
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open GroundTheory.Automorphic.MeasurablePartition
variable (p : MeasurablePartition X)
namespace GroundTheory.Automorphic.MeasurablePartition
theorem _root_.solution : Orthonormal ℂ (p.avgVec μ) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [avgVec, avgVec, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    L2.inner_indicatorConstLp_indicatorConstLp]
  split_ifs with h
  · subst h
    have hm := measureReal_pos i
    rw [Set.inter_self]
    simp only [inner_self_eq_norm_sq_to_K, norm_one, one_pow, RCLike.ofReal_one, mul_one,
      Complex.real_smul]
    have hr : (Real.sqrt (μ.real (p.E i)))⁻¹ * ((Real.sqrt (μ.real (p.E i)))⁻¹ *
        μ.real (p.E i)) = 1 := by
      rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hm.le, inv_mul_cancel₀ hm.ne']
    exact_mod_cast hr
  · have hij : (i : ℕ) ≠ j := fun h' => h (Subtype.ext h')
    rw [(p.disjoint hij).inter_eq]
    simp
end GroundTheory.Automorphic.MeasurablePartition
