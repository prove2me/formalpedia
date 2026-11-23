-- Prove2me | solution 1 for GlobalTheory.exists_smul_eq_of_forall_dual_dvd_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:34.172188+00:00
-- url     : https://prove2.me/submissions/1a9faa55-9aa2-45d0-972b-79b34963d808

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution [Module.Projective A M] {a : A} {m : M}
    (h : ∀ φ : Module.Dual A M, a ∣ φ m) : ∃ m', a • m' = m := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
  choose c hc using fun i : M => h (Finsupp.lapply i ∘ₗ s)
  refine ⟨∑ i ∈ (s m).support, c i • i, ?_⟩
  conv_rhs => rw [← hs m, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← hc i]
  rfl
end GlobalTheory
