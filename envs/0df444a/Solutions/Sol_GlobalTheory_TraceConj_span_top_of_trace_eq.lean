-- Prove2me | solution 1 for GlobalTheory.TraceConj.span_top_of_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:17.361344+00:00
-- url     : https://prove2.me/submissions/9ddb5a25-16b1-4d14-ad2a-2c6eb956bf39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlIntertwinerOfResidualSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLinearMapOfTraceEq
import Theorems.Thm_GlobalTheory_TraceConj_ker_le_ker_of_trace_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceConj
open IsLocalRing
namespace GlobalTheory.TraceConj
theorem _root_.solution {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K) (h : ∀ g, (M g).trace = (N g).trace)
    (hN : Submodule.span K (Set.range N) = ⊤) : Submodule.span K (Set.range M) = ⊤ := by
  classical
  let a := Finsupp.linearCombination K (fun g => M g)
  let b := Finsupp.linearCombination K (fun g => N g)
  have hker : LinearMap.ker a ≤ LinearMap.ker b := ker_le_ker_of_trace_eq M N h hN
  have hb : LinearMap.range b = ⊤ := by rw [Finsupp.range_linearCombination]; exact hN
  let f : LinearMap.range a →ₗ[K] Matrix (Fin n) (Fin n) K :=
    ((LinearMap.ker a).liftQ b hker).comp a.quotKerEquivRange.symm.toLinearMap
  have hf : Function.Surjective f := by
    intro Y
    obtain ⟨c, rfl⟩ := LinearMap.range_eq_top.1 hb Y
    refine ⟨a.quotKerEquivRange (Submodule.Quotient.mk c), ?_⟩
    simp [f]
  have hle := LinearMap.finrank_le_finrank_of_surjective hf
  have := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hle)
  rwa [Finsupp.range_linearCombination] at this
end GlobalTheory.TraceConj
