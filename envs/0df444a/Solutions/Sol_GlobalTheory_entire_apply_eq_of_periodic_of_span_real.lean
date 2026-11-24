-- Prove2me | solution 1 for GlobalTheory.entire_apply_eq_of_periodic_of_span_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:22.324028+00:00
-- url     : https://prove2.me/submissions/bcd05e7a-fde4-4ba2-8cff-31fb024e6412

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_isZLattice_periodic
import Theorems.Thm_GlobalTheory_periodic_of_mem_span_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Nat
open GlobalTheory
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) {S : Set E} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) (z w : E) : F z = F w := by
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent ℝ S
  let b : Module.Basis t ℝ E := Module.Basis.mk hli (by simp [hspan, hS])
  haveI : Finite t := Module.Finite.finite_basis b
  refine entire_apply_eq_of_isZLattice_periodic hF (Submodule.span ℤ (range b))
    (periodic_of_mem_span_int ?_) z w
  rintro x _ ⟨i, rfl⟩
  exact hper x _ (by simpa [b] using htS i.2)
end GlobalTheory
