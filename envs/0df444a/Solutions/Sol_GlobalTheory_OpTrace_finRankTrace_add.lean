-- Prove2me | solution 1 for GlobalTheory.OpTrace.finRankTrace_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:24.400926+00:00
-- url     : https://prove2.me/submissions/592d6fdf-dfc0-4057-8b39-a854d2a4de83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_finRankTrace_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.OpTrace
theorem _root_.solution (S T : V →ₗ[ℂ] V) [FiniteDimensional ℂ (LinearMap.range S)]
    [FiniteDimensional ℂ (LinearMap.range T)] :
    finRankTrace (S + T) = finRankTrace S + finRankTrace T := by
  have hS : ∀ x, S x ∈ LinearMap.range S ⊔ LinearMap.range T :=
    fun x => Submodule.mem_sup_left (LinearMap.mem_range_self S x)
  have hT : ∀ x, T x ∈ LinearMap.range S ⊔ LinearMap.range T :=
    fun x => Submodule.mem_sup_right (LinearMap.mem_range_self T x)
  rw [finRankTrace_eq S _ hS, finRankTrace_eq T _ hT,
    finRankTrace_eq (S + T) _ fun x => add_mem (hS x) (hT x), ← map_add]
  rfl
end GlobalTheory.OpTrace
