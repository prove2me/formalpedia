-- Prove2me | solution 1 for GlobalTheory.realLinear_eq_of_sub_mem_discrete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:19.391808+00:00
-- url     : https://prove2.me/submissions/7fa9ad20-a764-4e75-961c-fe40dd6f6168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_eventually_eq_zero_of_tendsto_of_mem_discrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {A : Type*} [AddCommGroup A]
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℝ M]
    {Γ : AddSubgroup F} (hΓ : IsDiscrete (Γ : Set F)) {L L' : M →ₗ[ℝ] F}
    (h : ∀ x, L x - L' x ∈ Γ) : L = L' := by
  ext x
  have ht : Tendsto (fun t : ℝ ↦ t • (L x - L' x)) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous fun t : ℝ ↦ t • (L x - L' x) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 := eventually_eq_zero_of_tendsto_of_mem_discrete hΓ ht
    (Eventually.of_forall fun t ↦ by simpa [smul_sub] using h (t • x))
  obtain ⟨t, ht0, ht⟩ := (h0.and self_mem_nhdsWithin).exists
  exact sub_eq_zero.1 ((smul_eq_zero.1 ht0).resolve_left ht)
end GlobalTheory
