-- Prove2me | solution 1 for GlobalTheory.existsUnique_realLinear_lift_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:36.136892+00:00
-- url     : https://prove2.me/submissions/38be2915-bc04-4c66-9732-5a96f34d6f1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_existsUnique_realLinear_of_eventually_add_mod_discrete
import Theorems.Thm_GlobalTheory_realLinear_eq_of_sub_mem_discrete
import Theorems.Thm_GlobalTheory_addMonoidHom_eq_of_eventuallyEq


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
theorem _root_.solution {ex : E →+ A} {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) {g : E → F} (hc : ContinuousAt g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) :
    ∃! L : E →L[ℝ] F, ∀ z, ex' (L z) = ex z := by
  have h0 : ex' (g 0) = 0 := by simpa using hg.self_of_nhds
  have hadd : Tendsto (fun p : E × E ↦ p.1 + p.2) (𝓝 0) (𝓝 0) := by
    simpa using continuous_add.tendsto (0 : E × E)
  obtain ⟨L, hL, -⟩ := existsUnique_realLinear_of_eventually_add_mod_discrete hker
    (g := fun z ↦ g z - g 0) (hc.sub continuousAt_const) (sub_self _) <| by
      filter_upwards [hadd.eventually hg, (continuous_fst.tendsto (0 : E × E)).eventually hg,
        (continuous_snd.tendsto (0 : E × E)).eventually hg] with p h1 h2 h3
      simp [AddMonoidHom.mem_ker, h0, h1, h2, h3]
  have hL' : ex'.comp (L : E →+ F) = ex := addMonoidHom_eq_of_eventuallyEq <| by
    filter_upwards [hL, hg] with z h1 h2
    change ex' (L z) = ex z
    rw [← h1, map_sub, h0, h2, sub_zero]
  have hL'' : ∀ z, ex' (L z) = ex z := fun z ↦ DFunLike.congr_fun hL' z
  refine ⟨L, hL'', fun L' h' ↦ ContinuousLinearMap.coe_injective ?_⟩
  exact realLinear_eq_of_sub_mem_discrete hker fun x ↦ by
    simp [AddMonoidHom.mem_ker, h', hL'']
end GlobalTheory
