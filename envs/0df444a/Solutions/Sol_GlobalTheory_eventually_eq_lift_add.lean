-- Prove2me | solution 1 for GlobalTheory.eventually_eq_lift_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:37:59.091614+00:00
-- url     : https://prove2.me/submissions/5dee9b59-e94f-4d7b-bb16-324de0c98fc7

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
theorem _root_.solution {ex : E →+ A} {ex' : F →+ A}
    (hker : IsDiscrete (ex'.ker : Set F)) {g : E → F} (hc : ContinuousAt g 0)
    (hg : ∀ᶠ z in 𝓝 0, ex' (g z) = ex z) {L : E →L[ℝ] F} (hL : ∀ z, ex' (L z) = ex z) :
    ∀ᶠ z in 𝓝 0, g z = L z + g 0 := by
  have h0 : ex' (g 0) = 0 := by simpa using hg.self_of_nhds
  have ht : Tendsto (fun z ↦ g z - (L z + g 0)) (𝓝 0) (𝓝 0) := by
    simpa using hc.tendsto.sub ((L.continuous.tendsto 0).add_const (g 0))
  have := eventually_eq_zero_of_tendsto_of_mem_discrete hker ht <| by
    filter_upwards [hg] with z hz
    simp [AddMonoidHom.mem_ker, hz, hL, h0]
  filter_upwards [this] with z hz using sub_eq_zero.1 hz
end GlobalTheory
