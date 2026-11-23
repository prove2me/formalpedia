-- Prove2me | solution 1 for GlobalTheory.existsUnique_realLinear_of_eventually_add_mod_discrete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:42.861802+00:00
-- url     : https://prove2.me/submissions/0e008dae-a2ea-49d0-a29e-0a4f6a3ff96f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Theorems.Thm_GlobalTheory_eventually_eq_zero_of_tendsto_of_mem_discrete
import Theorems.Thm_GlobalTheory_addMonoidHom_eq_of_eventuallyEq
import Theorems.Thm_GlobalTheory_exists_addMonoidHom_eventuallyEq


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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory
theorem _root_.solution {Γ : AddSubgroup F}
    (hΓ : IsDiscrete (Γ : Set F)) {g : E → F} (hc : ContinuousAt g 0) (h0 : g 0 = 0)
    (hg : ∀ᶠ p : E × E in 𝓝 0, g (p.1 + p.2) - g p.1 - g p.2 ∈ Γ) :
    ∃! L : E →L[ℝ] F, g =ᶠ[𝓝 0] L := by
  have ht : Tendsto g (𝓝 0) (𝓝 0) := by simpa [h0] using hc.tendsto
  have hadd : Tendsto (fun p : E × E ↦ p.1 + p.2) (𝓝 0) (𝓝 0) := by
    simpa using continuous_add.tendsto (0 : E × E)
  have h1 : Tendsto (fun p : E × E ↦ g (p.1 + p.2) - g p.1 - g p.2) (𝓝 0) (𝓝 0) := by
    simpa using ((ht.comp hadd).sub (ht.comp (continuous_fst.tendsto (0 : E × E)))).sub
      (ht.comp (continuous_snd.tendsto (0 : E × E)))
  obtain ⟨G, hG⟩ := exists_addMonoidHom_eventuallyEq (g := g) <| by
    filter_upwards [eventually_eq_zero_of_tendsto_of_mem_discrete hΓ h1 hg] with p hp
    rw [sub_sub, sub_eq_zero] at hp
    exact hp
  replace hG := hG.symm
  have hGc : Continuous G := continuous_of_continuousAt_zero G (hc.congr hG)
  refine ⟨G.toRealLinearMap hGc, hG, fun L hL ↦ ?_⟩
  have : (L : E →+ F) = G := addMonoidHom_eq_of_eventuallyEq (hL.symm.trans hG)
  ext x
  exact DFunLike.congr_fun this x
end GlobalTheory
