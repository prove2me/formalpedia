-- Prove2me | solution 1 for GlobalTheory.absOpInt_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:01.012082+00:00
-- url     : https://prove2.me/submissions/c27afd26-53ed-4530-b215-9e450fa11e41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AbsOpIntIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {Hp : Type} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hc : ∀ x, Continuous fun g => π g x) (φ : G → ℂ) (hφ : Integrable φ μ) (y : Hp) :
    Integrable (fun g => φ g • π g y) μ := by
  refine Integrable.mono' (hφ.norm.mul_const ‖y‖) ?_ (ae_of_all _ fun g => ?_)
  · exact hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable
  · rw [norm_smul, hn]
end GlobalTheory
