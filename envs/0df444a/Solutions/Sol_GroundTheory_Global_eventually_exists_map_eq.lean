-- Prove2me | solution 1 for GroundTheory.Global.eventually_exists_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:38.627335+00:00
-- url     : https://prove2.me/submissions/a910ad7e-748e-47db-b84d-be6345afd6e4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
import Theorems.Thm_GroundTheory_Global_eventually_mem_localizationAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution (E : WeierstrassCurve L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L v),
        W.map (algebraMap (localizationAt L v) L) = E := by
  filter_upwards [eventually_mem_localizationAt E.a₁, eventually_mem_localizationAt E.a₂,
    eventually_mem_localizationAt E.a₃, eventually_mem_localizationAt E.a₄,
    eventually_mem_localizationAt E.a₆] with v h₁ h₂ h₃ h₄ h₆
  exact ⟨⟨⟨_, h₁⟩, ⟨_, h₂⟩, ⟨_, h₃⟩, ⟨_, h₄⟩, ⟨_, h₆⟩⟩, rfl⟩
end GroundTheory.Global
