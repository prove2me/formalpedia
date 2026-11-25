-- Prove2me | solution 1 for GroundTheory.Global.eventually_exists_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:52.386669+00:00
-- url     : https://prove2.me/submissions/ac3c0225-b6ad-45c0-b494-f27a8d888280

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
import Theorems.Thm_GroundTheory_Global_eventually_exists_map_eq
import Theorems.Thm_GroundTheory_Global_isElliptic_of_map_eq
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
theorem _root_.solution (E : WeierstrassCurve L) [E.IsElliptic] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L v),
        W.IsElliptic ∧ W.map (algebraMap (localizationAt L v) L) = E := by
  filter_upwards [eventually_exists_map_eq E, eventually_mem_localizationAt E.Δ⁻¹] with v ⟨W, h⟩ hΔ
  exact ⟨W, isElliptic_of_map_eq h hΔ, h⟩
end GroundTheory.Global
