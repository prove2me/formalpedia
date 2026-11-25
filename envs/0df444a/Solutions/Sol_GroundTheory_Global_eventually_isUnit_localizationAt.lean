-- Prove2me | solution 1 for GroundTheory.Global.eventually_isUnit_localizationAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:39.767086+00:00
-- url     : https://prove2.me/submissions/8e7fa421-0848-49c6-aecf-6ff6a046b265

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Theorems.Thm_GroundTheory_Global_eventually_mem_localizationAt
import Theorems.Thm_GroundTheory_Global_isUnit_of_mem_of_inv_mem

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
open NumberField IsDedekindDomain Polynomial
noncomputable section
variable (L : Type*) [Field L] [NumberField L]
variable {L}
namespace GroundTheory.Global
theorem _root_.solution {x : L} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ h : x ∈ localizationAt L v, IsUnit (⟨x, h⟩ : localizationAt L v) := by
  filter_upwards [eventually_mem_localizationAt x, eventually_mem_localizationAt x⁻¹] with v h h'
  exact ⟨h, isUnit_of_mem_of_inv_mem hx h h'⟩
end GroundTheory.Global
