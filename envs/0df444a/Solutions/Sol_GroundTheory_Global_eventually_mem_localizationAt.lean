-- Prove2me | solution 1 for GroundTheory.Global.eventually_mem_localizationAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:16:31.206918+00:00
-- url     : https://prove2.me/submissions/d8c8a743-b660-48c7-8bbd-a96a4bf5fe06

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Theorems.Thm_GroundTheory_Global_mem_localizationAt_iff
import Theorems.Thm_GroundTheory_Global_finite_setOf_mem_asIdeal

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
theorem _root_.solution (x : L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, x ∈ localizationAt L v := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  refine Filter.eventually_cofinite.mpr
    ((finite_setOf_mem_asIdeal (nonZeroDivisors.ne_zero hb)).subset fun v hv => ?_)
  by_contra h
  exact hv (mem_localizationAt_iff.mpr ⟨a, b, h, div_eq_mul_inv _ _⟩)
end GroundTheory.Global
