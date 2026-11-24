-- Prove2me | solution 1 for GlobalTheory.RadialIntegral.radial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:06:00.049879+00:00
-- url     : https://prove2.me/submissions/8f265550-c7e4-4e9f-b73e-74b6be3da310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralComplexInvPowAddNormSq
import Theorems.Thm_GlobalTheory_RadialIntegral_hasDerivAt_prim
import Theorems.Thm_GlobalTheory_RadialIntegral_tendsto_prim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.RadialIntegral
namespace GlobalTheory.RadialIntegral
theorem _root_.solution (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal ((a ^ (m + 1))⁻¹ / (2 * (m + 1))) := by
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((a + r ^ 2) ^ (m + 2))⁻¹ := fun r hr => by
    have : (0 : ℝ) < r := hr
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)), hval]
  simp
end GlobalTheory.RadialIntegral
