-- Prove2me | solution 1 for GlobalTheory.Mem.RayPrimes.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:51.181234+00:00
-- url     : https://prove2.me/submissions/7ad11f2c-2f9e-42cd-a68f-b98fdd9ffe92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayPrimes
variable {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (a : ι → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
include hn ha
namespace GlobalTheory.Mem.RayPrimes
theorem _root_.solution (v : ι) {s t : ℝ} (hst : t ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ) ^ (-t) := by
  have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn v
  rw [norm_mul, norm_natCast_cpow_of_pos (by linarith [hn v])]
  simp only [neg_re, ofReal_re]
  calc ‖a v‖ * (n v : ℝ) ^ (-s) ≤ 1 * (n v : ℝ) ^ (-t) := by
        gcongr
        · exact ha v
        · linarith
    _ = _ := one_mul _
end GlobalTheory.Mem.RayPrimes
