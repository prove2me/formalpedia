-- Prove2me | solution 1 for GlobalTheory.Mem.RayPrimes.norm_term_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:18.757264+00:00
-- url     : https://prove2.me/submissions/e6ed072e-a2a6-493d-a04e-ee8ce5d65ca6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_norm_term_le

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
theorem _root_.solution (v : ι) {s : ℝ} (hs : 1 ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ)⁻¹ := by
  have := norm_term_le n hn a ha v hs
  rwa [Real.rpow_neg_one] at this
end GlobalTheory.Mem.RayPrimes
