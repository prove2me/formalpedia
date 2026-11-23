-- Prove2me | solution 1 for GlobalTheory.Mem.RayPrimes.summable_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:58.116529+00:00
-- url     : https://prove2.me/submissions/b4485baf-99b3-4579-be2b-40e51edc61c4

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
theorem _root_.solution (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) {s : ℝ} (h : 1 < s) :
    Summable fun v => a v * (n v : ℂ) ^ (-(s : ℂ)) :=
  Summable.of_norm_bounded (hs s h) fun v => norm_term_le n hn a ha v le_rfl
end GlobalTheory.Mem.RayPrimes
