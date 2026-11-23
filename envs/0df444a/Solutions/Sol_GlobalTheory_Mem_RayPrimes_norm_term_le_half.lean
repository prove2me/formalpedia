-- Prove2me | solution 1 for GlobalTheory.Mem.RayPrimes.norm_term_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:21.336011+00:00
-- url     : https://prove2.me/submissions/bd883345-13e1-40f5-b557-ec261e0bfc6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_norm_term_le_inv

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
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn v
  refine (norm_term_le_inv n hn a ha v hs).trans ?_
  rw [one_div]; gcongr
end GlobalTheory.Mem.RayPrimes
