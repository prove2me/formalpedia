-- Prove2me | solution 1 for GlobalTheory.Mem.natCast_pow_cpow_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:25.683674+00:00
-- url     : https://prove2.me/submissions/c7438130-cc25-42cb-9a81-4f9e9bf7f3f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay

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
open GlobalTheory GlobalTheory.Mem
namespace GlobalTheory.Mem
theorem _root_.solution (q k : ℕ) (z : ℂ) : ((q : ℂ) ^ k) ^ z = ((q : ℂ) ^ z) ^ k := by
  rw [← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
end GlobalTheory.Mem
