-- Prove2me | solution 1 for GlobalTheory.Mem.PosDirichlet.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:32:45.259108+00:00
-- url     : https://prove2.me/submissions/25e625de-ff55-4bd8-91d5-5a2aea615289

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_const
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_mul

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
open GlobalTheory.Mem.PosDirichlet
namespace GlobalTheory.Mem.PosDirichlet
theorem _root_.solution {F : ℂ → ℂ} (hF : PosDirichlet F) (j : ℕ) : PosDirichlet (fun s => F s ^ j) := by
  induction j with
  | zero => simpa using const zero_le_one
  | succ j ih => simpa only [pow_succ] using ih.mul hF
end GlobalTheory.Mem.PosDirichlet
