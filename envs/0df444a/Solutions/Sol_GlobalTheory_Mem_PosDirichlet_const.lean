-- Prove2me | solution 1 for GlobalTheory.Mem.PosDirichlet.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:01.200805+00:00
-- url     : https://prove2.me/submissions/548a3c1e-2c23-4144-b34c-583b0b6cdb33

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
open GlobalTheory.Mem.PosDirichlet
namespace GlobalTheory.Mem.PosDirichlet
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) : PosDirichlet (fun _ => (c : ℂ)) :=
  ⟨Unit, fun _ => c, fun _ => 1, fun _ => hc, fun _ => one_ne_zero, fun s _ => by
    simpa using hasSum_unique (fun _ : Unit => (c : ℂ))⟩
end GlobalTheory.Mem.PosDirichlet
