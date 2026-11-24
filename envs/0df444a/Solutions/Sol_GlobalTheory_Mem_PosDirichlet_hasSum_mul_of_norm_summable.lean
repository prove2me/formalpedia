-- Prove2me | solution 1 for GlobalTheory.Mem.PosDirichlet.hasSum_mul_of_norm_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:15.750257+00:00
-- url     : https://prove2.me/submissions/5157f330-f517-422d-a394-44d10a78ed85

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
theorem _root_.solution {ι κ : Type} {f : ι → ℂ} {g : κ → ℂ} {a b : ℂ} (hf : HasSum f a)
    (hg : HasSum g b) : HasSum (fun p : ι × κ => f p.1 * g p.2) (a * b) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)
end GlobalTheory.Mem.PosDirichlet
