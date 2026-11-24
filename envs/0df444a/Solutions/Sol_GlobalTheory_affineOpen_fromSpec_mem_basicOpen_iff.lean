-- Prove2me | solution 1 for GlobalTheory.affineOpen_fromSpec_mem_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:10.201686+00:00
-- url     : https://prove2.me/submissions/9b6e3b1b-f326-4d28-bd67-41b74edb058a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceTensorOfPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenFibresPreirreducibleSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenNbhdSectionFibreIsPreirreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U)
    (c : Γ(Y, U)) (P : PrimeSpectrum Γ(Y, U)) : hU.fromSpec P ∈ Y.basicOpen c ↔ c ∉ P.asIdeal :=
  SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen c) P
end GlobalTheory
