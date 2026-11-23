-- Prove2me | solution 1 for GlobalTheory.NormIntegers.isPrincipal_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:02.480402+00:00
-- url     : https://prove2.me/submissions/0ac9d652-5103-4321-ac99-057931121cfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
open GlobalTheory.NormIntegers
variable {C : Type*} [NormedField C] [IsUltrametricDist C] {O : Type*} [CommRing O] [Algebra O C]
  (hO : (NormedField.valuation (K := C)).Integers O)
include hO
namespace GlobalTheory.NormIntegers
theorem _root_.solution {J : Ideal O} (hJ : J.FG) : J.IsPrincipal :=
  haveI := isDomain hO
  haveI := ValuationRing.of_integers _ hO
  IsBezout.isPrincipal_of_FG J hJ
end GlobalTheory.NormIntegers
