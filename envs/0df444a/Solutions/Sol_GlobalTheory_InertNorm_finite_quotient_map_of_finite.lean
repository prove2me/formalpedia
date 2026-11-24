-- Prove2me | solution 1 for GlobalTheory.InertNorm.finite_quotient_map_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:46.815286+00:00
-- url     : https://prove2.me/submissions/699b31d9-c9cf-44e1-b361-bf452ac9bf16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqFixedUnitHenselianStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.InertNorm
namespace GlobalTheory.InertNorm
theorem _root_.solution {O : Type} [CommRing O] (I : Ideal O) [Finite (O ⧸ I)]
    (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    Finite (R ⧸ I.map (algebraMap O R)) := by
  have : Module.Finite O (R ⧸ I.map (algebraMap O R)) := inferInstance
  have : Module.Finite (O ⧸ I) (R ⧸ I.map (algebraMap O R)) :=
    Module.Finite.of_restrictScalars_finite O (O ⧸ I) _
  exact Module.finite_of_finite (O ⧸ I)
end GlobalTheory.InertNorm
