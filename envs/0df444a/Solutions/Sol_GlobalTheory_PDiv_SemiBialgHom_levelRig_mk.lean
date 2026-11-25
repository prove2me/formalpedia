-- Prove2me | solution 1 for GlobalTheory.PDiv.SemiBialgHom.levelRig_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:41:26.776093+00:00
-- url     : https://prove2.me/submissions/e2cc4512-1772-4242-aeac-596984e00137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDiv
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {A A' : Type} [CommRing A]
  [Bialgebra R A] [CommRing A'] [Bialgebra R' A']
variable [IsCocomm R A] [IsCocomm R' A']
namespace GlobalTheory.PDiv
namespace SemiBialgHom
theorem _root_.solution (f : SemiBialgHom σ A A')
    (x : symCocycles R A × Cot R A) :
    f.levelRig (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f.levelPair x) := rfl
end SemiBialgHom
end GlobalTheory.PDiv
