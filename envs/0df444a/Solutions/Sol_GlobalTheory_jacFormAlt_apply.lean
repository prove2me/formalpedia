-- Prove2me | solution 1 for GlobalTheory.jacFormAlt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:20.690518+00:00
-- url     : https://prove2.me/submissions/713c75b8-75a3-4430-97d7-ef1bf6dbfefb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_jacForm_eq_jetWedge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}
variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)
variable [Module R N] [IsScalarTower R A N] [IsScalarTower R A M]
namespace GlobalTheory
theorem _root_.solution (f : Fin (D + 1) → A) : jacobianMultilinearTo d ω f = jacForm d ω f :=
  (jacForm_eq_jetWedge d ω f).symm
end GlobalTheory
