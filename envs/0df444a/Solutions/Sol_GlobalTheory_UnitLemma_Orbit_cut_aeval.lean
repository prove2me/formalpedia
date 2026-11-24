-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.cut_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:02.090087+00:00
-- url     : https://prove2.me/submissions/5b48afba-2cb7-4c34-bf15-f45224b9e79b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (B : InvAlg K) (e : B.A) (he : B.σ e = e) (f : K.O[X]) :
    aeval (cut B e he).g f = Ideal.Quotient.mk (Ideal.span {e}) (aeval B.g f) :=
  aeval_algHom_apply (Ideal.Quotient.mkₐ K.O (Ideal.span {e})) B.g f
end GlobalTheory.UnitLemma.Orbit
