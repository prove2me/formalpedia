-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.val_conj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:04.615314+00:00
-- url     : https://prove2.me/submissions/1637fb74-2f68-4bd3-8d1c-d6efe46aef3f

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
theorem _root_.solution (x : K.E) (h : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≤ 1) :
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (K.c x) ≤ 1 := by
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h
  obtain ⟨b, hb⟩ := K.c_int a
  rw [hb]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
end GlobalTheory.UnitLemma.Orbit
