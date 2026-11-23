-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.val_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:51.523131+00:00
-- url     : https://prove2.me/submissions/4961e9b3-cbde-4650-8062-a5516a2b9451

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
theorem _root_.solution (u : K.O) (hu : IsUnit u) : val K.O (algebraMap K.O K.E u) = 0 := by
  unfold val
  have : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E u) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h => (mem_maximalIdeal u).1 h hu
  rw [this]; simp
end GlobalTheory.UnitLemma.Orbit
