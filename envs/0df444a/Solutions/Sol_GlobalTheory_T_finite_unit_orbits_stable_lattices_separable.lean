-- Prove2me | solution 1 for GlobalTheory.T.finite_unit_orbits_stable_lattices_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:15.233676+00:00
-- url     : https://prove2.me/submissions/0be49366-180a-4364-9c33-de82d225a62a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitOrbitsStableLatticesSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitOrbitsStableLatticesSeparableStatement
import Theorems.Thm_GlobalTheory_UnitLemma_finite_orbits_stLat_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Finite (MulAction.orbitRel.Quotient Aˣ (stLat O E g)) := by
  first | exact @GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable | exact GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable | (intros; apply GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable <;> assumption)
end _root_.GlobalTheory.T
