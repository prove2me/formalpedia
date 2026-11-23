-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.finiteType_of_closure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:28.336616+00:00
-- url     : https://prove2.me/submissions/12f0ab36-df21-4f91-8b5c-ae802d3d3db2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution {k J A : Type} [Field k] [Fintype J] [CommRing A] [Algebra k A] (r : J → A)
    (h : Subring.closure (Set.range (algebraMap k A) ∪ Set.range r) = ⊤) : Algebra.FiniteType k A := by
  refine ⟨Subalgebra.fg_def.2 ⟨Set.range r, Set.finite_range r, ?_⟩⟩
  apply Subalgebra.toSubring_injective
  rw [Algebra.adjoin_eq_ring_closure, h]
  rfl
end GlobalTheory.ZH.ConePrime
