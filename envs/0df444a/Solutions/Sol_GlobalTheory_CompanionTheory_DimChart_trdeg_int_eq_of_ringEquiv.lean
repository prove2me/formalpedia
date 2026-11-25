-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DimChart.trdeg_int_eq_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:52.352073+00:00
-- url     : https://prove2.me/submissions/c97d2dc6-e37f-43c5-9118-49796336392f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KrullDimQuotientEqTrdegSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DimChart
namespace GlobalTheory.CompanionTheory.DimChart
theorem _root_.solution {L L' : Type} [CommRing L] [CommRing L'] [Algebra ℤ L]
    [Algebra ℤ L'] (e : L ≃+* L') : Algebra.trdeg ℤ L = Algebra.trdeg ℤ L' := by
  obtain rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L := Subsingleton.elim _ _
  obtain rfl : ‹Algebra ℤ L'› = Ring.toIntAlgebra L' := Subsingleton.elim _ _
  exact e.toIntAlgEquiv.trdeg_eq
end GlobalTheory.CompanionTheory.DimChart
