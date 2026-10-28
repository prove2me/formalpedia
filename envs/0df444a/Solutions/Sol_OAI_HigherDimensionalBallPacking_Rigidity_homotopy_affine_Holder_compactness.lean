-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_Holder_compactness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:05:04.852458+00:00
-- url     : https://prove2.me/submissions/550055a7-1614-4d8d-bc2e-b8438d2f5399

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp005
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_affineHolderModuli_isCompact
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_homotopy_density_common_support

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity







open scoped ContDiff Topology
open Set Filter Function
section
open HigherDimensionalBallPacking.Rigidity
open FramedCR

theorem homotopy_affine_Holder_compactness_oai (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) :
    ∃ R > 0, IsCompact (affineHolderModuli J p q R) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
        AffineLineCurve (lineHomotopy J t) p q u →
        ∀ z, R < ‖z‖ → standardCurl u z=0) := by
  obtain ⟨R,hR,hRc⟩ := homotopy_density_common_support n hn J hJs hJ hc hs p q hpq
  exact ⟨R,hR,affineHolderModuli_isCompact n hn J hJs hJ hc hs p q hpq R hRc,hRc⟩

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function








open scoped ContDiff Topology
open Set Filter Function

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_Holder_compactness_oai := @OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_Holder_compactness_oai
