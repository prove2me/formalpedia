-- Prove2me | solution 1 for GlobalTheory.AffinePoints.mdifferentiableAt_pi_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:29.976418+00:00
-- url     : https://prove2.me/submissions/a02017d7-586b-4d88-9765-97eff4af21b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
open scoped Manifold ContDiff
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
variable [CompleteSpace 𝕜]
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
omit [CompleteSpace 𝕜]
namespace GlobalTheory.AffinePoints
theorem _root_.solution {ι : Type*} [Fintype ι] {f : M → ι → 𝕜} {x : M}
    (hf : ∀ i, MDifferentiableAt I 𝓘(𝕜) (fun m => f m i) x) :
    MDifferentiableAt I 𝓘(𝕜, ι → 𝕜) f x := by
  have h' := fun i => (mdifferentiableAt_iff _ _).1 (hf i)
  rw [mdifferentiableAt_iff]
  refine ⟨continuousAt_pi.2 fun i => (h' i).1, ?_⟩
  rw [differentiableWithinAt_pi]
  intro i
  exact (h' i).2
end GlobalTheory.AffinePoints
