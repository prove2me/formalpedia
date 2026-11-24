-- Prove2me | solution 1 for GlobalTheory.AffinePoints.exists_isAlgebraicChart_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:27:39.968547+00:00
-- url     : https://prove2.me/submissions/b3112acb-3efd-4c34-865d-1b5b9686bb12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Theorems.Thm_GlobalTheory_AffinePoints_exists_chart_of_etale


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
namespace GlobalTheory.AffinePoints
theorem _root_.solution (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale)
    (p : A →ₐ[𝕜] 𝕜) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), IsAlgebraicChart e ∧ p ∈ e.source ∧
      (e : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) = coords g := by
  obtain ⟨e, hp, he, ha⟩ := exists_chart_of_etale g hg p
  refine ⟨e, ⟨⟨fun i => g (X i), 1, fun q _ => ⟨by simp, fun i => ?_⟩⟩, ha⟩, hp, he⟩
  rw [he]
  simp [coords]
end GlobalTheory.AffinePoints
