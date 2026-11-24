-- Prove2me | solution 1 for GlobalTheory.AffinePoints.isLocalHomeomorph_coords_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:27:40.834798+00:00
-- url     : https://prove2.me/submissions/e390761a-5c46-4f6d-a66d-8ecba176077c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
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
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [CompleteSpace 𝕜] {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale) :
    IsLocalHomeomorph (coords g : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) := fun p => by
  obtain ⟨e, h1, h2, -⟩ := exists_chart_of_etale g hg p
  exact ⟨e, h1, h2.symm⟩
end GlobalTheory.AffinePoints
