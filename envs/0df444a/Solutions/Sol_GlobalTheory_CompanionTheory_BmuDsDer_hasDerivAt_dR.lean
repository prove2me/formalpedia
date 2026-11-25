-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDsDer.hasDerivAt_dR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:35:11.242191+00:00
-- url     : https://prove2.me/submissions/719a21cb-3a1c-4cb3-a011-bae355cb75df

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuDsDer
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
namespace GlobalTheory.CompanionTheory.BmuDsDer
theorem _root_.solution {Φ : Mat n × Mat n → H} (hΦ : ContDiff ℝ ∞ Φ) (X g y : Mat n) :
    HasDerivAt (fun t => Φ (g, y * ex X t)) (dR (fun y => y * X) Φ (g, y)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (g, y * ex X t)) ((0 : Mat n), y * X) 0 :=
    (hasDerivAt_const 0 g).prodMk (hasDerivAt_mul_ex y X)
  have h0 : (g, y) = (g, y * ex X 0) := by rw [ex_zero, mul_one]
  exact ((hΦ.differentiable (by simp)) (g, y)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ h0
end GlobalTheory.CompanionTheory.BmuDsDer
