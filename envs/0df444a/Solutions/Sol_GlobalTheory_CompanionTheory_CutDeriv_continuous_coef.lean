-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CutDeriv.continuous_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:33.586576+00:00
-- url     : https://prove2.me/submissions/879b2695-7545-44b7-8004-b76e44e62a95

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TruncatedDerivation
import Theorems.Thm_GlobalTheory_CompanionTheory_CutDeriv_continuous_of
import Theorems.Thm_GlobalTheory_CompanionTheory_CutDeriv_continuous_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Set Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CutDeriv
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.CompanionTheory.CutDeriv
theorem _root_.solution {ρ : Mat n → ℝ} (hρ : Continuous ρ) (R : ℝ) {F : Mat n → H} (hF : Continuous F) (v : H) :
    Continuous fun y : PI.MtM n => (ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ :=
  (Complex.continuous_ofReal.comp (hρ.comp (continuous_scale _))).mul
    ((hF.comp continuous_of).inner continuous_const)
end GlobalTheory.CompanionTheory.CutDeriv
