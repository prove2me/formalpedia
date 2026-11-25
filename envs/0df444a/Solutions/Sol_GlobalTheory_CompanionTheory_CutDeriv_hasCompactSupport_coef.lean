-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CutDeriv.hasCompactSupport_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:32:14.587189+00:00
-- url     : https://prove2.me/submissions/66546b96-cd6f-41f5-afb6-cdaaf052f418

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TruncatedDerivation
import Theorems.Thm_GlobalTheory_CompanionTheory_CutDeriv_notMem_tsupport
import Theorems.Thm_GlobalTheory_CompanionTheory_CutDeriv_isCompact_img

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
theorem _root_.solution {ρ : Mat n → ℝ} (hc : HasCompactSupport ρ) {R : ℝ} (hR : 0 < R)
    (φ : PI.MtM n → ℂ) : HasCompactSupport fun y : PI.MtM n => (ρ (R⁻¹ • Matrix.of y) : ℂ) * φ y := by
  refine HasCompactSupport.intro (isCompact_img hc R 0 (isCompact_singleton (x := (0 : ℝ)))) fun y hy => ?_
  have := notMem_tsupport hR 0 (mem_singleton _) hy
  rw [neg_zero, ex_zero, Matrix.one_mul] at this
  rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]
end GlobalTheory.CompanionTheory.CutDeriv
