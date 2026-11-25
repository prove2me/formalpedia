-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CutDeriv.cutI_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:10:47.162815+00:00
-- url     : https://prove2.me/submissions/e1d99c1c-0f41-4856-9736-5339194fa637

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TruncatedDerivation

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
variable {Hm : Mat n} {σ : Mat n → (H →L[ℂ] H)} {μ : Measure (PI.MtM n)} {w : H} {F : Mat n → H}
namespace GlobalTheory.CompanionTheory.CutDeriv
theorem _root_.solution (hμ : PI.IsHaarOnM (UH Hm) μ) (hFw : ∀ a ∈ UH Hm, F a = σ a w) (R : ℝ) (ρ : Mat n → ℝ) (v : H) :
    cutI σ μ w R ρ v =
      ∫ y : PI.MtM n, ((ρ (R⁻¹ • Matrix.of y) : ℂ) * ⟪F (Matrix.of y), v⟫_ℂ) • F (Matrix.of y) ∂μ := by
  have hae : ∀ᵐ g ∂μ, Matrix.of g ∈ UH Hm := hμ.2.2.1
  refine integral_congr_ae ?_
  filter_upwards [hae] with g hg
  rw [hFw _ hg, inner_conj_symm]
end GlobalTheory.CompanionTheory.CutDeriv
