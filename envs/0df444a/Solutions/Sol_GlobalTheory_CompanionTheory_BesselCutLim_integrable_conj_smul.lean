-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCutLim.integrable_conj_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:36:46.999984+00:00
-- url     : https://prove2.me/submissions/e541be73-260b-42f5-b911-5dc10eccfa14

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TruncatedDerivationLimit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCutLim
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BesselCutLim
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (Mat n)}
    (hG : IsClosed G) {μ : Measure (PI.MtM n)} (hae : ∀ᵐ y ∂μ, (Matrix.of y : Mat n) ∈ G)
    {c : PI.MtM n → ℂ} (hc : Integrable c μ) {g : Mat n → E} (hg : ContinuousOn g G) {K : ℝ}
    (hK : ∀ x ∈ G, ‖g x‖ ≤ K) : Integrable (fun y => conj (c y) • g (Matrix.of y)) μ := by
  have hms : MeasurableSet {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G} :=
    IsClosed.measurableSet (α := PI.MtM n) hG
  have hg' : ContinuousOn (fun y : PI.MtM n => g (Matrix.of y)) {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G} := hg
  have hm := hg'.aestronglyMeasurable (μ := μ) hms
  rw [Measure.restrict_eq_self_of_ae_mem (s := {y : PI.MtM n | (Matrix.of y : Mat n) ∈ G}) hae] at hm
  refine Integrable.mono' (hc.norm.mul_const K)
    ((Complex.continuous_conj.comp_aestronglyMeasurable hc.1).smul hm) ?_
  filter_upwards [hae] with y hy
  rw [norm_smul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (hK _ hy) (norm_nonneg _)
end GlobalTheory.CompanionTheory.BesselCutLim
