-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdExChart.contDiff_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:51:49.347188+00:00
-- url     : https://prove2.me/submissions/7bceaa09-f065-4dfb-8858-2d9505a73814

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_differentiableAt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_ex


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdExChart
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.ProdExChart
theorem _root_.solution (X : Mat n) : ContDiff ℝ ∞ (ex X) := by
  rw [contDiff_infty]
  intro m
  induction m with
  | zero => exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hasDerivAt_ex X t).continuousAt)
  | succ m ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hasDerivAt_ex X t).differentiableAt, by simp, ?_⟩
    have hc : ContDiff ℝ m (fun t => ex X t * X) :=
      (contDiff_mul.of_le (by exact_mod_cast le_top)).comp (ih.prodMk contDiff_const)
    exact contDiffOn_univ.1 ((contDiffOn_univ.2 hc).congr fun t _ => (hasDerivAt_ex X t).deriv)
end GlobalTheory.CompanionTheory.ProdExChart
