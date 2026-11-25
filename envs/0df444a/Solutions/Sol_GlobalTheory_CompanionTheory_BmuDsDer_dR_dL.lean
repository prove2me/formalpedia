-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDsDer.dR_dL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:31:29.698924+00:00
-- url     : https://prove2.me/submissions/9b755a71-cea5-4f2f-ac87-32e65a8d5f07

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
variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.CompanionTheory.BmuDsDer
theorem _root_.solution {a : E → E} (ha : ContDiff ℝ ∞ a) {b : E' → E'} (hb : ContDiff ℝ ∞ b) {Φ : E × E' → V}
    (hΦ : ContDiff ℝ ∞ Φ) : dR b (dL a Φ) = dL a (dR b Φ) := by
  funext q
  have hΦ1 : ContDiff ℝ ∞ (fderiv ℝ Φ) := (contDiff_infty_iff_fderiv.1 hΦ).2
  have hc : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) q) q :=
    ((hΦ1.differentiable (by simp)) q).hasFDerivAt
  have hua : HasFDerivAt (fun q : E × E' => (a q.1, (0 : E')))
      (((fderiv ℝ a q.1).comp (ContinuousLinearMap.fst ℝ E E')).prod 0) q :=
    (((ha.differentiable (by simp)) q.1).hasFDerivAt.comp q hasFDerivAt_fst).prodMk (hasFDerivAt_const 0 q)
  have hub : HasFDerivAt (fun q : E × E' => ((0 : E), b q.2))
      ((0 : E × E' →L[ℝ] E).prod ((fderiv ℝ b q.2).comp (ContinuousLinearMap.snd ℝ E E'))) q :=
    (hasFDerivAt_const 0 q).prodMk (((hb.differentiable (by simp)) q.2).hasFDerivAt.comp q hasFDerivAt_snd)
  have hsymm := ((contDiff_infty.1 hΦ 2).contDiffAt (x := q)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  show fderiv ℝ (dL a Φ) q (0, b q.2) = fderiv ℝ (dR b Φ) q (a q.1, 0)
  rw [show dL a Φ = fun y => fderiv ℝ Φ y (a y.1, 0) from rfl,
    show dR b Φ = fun y => fderiv ℝ Φ y (0, b y.2) from rfl,
    (hc.clm_apply hua).fderiv, (hc.clm_apply hub).fderiv]
  simp
  exact hsymm _ _
end GlobalTheory.CompanionTheory.BmuDsDer
