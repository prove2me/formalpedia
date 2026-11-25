-- Prove2me | solution 1 for GlobalTheory.SatFin.muF_lt_top_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:52:19.192303+00:00
-- url     : https://prove2.me/submissions/5e292249-376f-4925-adaf-40acf5fd1b7f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetBorSat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MuFLtTopOfIsCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_densF_continuousOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SatFin
open GlobalTheory.FrameMeas
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SatFin
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {K : Set (V (nd X))}
    (hK : IsCompact K) (hKO : K ⊆ OmF X x0) : muF X x0 K < ⊤ := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image (OntoB.densF_continuousOn.mono hKO)
  unfold muF
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (densF X x0 z) ∂(volume.restrict (OmF X x0))
      ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂(volume.restrict (OmF X x0)) :=
        setLIntegral_mono' hK.measurableSet fun z hz =>
          ENNReal.ofReal_le_ofReal (hM ⟨z, hz, rfl⟩)
    _ = ENNReal.ofReal M * (volume.restrict (OmF X x0)) K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)
end GlobalTheory.SatFin
