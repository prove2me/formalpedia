-- Prove2me | solution 1 for GlobalTheory.LineCos.FsLaw.map_cosSq_fs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:55:05.325091+00:00
-- url     : https://prove2.me/submissions/51035de0-03ee-4cde-9227-8c84bca59138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_measurable_lineVec
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_measurable_hform
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_measurable_cosSq
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_lintegral_false
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_lintegral_true

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LineCos GlobalTheory.LineCos.FsLaw
open GlobalTheory.LineCos
namespace GlobalTheory.LineCos.FsLaw
theorem _root_.solution (G : Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (hG : G.PosDef) :
    Measure.map (cosSq s G)
        (volume.withDensity fun x : ℂ => ENNReal.ofReal (G.det.re /
          (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2))) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hd : Measurable fun x : ℂ => ENNReal.ofReal (G.det.re /
      (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2)) := by
    have := Complex.measurable_re.comp (measurable_hform G (measurable_lineVec s) (measurable_lineVec s))
    exact (measurable_const.div ((this.pow_const 2).const_mul _)).ennreal_ofReal
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg (measurable_cosSq s G),
    lintegral_withDensity_eq_lintegral_mul _ hd (g := fun x => g (cosSq s G x)) (hg.comp (measurable_cosSq s G)),
    ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  cases s
  · exact lintegral_false hG g hg
  · exact lintegral_true hG g hg
end GlobalTheory.LineCos.FsLaw
