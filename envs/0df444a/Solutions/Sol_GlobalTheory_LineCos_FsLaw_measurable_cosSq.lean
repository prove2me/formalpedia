-- Prove2me | solution 1 for GlobalTheory.LineCos.FsLaw.measurable_cosSq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:27.904401+00:00
-- url     : https://prove2.me/submissions/e1e293db-b842-4dc1-8287-e5d00c3eb217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_measurable_lineVec
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_measurable_hform

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
theorem _root_.solution (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) : Measurable (cosSq s G) := by
  have h1 : Measurable fun x : ℂ => hform G (lineVec s x) (Pi.single (0 : Fin 2) (1 : ℂ)) :=
    measurable_hform G (b := fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) (measurable_lineVec s) fun _ => measurable_const
  have h2 : Measurable fun x : ℂ => (hform G (lineVec s x) (lineVec s x)).re :=
    Complex.measurable_re.comp (measurable_hform G (measurable_lineVec s) (measurable_lineVec s))
  exact (h1.norm.pow_const 2).div (h2.mul_const _)
end GlobalTheory.LineCos.FsLaw
