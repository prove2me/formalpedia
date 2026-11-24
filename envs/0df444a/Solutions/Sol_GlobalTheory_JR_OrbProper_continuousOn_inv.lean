-- Prove2me | solution 1 for GlobalTheory.JR.OrbProper.continuousOn_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:11:12.160095+00:00
-- url     : https://prove2.me/submissions/85a285c8-2bc2-41ab-8475-86a8f7517c31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitProperOfInvertibleKrylovColumns

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbProper
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}
namespace GlobalTheory.JR.OrbProper
theorem _root_.solution {X : Type} [TopologicalSpace X] {Ω : Set X} {h : X → Matrix (Fin r) (Fin r) E}
    (hh : ContinuousOn h Ω) (hu : ∀ a ∈ Ω, IsUnit (h a).det) : ContinuousOn (fun a => (h a)⁻¹) Ω := by
  have : (fun a => (h a)⁻¹) = fun a => ((h a).det)⁻¹ • (h a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  refine ContinuousOn.smul (f := fun a => ((h a).det)⁻¹) (g := fun a => (h a).adjugate) ?_ ?_
  · exact (continuous_id.matrix_det.comp_continuousOn hh).inv₀ fun a ha => (hu a ha).ne_zero
  · exact continuous_id.matrix_adjugate.comp_continuousOn hh
end GlobalTheory.JR.OrbProper
