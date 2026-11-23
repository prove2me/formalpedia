-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.DCalc.contDiff_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:30.276342+00:00
-- url     : https://prove2.me/submissions/90367385-e9a0-4e3f-b974-d2a725f9725d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.DCalc
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B}
namespace GlobalTheory.Mem.Lift.DCalc
theorem _root_.solution {f : B} (hf : Sm ρ f) : ContDiff ℝ ∞ (fderiv ℝ fun u => ρ u f) := (contDiff_infty_iff_fderiv.1 (show ContDiff ℝ ∞ (fun u => ρ u f) from hf)).2
end GlobalTheory.Mem.Lift.DCalc
