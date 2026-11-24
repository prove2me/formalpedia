-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.hasDerivAt_line_dH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:57.485444+00:00
-- url     : https://prove2.me/submissions/191d74ef-a80e-42e5-be4e-1bdc07034471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HasDerivAtLineDH
import Theorems.Thm_GlobalTheory_Mem_Lift_hasDerivAt_dH


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
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift
namespace GlobalTheory.Mem.Lift
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) {ρ : V → B →L[ℂ] B} (h0 : ∀ x, om x x = 0)
    (h : IsHeis (fun x y => om x y) ρ) (v : V) {f : B} (hf : Sm ρ f) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ρ (t • v) f) (ρ (s • v) (dH ρ v f)) s := by
  have e : (fun t : ℝ => ρ (t • v) f) = fun t : ℝ => ρ (s • v) (ρ ((t - s) • v) f) := by
    funext t
    rw [h.2.1, ← add_smul]
    simp [h0]
  have h1 : HasDerivAt (fun t : ℝ => ρ ((t - s) • v) f) (dH ρ v f) s := by
    have h2 : HasDerivAt (fun t : ℝ => ρ (t • v) f) (dH ρ v f) (s - s) := by
      rw [sub_self]; exact hasDerivAt_dH v hf
    exact h2.comp_sub_const s s
  rw [e]
  exact ((ρ (s • v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
end GlobalTheory.Mem.Lift
