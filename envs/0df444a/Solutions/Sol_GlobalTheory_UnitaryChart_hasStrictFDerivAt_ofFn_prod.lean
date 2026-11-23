-- Prove2me | solution 1 for GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:26.008087+00:00
-- url     : https://prove2.me/submissions/346a1197-5e53-46ea-9aa4-29a7a645e8ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnitaryChart
open Topology Filter
namespace GlobalTheory.UnitaryChart
theorem _root_.solution {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedRing E] [NormedAlgebra ℝ E] :
    ∀ (N : ℕ) (g : Fin N → F → E) (g' : Fin N → F →L[ℝ] E),
      (∀ i, g i 0 = 1 ∧ HasStrictFDerivAt (g i) (g' i) 0) →
      (List.ofFn fun i => g i 0).prod = 1 ∧
        HasStrictFDerivAt (fun t => (List.ofFn fun i => g i t).prod) (∑ i, g' i) 0 := by
  intro N
  induction N with
  | zero =>
    intro g g' _
    simpa using hasStrictFDerivAt_const (𝕜 := ℝ) (1 : E) (0 : F)
  | succ N ih =>
    intro g g' h
    obtain ⟨h1, h2⟩ := ih (fun i => g i.succ) (fun i => g' i.succ) (fun i => h i.succ)
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    refine ⟨by rw [h1, (h 0).1, mul_one], ?_⟩
    have h3 := (h 0).2.mul' h2
    refine (h3.congr_fderiv ?_)
    ext y
    simp [h1, (h 0).1, add_comm]
end GlobalTheory.UnitaryChart
