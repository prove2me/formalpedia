-- Prove2me | solution 1 for GlobalTheory.JR.UnitGLift.norm_full_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:34.253231+00:00
-- url     : https://prove2.me/submissions/755a3269-1a7b-4ec1-b11e-5ce5ef9ddf07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis
import Theorems.Thm_GlobalTheory_JR_UnitGLift_full_apply_cc
import Theorems.Thm_GlobalTheory_JR_UnitGLift_full_apply_cl
import Theorems.Thm_GlobalTheory_JR_UnitGLift_full_apply_lc
import Theorems.Thm_GlobalTheory_JR_UnitGLift_full_apply_ll

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.UnitGLift
namespace GlobalTheory.JR.UnitGLift
theorem _root_.solution {F : Type} [NormedField F] {r : ℕ} (Z : Gl r F) :
    (∀ i j, ‖full Z i j‖ ≤ 1) ↔
      ((∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1) := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩
    · simpa [full_apply_cc] using h (Fin.castSucc i) (Fin.castSucc j)
    · simpa [full_apply_cl] using h (Fin.castSucc i) (Fin.last r)
    · simpa [full_apply_lc] using h (Fin.last r) (Fin.castSucc j)
    · simpa [full_apply_ll] using h (Fin.last r) (Fin.last r)
  · rintro ⟨h1, h2, h3, h4⟩ i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa [full_apply_ll] using h4
      | cast j => simpa [full_apply_lc] using h3 j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [full_apply_cl] using h2 i
      | cast j => simpa [full_apply_cc] using h1 i j
end GlobalTheory.JR.UnitGLift
