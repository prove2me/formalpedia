-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining.om_uGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:42.101216+00:00
-- url     : https://prove2.me/submissions/9070b9a2-54a9-4c3d-978d-eb0aad8d702b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.SplitWeil
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
variable {k : Type} [Field k]
variable {ρ v W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
theorem _root_.solution [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Fintype W] [DecidableEq W] (μ : kˣ →* ℂˣ) (ν : Matrix v ρ k) (ν' : Matrix ρ v k)
    (b : Matrix ρ ρ k) (Φ : Matrix W (ρ ⊕ v ⊕ ρ) k → ℂ) (x : Matrix W (ρ ⊕ v ⊕ ρ) k) :
    om μ (uGL ν ν' b) 1 Φ x = Φ (x * uMat ν ν' b) := by
  have h : Matrix.GeneralLinearGroup.det (uGL ν ν' b) = 1 := by
    ext; simp [uGL, det_uMat]
  have h2 : (uGL ν ν' b).val = uMat ν ν' b := rfl
  simp [om, h, h2, nabs]
end GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
