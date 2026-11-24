-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.mOp_nOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:14.335809+00:00
-- url     : https://prove2.me/submissions/b4d253ca-68c8-49fa-a253-f4f7b9cd239f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilTorusMulUnipotentCommute
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NL_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad
namespace GlobalTheory.JR.WeilQuad
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (z : A.K) (φ : A.L → ℂ),
      mOp A ω s (nOp A ψ x z φ) = nOp A ψ x ((s : A.K) ^ 2 * z) (mOp A ω s φ) := by
  intro F E _ _ _ _ _ A ψ x μ ω _ s z φ
  funext y
  simp only [mOp, nOp, NL_smul]
  rw [show (z * (x : A.K) * ((s : A.K) ^ 2 * A.NL y)) = (s : A.K) ^ 2 * z * x * A.NL y by ring]
  ring
end GlobalTheory.JR.WeilQuad
