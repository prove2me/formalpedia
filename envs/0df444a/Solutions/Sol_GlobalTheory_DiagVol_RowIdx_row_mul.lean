-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.row_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:21:52.845423+00:00
-- url     : https://prove2.me/submissions/32be81c2-ac29-4e12-9480-51c86940a137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.DiagVol GlobalTheory.DiagVol.RowIdx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.DiagVol.RowIdx
theorem _root_.solution {R : Type} [CommRing R] (P Q : Matrix ι ι R) (t : ι) : (P * Q) t = Matrix.vecMul (P t) Q := by
  funext s; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
end GlobalTheory.DiagVol.RowIdx
