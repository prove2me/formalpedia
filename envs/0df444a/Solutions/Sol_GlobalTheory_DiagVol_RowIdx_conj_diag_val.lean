-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.conj_diag_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:23:46.869949+00:00
-- url     : https://prove2.me/submissions/5ff51f09-860f-40af-b5f5-dfd293155552

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
theorem _root_.solution (ϖ : kˣ) (t : ι) (z : GL ι k) (r s : ι) :
    ((diagGL (Pi.mulSingle t ϖ))⁻¹ * z * diagGL (Pi.mulSingle t ϖ)).val r s =
      (if r = t then (ϖ : k)⁻¹ else 1) * z.val r s * (if s = t then (ϖ : k) else 1) := by
  have hi : ((diagGL (Pi.mulSingle t ϖ))⁻¹).val = diagonal fun i => ((((Pi.mulSingle t ϖ : ι → kˣ) i)⁻¹ : kˣ) : k) := rfl
  rw [Units.val_mul, Units.val_mul, hi, diagGL_val, mul_diagonal, diagonal_mul]
  by_cases hr : r = t <;> by_cases hs : s = t <;> simp [hr, hs, Pi.mulSingle_apply]
end GlobalTheory.DiagVol.RowIdx
