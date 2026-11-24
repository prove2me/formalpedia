-- Prove2me | solution 1 for GlobalTheory.IndexCol.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:41.625685+00:00
-- url     : https://prove2.me/submissions/cfdb5bfe-7aea-483e-8241-32cec0d52878

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence

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
open GlobalTheory GlobalTheory.IndexCol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.IndexCol
theorem _root_.solution (ϖ : kˣ) (t : ι) (z : Matrix ι ι k) (r s : ι) :
    ((diagGL (Pi.mulSingle t ϖ : ι → kˣ)).val * z * ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val) r s =
      ((Pi.mulSingle t ϖ : ι → kˣ) r : k) * z r s * ((((Pi.mulSingle t ϖ : ι → kˣ) s)⁻¹ : kˣ) : k) := by
  have hi : ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val = diagonal fun i => ((((Pi.mulSingle t ϖ : ι → kˣ) i)⁻¹ : kˣ) : k) := rfl
  rw [hi, diagGL_val, mul_diagonal, diagonal_mul]
end GlobalTheory.IndexCol
