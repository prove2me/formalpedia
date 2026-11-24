-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.red_incl_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:41:08.139806+00:00
-- url     : https://prove2.me/submissions/98f77660-7a6f-4bbc-b667-cfbce065ff6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_red_val

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
namespace GlobalTheory.DiagVol.RowIdx
theorem _root_.solution {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) (z : H) (r s : ι) (h : (z : GL ι k).val r s ∈ 𝒪[k]) :
    (red (Subgroup.inclusion hHK z)).val r s = IsLocalRing.residue 𝒪[k] ⟨(z : GL ι k).val r s, h⟩ :=
  red_val (Subgroup.inclusion hHK z) r s h
end GlobalTheory.DiagVol.RowIdx
