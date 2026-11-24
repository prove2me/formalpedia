-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.residue_eq_zero_iff_of_isUnif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:22:09.243409+00:00
-- url     : https://prove2.me/submissions/31df66d6-2894-4411-8920-e1d609775892

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
import Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_maximalIdeal_eq


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
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : k) (ha : a ∈ 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] ⟨a, ha⟩ = 0 ↔ (ϖ : k)⁻¹ * a ∈ 𝒪[k] := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have : a = ϖ * c := congrArg Subtype.val hc
    rw [this, ← mul_assoc, inv_mul_cancel₀ ϖ.ne_zero, one_mul]; exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    show a = ϖ * ((ϖ : k)⁻¹ * a)
    rw [← mul_assoc, mul_inv_cancel₀ ϖ.ne_zero, one_mul]
end GlobalTheory.DiagVol.RowIdx
