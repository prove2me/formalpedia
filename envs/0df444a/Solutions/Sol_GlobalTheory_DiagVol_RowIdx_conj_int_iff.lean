-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.conj_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:42:58.969864+00:00
-- url     : https://prove2.me/submissions/b6632818-8595-43c9-9e60-c81288bf0906

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
import Theorems.Thm_GlobalTheory_DiagVol_RowIdx_conj_diag_val

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
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) (z : GL ι k) (hz : ∀ r s, z.val r s ∈ 𝒪[k]) :
    (∀ r s, ((diagGL (Pi.mulSingle t ϖ))⁻¹ * z * diagGL (Pi.mulSingle t ϖ)).val r s ∈ 𝒪[k]) ↔
      ∀ s, s ≠ t → (ϖ : k)⁻¹ * z.val t s ∈ 𝒪[k] := by
  simp only [conj_diag_val]
  constructor
  · intro h s hs
    simpa [hs] using h t s
  · intro h r s
    by_cases hr : r = t
    · subst hr
      by_cases hs : s = r
      · subst hs
        simp only [if_true]
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ ϖ.ne_zero, one_mul]; exact hz _ _
      · simpa [hs] using h s hs
    · simp only [hr, if_false, one_mul]
      split_ifs
      · exact Subring.mul_mem _ (hz r s) hϖ.mem
      · simpa using hz r s
end GlobalTheory.DiagVol.RowIdx
