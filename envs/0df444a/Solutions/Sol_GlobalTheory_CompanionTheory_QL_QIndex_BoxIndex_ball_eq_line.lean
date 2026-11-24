-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.ball_eq_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:17.064799+00:00
-- url     : https://prove2.me/submissions/6f70e1e4-c2f2-4ae4-8554-b60a416ff65c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_mem_line
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitRow_IdxV_mem_ball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
theorem _root_.solution (h : LF O ϖ nrm q) {d : F} (hd : d ≠ 0) : ball d = line O d⁻¹ := by
  ext x
  rw [mem_ball, mem_line, ← h.O_eq]
  constructor
  · intro hx
    exact ⟨_, hx, by field_simp⟩
  · rintro ⟨o, ho, rfl⟩
    rwa [mul_comm d⁻¹, mul_assoc, inv_mul_cancel₀ hd, mul_one]
end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
