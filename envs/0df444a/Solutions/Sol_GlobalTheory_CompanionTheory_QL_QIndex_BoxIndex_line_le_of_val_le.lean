-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.line_le_of_val_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:23.740178+00:00
-- url     : https://prove2.me/submissions/9263e28a-4b76-42e2-ac43-395fee8a55b1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_mem_line
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_mem_iff_val_le


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
theorem _root_.solution (h : LF O ϖ nrm q) {x y : F} (hy : y ≠ 0)
    (hxy : ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y) : line O x ≤ line O y := by
  have hvy : 0 < ValuativeRel.valuation F y := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy)
  have h1 : x / y ∈ O := by
    rw [mem_iff_val_le h, map_div₀]
    exact div_le_one_of_le₀ hxy zero_le'
  intro z hz
  obtain ⟨o, ho, rfl⟩ := mem_line.1 hz
  exact mem_line.2 ⟨x / y * o, O.mul_mem h1 ho, by field_simp⟩
end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
