-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.relIndex_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:17:51.535288+00:00
-- url     : https://prove2.me/submissions/a2ad3956-6342-4f22-8d24-c88901943a20

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_line_eq_of_val_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_relIndex_line_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_mem_iff_val_le
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_nrm_eq_zpow
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_one_lt_q
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_val_eq_pow_of_int


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
theorem _root_.solution (h : LF O ϖ nrm q) {c o : F} (hc : c ≠ 0) (ho : o ∈ O) (ho0 : o ≠ 0) :
    (((line O (c * o)).relIndex (line O c) : ℕ) : ℝ) = nrm c / nrm (c * o) := by
  obtain ⟨k, hk⟩ := val_eq_pow_of_int h ho0 ((mem_iff_val_le h o).1 ho)
  have hline : line O (c * o) = line O (c * ϖ ^ k) :=
    line_eq_of_val_eq h (mul_ne_zero hc ho0) (mul_ne_zero hc (pow_ne_zero _ h.ne))
      (by rw [map_mul, map_mul, hk, map_pow])
  have hq : (q : ℝ) ≠ 0 := by
    have := one_lt_q h
    exact_mod_cast (by omega : q ≠ 0)
  have hn : nrm o = ((q : ℝ) ^ k)⁻¹ := by
    have := nrm_eq_zpow h (x := o) (e := (k : ℤ)) (by simpa using hk)
    simpa [_root_.zpow_neg] using this
  have hnc : nrm c ≠ 0 := (nrm.pos hc).ne'
  rw [hline, relIndex_line_pow h hc k, map_mul, hn]
  push_cast
  field_simp
end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
