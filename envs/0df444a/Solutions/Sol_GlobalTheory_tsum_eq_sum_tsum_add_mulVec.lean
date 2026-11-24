-- Prove2me | solution 1 for GlobalTheory.tsum_eq_sum_tsum_add_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:57.303399+00:00
-- url     : https://prove2.me/submissions/fd6a8306-3d05-45d6-89d6-ede062e4fcb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_IsSiegel_mk
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_siegelUpperCoords
import Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.mem_siegelUpperCoords
attribute [local simp] GlobalTheory.riemannThetaJointForm_apply



set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : Matrix ι ι ℤ}
namespace GlobalTheory
theorem _root_.solution (hd : d.det ≠ 0) {κ : Type*} [Fintype κ] (r : κ → ι → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (ι → ℤ) ⧸ LinearMap.range d.mulVecLin))
    {f : (ι → ℤ) → ℂ} (hf : Summable f) :
    ∑' n, f n = ∑ k, ∑' m, f (r k + d *ᵥ m) := by
  have hb : Function.Bijective fun p : κ × (ι → ℤ) => r p.1 + d *ᵥ p.2 := by
    refine ⟨?_, fun n => ?_⟩
    · rintro ⟨k, m⟩ ⟨k', m'⟩ h
      simp only at h
      obtain rfl : k = k' := hr.1 ((Submodule.Quotient.eq _).2 ⟨m' - m, by
        rw [mulVecLin_apply, mulVec_sub, sub_eq_sub_iff_add_eq_add, add_comm, ← h, add_comm]⟩)
      have h1 : d *ᵥ (m - m') = 0 := by rw [mulVec_sub, add_left_cancel h, sub_self]
      rw [sub_eq_zero.1 (eq_zero_of_mulVec_eq_zero hd h1)]
    · obtain ⟨k, hk⟩ := hr.2 (Submodule.Quotient.mk n)
      obtain ⟨m, hm⟩ := (Submodule.Quotient.eq _).1 hk.symm
      exact ⟨(k, m), by simp only [← mulVecLin_apply, hm, add_sub_cancel]⟩
  rw [← (Equiv.ofBijective _ hb).tsum_eq]
  exact ((Equiv.ofBijective _ hb).summable_iff.2 hf).tsum_prod.trans (tsum_fintype _)
end GlobalTheory
