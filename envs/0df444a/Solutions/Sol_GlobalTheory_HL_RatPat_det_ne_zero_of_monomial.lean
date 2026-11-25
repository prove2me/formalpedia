-- Prove2me | solution 1 for GlobalTheory.HL.RatPat.det_ne_zero_of_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:09.95815+00:00
-- url     : https://prove2.me/submissions/05169eef-f043-4c4b-a714-ee8d99a35efe

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliser
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatPat
namespace GlobalTheory.HL.RatPat
theorem _root_.solution {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (σ : Equiv.Perm (Fin m)) (hM : ∀ a b, M a b ≠ 0 ↔ b = σ a) : M.det ≠ 0 := by
  rw [Matrix.det_apply, Finset.sum_eq_single σ⁻¹]
  · have hp : ∏ i, M ((σ⁻¹ : Equiv.Perm (Fin m)) i) i ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [hM]
      simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> rw [h] <;> simpa using hp
  · intro τ _ hτ
    have : ∃ i, σ (τ i) ≠ i := by
      by_contra h
      push_neg at h
      apply hτ
      refine Equiv.ext fun i => ?_
      show τ i = σ⁻¹ i
      rw [Equiv.Perm.eq_inv_iff_eq]
      exact h i
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i), smul_zero]
    by_contra h
    exact hi ((hM _ _).1 h).symm
  · simp
end GlobalTheory.HL.RatPat
