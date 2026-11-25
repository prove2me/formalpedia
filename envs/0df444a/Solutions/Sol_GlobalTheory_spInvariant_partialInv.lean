-- Prove2me | solution 1 for GlobalTheory.spInvariant_partialInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:30.948015+00:00
-- url     : https://prove2.me/submissions/2bf60935-15b1-4ce8-b540-354c0aa4afc9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteAbsLeOneMulMemRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_isUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_nAut_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spH_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spPJ_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology
open GlobalTheory
variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}
namespace GlobalTheory
theorem _root_.solution (hH : IsSpInvariant g H) (e : Fin g)
    {τ σ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    (h : ∀ i k, σ i k - σ i e * (τ e k + if e = k then 1 else 0) =
      τ i k + if i = e then (if e = k then 1 else 0) - τ e k else 0) : H σ = H τ := by
  have hm := spH_le g (spPJ_mem e)
  have hj := jAut_isUnit hm hτ
  have : σ * jAut (spPJ e) τ = nAut (spPJ e) τ := by
    have e1 : jAut (spPJ e) τ = 1 - single e e (1 : ℂ) * (τ + 1) := by
      ext i k
      by_cases hi : e = i <;> simp [jAut_eq, cMat, spPJ, toBlocks₂₁, toBlocks₂₂, mul_apply,
        one_apply, single_apply, ite_and, hi]
    have e2 : nAut (spPJ e) τ = τ + single e e (1 : ℂ) * (1 - τ) := by
      ext i k
      by_cases hi : e = i <;> simp [nAut_eq, cMat, spPJ, toBlocks₁₁, toBlocks₁₂, mul_apply,
        one_apply, single_apply, ite_and, hi]
    ext i k
    rw [e1, e2, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
    have := h i k
    by_cases hi : i = e
    · subst hi
      simpa [mul_apply, single_apply, ite_and, one_apply] using this
    · simpa [mul_apply, single_apply, ite_and, one_apply, hi, Ne.symm hi] using this
  have e2 : σ = spAct (spPJ e) τ := by
    rw [spAct_eq, ← this, Matrix.mul_nonsing_inv_cancel_right _ _ hj]
  rw [e2]
  exact hH _ hm τ hτ
end GlobalTheory
