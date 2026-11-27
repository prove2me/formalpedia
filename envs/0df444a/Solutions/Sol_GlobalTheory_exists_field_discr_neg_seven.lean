-- Prove2me | solution 1 for GlobalTheory.exists_field_discr_neg_seven
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:39.776134+00:00
-- url     : https://prove2.me/submissions/2558c698-0084-4f10-807c-499afdca96dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_discr_eq_neg_of_sq_eq
import Theorems.Thm_GlobalTheory_exists_isKroneckerChar_of_discr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution : ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K)
    (χ : DirichletCharacter ℂ 7), finrank ℚ K = 2 ∧ discr K = -(7 : ℕ) ∧ IsKroneckerChar χ := by
  let r : ℂ := √7 * Complex.I
  have hr : r ^ 2 = -7 := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    simp
  have hm : (Polynomial.X ^ 2 + Polynomial.C 7 : Polynomial ℚ).Monic := by monicity!
  have he : Polynomial.aeval r (Polynomial.X ^ 2 + Polynomial.C 7 : Polynomial ℚ) = 0 := by
    simp [hr]
  have hi : IsIntegral ℚ r := ⟨_, hm, he⟩
  have hfin := IntermediateField.adjoin.finiteDimensional hi
  have hK : NumberField (IntermediateField.adjoin ℚ {r}) := ⟨⟩
  have h2 : finrank ℚ (IntermediateField.adjoin ℚ {r}) = 2 := by
    rw [IntermediateField.adjoin.finrank hi]
    refine le_antisymm ((Polynomial.natDegree_le_natDegree (minpoly.min ℚ r hm he)).trans
      (by compute_degree)) ((minpoly.two_le_natDegree_iff hi).2 ?_)
    rintro ⟨q, hq⟩
    have := congrArg Complex.im hq
    simp [r, eq_comm (a := (0 : ℝ))] at this
  have hD : discr (IntermediateField.adjoin ℚ {r}) = -(7 : ℕ) :=
    discr_eq_neg_of_sq_eq h2 (by norm_num : Nat.Prime 7).squarefree rfl
      (r := IntermediateField.AdjoinSimple.gen ℚ r) (Subtype.ext (by simp [hr]; rfl))
  obtain ⟨χ, hχ⟩ := exists_isKroneckerChar_of_discr h2 hD
  exact ⟨_, hK, χ, h2, hD, hχ⟩
end GlobalTheory
