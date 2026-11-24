-- Prove2me | solution 1 for GlobalTheory.SymbolOne.deriv_prod_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:25:55.329147+00:00
-- url     : https://prove2.me/submissions/3f5c6c9e-aadd-451c-a966-3a5f954d4f66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Theorems.Thm_GlobalTheory_SymbolOne_prod_pow_mem
import Theorems.Thm_GlobalTheory_SymbolOne_sum_update_pred
import Theorems.Thm_GlobalTheory_SymbolOne_deriv_prod_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.SymbolOne
variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SymbolOne
theorem _root_.solution (D : Derivation k A A) (I : Ideal A) (lam : ι → A) (hlam : ∀ l, lam l ∈ I)
    (a : ι → ℕ) (l₀ : ι) (r : k)
    (hD : ∀ l, a l ≠ 0 → D (lam l) - algebraMap k A (if l = l₀ then r else 0) ∈ I) (E : A) :
    D ((∏ l, lam l ^ a l) * E) -
      ((a l₀ : k) * r) • ((∏ l, lam l ^ Function.update a l₀ (a l₀ - 1) l) * E) ∈ I ^ (∑ l, a l) := by
  have h1 : ∑ j, (a j : A) * (∏ l, lam l ^ Function.update a j (a j - 1) l) *
      (D (lam j) - algebraMap k A (if j = l₀ then r else 0)) ∈ I ^ (∑ l, a l) := by
    refine Ideal.sum_mem _ fun j _ => ?_
    by_cases hj : a j = 0
    · simp [hj]
    · rw [← sum_update_pred a j hj, pow_succ, mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (prod_pow_mem I lam hlam _) (hD j hj))
  have h2 : ∑ j, (a j : A) * (∏ l, lam l ^ Function.update a j (a j - 1) l) *
      algebraMap k A (if j = l₀ then r else 0) =
      (a l₀ : A) * (∏ l, lam l ^ Function.update a l₀ (a l₀ - 1) l) * algebraMap k A r := by
    rw [Finset.sum_eq_single l₀]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  simp only [mul_sub, Finset.sum_sub_distrib] at h1
  rw [h2, ← deriv_prod_pow] at h1
  have h3 := add_mem (Ideal.mul_mem_right (D E) _ (prod_pow_mem I lam hlam a))
    (Ideal.mul_mem_right E _ h1)
  convert h3 using 1
  rw [Derivation.leibniz, Algebra.smul_def (_ * r)]
  simp only [smul_eq_mul, map_mul, map_natCast]
  ring
end GlobalTheory.SymbolOne
