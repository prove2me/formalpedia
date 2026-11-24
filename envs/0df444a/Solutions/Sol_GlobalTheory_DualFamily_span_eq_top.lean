-- Prove2me | solution 1 for GlobalTheory.DualFamily.span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:43:04.550025+00:00
-- url     : https://prove2.me/submissions/5a0fe7f1-86d4-471e-b422-391ea07a4578

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Theorems.Thm_GlobalTheory_DualFamily_herm_one_eq
import Theorems.Thm_GlobalTheory_DualFamily_herm_one_symm
import Theorems.Thm_GlobalTheory_DualFamily_exists_herm_eq
import Theorems.Thm_GlobalTheory_DualFamily_eq_zero_of_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.DualFamily
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.DualFamily
namespace _root_.GlobalTheory.DualFamily
theorem _root_.solution {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.DualFamily.exists_herm_eq f
  have hline : ∀ c : E, c • w ∈ Λ := fun c => hdual _ fun y hy => by
    have hfy : f y = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span hy))
    have hsmul : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (c • w) y = c * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 w y := by
      simp only [_root_.GlobalTheory.DualFamily.herm_one_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        mul_assoc]
    rw [hsmul, _root_.GlobalTheory.DualFamily.herm_one_symm w y, ← hw, hfy]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    rw [map_zero, mul_zero]
    exact isIntegral_zero
  have hw0 := _root_.GlobalTheory.DualFamily.eq_zero_of_line Λ hfg w hline
  exact hf0 (LinearMap.ext fun u => by simp [hw u, hw0, _root_.GlobalTheory.DualFamily.herm_one_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc])
end _root_.GlobalTheory.DualFamily
end GlobalTheory.DualFamily
