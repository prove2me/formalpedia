-- Prove2me | solution 1 for GlobalTheory.TensorLat.exists_nsmul_stdLat_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:49:20.904497+00:00
-- url     : https://prove2.me/submissions/66bd60c4-cef0-45c4-9f13-0b313c464095

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Theorems.Thm_GlobalTheory_DualFamily_herm_one_eq
import Theorems.Thm_GlobalTheory_TensorLat_mem_stdLat
import Theorems.Thm_GlobalTheory_exists_dual_family
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}
namespace GlobalTheory.TensorLat
theorem _root_.solution (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ u ∈ stdLat E n, N • u ∈ Λ' := by
  classical
  have : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨-, m, v, w, hv, hw, hexp⟩ := GlobalTheory.exists_dual_family Λ' hfg hint hdual
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image fun p : Fin m × Fin n => cc (w p.1 p.2))
  have hN : ((y.natAbs : ℕ) : E) = (y : E) ∨ ((y.natAbs : ℕ) : E) = -(y : E) := by
    rcases Int.natAbs_eq y with hq | hq
    · left
      conv_rhs => rw [hq]
      simp
    · right
      conv_rhs => rw [hq]
      simp
  have hyz : ∀ i a, IsIntegral ℤ ((y.natAbs : E) * cc (w i a)) := by
    intro i a
    have h := hy _ (Finset.mem_image.2 ⟨(i, a), Finset.mem_univ _, rfl⟩)
    rw [zsmul_eq_mul] at h
    rcases hN with e | e
    · rw [e]
      exact h
    · rw [e, neg_mul]
      exact h.neg
  refine ⟨y.natAbs, Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hy0), fun u hu => ?_⟩
  have hc : ∀ i, IsIntegral ℤ ((y.natAbs : E) * herm 1 u (w i)) := by
    intro i
    rw [DualFamily.herm_one_eq, Finset.mul_sum]
    refine IsIntegral.sum _ fun a _ => ?_
    rw [mul_left_comm]
    exact (mem_stdLat.1 hu a).mul (hyz i a)
  have hmem : ∑ i, (⟨_, hc i⟩ : 𝓞 E) • v i ∈ Λ' :=
    Λ'.sum_mem fun i _ => Λ'.smul_mem _ (hv i)
  convert hmem using 1
  conv_lhs => rw [hexp u]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  rw [Algebra.smul_def, ← mul_assoc]
  rfl
end GlobalTheory.TensorLat
