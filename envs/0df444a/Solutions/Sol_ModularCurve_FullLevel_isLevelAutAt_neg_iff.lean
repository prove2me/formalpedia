-- Prove2me | solution 1 for ModularCurve.FullLevel.isLevelAutAt_neg_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/50a69b40-e196-5998-94ad-40ec81a4fa0e

import Mathlib
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isLevelAutAt_neg_iff

set_option autoImplicit false

open scoped MatrixGroups

namespace SignInvariance

open scoped ModularForm
open UpperHalfPlane

theorem slash_neg_of_odd {k : ℤ} (hk : Odd k) (F : ℍ → ℂ) (A : GL (Fin 2) ℝ) :
    F ∣[k] (-A) = -(F ∣[k] A) := by
  ext τ
  rw [Pi.neg_apply, ModularForm.slash_apply, ModularForm.slash_apply, UpperHalfPlane.neg_smul,
    UpperHalfPlane.σ_neg, UpperHalfPlane.denom_neg, hk.neg.neg_zpow]
  have hdet : (-A).det = A.det := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_neg]
  rw [hdet]
  ring

theorem slash_neg_of_even {k : ℤ} (hk : Even k) (F : ℍ → ℂ) (A : GL (Fin 2) ℝ) :
    F ∣[k] (-A) = F ∣[k] A := by
  ext τ
  rw [ModularForm.slash_apply, ModularForm.slash_apply, UpperHalfPlane.neg_smul,
    UpperHalfPlane.σ_neg, UpperHalfPlane.denom_neg, hk.neg.neg_zpow]
  have hdet : (-A).det = A.det := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_neg]
  rw [hdet]

theorem conjElemN_neg (m : ℕ) [NeZero m] (γ : SL(2, ℤ)) :
    ModularCurve.FullLevel.conjElemN m (-γ) = -ModularCurve.FullLevel.conjElemN m γ := by
  rw [Matrix.GeneralLinearGroup.ext_iff]
  intro i j
  simp only [ModularCurve.FullLevel.conjElemN, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Units.val_neg,
    Matrix.neg_apply, Matrix.SpecialLinearGroup.coe_neg, Int.cast_neg]
  fin_cases i <;> fin_cases j <;> simp [neg_div, mul_neg]

theorem one_mem_strictPeriods (N₀ : ℕ) (H : Subgroup (ZMod N₀)ˣ) :
    (1 : ℝ) ∈ ((CohCarrier.GammaH N₀ H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N₀ := by simp [ModularGroup.T]
  have hT : ModularGroup.T ∈ CohCarrier.GammaH N₀ H := by
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hT0, ?_⟩
    have : CohCarrier.gamma0Units N₀ ⟨ModularGroup.T, hT0⟩ = 1 := by
      ext
      rw [CohCarrier.val_gamma0Units]
      simp [CongruenceSubgroup.Gamma0Map, ModularGroup.T]
    rw [this]
    exact one_mem H
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

theorem aux (L : Type) [Field L] [CharZero L] (n : ℕ) (ζ : L) (m : ℕ) [NeZero m]
    (N₀ : ℕ) (H : Subgroup (ZMod N₀)ˣ) (γ : SL(2, ℤ))
    (K : IntermediateField L (LaurentSeries L)) (τ : ↥K ≃ₐ[L] ↥K)
    (h : ModularCurve.FullLevel.IsLevelAutAt L n ζ m N₀ H γ K τ) :
    ModularCurve.FullLevel.IsLevelAutAt L n ζ m N₀ H (-γ) K τ := by
  intro k f g pf pg hf hg hg0 x hx ι hι
  rw [conjElemN_neg]
  rcases Int.even_or_odd k with hk | hk
  · rw [slash_neg_of_even hk, slash_neg_of_even hk]
    exact h k f g pf pg hf hg hg0 x hx ι hι
  · rw [slash_neg_of_odd hk, slash_neg_of_odd hk]
    have h1 := one_mem_strictPeriods N₀ H
    have hf' : ModularCurve.IsIntegralQExp (⇑(-f)) (-pf) := by
      unfold ModularCurve.IsIntegralQExp at hf ⊢
      rw [map_neg, hf]
      exact (ModularFormClass.qExpansion_neg one_pos h1 f).symm
    have hg' : ModularCurve.IsIntegralQExp (⇑(-g)) (-pg) := by
      unfold ModularCurve.IsIntegralQExp at hg ⊢
      rw [map_neg, hg]
      exact (ModularFormClass.qExpansion_neg one_pos h1 g).symm
    have hneg : ∀ p : PowerSeries ℤ, ModularCurve.intSeriesC ℚ (-p) = -ModularCurve.intSeriesC ℚ p := by
      intro p
      simp [ModularCurve.intSeriesC]
    have hg0' : ModularCurve.intSeriesC ℚ (-pg) ≠ 0 := by
      rw [hneg]; exact neg_ne_zero.mpr hg0
    have hx' : ((x : ↥K) : LaurentSeries L) =
        ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ (-pf) / ModularCurve.intSeriesC ℚ (-pg)) := by
      rw [hneg, hneg, neg_div_neg_eq]; exact hx
    have := h k (-f) (-g) (-pf) (-pg) hf' hg' hg0' x hx' ι hι
    rw [ModularForm.coe_neg, ModularForm.coe_neg, SlashAction.neg_slash, SlashAction.neg_slash] at this
    exact this

end SignInvariance

theorem solution
    (L : Type) [Field L] [CharZero L] (n : ℕ) (ζ : L) (m : ℕ) [NeZero m]
    (N₀ : ℕ) (H : Subgroup (ZMod N₀)ˣ) (γ : SL(2, ℤ))
    (K : IntermediateField L (LaurentSeries L)) (τ : ↥K ≃ₐ[L] ↥K) :
    ModularCurve.FullLevel.IsLevelAutAt L n ζ m N₀ H (-γ) K τ ↔
      ModularCurve.FullLevel.IsLevelAutAt L n ζ m N₀ H γ K τ := by
  constructor
  · intro h
    have := SignInvariance.aux L n ζ m N₀ H (-γ) K τ h
    rwa [neg_neg] at this
  · exact SignInvariance.aux L n ζ m N₀ H γ K τ

end S_ModularCurve_FullLevel_isLevelAutAt_neg_iff
end P2MW
export P2MW.S_ModularCurve_FullLevel_isLevelAutAt_neg_iff (solution)
