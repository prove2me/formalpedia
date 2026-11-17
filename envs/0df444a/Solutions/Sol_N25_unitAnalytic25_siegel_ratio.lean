-- Prove2me | solution 1 for N25.unitAnalytic25_siegel_ratio
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:31.371999+00:00
-- url     : https://prove2.me/submissions/580bcac0-0fbf-45e6-90d6-ea46f4557627

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_siegelFun_specialLinearGroup_smul

set_option autoImplicit false

namespace N25

/-- A dilation-compatible matrix action expresses the original unpowered unit
as a quotient of four transformed Siegel functions; its common multiplier cancels. -/
theorem _root_.solution
    (i : Fin 5) (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (φ : UpperHalfPlane → UpperHalfPlane)
    (hφ : ∀ τ : UpperHalfPlane, ((B • φ τ : UpperHalfPlane) : ℂ) =
      25*((A • τ : UpperHalfPlane) : ℂ)) (τ : UpperHalfPlane) :
    unitAnalytic25 i (A • τ) =
      (ModularCurve.siegelFun 25
          (((unitResidues25 i).1 : ℤ) * B 0 0) (((unitResidues25 i).1 : ℤ) * B 0 1) (φ τ : ℂ) *
        ModularCurve.siegelFun 25
          (((unitResidues25 i).2 : ℤ) * B 0 0) (((unitResidues25 i).2 : ℤ) * B 0 1) (φ τ : ℂ)) /
      (ModularCurve.siegelFun 25
          (((unitResidues25 (i+1)).1 : ℤ) * B 0 0) (((unitResidues25 (i+1)).1 : ℤ) * B 0 1) (φ τ : ℂ) *
        ModularCurve.siegelFun 25
          (((unitResidues25 (i+1)).2 : ℤ) * B 0 0) (((unitResidues25 (i+1)).2 : ℤ) * B 0 1) (φ τ : ℂ)) := by
  obtain ⟨μ, hμ, ht⟩ := ModularCurve.siegelFun_specialLinearGroup_smul 25 B
  have hμne : μ ≠ 0 := by
    intro hz
    rw [hz] at hμ
    norm_num at hμ
  have E (g : ℕ) : etaAnalytic25 g (A • τ) = (-μ) *
      ModularCurve.siegelFun 25 ((g : ℤ)*B 0 0) ((g : ℤ)*B 0 1) (φ τ : ℂ) := by
    unfold etaAnalytic25
    rw [← hφ τ, ht]
    simp only [zero_mul, add_zero] <;> ring
  have P (g h : ℕ) : etaAnalytic25 g (A • τ) * etaAnalytic25 h (A • τ) = μ^2 *
      (ModularCurve.siegelFun 25 ((g : ℤ)*B 0 0) ((g : ℤ)*B 0 1) (φ τ : ℂ) *
        ModularCurve.siegelFun 25 ((h : ℤ)*B 0 0) ((h : ℤ)*B 0 1) (φ τ : ℂ)) := by
    rw [E, E]
    ring
  unfold unitAnalytic25
  rw [P, P]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hμne)

end N25
