-- Prove2me | solution 1 for N25.unitAnalytic25_affine_leading_limit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:32.208827+00:00
-- url     : https://prove2.me/submissions/898f47e2-1b4f-4276-8bf4-f0c5fdd7ab59

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_four_factor_exp_ratio_tendsto
import Theorems.Thm_N25_unitAnalytic25_siegel_ratio
import Theorems.Thm_N25_siegelFun25_affine_nonzero_leading_limit
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_N25_siegelIndex25_nontrivial
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false

open Filter Topology

namespace N25

theorem _root_.solution
    (i : Fin 5) (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (φ : UpperHalfPlane → UpperHalfPlane) (a b : ℝ) (ha : 0 < a)
    (hφ : ∀ τ : UpperHalfPlane, (φ τ : ℂ) = (a : ℂ)*(τ : ℂ)+(b : ℂ))
    (harg : ∀ τ : UpperHalfPlane, ((B • φ τ : UpperHalfPlane) : ℂ) =
      25*((A • τ : UpperHalfPlane) : ℂ)) :
    let β : ℕ → ℝ := fun g =>
      (((((g : ℤ)*B 0 0)%25 : ℤ) : ℝ)/25)^2 -
        ((((g : ℤ)*B 0 0)%25 : ℤ) : ℝ)/25 + 1/6
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto
      (fun τ : UpperHalfPlane => unitAnalytic25 i (A • τ) /
        Complex.exp (Real.pi*Complex.I*
          (((β (unitResidues25 i).1+β (unitResidues25 i).2-
            (β (unitResidues25 (i+1)).1+β (unitResidues25 (i+1)).2))*a : ℝ) : ℂ)*(τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c) := by
  classical
  let β : ℕ → ℝ := fun g =>
    (((((g : ℤ)*B 0 0)%25 : ℤ) : ℝ)/25)^2 -
      ((((g : ℤ)*B 0 0)%25 : ℤ) : ℝ)/25 + 1/6
  let G : Fin 4 → ℕ := ![(unitResidues25 i).1, (unitResidues25 i).2,
    (unitResidues25 (i+1)).1, (unitResidues25 (i+1)).2]
  let f (j : Fin 4) (τ : UpperHalfPlane) : ℂ :=
    ModularCurve.siegelFun 25 ((G j : ℤ)*B 0 0) ((G j : ℤ)*B 0 1) (φ τ : ℂ)
  let r (j : Fin 4) : ℝ := β (G j)*a
  have hres (k : Fin 5) :
      (0 < (unitResidues25 k).1 ∧ (unitResidues25 k).1 < 25) ∧
      (0 < (unitResidues25 k).2 ∧ (unitResidues25 k).2 < 25) := by
    fin_cases k <;> norm_num [unitResidues25]
  have hg (j : Fin 4) : 0 < G j ∧ G j < 25 := by
    fin_cases j
    · simpa [G] using (hres i).1
    · simpa [G] using (hres i).2
    · simpa [G] using (hres (i+1)).1
    · simpa [G] using (hres (i+1)).2
  have hlim (j : Fin 4) : ∃ c : ℂ, c ≠ 0 ∧ Tendsto
      (fun τ : UpperHalfPlane => f j τ /
        Complex.exp (Real.pi*Complex.I*(r j : ℂ)*(τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c) := by
    have hnot : ¬(25 : ℤ) ∣ (G j : ℤ) := by
      rintro ⟨k, hk⟩
      have hp := (hg j).1
      have hq := (hg j).2
      omega
    obtain ⟨c, hc, hl⟩ := siegelFun25_affine_nonzero_leading_limit
      ((G j : ℤ)*B 0 0) ((G j : ℤ)*B 0 1)
      (siegelIndex25_nontrivial B (G j : ℤ) hnot) φ a b ha hφ
    refine ⟨c, hc, ?_⟩
    simpa [f, r, β, mul_assoc] using hl
  choose c hc hl using hlim
  have ht := four_factor_exp_ratio_tendsto f r c hc hl
  have hrate : r 0+r 1-(r 2+r 3) =
      (β (unitResidues25 i).1+β (unitResidues25 i).2-
        (β (unitResidues25 (i+1)).1+β (unitResidues25 (i+1)).2))*a := by
    simp [r, G] <;> ring
  rw [hrate] at ht
  refine ⟨(c 0*c 1)/(c 2*c 3),
    div_ne_zero (mul_ne_zero (hc 0) (hc 1)) (mul_ne_zero (hc 2) (hc 3)), ?_⟩
  apply ht.congr'
  filter_upwards [] with τ
  rw [unitAnalytic25_siegel_ratio i A B φ harg τ]
  rfl

end N25
