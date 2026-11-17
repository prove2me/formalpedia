-- Prove2me | solution 1 for N25.unitAnalytic25_cusp_leading_limit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:13.034878+00:00
-- url     : https://prove2.me/submissions/c5358b3f-2837-4c28-93ea-20d3a3bc5fce

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_four_factor_exp_ratio_tendsto
import Theorems.Thm_N25_unitAnalytic25_siegel_ratio
import Theorems.Thm_N25_siegelFun25_affine_nonzero_leading_limit
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_N25_siegelIndex25_nontrivial
import Theorems.Thm_N25_matrix_det25_triangular
import Theorems.Thm_N25_dilation25_triangular_action
import Theorems.Thm_N25_unitResidues25_bernoulli_lower_int
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false

open Filter Topology

namespace N25

private theorem unit_leading_of_affine
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

/-- At every transformed cusp, the original unpowered unit has a nonzero
normalized leading limit whose real q-exponent is at least minus three. -/
theorem _root_.solution
    (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ ℓ : ℝ, -3 ≤ ℓ ∧ ∃ c : ℂ, c ≠ 0 ∧ Filter.Tendsto
      (fun τ : UpperHalfPlane => unitAnalytic25 i (A • τ) /
        Complex.exp (2*Real.pi*Complex.I*(ℓ : ℂ)*(τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c) := by
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![25,0;0,1] * (A : Matrix (Fin 2) (Fin 2) ℤ)
  have hM : M.det = 25 := by
    dsimp only [M]
    rw [Matrix.det_mul, A.prop]
    norm_num [Matrix.det_fin_two]
  obtain ⟨B, d, e, v, _, hd, he, hde, hm⟩ := matrix_det25_triangular M hM
  let a : ℝ := (d : ℝ)/(e : ℝ)
  let b : ℝ := (v : ℝ)/(e : ℝ)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have ha : 0 < a := div_pos hdR heR
  let φ (τ : UpperHalfPlane) : UpperHalfPlane :=
    ⟨(a : ℂ)*(τ : ℂ)+(b : ℂ), by simpa using mul_pos ha τ.im_pos⟩
  have hφ (τ : UpperHalfPlane) : (φ τ : ℂ) = (a : ℂ)*(τ : ℂ)+(b : ℂ) := rfl
  have harg (τ : UpperHalfPlane) : ((B • φ τ : UpperHalfPlane) : ℂ) =
      25*((A • τ : UpperHalfPlane) : ℂ) := by
    obtain ⟨z, hz, hact⟩ := dilation25_triangular_action A B (d : ℤ) e v
      (by exact_mod_cast hd) he hm τ
    have hf : φ τ = z := by
      apply UpperHalfPlane.ext
      rw [hz]
      dsimp only [φ, a, b]
      push_cast
      ring
    rw [hf]
    exact hact
  let β : ℕ → ℝ := fun g =>
    (((((g : ℤ)*B 0 0)%25 : ℤ) : ℝ)/25)^2 -
      ((((g : ℤ)*B 0 0)%25 : ℤ) : ℝ)/25 + 1/6
  let βQ : ℕ → ℚ := fun g =>
    ((((B 0 0*(g : ℤ))%25 : ℤ) : ℚ))^2/625 -
      (((B 0 0*(g : ℤ))%25 : ℤ) : ℚ)/25 + 1/6
  let diff : ℝ := β (unitResidues25 i).1+β (unitResidues25 i).2-
    (β (unitResidues25 (i+1)).1+β (unitResidues25 (i+1)).2)
  have hβ (g : ℕ) : β g = (βQ g : ℝ) := by
    dsimp only [β, βQ]
    rw [mul_comm (g : ℤ) (B 0 0)]
    push_cast
    ring
  have hlower : (-6/25 : ℝ) ≤ diff := by
    dsimp only [diff]
    simp only [hβ]
    dsimp only [βQ]
    have hq := unitResidues25_bernoulli_lower_int (B 0 0) i
    dsimp only at hq
    exact_mod_cast hq
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast (show (1 : ℤ) ≤ e by omega)
  have hdeR : (d : ℝ)*(e : ℝ) = 25 := by exact_mod_cast hde
  have hd25 : (d : ℝ) ≤ 25 := by
    nlinarith [mul_nonneg hdR.le (sub_nonneg.mpr he1)]
  have ha25 : a ≤ 25 := by
    apply (div_le_iff₀ heR).mpr
    nlinarith
  let ℓ : ℝ := a/2*diff
  have hℓ : -3 ≤ ℓ := by
    dsimp only [ℓ]
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hlower)]
  obtain ⟨c, hc, hl⟩ := unit_leading_of_affine i A B φ a b ha hφ harg
  refine ⟨ℓ, hℓ, c, hc, ?_⟩
  apply hl.congr'
  filter_upwards [] with τ
  change unitAnalytic25 i (A • τ) /
      Complex.exp (Real.pi*Complex.I*((diff*a : ℝ) : ℂ)*(τ : ℂ)) = _
  congr 1
  congr 1
  dsimp only [ℓ]
  push_cast
  ring

end N25
