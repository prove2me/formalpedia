-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f5da8ea6-590f-599e-8c91-fdb3e9e9e388

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.principalSeries3 CubicInduction.upperUnipotent3 CubicInduction.iotaGL CubicInduction.LocalGL3 TateLocal.higherUnitsAt CubicInduction.diagUnitGL2 CubicInduction.lowerUnipotent21 CubicInduction.eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnitGL2 diagUnits2 coe_diagUnits2 lowerUnipotent21 eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level"
namespace ClosedCell
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level.LanglandsTunnell.CubicInduction"

section GL2

variable {F : Type*} [Field F]

def lowerU (s : F) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : F), 0; s, 1] (by simp [Matrix.det_fin_two_of])

@[scoped simp] theorem coe_lowerU (s : F) : ((lowerU s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; s, 1] := rfl

def weyl : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : F), 1; 1, 0] (by simp [Matrix.det_fin_two_of])

@[scoped simp] theorem coe_weyl : ((weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

theorem det_coe_ne_zero (k : GL (Fin 2) F) : (k : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det k).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h

theorem factor_of_corner_ne_zero (k : GL (Fin 2) F) (hd : (k : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0) :
    ∃ (p : Fˣ) (x : F),
      k = diagUnits2 p (Units.mk0 _ hd) * AutomorphicForm.unipotentGL2 x *
        lowerU ((k : Matrix (Fin 2) (Fin 2) F) 1 0 / (k : Matrix (Fin 2) (Fin 2) F) 1 1) := by
  have hdet := det_coe_ne_zero k
  have hp : (k : Matrix (Fin 2) (Fin 2) F).det / (k : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := div_ne_zero hdet hd
  refine ⟨Units.mk0 _ hp, (k : Matrix (Fin 2) (Fin 2) F) 0 1 / ((k : Matrix (Fin 2) (Fin 2) F).det /
    (k : Matrix (Fin 2) (Fin 2) F) 1 1), ?_⟩
  refine Units.ext ?_
  simp only [Units.val_mul, coe_diagUnits2, AutomorphicForm.unipotentGL2_coe, coe_lowerU, Units.val_mk0]
  rw [Matrix.det_fin_two] at hp ⊢
  have hdet' : (k : Matrix (Fin 2) (Fin 2) F) 0 0 * (k : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (k : Matrix (Fin 2) (Fin 2) F) 0 1 * (k : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    rwa [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring_nf

theorem factor_of_corner' (k : GL (Fin 2) F) (hc : (k : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    ∃ (p : Fˣ) (x : F),
      k = diagUnits2 p (Units.mk0 _ hc) * AutomorphicForm.unipotentGL2 x *
        (weyl * AutomorphicForm.unipotentGL2 ((k : Matrix (Fin 2) (Fin 2) F) 1 1 / (k : Matrix (Fin 2) (Fin 2) F) 1 0)) := by
  have hdet := det_coe_ne_zero k
  have hp : -(k : Matrix (Fin 2) (Fin 2) F).det / (k : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hdet) hc
  refine ⟨Units.mk0 _ hp, (k : Matrix (Fin 2) (Fin 2) F) 0 0 / (-(k : Matrix (Fin 2) (Fin 2) F).det /
    (k : Matrix (Fin 2) (Fin 2) F) 1 0), ?_⟩
  refine Units.ext ?_
  simp only [Units.val_mul, coe_diagUnits2, AutomorphicForm.unipotentGL2_coe, coe_weyl, Units.val_mk0]
  rw [Matrix.det_fin_two] at hp ⊢
  have hdet' : (k : Matrix (Fin 2) (Fin 2) F) 0 0 * (k : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (k : Matrix (Fin 2) (Fin 2) F) 0 1 * (k : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    rwa [Matrix.det_fin_two] at hdet
  have hdet'' : (k : Matrix (Fin 2) (Fin 2) F) 0 1 * (k : Matrix (Fin 2) (Fin 2) F) 1 0 -
      (k : Matrix (Fin 2) (Fin 2) F) 0 0 * (k : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h; apply hdet'; linear_combination -h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring_nf

theorem iotaGL_lowerU (s : F) : iotaGL (lowerU s) = lowerUnipotent21 s := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, lowerU]

end GL2

section Local

variable {v : HeightOneSpectrum (𝓞 ℚ)} {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}

theorem iotaGL_diagUnits2 (u₁ u₂ : (v.adicCompletion ℚ)ˣ) :
    (iotaGL (diagUnits2 u₁ u₂) : LocalGL3 v) = diagonal3 v ![u₁, u₂, 1] := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, diagonal3, Matrix.diagonal]

theorem norm_eq_one_of_valued_eq_one {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, hu, map_one, NNReal.coe_one]

theorem apply_iotaGL_diagUnits2_mul {Φ : LocalGL3 v → ℂ} (hΦ : Φ ∈ principalSeries3 v χ)
    (u₁ u₂ : (v.adicCompletion ℚ)ˣ) (hu₁ : Valued.v (u₁ : v.adicCompletion ℚ) = 1)
    (_hu₂ : Valued.v (u₂ : v.adicCompletion ℚ) = 1) (g : LocalGL3 v) :
    Φ (iotaGL (diagUnits2 u₁ u₂) * g) = ((χ 0 u₁ : ℂˣ) : ℂ) * ((χ 1 u₂ : ℂˣ) : ℂ) * Φ g := by
  rw [iotaGL_diagUnits2, apply_diagonal3_mul_of_mem_principalSeries3 hΦ]
  simp only [torusChar3, halfModulus3, Fin.prod_univ_three]
  simp [norm_eq_one_of_valued_eq_one hu₁]

theorem apply_iotaGL_diagUnits2_mul' {Φ : LocalGL3 v → ℂ} (hΦ : Φ ∈ principalSeries3 v χ)
    (p d : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    Φ (iotaGL (diagUnits2 p d) * g) = torusChar3 v χ ![p, d, 1] * halfModulus3 v ![p, d, 1] * Φ g := by
  rw [iotaGL_diagUnits2, apply_diagonal3_mul_of_mem_principalSeries3 hΦ]

theorem lowerU_inv (y : v.adicCompletion ℚ) : (lowerU y)⁻¹ = lowerU (-y) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, coe_lowerU, coe_lowerU, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_mul_unipotent_inv (y : v.adicCompletion ℚ) :
    (weyl * AutomorphicForm.unipotentGL2 y)⁻¹ = AutomorphicForm.unipotentGL2 (-y) * weyl := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_weyl, AutomorphicForm.unipotentGL2_coe,
    AutomorphicForm.unipotentGL2_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem integral_lowerU {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1) :
    (∀ i j, Valued.v ((lowerU y : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (((lowerU y)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1 := by
  have hy' : Valued.v (-y) ≤ 1 := by rwa [Valuation.map_neg]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hy]
  · rw [lowerU_inv]
    fin_cases i <;> fin_cases j <;> simp [hy]

theorem integral_weyl_mul_unipotent {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1) :
    (∀ i j, Valued.v ((weyl * AutomorphicForm.unipotentGL2 y : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (((weyl * AutomorphicForm.unipotentGL2 y)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1 := by
  have h1 : (((weyl * AutomorphicForm.unipotentGL2 y : GL (Fin 2) (v.adicCompletion ℚ))) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, y] := by
    rw [Units.val_mul, coe_weyl, AutomorphicForm.unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : ((((weyl * AutomorphicForm.unipotentGL2 y)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![-y, 1; 1, 0] := by
    rw [weyl_mul_unipotent_inv, Units.val_mul, coe_weyl, AutomorphicForm.unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [h1]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · rw [h2]
    fin_cases i <;> fin_cases j <;> simp [hy]

theorem parabolic_factor (x : LocalGL3 v)
    (h20 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) :
    ∃ (A : GL (Fin 2) (v.adicCompletion ℚ)) (t : (v.adicCompletion ℚ)ˣ) (y z : v.adicCompletion ℚ),
      x = upperUnipotent3 0 y z * diagonal3 v ![1, 1, t] * iotaGL A := by
  have hdetx : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det x).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  set X := (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) with hX
  have hdet3 : X.det = (X 0 0 * X 1 1 - X 0 1 * X 1 0) * X 2 2 := by
    rw [Matrix.det_fin_three, h20, h21]; ring
  have ht : X 2 2 ≠ 0 := fun h => hdetx (by rw [hdet3, h, mul_zero])
  have hA : (!![X 0 0, X 0 1; X 1 0, X 1 1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det ≠ 0 := by
    intro h
    apply hdetx
    rw [hdet3, ← Matrix.det_fin_two_of, h, zero_mul]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA, Units.mk0 _ ht, X 1 2 / X 2 2, X 0 2 / X 2 2, ?_⟩
  have hcoe : ((diagonal3 v ![1, 1, Units.mk0 _ ht] : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, 0, 0; 0, 1, 0; 0, 0, X 2 2] := by
    rw [diagonal3_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have hι : ((iotaGL (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, 1] := by
    rw [coe_iotaGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  refine Units.ext ?_
  change X = _
  rw [Units.val_mul, Units.val_mul, upperUnipotent3_coe, hcoe, hι]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21] <;> field_simp

end Local

end LanglandsTunnell.CubicInduction.ClosedCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level.LanglandsTunnell.CubicInduction.ClosedCell"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level.LanglandsTunnell"

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.ClosedCell in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ₀ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ 0 u ≠ 1)
    (hχ₁ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ 1 u ≠ 1)
    (Φ : LanglandsTunnell.CubicInduction.LocalGL3 v → ℂ)
    (hΦ : Φ ∈ LanglandsTunnell.CubicInduction.principalSeries3 v χ)
    (hdiag : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 →
      Φ (g * LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 u)) = Φ g)
    (hupper : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.upperUnipotent3 s 0 0) = Φ g)
    (hlower : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.lowerUnipotent21 s) = Φ g)
    (x : LanglandsTunnell.CubicInduction.LocalGL3 v)
    (h20 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) :
    Φ x = 0 := by

  set F₀ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ := fun k => Φ (iotaGL k) with hF₀
  have hF₀ : ∀ k : GL (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) → F₀ k = 0 := by
    intro k hk hkinv
    refine LanglandsTunnell.CubicInduction.eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level v b (χ 0) (χ 1)
      hχ₀ hχ₁ F₀ ?_ ?_ ?_ ?_ ?_ k hk hkinv
    · intro u₁ u₂ k _ _ hu₁ hu₂
      simp only [hF₀, map_mul]
      exact apply_iotaGL_diagUnits2_mul hΦ u₁ u₂ hu₁ hu₂ _
    · intro y k _ _ _
      simp only [hF₀, map_mul, iotaGL_unipotentGL2]
      exact apply_upperUnipotent3_mul_of_mem_principalSeries3 hΦ _ _ _ _
    · intro k u hu
      simp only [hF₀, map_mul]
      exact hdiag _ u hu
    · intro k s hs
      simp only [hF₀, map_mul, iotaGL_unipotentGL2]
      exact hupper _ s hs
    · intro k s hs
      simp only [hF₀, map_mul]
      rw [show Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0; s, 1]
          (by simp [Matrix.det_fin_two_of]) = lowerU s from rfl, iotaGL_lowerU]
      exact hlower _ s hs

  obtain ⟨A, t, y, z, rfl⟩ := parabolic_factor x h20 h21
  rw [mul_assoc, apply_upperUnipotent3_mul_of_mem_principalSeries3 hΦ, apply_diagonal3_mul_of_mem_principalSeries3 hΦ]
  suffices h : Φ (iotaGL A) = 0 by rw [h, mul_zero]

  by_cases hcd : Valued.v ((A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0) ≤
      Valued.v ((A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)
  ·
    have hd : (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 ≠ 0 := by
      intro hd
      rw [hd, map_zero, le_zero_iff, map_eq_zero] at hcd
      apply det_coe_ne_zero A
      rw [Matrix.det_fin_two, hd, hcd]; ring
    obtain ⟨p, x', hfac⟩ := factor_of_corner_ne_zero A hd
    have hy : Valued.v ((A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
        (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hcd zero_le'
    rw [hfac, map_mul, map_mul, mul_assoc, apply_iotaGL_diagUnits2_mul' hΦ, iotaGL_unipotentGL2,
      apply_upperUnipotent3_mul_of_mem_principalSeries3 hΦ]
    suffices h : Φ (iotaGL (lowerU ((A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
        (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1))) = 0 by rw [h, mul_zero]
    exact hF₀ _ (integral_lowerU hy).1 (integral_lowerU hy).2
  ·
    push Not at hcd
    have hc : (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 ≠ 0 := by
      intro hc
      rw [hc, map_zero] at hcd
      exact not_lt_zero hcd
    obtain ⟨p, x', hfac⟩ := factor_of_corner' A hc
    have hy : Valued.v ((A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 /
        (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hcd.le zero_le'
    rw [hfac, map_mul, map_mul, mul_assoc, apply_iotaGL_diagUnits2_mul' hΦ, iotaGL_unipotentGL2,
      apply_upperUnipotent3_mul_of_mem_principalSeries3 hΦ]
    suffices h : Φ (iotaGL (weyl * AutomorphicForm.unipotentGL2 ((A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 /
        (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0))) = 0 by rw [h, mul_zero]
    exact hF₀ _ (integral_weyl_mul_unipotent hy).1 (integral_weyl_mul_unipotent hy).2

end S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level (solution)
