-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a52535a1-a88e-530c-b2c0-e525f21d587e

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.higherUnitsAt CubicInduction.diagUnitGL2 CubicInduction.diagUnits2"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagUnitGL2 coe_diagUnitGL2 diagUnits2 coe_diagUnits2"
namespace LevelVanishing
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level.LanglandsTunnell.CubicInduction"

section GL2

variable {F : Type*} [Field F]

def lowerU (s : F) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : F), 0; s, 1] (by simp [Matrix.det_fin_two_of])

@[scoped simp] theorem coe_lowerU (s : F) : ((lowerU s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; s, 1] := rfl

def weyl : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : F), 1; 1, 0] (by simp [Matrix.det_fin_two_of])

@[scoped simp] theorem coe_weyl : ((weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

theorem lowerU_add (s t : F) : lowerU (s + t) = lowerU s * lowerU t := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_lowerU, coe_lowerU, coe_lowerU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lowerU_mul_diagUnitGL2 (y : F) (u : Fˣ) :
    lowerU y * diagUnitGL2 u = diagUnits2 u 1 * lowerU (y * u) := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_lowerU, coe_diagUnitGL2, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_mul_unipotent_mul_diagUnitGL2 (x : F) (u : Fˣ) :
    weyl * AutomorphicForm.unipotentGL2 x * diagUnitGL2 u =
      diagUnits2 1 u * (weyl * AutomorphicForm.unipotentGL2 (x * ((u⁻¹ : Fˣ) : F))) := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_weyl, coe_diagUnitGL2, coe_diagUnits2, AutomorphicForm.unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [mul_left_comm, mul_inv_cancel₀ u.ne_zero, mul_one]

theorem factor_of_corner_ne_zero (k : GL (Fin 2) F) (hd : (k : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0) :
    ∃ (p : Fˣ) (x : F),
      (p : F) = (k : Matrix (Fin 2) (Fin 2) F).det / (k : Matrix (Fin 2) (Fin 2) F) 1 1 ∧
      x = (k : Matrix (Fin 2) (Fin 2) F) 0 1 / (p : F) ∧
      k = diagUnits2 p (Units.mk0 _ hd) * AutomorphicForm.unipotentGL2 x *
        lowerU ((k : Matrix (Fin 2) (Fin 2) F) 1 0 / (k : Matrix (Fin 2) (Fin 2) F) 1 1) := by
  have hdet : (k : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det k).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  have hp : (k : Matrix (Fin 2) (Fin 2) F).det / (k : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := div_ne_zero hdet hd
  refine ⟨Units.mk0 _ hp, (k : Matrix (Fin 2) (Fin 2) F) 0 1 / ((k : Matrix (Fin 2) (Fin 2) F).det /
    (k : Matrix (Fin 2) (Fin 2) F) 1 1), rfl, rfl, ?_⟩
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
      (p : F) = -(k : Matrix (Fin 2) (Fin 2) F).det / (k : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
      x = (k : Matrix (Fin 2) (Fin 2) F) 0 0 / (p : F) ∧
      k = diagUnits2 p (Units.mk0 _ hc) * AutomorphicForm.unipotentGL2 x *
        (weyl * AutomorphicForm.unipotentGL2 ((k : Matrix (Fin 2) (Fin 2) F) 1 1 / (k : Matrix (Fin 2) (Fin 2) F) 1 0)) := by
  have hdet : (k : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have h := (Matrix.GeneralLinearGroup.det k).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h
  have hp : -(k : Matrix (Fin 2) (Fin 2) F).det / (k : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hdet) hc
  refine ⟨Units.mk0 _ hp, (k : Matrix (Fin 2) (Fin 2) F) 0 0 / (-(k : Matrix (Fin 2) (Fin 2) F).det /
    (k : Matrix (Fin 2) (Fin 2) F) 1 0), rfl, rfl, ?_⟩
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

end GL2

section Valued

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem valued_sub_one_le_of_mem_higherUnitsAt {b : ℕ} {u : (v.adicCompletion ℚ)ˣ}
    (hu : u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b) :
    Valued.v (u : v.adicCompletion ℚ) = 1 ∧ Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
  obtain ⟨hval, hball⟩ := hu
  refine ⟨hval, ?_⟩
  rcases hball with hb | hle
  · subst hb
    calc Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ max (Valued.v (u : v.adicCompletion ℚ)) (Valued.v (1 : v.adicCompletion ℚ)) :=
          Valuation.map_sub _ _ _
      _ = 1 := by rw [hval, map_one, max_self]
      _ = WithZero.exp (-((0 : ℕ) : ℤ)) := by simp
  · exact hle

theorem valued_det_eq_one {k : GL (Fin 2) (v.adicCompletion ℚ)}
    (hk : ∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (hkinv : ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
  have hle : ∀ (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)), (∀ i j, Valued.v (m i j) ≤ 1) →
      Valued.v m.det ≤ 1 := fun m hm => by
    rw [Matrix.det_fin_two]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul]; exact mul_le_one' (hm 0 0) (hm 1 1)
    · rw [map_mul]; exact mul_le_one' (hm 0 1) (hm 1 0)
  have h1 := hle _ hk
  have h2 := hle _ hkinv
  have hprod : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det *
      ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hv : Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det *
      Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
    rw [← map_mul, hprod, map_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push Not at hlt
  have : Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det *
      Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [hv] at this
  exact lt_irrefl _ this

def IsInt (k : GL (Fin 2) (v.adicCompletion ℚ)) : Prop :=
  (∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) ∧
    ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1

theorem valued_mul_apply_le_one {a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (ha : ∀ i j, Valued.v (a i j) ≤ 1) (hb : ∀ i j, Valued.v (b i j) ≤ 1) (i j : Fin 2) :
    Valued.v ((a * b) i j) ≤ 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (ha _ _) (hb _ _)

theorem isInt_mul {k₁ k₂ : GL (Fin 2) (v.adicCompletion ℚ)} (h₁ : IsInt k₁) (h₂ : IsInt k₂) : IsInt (k₁ * k₂) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]
    exact valued_mul_apply_le_one h₁.1 h₂.1 i j
  · rw [_root_.mul_inv_rev, Units.val_mul]
    exact valued_mul_apply_le_one h₂.2 h₁.2 i j

theorem isInt_unipotent {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) : IsInt (AutomorphicForm.unipotentGL2 x) := by
  have hinv : (((AutomorphicForm.unipotentGL2 x)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, -x; 0, 1] := rfl
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [AutomorphicForm.unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [hinv]
    fin_cases i <;> fin_cases j <;> simp [hx]

theorem lowerU_inv (y : v.adicCompletion ℚ) : (lowerU y)⁻¹ = lowerU (-y) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, coe_lowerU, coe_lowerU, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem isInt_lowerU {y : v.adicCompletion ℚ} (hy : Valued.v y ≤ 1) : IsInt (lowerU y) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_lowerU]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · rw [lowerU_inv, coe_lowerU]
    fin_cases i <;> fin_cases j <;> simp [hy]

theorem weyl_inv : (weyl : GL (Fin 2) (v.adicCompletion ℚ))⁻¹ = weyl := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  rw [Units.val_mul, coe_weyl, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem isInt_weyl : IsInt (weyl : GL (Fin 2) (v.adicCompletion ℚ)) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_weyl]
    fin_cases i <;> fin_cases j <;> simp
  · rw [weyl_inv, coe_weyl]
    fin_cases i <;> fin_cases j <;> simp

end Valued

end LanglandsTunnell.CubicInduction.LevelVanishing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level.LanglandsTunnell.CubicInduction.LevelVanishing"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level.LanglandsTunnell"

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.LevelVanishing in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (b : ℕ) (μ₁ μ₂ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hμ₁ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, μ₁ u ≠ 1)
    (hμ₂ : ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, μ₂ u ≠ 1)
    (F₀ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hleft : ∀ (u₁ u₂ : (v.adicCompletion ℚ)ˣ) (k : GL (Fin 2) (v.adicCompletion ℚ)),
      (∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      Valued.v (u₁ : v.adicCompletion ℚ) = 1 → Valued.v (u₂ : v.adicCompletion ℚ) = 1 →
      F₀ (LanglandsTunnell.CubicInduction.diagUnits2 u₁ u₂ * k) =
        ((μ₁ u₁ : ℂˣ) : ℂ) * ((μ₂ u₂ : ℂˣ) : ℂ) * F₀ k)
    (hleftU : ∀ (x : v.adicCompletion ℚ) (k : GL (Fin 2) (v.adicCompletion ℚ)),
      (∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      Valued.v x ≤ 1 →
      F₀ (AutomorphicForm.unipotentGL2 x * k) = F₀ k)
    (hdiag : ∀ (k : GL (Fin 2) (v.adicCompletion ℚ)) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 → F₀ (k * LanglandsTunnell.CubicInduction.diagUnitGL2 u) = F₀ k)
    (hupper : ∀ (k : GL (Fin 2) (v.adicCompletion ℚ)) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) → F₀ (k * AutomorphicForm.unipotentGL2 s) = F₀ k)
    (hlower : ∀ (k : GL (Fin 2) (v.adicCompletion ℚ)) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      F₀ (k * Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0; s, 1]
        (by simp [Matrix.det_fin_two_of])) = F₀ k)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (hkinv : ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    F₀ k = 0 := by
  have hlower' : ∀ (k : GL (Fin 2) (v.adicCompletion ℚ)) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) → F₀ (k * lowerU s) = F₀ k := hlower

  obtain ⟨u₁, hu₁, hne₁⟩ := hμ₁
  obtain ⟨u₂, hu₂, hne₂⟩ := hμ₂
  obtain ⟨hv₁, hb₁⟩ := valued_sub_one_le_of_mem_higherUnitsAt hu₁
  obtain ⟨hv₂, hb₂⟩ := valued_sub_one_le_of_mem_higherUnitsAt hu₂
  have hne₁' : ((μ₁ u₁ : ℂˣ) : ℂ) ≠ 1 := fun h => hne₁ (Units.ext h)
  have hne₂' : ((μ₂ u₂ : ℂˣ) : ℂ) ≠ 1 := fun h => hne₂ (Units.ext h)
  have hone : Valued.v ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by simp

  have hlow : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ 1 → F₀ (lowerU y) = 0 := by
    intro y hy
    have h1 : F₀ (lowerU y) = ((μ₁ u₁ : ℂˣ) : ℂ) * F₀ (lowerU y) := by
      calc F₀ (lowerU y) = F₀ (lowerU y * diagUnitGL2 u₁) := (hdiag _ _ hv₁).symm
        _ = F₀ (diagUnits2 u₁ 1 * lowerU (y * u₁)) := by rw [lowerU_mul_diagUnitGL2]
        _ = ((μ₁ u₁ : ℂˣ) : ℂ) * F₀ (lowerU (y * u₁)) := by
            have hI : IsInt (lowerU (y * (u₁ : v.adicCompletion ℚ))) := isInt_lowerU (by rw [map_mul, hv₁, mul_one]; exact hy)
            rw [hleft _ _ _ hI.1 hI.2 hv₁ hone, map_one, Units.val_one, mul_one]
        _ = ((μ₁ u₁ : ℂˣ) : ℂ) * F₀ (lowerU y * lowerU (y * ((u₁ : v.adicCompletion ℚ) - 1))) := by
            rw [← lowerU_add]; congr 2; ring
        _ = ((μ₁ u₁ : ℂˣ) : ℂ) * F₀ (lowerU y) := by
            rw [hlower' _ _ ?_]
            rw [map_mul]
            calc Valued.v y * Valued.v ((u₁ : v.adicCompletion ℚ) - 1) ≤ 1 * WithZero.exp (-(b : ℤ)) :=
                  mul_le_mul' hy hb₁
              _ = WithZero.exp (-(b : ℤ)) := one_mul _
    have h2 : (((μ₁ u₁ : ℂˣ) : ℂ) - 1) * F₀ (lowerU y) = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne₁')

  have hwn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → F₀ (weyl * AutomorphicForm.unipotentGL2 x) = 0 := by
    intro x hx
    have hu₂0 : (u₂ : v.adicCompletion ℚ) ≠ 0 := u₂.ne_zero
    have h1 : F₀ (weyl * AutomorphicForm.unipotentGL2 x) = ((μ₂ u₂ : ℂˣ) : ℂ) * F₀ (weyl * AutomorphicForm.unipotentGL2 x) := by
      calc F₀ (weyl * AutomorphicForm.unipotentGL2 x)
          = F₀ (weyl * AutomorphicForm.unipotentGL2 x * diagUnitGL2 u₂) := (hdiag _ _ hv₂).symm
        _ = F₀ (diagUnits2 1 u₂ * (weyl * AutomorphicForm.unipotentGL2 (x * ((u₂⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)))) := by
            rw [weyl_mul_unipotent_mul_diagUnitGL2]
        _ = ((μ₂ u₂ : ℂˣ) : ℂ) * F₀ (weyl * AutomorphicForm.unipotentGL2 (x * ((u₂⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ))) := by
            have hI : IsInt (weyl * AutomorphicForm.unipotentGL2 (x * ((u₂⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ))) :=
              isInt_mul isInt_weyl (isInt_unipotent (by
                rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hv₂, inv_one, mul_one]; exact hx))
            rw [hleft _ _ _ hI.1 hI.2 hone hv₂, map_one, Units.val_one, one_mul]
        _ = ((μ₂ u₂ : ℂˣ) : ℂ) * F₀ (weyl * AutomorphicForm.unipotentGL2 x *
              AutomorphicForm.unipotentGL2 (x * ((u₂⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - x)) := by
            rw [mul_assoc weyl, ← AutomorphicForm.unipotentGL2_add]; congr 3; ring
        _ = ((μ₂ u₂ : ℂˣ) : ℂ) * F₀ (weyl * AutomorphicForm.unipotentGL2 x) := by
            rw [hupper _ _ ?_]
            have hrew : x * ((u₂⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - x =
                x * (1 - (u₂ : v.adicCompletion ℚ)) * ((u₂⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
              rw [Units.val_inv_eq_inv_val]; field_simp
            rw [hrew, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hv₂, inv_one, mul_one,
              ← neg_sub, Valuation.map_neg]
            calc Valued.v x * Valued.v ((u₂ : v.adicCompletion ℚ) - 1) ≤ 1 * WithZero.exp (-(b : ℤ)) :=
                  mul_le_mul' hx hb₂
              _ = WithZero.exp (-(b : ℤ)) := one_mul _
    have h2 : (((μ₂ u₂ : ℂˣ) : ℂ) - 1) * F₀ (weyl * AutomorphicForm.unipotentGL2 x) = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne₂')

  have hdet := valued_det_eq_one hk hkinv

  by_cases hd : Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 1) = 1
  ·
    have hd0 : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 ≠ 0 := fun h => by
      rw [show ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 1) = (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 from rfl,
        h, map_zero] at hd
      exact zero_ne_one hd
    obtain ⟨p, x, hp, hx, hfac⟩ := factor_of_corner_ne_zero k hd0
    have hvp : Valued.v (p : v.adicCompletion ℚ) = 1 := by
      rw [hp, map_div₀, hdet]
      change 1 / Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 1) = 1
      rw [hd, div_one]
    have hvd : Valued.v ((Units.mk0 _ hd0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := hd
    have hvx : Valued.v x ≤ 1 := by
      rw [hx, map_div₀, hvp, div_one]; exact hk 0 1
    have hvy : Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
        (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) ≤ 1 := by
      rw [map_div₀]
      change Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 0) / Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 1) ≤ 1
      rw [hd, div_one]; exact hk 1 0
    have hI₁ : IsInt (lowerU ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 /
        (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)) := isInt_lowerU hvy
    have hI₂ := isInt_mul (isInt_unipotent hvx) hI₁
    rw [hfac, mul_assoc, hleft _ _ _ hI₂.1 hI₂.2 hvp hvd, hleftU _ _ hI₁.1 hI₁.2 hvx, hlow _ hvy, mul_zero]
  ·
    have hdlt : Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 1) < 1 := lt_of_le_of_ne (hk 1 1) hd
    have hc : Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 0) = 1 := by
      by_contra hc
      have hclt : Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 0) < 1 := lt_of_le_of_ne (hk 1 0) hc
      have : Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det < 1 := by
        rw [Matrix.det_fin_two]
        refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
        · rw [map_mul]
          calc Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0) *
                Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)
              ≤ 1 * Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) := mul_le_mul_left (hk 0 0) _
            _ < 1 := by rw [one_mul]; exact hdlt
        · rw [map_mul]
          calc Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) *
                Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0)
              ≤ 1 * Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0) := mul_le_mul_left (hk 0 1) _
            _ < 1 := by rw [one_mul]; exact hclt
      rw [hdet] at this
      exact lt_irrefl _ this
    have hc0 : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 ≠ 0 := fun h => by
      rw [show ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 0) = (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 from rfl,
        h, map_zero] at hc
      exact zero_ne_one hc
    obtain ⟨p, x, hp, hx, hfac⟩ := factor_of_corner' k hc0
    have hvp : Valued.v (p : v.adicCompletion ℚ) = 1 := by
      rw [hp, map_div₀, Valuation.map_neg, hdet]
      change 1 / Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 0) = 1
      rw [hc, div_one]
    have hvc : Valued.v ((Units.mk0 _ hc0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := hc
    have hvx : Valued.v x ≤ 1 := by
      rw [hx, map_div₀, hvp, div_one]; exact hk 0 0
    have hvt : Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 /
        (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0) ≤ 1 := by
      rw [map_div₀]
      change Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 1) / Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) 1 0) ≤ 1
      rw [hc, div_one]; exact hk 1 1
    have hI₁ : IsInt (weyl * AutomorphicForm.unipotentGL2 ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 /
        (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0)) := isInt_mul isInt_weyl (isInt_unipotent hvt)
    have hI₂ := isInt_mul (isInt_unipotent hvx) hI₁
    rw [hfac, mul_assoc, hleft _ _ _ hI₂.1 hI₂.2 hvp hvc, hleftU _ _ hI₁.1 hI₁.2 hvx, hwn _ hvt, mul_zero]

end S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level (solution)
