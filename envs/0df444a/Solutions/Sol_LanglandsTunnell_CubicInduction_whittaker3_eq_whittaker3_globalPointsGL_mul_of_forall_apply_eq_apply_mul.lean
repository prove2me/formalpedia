-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ed7ab824-9574-571f-b6f2-c41f727befd7

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Theorems.Thm_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open MeasureTheory
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel

local notation "μbox" =>
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "whittaker3 AdelicGL globalPointsGL upperUnipotent3 upperUnipotent3_coe"
namespace CoefficientDilation
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Unipotent

variable {A : Type*} [CommRing A]

private theorem upperUnipotent3_mul (a b c x y z : A) :
    upperUnipotent3 a b c * upperUnipotent3 x y z = upperUnipotent3 (a + x) (b + y) (c + z + a * y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, upperUnipotent3_coe, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end Unipotent

section Invariance

variable {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
  (hΦ : ∀ (x y z : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y)
      (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) * g) = Φ g)
include hΦ

private theorem apply_corner_add (α : ℚ) (a b c : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Φ (upperUnipotent3 a b (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + c) * g) = Φ (upperUnipotent3 a b c * g) := by
  have h := hΦ 0 0 α (upperUnipotent3 a b c * g)
  simp only [map_zero, ← mul_assoc, upperUnipotent3_mul, zero_add, zero_mul, add_zero] at h
  exact h

private theorem apply_middle_add (α : ℚ) (a b c : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Φ (upperUnipotent3 a (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + b) c * g) = Φ (upperUnipotent3 a b c * g) := by
  have h := hΦ 0 α 0 (upperUnipotent3 a b c * g)
  simp only [map_zero, ← mul_assoc, upperUnipotent3_mul, zero_add, zero_mul, add_zero] at h
  exact h

private theorem apply_left_add (α : ℚ) (a b c : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + a) b c * g) =
      Φ (upperUnipotent3 a b (c - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * b) * g) := by
  have h := hΦ α 0 0 (upperUnipotent3 a b (c - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * b) * g)
  simp only [map_zero, ← mul_assoc, upperUnipotent3_mul, zero_add, sub_add_cancel] at h
  exact h

end Invariance

section Character

private theorem addChar_algebraMap_add {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsPrincipalInvariantAddChar ℚ ψ)
    (α : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ) : ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + u) = ψ u := by
  rw [AddChar.map_add_eq_mul, hψ α, one_mul]

end Character

section Box

private theorem setIntegral_adelicBox_comp_add_right {f : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ (α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y) = f y)
    (s : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ y in AdelicBox.adelicBox ℚ, f (y + s) ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
      ∫ y in AdelicBox.adelicBox ℚ, f y ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  set μ : Measure (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ with hμ

  have hf' : ∀ (γ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (γ +ᵥ y) = f y := by
    intro γ y
    obtain ⟨α, hα⟩ := RingHom.mem_range.mp γ.2
    show f ((γ : AdeleRing (𝓞 ℚ) ℚ) + y) = f y
    rw [← hα]
    exact hf α y
  have hbox := AdelicBox.isAddFundamentalDomain_adelicBox ℚ μ

  haveI : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
    refine Function.Surjective.countable (f := fun α : ℚ =>
      (⟨algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α, ⟨α, rfl⟩⟩ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨α, rfl⟩ := RingHom.mem_range.mp hx
    exact ⟨α, rfl⟩

  have hbox' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (s +ᵥ AdelicBox.adelicBox ℚ) μ :=
    hbox.vadd_of_comm s

  have hpre : (fun y : AdeleRing (𝓞 ℚ) ℚ => y + s) ⁻¹' (s +ᵥ AdelicBox.adelicBox ℚ) = AdelicBox.adelicBox ℚ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    rw [show -s + (y + s) = y by abel]
  have hshift := (measurePreserving_add_right μ s).setIntegral_preimage_emb
    (MeasurableEquiv.addRight s).measurableEmbedding f (s +ᵥ AdelicBox.adelicBox ℚ)
  rw [hpre] at hshift
  rw [hshift]
  exact hbox'.setIntegral_eq hbox hf'

private theorem integral_cond_adelicBox_comp_add_right {f : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ (α : ℚ) (y : AdeleRing (𝓞 ℚ) ℚ), f (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y) = f y)
    (s : AdeleRing (𝓞 ℚ) ℚ) : ∫ y, f (y + s) ∂μbox = ∫ y, f y ∂μbox := by
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure,
    setIntegral_adelicBox_comp_add_right hf s]

end Box

section Rational

private theorem globalPointsGL_upperUnipotent3 (x y z : ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (upperUnipotent3 x y z) =
      upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalPointsGL, Matrix.GeneralLinearGroup.map_apply, upperUnipotent3_coe]

private theorem upperUnipotent3_mul_globalPointsGL {a : ℚ} (ha : a ≠ 0) (t : GL (Fin 3) ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) ℚ) = Matrix.diagonal ![a ^ 2, a, 1]) (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    upperUnipotent3 x y z * globalPointsGL 3 (𝓞 ℚ) ℚ t =
      globalPointsGL 3 (𝓞 ℚ) ℚ t * upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * x)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * y)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * z)) := by
  have hu : algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  have h00 : (t : Matrix (Fin 3) (Fin 3) ℚ) 0 0 = a ^ 2 := by simp [ht]
  have h11 : (t : Matrix (Fin 3) (Fin 3) ℚ) 1 1 = a := by simp [ht]
  have h22 : (t : Matrix (Fin 3) (Fin 3) ℚ) 2 2 = 1 := by simp [ht]
  have h01 : (t : Matrix (Fin 3) (Fin 3) ℚ) 0 1 = 0 := by simp [ht]
  have h02 : (t : Matrix (Fin 3) (Fin 3) ℚ) 0 2 = 0 := by simp [ht]
  have h10 : (t : Matrix (Fin 3) (Fin 3) ℚ) 1 0 = 0 := by simp [ht]
  have h12 : (t : Matrix (Fin 3) (Fin 3) ℚ) 1 2 = 0 := by simp [ht]
  have h20 : (t : Matrix (Fin 3) (Fin 3) ℚ) 2 0 = 0 := by simp [ht]
  have h21 : (t : Matrix (Fin 3) (Fin 3) ℚ) 2 1 = 0 := by simp [ht]
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalPointsGL, Matrix.GeneralLinearGroup.map_apply, upperUnipotent3_coe, Matrix.mul_apply,
      Fin.sum_univ_three, h00, h11, h22, h01, h02, h10, h12, h20, h21]
  · linear_combination (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x)) * hu
  · linear_combination (-(z * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ + 1))) * hu
  · linear_combination (-y) * hu

end Rational

end LanglandsTunnell.CubicInduction.CoefficientDilation

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul.LanglandsTunnell.CubicInduction in
theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ ψ' : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsPrincipalInvariantAddChar ℚ ψ)
    (a : ℚ) (hψ' : ∀ x : AdeleRing (𝓞 ℚ) ℚ, ψ' x = ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x))
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (t : GL (Fin 3) ℚ) (ht : (t : Matrix (Fin 3) (Fin 3) ℚ) = Matrix.diagonal ![a ^ 2, a, 1])
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ' Φ g =
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ (globalPointsGL 3 (𝓞 ℚ) ℚ t * g) := by

  have ha : a ≠ 0 := by
    intro h0
    have hdet := (Matrix.GeneralLinearGroup.det t).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, ht, h0, Matrix.det_diagonal] at hdet
    simp [Fin.prod_univ_three] at hdet

  have hΦ : ∀ (x y z : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) * g) = Φ g := fun x y z g => by
    rw [← CoefficientDilation.globalPointsGL_upperUnipotent3]
    exact haut _ g
  show (∫ x, ∫ y, ∫ z, Φ (upperUnipotent3 x y z * g) * ψ' (-(x + y)) ∂μbox ∂μbox ∂μbox) =
    ∫ x, ∫ y, ∫ z, Φ (upperUnipotent3 x y z * (globalPointsGL 3 (𝓞 ℚ) ℚ t * g)) * ψ (-(x + y))
      ∂μbox ∂μbox ∂μbox

  have h1 : ∀ x y z : AdeleRing (𝓞 ℚ) ℚ, Φ (upperUnipotent3 x y z * (globalPointsGL 3 (𝓞 ℚ) ℚ t * g)) =
      Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * y)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * z)) * g) := by
    intro x y z
    rw [← mul_assoc, CoefficientDilation.upperUnipotent3_mul_globalPointsGL ha t ht, mul_assoc, haut]
  simp_rw [h1]

  have h2 : ∀ x y : AdeleRing (𝓞 ℚ) ℚ, ψ' (-(x + y)) =
      ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) := by
    intro x y
    rw [hψ', mul_neg, mul_add]
  simp_rw [h2]

  have h3 : (∫ x, ∫ y, ∫ z, Φ (upperUnipotent3 x y z * g) *
      ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) ∂μbox ∂μbox ∂μbox) =
        ∫ x, ∫ y, ∫ z, Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * x) y z * g) *
          ψ (-(x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) ∂μbox ∂μbox ∂μbox := by
    have e : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * x) = x := fun x => by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
    have key := (NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap ℚ
      (f := fun x => ∫ y, ∫ z, Φ (upperUnipotent3 x y z * g) *
        ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) ∂μbox ∂μbox)
      (fun k x => by
        have eψ : ∀ y : AdeleRing (𝓞 ℚ) ℚ,
            ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k + x) +
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) =
              ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) := fun y => by
          rw [show -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k + x) +
                algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y) =
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-(a * k)) +
                -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y) by
              rw [map_neg, map_mul]; ring,
            CoefficientDilation.addChar_algebraMap_add hψ]
        have ez : ∀ y : AdeleRing (𝓞 ℚ) ℚ,
            (∫ z, Φ (upperUnipotent3 x y (z - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k * y) * g) *
                ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) ∂μbox) =
              ∫ z, Φ (upperUnipotent3 x y z * g) *
                ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) ∂μbox :=
            fun y => by
          simpa only [sub_eq_add_neg] using CoefficientDilation.integral_cond_adelicBox_comp_add_right
            (f := fun z => Φ (upperUnipotent3 x y z * g) *
              ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)))
            (fun β z => by simp only [CoefficientDilation.apply_corner_add hΦ])
            (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k * y))
        simp only [CoefficientDilation.apply_left_add hΦ, eψ, ez])
      a⁻¹ (inv_ne_zero ha)).symm
    simpa only [e] using key
  rw [h3]

  have h4 : ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y, ∫ z, Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * x) y z * g) *
        ψ (-(x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) ∂μbox ∂μbox) =
        ∫ y, ∫ z, Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * x)
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * y) z * g) * ψ (-(x + y)) ∂μbox ∂μbox := by
    intro x
    have e : ∀ y : AdeleRing (𝓞 ℚ) ℚ,
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * y) = y := fun y => by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
    have key := (NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap ℚ
      (f := fun y => ∫ z, Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * x) y z * g) *
        ψ (-(x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) ∂μbox)
      (fun k y => by
        have eψ : ψ (-(x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k + y))) =
            ψ (-(x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y)) := by
          rw [show -(x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k + y)) =
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-(a * k)) + -(x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * y) by
              rw [map_neg, map_mul]; ring,
            CoefficientDilation.addChar_algebraMap_add hψ]
        simp only [CoefficientDilation.apply_middle_add hΦ, eψ])
      a⁻¹ (inv_ne_zero ha)).symm
    simpa only [e] using key
  simp_rw [h4]

  have h5 : ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
      (∫ z, Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * x)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * y) z * g) * ψ (-(x + y)) ∂μbox) =
        ∫ z, Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * y)
          (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * z)) * g) *
            ψ (-(x + y)) ∂μbox := by
    intro x y
    have e : ∀ z : AdeleRing (𝓞 ℚ) ℚ, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (a⁻¹ * a⁻¹) * z =
        algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * z) := fun z => by
      rw [map_mul, mul_assoc]
    have key := (NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap ℚ
      (f := fun z => Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * x)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a⁻¹ * y) z * g) * ψ (-(x + y)))
      (fun k z => by simp only [CoefficientDilation.apply_corner_add hΦ]) (a⁻¹ * a⁻¹)
      (mul_ne_zero (inv_ne_zero ha) (inv_ne_zero ha))).symm
    simpa only [e] using key
  simp_rw [h5]

end S_LanglandsTunnell_CubicInduction_whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_whittaker3_eq_whittaker3_globalPointsGL_mul_of_forall_apply_eq_apply_mul (solution)
