-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/af57ebb9-100b-5686-bf6c-48797c4c8d13

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open MeasureTheory
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel

local notation "μbox" =>
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn whittaker3 AdelicGL upperUnipotent3 upperUnipotent3_coe"
namespace GlobalWhittakerLaw
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

section Law

private theorem whittaker3_upperUnipotent3_mul (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsPrincipalInvariantAddChar ℚ ψ) {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hΦ : ∀ (x y z : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) * g) = Φ g)
    (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ (upperUnipotent3 x y z * g) =
      ψ (x + y) * whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ g := by
  show (∫ x', ∫ y', ∫ z', Φ (upperUnipotent3 x' y' z' * (upperUnipotent3 x y z * g)) * ψ (-(x' + y'))
      ∂μbox ∂μbox ∂μbox) =
    ψ (x + y) * ∫ x', ∫ y', ∫ z', Φ (upperUnipotent3 x' y' z' * g) * ψ (-(x' + y')) ∂μbox ∂μbox ∂μbox

  have h1 : ∀ x' y' z' : AdeleRing (𝓞 ℚ) ℚ, Φ (upperUnipotent3 x' y' z' * (upperUnipotent3 x y z * g)) =
      Φ (upperUnipotent3 (x' + x) (y' + y) (z' + (z + x' * y)) * g) := by
    intro x' y' z'
    rw [← mul_assoc, upperUnipotent3_mul, add_assoc z' z]
  simp_rw [h1]

  have h2 : ∀ x' y' : AdeleRing (𝓞 ℚ) ℚ,
      (∫ z', Φ (upperUnipotent3 (x' + x) (y' + y) (z' + (z + x' * y)) * g) * ψ (-(x' + y')) ∂μbox) =
        ∫ z', Φ (upperUnipotent3 (x' + x) (y' + y) z' * g) * ψ (-(x' + y')) ∂μbox := fun x' y' =>
    integral_cond_adelicBox_comp_add_right
      (f := fun z'' => Φ (upperUnipotent3 (x' + x) (y' + y) z'' * g) * ψ (-(x' + y')))
      (fun α z'' => by simp only [apply_corner_add hΦ]) (z + x' * y)
  simp_rw [h2]

  have h3 : ∀ x' : AdeleRing (𝓞 ℚ) ℚ,
      (∫ y', ∫ z', Φ (upperUnipotent3 (x' + x) (y' + y) z' * g) * ψ (-(x' + y')) ∂μbox ∂μbox) =
        ∫ y', ∫ z', Φ (upperUnipotent3 (x' + x) y' z' * g) * ψ (-(x' + y' - y)) ∂μbox ∂μbox := by
    intro x'
    have e : ∀ y'' : AdeleRing (𝓞 ℚ) ℚ, x' + (y'' + y) - y = x' + y'' := fun y'' => by ring
    have key := integral_cond_adelicBox_comp_add_right
      (f := fun y'' => ∫ z', Φ (upperUnipotent3 (x' + x) y'' z' * g) * ψ (-(x' + y'' - y)) ∂μbox)
      (fun α y'' => by
        have eψ : ψ (-(x' + (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y'') - y)) = ψ (-(x' + y'' - y)) := by
          rw [show -(x' + (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + y'') - y) =
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-α) + -(x' + y'' - y) by rw [map_neg]; ring,
            addChar_algebraMap_add hψ]
        simp only [apply_middle_add hΦ, eψ])
      y
    simpa only [e] using key
  simp_rw [h3]

  have h4 : (∫ x', ∫ y', ∫ z', Φ (upperUnipotent3 (x' + x) y' z' * g) * ψ (-(x' + y' - y))
      ∂μbox ∂μbox ∂μbox) =
        ∫ x', ∫ y', ∫ z', Φ (upperUnipotent3 x' y' z' * g) * ψ (-(x' - x + y' - y)) ∂μbox ∂μbox ∂μbox := by
    have e : ∀ x'' : AdeleRing (𝓞 ℚ) ℚ, x'' + x - x = x'' := fun x'' => by ring
    have key := integral_cond_adelicBox_comp_add_right
      (f := fun x'' => ∫ y', ∫ z', Φ (upperUnipotent3 x'' y' z' * g) * ψ (-(x'' - x + y' - y)) ∂μbox ∂μbox)
      (fun α x'' => by
        have eψ : ∀ y' : AdeleRing (𝓞 ℚ) ℚ,
            ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + x'' - x + y' - y)) = ψ (-(x'' - x + y' - y)) := fun y' => by
          rw [show -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α + x'' - x + y' - y) =
              algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-α) + -(x'' - x + y' - y) by rw [map_neg]; ring,
            addChar_algebraMap_add hψ]
        have ez : ∀ y' : AdeleRing (𝓞 ℚ) ℚ,
            (∫ z', Φ (upperUnipotent3 x'' y' (z' - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * y') * g) *
                ψ (-(x'' - x + y' - y)) ∂μbox) =
              ∫ z', Φ (upperUnipotent3 x'' y' z' * g) * ψ (-(x'' - x + y' - y)) ∂μbox := fun y' => by
          simpa only [sub_eq_add_neg] using integral_cond_adelicBox_comp_add_right
            (f := fun z'' => Φ (upperUnipotent3 x'' y' z'' * g) * ψ (-(x'' - x + y' - y)))
            (fun β z'' => by simp only [apply_corner_add hΦ]) (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * y'))
        simp only [apply_left_add hΦ, eψ, ez])
      x
    simpa only [e] using key
  rw [h4]

  have h5 : ∀ x' y' z' : AdeleRing (𝓞 ℚ) ℚ, Φ (upperUnipotent3 x' y' z' * g) * ψ (-(x' - x + y' - y)) =
      ψ (x + y) * (Φ (upperUnipotent3 x' y' z' * g) * ψ (-(x' + y'))) := by
    intro x' y' z'
    rw [show -(x' - x + y' - y) = (x + y) + -(x' + y') by ring, AddChar.map_add_eq_mul]
    ring
  simp_rw [h5, integral_const_mul]

end Law

end LanglandsTunnell.CubicInduction.GlobalWhittakerLaw

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq.LanglandsTunnell.CubicInduction"

theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsPrincipalInvariantAddChar ℚ ψ)
    (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hΦ : ∀ (x y z : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (upperUnipotent3 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) y)
        (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) z) * g) = Φ g) :
    IsGL3PsiWhittakerFn ψ (whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ Φ) := by
  exact LanglandsTunnell.CubicInduction.GlobalWhittakerLaw.whittaker3_upperUnipotent3_mul D U gen hψ hΦ

end S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isGL3PsiWhittakerFn_whittaker3_of_forall_upperUnipotent3_mul_eq (solution)
