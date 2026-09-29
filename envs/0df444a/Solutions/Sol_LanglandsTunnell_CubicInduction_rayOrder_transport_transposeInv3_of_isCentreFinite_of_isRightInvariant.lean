-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.rayOrder_transport_transposeInv3_of_isCentreFinite_of_isRightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c2259d44-8d4f-5b38-84d2-958d00b0b2d3

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_norm_whittaker3_archRealLift3_diag_mul_eq_norm_whittaker3_comp_transposeInv3
import Theorems.Thm_LanglandsTunnell_CubicInduction_archPackage_comp_transposeInv3_of_isCentreFinite
import Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_isCuspidalAlong_isModerateGrowth3_dualForm
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum
import Theorems.Thm_LanglandsTunnell_CubicInduction_continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_rayOrder_transport_transposeInv3_of_isCentreFinite_of_isRightInvariant
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicInduction.WhittakerBlock (IsCentreFinite)

namespace ArchPkgInv

theorem archDeriv_aut_cen (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), ψ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = ψ g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), ψ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * ψ g)
    (i j : Fin 3) :
    (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        WhittakerBlock.archDeriv i j ψ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = WhittakerBlock.archDeriv i j ψ g) ∧
      ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        WhittakerBlock.archDeriv i j ψ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * WhittakerBlock.archDeriv i j ψ g := by
  refine ⟨fun γ g => ?_, fun z g => ?_⟩
  · simp only [WhittakerBlock.archDeriv, mul_assoc, haut]
  · simp only [WhittakerBlock.archDeriv, mul_assoc, hcen, deriv_const_mul_field']

theorem word_aut_cen (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), ψ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = ψ g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), ψ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * ψ g)
    (w : List (Fin 3 × Fin 3)) :
    (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) ψ w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) =
          List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) ψ w g) ∧
      ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) ψ w (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) =
          (ω z : ℂ) * List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) ψ w g := by
  induction w with
  | nil => exact ⟨haut, hcen⟩
  | cons ij w ih =>
    simp only [List.foldr_cons]
    exact archDeriv_aut_cen ω _ ih.1 ih.2 ij.1 ij.2

theorem span_pkg (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hmg : IsModerateGrowth3 ℚ f) (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i))
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hu : u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun g => ∑ i, c i * f (g * h * t i)) w}) :
    Continuous u ∧
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) ∧
      ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g := by
  have hcw := (continuous_and_norm_iterate_archDeriv_sum_translate_le_of_isCentreFinite f hc hmg hsa hKf n c t ht
    hz).1
  have hsaV : WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) := by
    intro g
    exact ContDiffOn.sum fun i _ => contDiffOn_const.mul (isArchSmooth3_mul_right f hsa (t i) g)
  induction hu using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨w, h, rfl⟩ := hφ
    have hautV : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        (fun g => ∑ i, c i * f (g * h * t i)) (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) =
          (fun g => ∑ i, c i * f (g * h * t i)) g := by
      intro γ g; simp only [mul_assoc, haut]
    have hcenV : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        (fun g => ∑ i, c i * f (g * h * t i)) (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) =
          (ω z : ℂ) * (fun g => ∑ i, c i * f (g * h * t i)) g := by
      intro z g
      simp only [mul_assoc, hcen, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine ⟨?_, (word_aut_cen ω _ hautV hcenV w).1, (word_aut_cen ω _ hautV hcenV w).2⟩
    obtain ⟨coeff, -, hexp⟩ := exists_continuous_coeff_foldr_archDeriv_mul_right_eq_sum w
    have hfun : (fun g => ∑ i, c i * f (g * h * t i)) = (fun x => (fun y => ∑ i, c i * f (y * t i)) (x * h)) := rfl
    have hrew : List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) (fun g => ∑ i, c i * f (g * h * t i)) w =
        fun g => ∑ f' : Fin w.length → Fin 3 × Fin 3,
          coeff h f' * List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
            (fun x => ∑ i, c i * f (x * t i)) (List.ofFn f') (g * h) := by
      funext g; rw [hfun]; exact hexp _ hsaV h g
    rw [hrew]
    exact continuous_finsetSum _ fun f' _ =>
      (continuous_const.mul ((hcw (List.ofFn f')).comp (continuous_mul_const h)))
  | zero => exact ⟨continuous_const, fun _ _ => rfl, fun z g => by simp⟩
  | add u₁ u₂ _ _ ih₁ ih₂ =>
    refine ⟨ih₁.1.add ih₂.1, fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.add_apply, ih₁.2.1, ih₂.2.1]
    · simp only [Pi.add_apply, ih₁.2.2, ih₂.2.2, mul_add]
  | smul a u _ ih =>
    refine ⟨ih.1.const_smul a, fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.smul_apply, ih.2.1]
    · simp only [Pi.smul_apply, ih.2.2, smul_eq_mul]; ring

end ArchPkgInv

open ArchPkgInv in

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g)
    (hmg : IsModerateGrowth3 ℚ f)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) f)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) f)
    (hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (g * localToAdelic3 v k) = f g)
    (hsa : WhittakerBlock.IsArchSmooth3 f)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1)
    (hz : IsCentreFinite fun x => ∑ i, c i * f (x * t i)) :

    (Continuous fun g => f (transposeInv3 g)) ∧
    (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (transposeInv3 (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g)) = f (transposeInv3 g)) ∧
    (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (transposeInv3 (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)) = (ω⁻¹ z : ℂ) * f (transposeInv3 g)) ∧
    (∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω⁻¹ z : ℂ)‖ = 1) ∧
    IsModerateGrowth3 ℚ (fun g => f (transposeInv3 g)) ∧
    IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) (fun g => f (transposeInv3 g)) ∧
    IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) (fun g => f (transposeInv3 g)) ∧
    (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (fun g => f (transposeInv3 g))) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, f (transposeInv3 (g * localToAdelic3 v k)) = f (transposeInv3 g)) ∧
    WhittakerBlock.IsArchSmooth3 (fun g => f (transposeInv3 g)) ∧
    (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => f (transposeInv3 (g * k))) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
    (∀ i, archComponent3 (𝓞 ℚ) ℚ (transposeInv3 (t i)) = 1) ∧

    IsCentreFinite (fun x => ∑ i, c i * f (transposeInv3 (x * transposeInv3 (t i)))) ∧

    (∀ h : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ h' : AdelicGL 3 (𝓞 ℚ) ℚ, ∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      u ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ | ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (g * h * t i)) w} →
      (fun g => u (transposeInv3 g)) ∈ Submodule.span ℂ {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ |
        ∃ (w : List (Fin 3 × Fin 3)) (h : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ = List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ)
          (fun g => ∑ i, c i * f (transposeInv3 (g * h * transposeInv3 (t i)))) w} ∧
      ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ u
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * h)‖ =
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (fun g => u (transposeInv3 g))
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₂ * y₁, y₁, 1] i else 0) * h')‖) := by
  obtain ⟨hc', haut', hcen', hP21', hP12', hmg'⟩ :=
    continuous_isCuspidalAlong_isModerateGrowth3_dualForm ∅ (fun _ => ⊥) (fun _ => 1) ω f hc haut hcen hP21 hP12 hmg
  obtain ⟨hK', hsm', hsa', hKf', ht', hz', hspan⟩ :=
    archPackage_comp_transposeInv3_of_isCentreFinite f S hK hsm hsa hKf n c t ht hz
  have hω' : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω⁻¹ z : ℂ)‖ = 1 := by
    intro z
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hω z, inv_one]
  have hcen'' : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      f (transposeInv3 (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)) = (ω⁻¹ z : ℂ) * f (transposeInv3 g) := by
    intro z g
    have := hcen' z g
    simp only [dualForm] at this
    rw [this, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  refine ⟨hc', haut', hcen'', hω', hmg', hP21', hP12', hK', hsm', hsa', hKf', ht', hz', fun h => ?_⟩
  obtain ⟨h', H⟩ := norm_whittaker3_archRealLift3_diag_mul_eq_norm_whittaker3_comp_transposeInv3 h
  refine ⟨h', fun u hu => ⟨hspan u hu, fun y₁ y₂ hy₁ hy₂ => ?_⟩⟩
  obtain ⟨huc, huaut, hucen⟩ := span_pkg ω f hc haut hcen hmg hsa hKf c t ht hz u hu
  exact H ω hω u huc huaut hucen y₁ y₂ hy₁ hy₂

end S_LanglandsTunnell_CubicInduction_rayOrder_transport_transposeInv3_of_isCentreFinite_of_isRightInvariant
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_rayOrder_transport_transposeInv3_of_isCentreFinite_of_isRightInvariant (solution)
