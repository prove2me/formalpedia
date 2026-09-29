-- Prove2me | solution 1 for NumberField.PlaceDecomp.adicCompletionSemialgHom_norm_eq_finprod_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/79ca1561-62e0-531d-835f-4071afe68dce

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
import Theorems.Thm_Algebra_algebraMap_norm_eq_prod_apply_of_card_eq_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_PlaceDecomp_adicCompletionSemialgHom_norm_eq_finprod_smul

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 F)) (b : w.1.adicCompletion F) :
    IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F w (Algebra.norm (v.adicCompletion E) b) =
      ∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w.1), σ • b := by
  classical
  haveI : Fintype ↥(NumberField.PlaceDecomp.decomp E F w.1) := Fintype.ofFinite _
  set ι := IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F w with hι

  have halg : ∀ a, algebraMap (v.adicCompletion E) (w.1.adicCompletion F) a = ι a := fun a => rfl

  have hfix : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F w.1)) (a : v.adicCompletion E), σ • ι a = ι a := by
    intro σ a
    obtain ⟨a, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective (K := E) (v := v) a
    induction a using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq ((((NumberField.PlaceDecomp.continuous_actRingEquiv σ).comp
          (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous E F w)).comp
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion E v)) |>.congr
            fun x => (NumberField.PlaceDecomp.smul_def σ _).symm)
        ((IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous E F w).comp
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion E v))
    | ih x =>
      change σ • ι (x : v.adicCompletion E) = ι (x : v.adicCompletion E)
      rw [hι, IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe, NumberField.PlaceDecomp.smul_def]
      rw [NumberField.PlaceDecomp.actRingEquiv_coe]
      apply congrArg (fun t : WithVal (w.1.valuation F) => (t : w.1.adicCompletion F))
      rw [WithVal.congr_apply]
      change WithVal.toVal (w.1.valuation F) ((σ : F ≃ₐ[E] F) (algebraMap E F x.ofVal)) =
        WithVal.toVal (w.1.valuation F) (algebraMap E F x.ofVal)
      rw [AlgEquiv.commutes]

  let φ : ↥(NumberField.PlaceDecomp.decomp E F w.1) → (w.1.adicCompletion F →ₐ[v.adicCompletion E] w.1.adicCompletion F) :=
    fun σ =>
      { (NumberField.PlaceDecomp.actRingEquiv σ).toRingHom with
        commutes' := fun a => by
          change NumberField.PlaceDecomp.actRingEquiv σ (algebraMap _ _ a) = algebraMap _ _ a
          rw [halg, ← NumberField.PlaceDecomp.smul_def, hfix] }
  have hφ : ∀ σ x, φ σ x = σ • x := fun σ x => by
    rw [NumberField.PlaceDecomp.smul_def]; rfl

  have hinj : Function.Injective φ := by
    intro σ τ hστ
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    have hx := congrArg (fun ψ => ψ ((WithVal.toVal (w.1.valuation F) x : WithVal (w.1.valuation F)) : w.1.adicCompletion F)) hστ
    simp only [hφ, NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.actRingEquiv_coe] at hx
    have hx' := UniformSpace.Completion.coe_injective _
      (congrArg IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion hx)
    rw [WithVal.congr_apply, WithVal.congr_apply] at hx'
    exact WithVal.toVal_injective _ hx'

  have hcard : Fintype.card ↥(NumberField.PlaceDecomp.decomp E F w.1) =
      Module.finrank (v.adicCompletion E) (w.1.adicCompletion F) := by
    have h1 := NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg E F w.1
    rw [w.2] at h1
    rw [← Nat.card_eq_fintype_card, h1]
    exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank E F w

  have key := Algebra.algebraMap_norm_eq_prod_apply_of_card_eq_finrank φ hinj hcard b
  rw [halg] at key
  rw [key, finprod_eq_prod_of_fintype]
  exact Finset.prod_congr rfl fun σ _ => hφ σ b

end S_NumberField_PlaceDecomp_adicCompletionSemialgHom_norm_eq_finprod_smul
end P2MW
export P2MW.S_NumberField_PlaceDecomp_adicCompletionSemialgHom_norm_eq_finprod_smul (solution)
