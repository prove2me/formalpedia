-- Prove2me | solution 1 for NumberField.TateGlobal.setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a5116abf-feae-5220-92ad-6fb4ebd47cc1

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne

set_option autoImplicit false

open MeasureTheory NumberField
open scoped Pointwise

noncomputable section

namespace R1MellinOrthogonality

section Abstract

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem integral_eq_zero_of_mul_left {μ : Measure G} [μ.IsMulLeftInvariant]
    (f : G → ℂ) (g₀ : G) (c : ℂ) (hc : c ≠ 1) (hf : ∀ x, f (g₀ * x) = c * f x)
    (Ω : Set G)
    (hΩ : ∫ x in (fun x => g₀ * x) '' Ω, f x ∂μ = ∫ x in Ω, f x ∂μ) :
    ∫ x in Ω, f x ∂μ = 0 := by
  have hpres : MeasurePreserving (fun x => g₀ * x) μ μ := measurePreserving_mul_left μ g₀
  have hemb : MeasurableEmbedding (fun x : G => g₀ * x) := measurableEmbedding_mulLeft g₀
  have h1 : ∫ x in (fun x => g₀ * x) '' Ω, f x ∂μ = ∫ x in Ω, f (g₀ * x) ∂μ :=
    hpres.setIntegral_image_emb hemb f Ω
  have h2 : ∫ x in Ω, f (g₀ * x) ∂μ = c * ∫ x in Ω, f x ∂μ := by
    simp_rw [hf]
    exact integral_const_mul c _
  have h3 : ∫ x in Ω, f x ∂μ = c * ∫ x in Ω, f x ∂μ := by rw [← h2, ← h1, hΩ]
  have h4 : (1 - c) * ∫ x in Ω, f x ∂μ = 0 := by
    rw [sub_mul, one_mul, ← h3, sub_self]
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc
  · exact h

end Abstract

section Idele

variable (F : Type) [Field F] [NumberField F]

def principalUnits : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range

variable {F}

theorem ideleNorm_principal (u : Fˣ) :
    NumberField.TateGlobal.ideleNorm F
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
  unfold NumberField.TateGlobal.ideleNorm
  have h' : distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := h
  rw [h']
  rfl

theorem ideleNorm_of_mem_principalUnits {h : (AdeleRing (𝓞 F) F)ˣ} (hh : h ∈ principalUnits F) :
    NumberField.TateGlobal.ideleNorm F h = 1 := by
  obtain ⟨u, rfl⟩ := hh
  exact ideleNorm_principal u

theorem char_of_mem_principalUnits {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ)
    {h : (AdeleRing (𝓞 F) F)ˣ} (hh : h ∈ principalUnits F) : χ h = 1 := by
  obtain ⟨u, rfl⟩ := hh
  exact hχF u

end Idele

end R1MellinOrthogonality

open R1MellinOrthogonality in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ)
    (hχ : ∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = 1 ∧ χ z ≠ 1)
    (g : ℝ → ℂ) :
    ∫ a in Ω, ((χ a : ℂˣ) : ℂ) * g (NumberField.TateGlobal.ideleNorm F a) ∂ν = 0 := by
  obtain ⟨z, hz1, hzχ⟩ := hχ
  set f : (AdeleRing (𝓞 F) F)ˣ → ℂ := fun a =>
    ((χ a : ℂˣ) : ℂ) * g (NumberField.TateGlobal.ideleNorm F a) with hfdef

  have hf : ∀ x, f (z * x) = ((χ z : ℂˣ) : ℂ) * f x := by
    intro x
    simp only [hfdef, map_mul, Units.val_mul, NumberField.TateGlobal.ideleNorm_mul, hz1, one_mul]
    ring
  have hc : ((χ z : ℂˣ) : ℂ) ≠ 1 := by
    intro h
    exact hzχ (Units.ext h)

  have hfinv : ∀ (γ : ↥(principalUnits F)) (x : (AdeleRing (𝓞 F) F)ˣ), f (γ • x) = f x := by
    intro γ x
    show f ((γ : (AdeleRing (𝓞 F) F)ˣ) * x) = f x
    simp only [hfdef, map_mul, NumberField.TateGlobal.ideleNorm_mul,
      char_of_mem_principalUnits hχF γ.2, ideleNorm_of_mem_principalUnits γ.2, one_mul]

  haveI : SMulInvariantMeasure (AdeleRing (𝓞 F) F)ˣ (AdeleRing (𝓞 F) F)ˣ ν := inferInstance
  haveI : SMulCommClass (AdeleRing (𝓞 F) F)ˣ (↥(principalUnits F)) (AdeleRing (𝓞 F) F)ˣ :=
    ⟨fun a γ x => by
      show a * ((γ : (AdeleRing (𝓞 F) F)ˣ) * x) = (γ : (AdeleRing (𝓞 F) F)ˣ) * (a * x)
      rw [← mul_assoc, mul_comm a, mul_assoc]⟩
  have hΩ' : IsFundamentalDomain (↥(principalUnits F)) (z • Ω) ν := hΩ.smul_of_comm z

  haveI : Countable F :=
    (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable Fˣ :=
    Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective
  haveI : Countable (↥(principalUnits F)) :=
    Function.Surjective.countable (MonoidHom.rangeRestrict_surjective _)
  haveI : SMulInvariantMeasure (↥(principalUnits F)) (AdeleRing (𝓞 F) F)ˣ ν :=
    ⟨fun γ A hA => by
      show ν ((fun x => (γ : (AdeleRing (𝓞 F) F)ˣ) * x) ⁻¹' A) = ν A
      exact measure_preimage_mul _ _ _⟩
  have heq : ∫ x in (fun x => z * x) '' Ω, f x ∂ν = ∫ x in Ω, f x ∂ν := by
    have himg : (fun x => z * x) '' Ω = z • Ω := rfl
    rw [himg]
    exact hΩ'.setIntegral_eq hΩ hfinv
  exact integral_eq_zero_of_mul_left f z _ hc hf Ω heq

end

end S_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne
end P2MW
export P2MW.S_NumberField_TateGlobal_setIntegral_mul_apply_ideleNorm_eq_zero_of_isIdeleClassChar_of_exists_ideleNorm_eq_one_ne (solution)
