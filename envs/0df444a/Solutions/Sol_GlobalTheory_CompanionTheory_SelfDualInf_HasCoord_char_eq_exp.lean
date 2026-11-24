-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.HasCoord.char_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:39.05044+00:00
-- url     : https://prove2.me/submissions/b9d7076a-9e3d-4b07-85b4-7586af5d9d5a

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
namespace GlobalTheory.CompanionTheory.SelfDualInf
namespace HasCoord
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] (h : HasCoord V)
    (χ : V → ℂ) (hc : Continuous χ) (ha : ∀ x y, χ (x + y) = χ x * χ y) (hn : ∀ x, ‖χ x‖ = 1) :
    ∃ L : V →+ ℝ, Continuous L ∧ ∀ x, χ x = Complex.exp ((L x : ℂ) * Complex.I) := by
  obtain ⟨N, e, g1, g2⟩ := h
  let f : C((Fin N → ℝ), Circle) :=
    ⟨fun u => ⟨χ (e.symm u), mem_sphere_zero_iff_norm.2 (hn _)⟩,
      (hc.comp g2).subtype_mk fun u => mem_sphere_zero_iff_norm.2 (hn _)⟩
  have hfa : ∀ u v, f (u + v) = f u * f v := fun u v => by
    apply Subtype.ext
    show χ (e.symm (u + v)) = χ (e.symm u) * χ (e.symm v)
    rw [map_add, ha]
  have hf0 : f 0 = 1 := by
    have := hfa 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := f 0) (by rw [mul_one]; exact this.symm)
  obtain ⟨G, ⟨hG0, hG⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (by rw [hf0]; exact Circle.exp_zero)
  have hGx : ∀ u, Circle.exp (G u) = f u := fun u => congrFun hG u
  have hadd : ∀ u v, G (u + v) = G u + G v := by
    intro u v
    have := Circle.isCoveringMap_exp.eq_of_comp_eq (g₁ := fun u => G (u + v))
      (g₂ := fun u => G u + G v) (by fun_prop) (by fun_prop)
      (by funext u; simp only [Function.comp, Circle.exp_add, hGx, hfa]) 0 (by simp [hG0])
    exact congrFun this u
  refine ⟨(AddMonoidHom.mk' G hadd).comp e.toAddMonoidHom, G.continuous.comp g1, fun x => ?_⟩
  have := congrArg (fun z : Circle => (z : ℂ)) (hGx (e x))
  simp only [Circle.coe_exp] at this
  show χ x = Complex.exp ((G (e x) : ℂ) * Complex.I)
  rw [this]
  show χ x = χ (e.symm (e x))
  rw [e.symm_apply_apply]
end HasCoord
end GlobalTheory.CompanionTheory.SelfDualInf
