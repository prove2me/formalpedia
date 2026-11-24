-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCover.cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:20:14.443737+00:00
-- url     : https://prove2.me/submissions/eabe4360-27ed-483c-8517-b72ca54b6ac8

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_glRel_add
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_glRel_map
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_pd_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_pd_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_word_tens
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open scoped TensorProduct
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCover
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC
namespace GlobalTheory.CompanionTheory.DSCover
theorem _root_.solution : Koszul → Verma → Cover := by
  intro hK hV n ε V _ _ E hE
  classical
  obtain ⟨M, hM, hX, h0⟩ := hV n ε
  let P := MvPolynomial (NC ε) ℂ
  let EY : Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] P) := fun a b => (E a b).rTensor P + (M a b).lTensor V
  have hEY : GlRel EY := by
    refine glRel_add (E := fun a b => ((E a b).rTensor P : Module.End ℂ (V ⊗[ℂ] P)))
      (F := fun a b => ((M a b).lTensor V : Module.End ℂ (V ⊗[ℂ] P))) ?_ ?_ ?_
    · exact glRel_map (Module.End.rTensorAlgHom ℂ V P).toRingHom hE
    · exact glRel_map (Module.End.lTensorAlgHom ℂ P V).toRingHom hM
    · intro a b c d
      apply TensorProduct.ext'
      intro v f
      simp [Module.End.mul_apply]
  let cc : P →ₗ[ℂ] ℂ := (MvPolynomial.lcoeff ℂ (0 : NC ε →₀ ℕ))
  have hcc : ∀ f : P, cc f = constantCoeff f := fun f => rfl
  refine ⟨V ⊗[ℂ] P, inferInstance, inferInstance, EY, (TensorProduct.rid ℂ V).toLinearMap ∘ₗ cc.lTensor V,
    hEY, ?_, ?_, ?_⟩
  · intro v
    exact ⟨v ⊗ₜ 1, by simp [hcc]⟩
  · intro a b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [EY, hcc, h0]
    | add p q hp hq => simp only [map_add, hp, hq]
  · refine hK n ε (V ⊗[ℂ] P) (fun i => EY i.1.1 i.1.2) (fun i => (pd i).lTensor V) ?_ ?_ ?_ ?_
    · intro i j
      have h := hEY i.1.1 i.1.2 j.1.1 j.1.2
      have h1 : i.1.2 ≠ j.1.1 := fun e => by
        have := i.2.2; rw [e, j.2.1] at this; exact Bool.noConfusion this
      have h2 : j.1.2 ≠ i.1.1 := fun e => by
        have := j.2.2; rw [e, i.2.1] at this; exact Bool.noConfusion this
      rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
      exact h
    · intro i j
      apply TensorProduct.ext'
      intro v f
      have := congrArg (fun T : Module.End ℂ P => T f) (pd_comm i j)
      simp only [Module.End.mul_apply] at this
      simp only [Module.End.mul_apply, LinearMap.lTensor_tmul, this]
    · intro i j
      apply TensorProduct.ext'
      intro v f
      simp only [EY, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.lTensor_tmul,
        LinearMap.rTensor_tmul, map_add, hX, pd_apply, Derivation.leibniz, pderiv_X, smul_eq_mul,
        TensorProduct.tmul_add]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro z
      obtain ⟨m, hm⟩ := word_tens z
      exact ⟨m, fun l hl => hm l hl.ge⟩
end GlobalTheory.CompanionTheory.DSCover
