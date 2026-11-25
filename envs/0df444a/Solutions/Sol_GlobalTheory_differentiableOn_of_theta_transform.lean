-- Prove2me | solution 1 for GlobalTheory.differentiableOn_of_theta_transform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:10.47532+00:00
-- url     : https://prove2.me/submissions/3229fb5d-0e7a-4202-8ff9-5e1d8a3ab8cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_differentiableOn_nonsing_inv_apply
import Theorems.Thm_GlobalTheory_differentiableOn_matrix_mul_apply
import Theorems.Thm_GlobalTheory_differentiableOn_riemannTheta_comp
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_siegelUpperCoords
import Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_isUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.mem_siegelUpperCoords
attribute [local simp] GlobalTheory.riemannThetaJointForm_apply



set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
namespace GlobalTheory
theorem _root_.solution (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    {l : Matrix (Fin g) (Fin g) ℂ → ℂ} (hl : ∀ τ ∈ SiegelH (Fin g), ∀ z,
      theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l τ * theta 0 0 z τ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : E → Matrix (Fin g) (Fin g) ℂ}
    {U : Set E} (hT : ∀ x ∈ U, T x ∈ SiegelH (Fin g))
    (h1 : ∀ i j, DifferentiableOn ℂ (fun x => T x i j) U) :
    DifferentiableOn ℂ (fun x => l (T x)) U := by
  intro x₀ hx₀
  have hS {τ : Matrix (Fin g) (Fin g) ℂ} (h : τ ∈ SiegelH (Fin g)) : IsSiegel τ := ⟨h.1, h.2⟩
  obtain ⟨z, hz⟩ := Function.ne_iff.1 ((hS (hT _ hx₀)).riemannTheta_ne_zero 0 0)
  have h0 (A B : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
      DifferentiableOn ℂ (fun x => (A * T x + B) i j) U :=
    (differentiableOn_matrix_mul_apply (M := fun _ => A) (fun _ _ => differentiableOn_const _)
      h1 i j).add_const _
  have h2 (i j : Fin g) : DifferentiableOn ℂ (fun x => (jAut γ (T x))⁻¹ i j) U :=
    differentiableOn_nonsing_inv_apply (M := fun x => jAut γ (T x)) (h0 _ _)
      (fun x hx => jAut_isUnit hγ (hT x hx)) i j
  have h3 : DifferentiableOn ℂ (fun x => riemannTheta 0 0 (T x) z) U :=
    differentiableOn_riemannTheta_comp 0 0 (fun x hx => hS (hT x hx)) h1 (differentiableOn_const _)
  have h4 : DifferentiableOn ℂ (fun x => riemannTheta 0 0 (spAct γ (T x)) (zAct γ (T x) z)) U :=
    differentiableOn_riemannTheta_comp 0 0 (fun x hx => hS (spAct_mem hγ (hT x hx)))
      (differentiableOn_matrix_mul_apply (N := fun x => (jAut γ (T x))⁻¹) (h0 _ _) h2)
      (differentiableOn_pi.2 fun i => DifferentiableOn.fun_sum (u := Finset.univ) fun k _ =>
        (h2 k i).mul_const (z k))
  have h5 : DifferentiableOn ℂ (fun x => expArg γ (T x) z) U :=
    DifferentiableOn.fun_sum (u := Finset.univ) fun i _ =>
      (DifferentiableOn.fun_sum (u := Finset.univ) fun k _ =>
      (differentiableOn_matrix_mul_apply (N := fun _ => (cMat γ).toBlocks₂₁) h2
        (fun _ _ => differentiableOn_const _) i k).mul_const (z k)).const_mul (z i)
  have h6 : DifferentiableOn ℂ (fun x => eC (-expArg γ (T x) z / 2)) U := by
    simp only [eC, div_eq_mul_inv]
    exact ((h5.neg.mul_const _).const_mul _).cexp
  have h7 := (h3 x₀ hx₀).continuousWithinAt.eventually_ne hz
  refine ((((h4 x₀ hx₀).mul (h6 x₀ hx₀)).mul ((h3 x₀ hx₀).inv hz)).congr_of_eventuallyEq ?_
    ((eq_mul_inv_iff_mul_eq₀ hz).2 (hl _ (hT _ hx₀) z).symm))
  filter_upwards [h7, self_mem_nhdsWithin] with x hx hx'
  exact (eq_mul_inv_iff_mul_eq₀ hx).2 (hl _ (hT _ hx') z).symm
end GlobalTheory
