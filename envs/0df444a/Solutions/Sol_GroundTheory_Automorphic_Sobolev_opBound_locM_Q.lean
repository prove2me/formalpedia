-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.opBound_locM_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:31.894243+00:00
-- url     : https://prove2.me/submissions/905c8adb-10a6-4501-a931-409ecd8fb821

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_mono
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_congr_idx
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_iteratedLineDeriv
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_smulLeft
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_mulPrin
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_mono
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsEllipticAt_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_mulConst_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_eq_mulPrin_add_mulRem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E)
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) (Q : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (s : ℝ)
    {η CQ κ : ℝ} (hη : 0 ≤ η) (hCQ : 0 ≤ CQ) (hκ : 0 ≤ κ)
    (hg : ∀ i x, ‖locCoeff a x₀ hδ i x‖ ≤ η)
    (hQ : OpBound Q s (s + m) CQ) (hQs : OpBound Q s (s + m - 1) κ)
    {Cr : Fin n → ℝ} (hCr0 : ∀ i, 0 ≤ Cr i)
    (hCr : ∀ i, OpBound (mulRem (locCoeff a x₀ hδ i) s) (s - 1) s (Cr i))
    {CN : ℝ} (hCN0 : 0 ≤ CN) (hCN : OpBound N (s + m - 1) s CN) :
    OpBound (locM a w N x₀ hδ ∘L Q) s s
      (CQ * (η * ∑ i, ∏ j, (2 * Real.pi * ‖w i j‖)) +
        κ * (∑ i, Cr i * ∏ j, (2 * Real.pi * ‖w i j‖) + mulConst s (bump x₀ hδ) * CN)) := by
  have hP : ∀ i, 0 ≤ ∏ j, (2 * Real.pi * ‖w i j‖) := fun i ↦
    Finset.prod_nonneg fun j _ ↦ by positivity
  have e : locM a w N x₀ hδ ∘L Q =
      ∑ i, (mulPrin (locCoeff a x₀ hδ i) s ∘L (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i) ∘L Q) +
        mulRem (locCoeff a x₀ hδ i) s ∘L (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i) ∘L Q)) +
      smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) ∘L (N ∘L Q) := by
    ext1 u
    simp only [locM, prinOp, ContinuousLinearMap.comp_apply, add_apply, sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smulLeftCLM_eq_mulPrin_add_mulRem _ s]
  rw [e]
  have hterm : ∀ i ∈ Finset.univ, OpBound
      (mulPrin (locCoeff a x₀ hδ i) s ∘L (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i) ∘L Q) +
        mulRem (locCoeff a x₀ hδ i) s ∘L (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i) ∘L Q)) s s
      (η * ((∏ j, (2 * Real.pi * ‖w i j‖)) * CQ) + Cr i * ((∏ j, (2 * Real.pi * ‖w i j‖)) * κ)) := by
    intro i _
    have h1 := (opBound_mulPrin _ hη (hg i) s).comp
      (((opBound_iteratedLineDeriv (w i) (s + m)).congr_idx rfl (by ring)).comp hQ (hP i)) hη
    have h2 := (hCr i).comp
      (((opBound_iteratedLineDeriv (w i) (s + m - 1)).congr_idx rfl (by ring)).comp hQs (hP i))
      (hCr0 i)
    exact h1.add h2 (by have := hP i; positivity) (by have := hP i; have := hCr0 i; positivity)
  have hsum := OpBound.sum Finset.univ (fun i _ ↦ by have := hP i; have := hCr0 i; positivity) hterm
  have h3 := (opBound_smulLeft (bump x₀ hδ) s).comp (hCN.comp hQs hCN0) (mulConst_nonneg _ _)
  refine (hsum.add h3 (Finset.sum_nonneg fun i _ ↦ by have := hP i; have := hCr0 i; positivity)
    (by have := mulConst_nonneg s (bump x₀ hδ); positivity)).mono (le_of_eq ?_)
  rw [Finset.sum_add_distrib]
  have e1 : ∑ i, η * ((∏ j, (2 * Real.pi * ‖w i j‖)) * CQ) =
      CQ * (η * ∑ i, ∏ j, (2 * Real.pi * ‖w i j‖)) := by
    rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e2 : ∑ i, Cr i * ((∏ j, (2 * Real.pi * ‖w i j‖)) * κ) =
      κ * ∑ i, Cr i * ∏ j, (2 * Real.pi * ‖w i j‖) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e1, e2]; ring
end GroundTheory.Automorphic.Sobolev
