-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.opBound_Q_locM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:28.314458+00:00
-- url     : https://prove2.me/submissions/d228e00c-9abe-4c71-bb5d-de05e73e5b23

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_mono
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
    (hQ : OpBound Q (s - m) s CQ) (hQs : OpBound Q (s - m + 1) s κ)
    {Cr : Fin n → ℝ} (hCr0 : ∀ i, 0 ≤ Cr i)
    (hCr : ∀ i, OpBound (mulRem (locCoeff a x₀ hδ i) (s - m)) (s - m) (s - m + 1) (Cr i))
    {CN : ℝ} (hCN0 : 0 ≤ CN) (hCN : OpBound N s (s - m + 1) CN) :
    OpBound (Q ∘L locM a w N x₀ hδ) s s
      (CQ * (η * ∑ i, ∏ j, (2 * Real.pi * ‖w i j‖)) +
        κ * (∑ i, Cr i * ∏ j, (2 * Real.pi * ‖w i j‖) + mulConst (s - m + 1) (bump x₀ hδ) * CN)) := by
  have hP : ∀ i, 0 ≤ ∏ j, (2 * Real.pi * ‖w i j‖) := fun i ↦
    Finset.prod_nonneg fun j _ ↦ by positivity
  have e : Q ∘L locM a w N x₀ hδ =
      ∑ i, (Q ∘L (mulPrin (locCoeff a x₀ hδ i) (s - m) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i)) +
        Q ∘L (mulRem (locCoeff a x₀ hδ i) (s - m) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i))) +
      Q ∘L (smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) ∘L N) := by
    ext1 u
    simp only [locM, prinOp, ContinuousLinearMap.comp_apply, add_apply, sum_apply, map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smulLeftCLM_eq_mulPrin_add_mulRem _ (s - m), map_add]
  rw [e]
  have hterm : ∀ i ∈ Finset.univ, OpBound
      (Q ∘L (mulPrin (locCoeff a x₀ hδ i) (s - m) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i)) +
        Q ∘L (mulRem (locCoeff a x₀ hδ i) (s - m) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i))) s s
      (CQ * (η * ∏ j, (2 * Real.pi * ‖w i j‖)) + κ * (Cr i * ∏ j, (2 * Real.pi * ‖w i j‖))) := by
    intro i _
    have h1 := hQ.comp ((opBound_mulPrin _ hη (hg i) (s - m)).comp
      (opBound_iteratedLineDeriv (w i) s) hη) hCQ
    have h2 := hQs.comp ((hCr i).comp (opBound_iteratedLineDeriv (w i) s) (hCr0 i)) hκ
    exact h1.add h2 (by have := hP i; positivity) (by have := hP i; have := hCr0 i; positivity)
  have hsum := OpBound.sum Finset.univ (fun i _ ↦ by have := hP i; have := hCr0 i; positivity) hterm
  have h3 := hQs.comp ((opBound_smulLeft (bump x₀ hδ) (s - m + 1)).comp hCN
    (mulConst_nonneg _ _)) hκ
  refine (hsum.add h3 (Finset.sum_nonneg fun i _ ↦ by have := hP i; have := hCr0 i; positivity)
    (by have := mulConst_nonneg (s - m + 1) (bump x₀ hδ); positivity)).mono (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring
end GroundTheory.Automorphic.Sobolev
