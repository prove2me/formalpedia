-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.exists_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:49:10.542004+00:00
-- url     : https://prove2.me/submissions/b3c93cfa-5044-47cf-ae7e-e16229a4b476

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_exists_qSymb_small
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_locCoeff_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_mono
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_congr_idx
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_Qop
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_Qop_small
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_exists_coeff_small
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_Q_locM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_locM_Q
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_mono
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_mulRem
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_mulConst_nonneg
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
  (x₀ : E) {cl Cu : ℝ} (hcl : 0 < cl) (hCu : 0 ≤ Cu)
  (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 (fun i ↦ a i x₀) w ξ‖)
  (hup : ∀ ξ, ‖symb0 (fun i ↦ a i x₀) w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (hm : 1 ≤ m) (hN : HasOrder N ((m : ℝ) - 1)) (k : ℕ) :
    ∃ δ, ∃ hδ : 0 < δ, ∀ S : Finset ℝ, ∃ μ, 0 < μ ∧ μ ≤ 1 ∧ ∀ s ∈ S,
      OpBound (Qop a w x₀ μ k ∘L locM a w N x₀ hδ) s s (1 / 2) ∧
      OpBound (locM a w N x₀ hδ ∘L Qop a w x₀ μ k) s s (1 / 2) := by
  have hP : ∀ i, 0 ≤ ∏ j, (2 * Real.pi * ‖w i j‖) := fun i ↦
    Finset.prod_nonneg fun j _ ↦ by positivity
  obtain ⟨CQ, hCQ0, hCQ_def⟩ : ∃ CQ : ℝ, 0 ≤ CQ ∧ CQ = k * (2 ^ m * (cl⁻¹ + Cu)) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨SP, hSP0, hSP_def⟩ : ∃ SP : ℝ, 0 ≤ SP ∧ SP = ∑ i, ∏ j, (2 * Real.pi * ‖w i j‖) :=
    ⟨_, Finset.sum_nonneg fun i _ ↦ hP i, rfl⟩
  obtain ⟨η, hη, hη_def⟩ : ∃ η : ℝ, 0 < η ∧ η = 1 / (4 * (CQ * SP + 1)) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨δ, hδ, hsmall⟩ := exists_coeff_small a x₀ hη
  refine ⟨δ, hδ, fun S ↦ ?_⟩
  have hg : ∀ i x, ‖locCoeff a x₀ hδ i x‖ ≤ η := fun i ↦
    norm_locCoeff_le a x₀ hδ i hη.le (hsmall i)
  have hrem : ∀ (i : Fin n) (r t : ℝ), ∃ C, 0 ≤ C ∧
      OpBound (mulRem (locCoeff a x₀ hδ i) r) t (t + 1) C := by
    intro i r t
    obtain ⟨C, hC0, hC⟩ := hasOrder_mulRem (locCoeff a x₀ hδ i) r t
    exact ⟨C, hC0, fun u hu ↦ by simpa using hC u hu⟩
  choose Cr hCr0 hCr using hrem
  have hNb : ∀ r : ℝ, ∃ C, 0 ≤ C ∧ OpBound N r (r - m + 1) C := by
    intro r
    obtain ⟨C, hC0, hC⟩ := hN r
    exact ⟨C, hC0, fun u hu ↦ by
      have := hC u hu; rwa [show r - ((m : ℝ) - 1) = r - m + 1 by ring] at this⟩
  choose CN hCN0 hCN using hNb
  obtain ⟨X, hX0, hX_def⟩ : ∃ X : ℝ → ℝ, (∀ s, 0 ≤ X s) ∧ X = fun s ↦
      (∑ i, Cr i (s - m) (s - m) * ∏ j, (2 * Real.pi * ‖w i j‖) +
        mulConst (s - m + 1) (bump x₀ hδ) * CN s) +
      (∑ i, Cr i s (s - 1) * ∏ j, (2 * Real.pi * ‖w i j‖) +
        mulConst s (bump x₀ hδ) * CN (s + m - 1)) := by
    refine ⟨_, fun s ↦ ?_, rfl⟩
    have h1 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ mul_nonneg (hCr0 i (s - m) (s - m)) (hP i)
    have h2 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ mul_nonneg (hCr0 i s (s - 1)) (hP i)
    have := mulConst_nonneg (s - m + 1) (bump x₀ hδ); have := mulConst_nonneg s (bump x₀ hδ)
    have := hCN0 s; have := hCN0 (s + m - 1)
    positivity
  have hSum : 0 ≤ ∑ s ∈ S, X s := Finset.sum_nonneg fun s _ ↦ hX0 s
  obtain ⟨ε, hε, hε_def⟩ : ∃ ε : ℝ, 0 < ε ∧ ε = 1 / (4 * (k + 1) * (∑ s ∈ S, X s + 1)) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨μ, hμ0, hμ1, hq⟩ := exists_qSymb_small _ w hcl hCu hlow hup hm hε
  refine ⟨μ, hμ0, hμ1, fun s hs ↦ ?_⟩
  have hXs : X s ≤ ∑ s ∈ S, X s := Finset.single_le_sum (fun s _ ↦ hX0 s) hs
  have hkε : (k : ℝ) * ε * X s ≤ 1 / 4 := by
    have h1 : (k : ℝ) * X s ≤ (k + 1) * (∑ s ∈ S, X s + 1) := by
      have := hX0 s
      nlinarith
    have hpos : 0 < 4 * (k + 1) * (∑ s ∈ S, X s + 1) := by positivity
    rw [hε_def, show (k : ℝ) * (1 / (4 * (k + 1) * (∑ s ∈ S, X s + 1))) * X s =
      (k * X s) / (4 * (k + 1) * (∑ s ∈ S, X s + 1)) by ring, div_le_iff₀ hpos]
    nlinarith
  have hηSP : CQ * (η * SP) ≤ 1 / 4 := by
    rw [hη_def, show CQ * (1 / (4 * (CQ * SP + 1)) * SP) = (CQ * SP) / (4 * (CQ * SP + 1)) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hQ : ∀ t, OpBound (Qop a w x₀ μ k) (t - m) t CQ := fun t ↦ by
    rw [hCQ_def]; exact opBound_Qop a w x₀ hcl hCu hlow hup hμ0.le hμ1 k t
  have hQs : ∀ t, OpBound (Qop a w x₀ μ k) (t - m + 1) t (k * ε) :=
    opBound_Qop_small a w x₀ hcl hCu hlow hup hm hμ0.le hq k
  have hkε0 : 0 ≤ (k : ℝ) * ε := by positivity
  have hXs_def := congrFun hX_def s
  constructor
  · refine (opBound_Q_locM a w N x₀ hδ _ s hη.le hCQ0 hkε0 hg (hQ s) (hQs s)
      (fun i ↦ hCr0 i (s - m) (s - m)) (fun i ↦ (hCr i (s - m) (s - m)).congr_idx rfl (by ring))
      (hCN0 s) (hCN s)).mono ?_
    rw [← hSP_def]
    have : ∑ i, Cr i (s - m) (s - m) * ∏ j, (2 * Real.pi * ‖w i j‖) +
        mulConst (s - m + 1) (bump x₀ hδ) * CN s ≤ X s := by
      have h2 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ mul_nonneg (hCr0 i s (s - 1)) (hP i)
      have := mulConst_nonneg s (bump x₀ hδ); have := hCN0 (s + m - 1)
      rw [hXs_def]; nlinarith
    nlinarith
  · refine (opBound_locM_Q a w N x₀ hδ _ s hη.le hCQ0 hkε0 hg ((hQ (s + m)).congr_idx (by ring) rfl)
      ((hQs (s + m - 1)).congr_idx (by ring) rfl) (fun i ↦ hCr0 i s (s - 1))
      (fun i ↦ (hCr i s (s - 1)).congr_idx rfl (by ring))
      (hCN0 (s + m - 1)) ((hCN (s + m - 1)).congr_idx rfl (by ring))).mono ?_
    rw [← hSP_def]
    have : ∑ i, Cr i s (s - 1) * ∏ j, (2 * Real.pi * ‖w i j‖) +
        mulConst s (bump x₀ hδ) * CN (s + m - 1) ≤ X s := by
      have h1 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ mul_nonneg (hCr0 i (s - m) (s - m)) (hP i)
      have := mulConst_nonneg (s - m + 1) (bump x₀ hδ); have := hCN0 s
      rw [hXs_def]; nlinarith
    nlinarith
end GroundTheory.Automorphic.Sobolev
