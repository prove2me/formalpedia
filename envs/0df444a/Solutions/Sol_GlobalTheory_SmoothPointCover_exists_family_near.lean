-- Prove2me | solution 1 for GlobalTheory.SmoothPointCover.exists_family_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:19:44.734798+00:00
-- url     : https://prove2.me/submissions/e3892c98-dd22-4514-8c2e-d04c830d1653

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsHolomorphicFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DenseMvPolynomialEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEmbeddingsOverInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsCountableHolomorphicFamiliesSmooth
import Theorems.Thm_GlobalTheory_SmoothPointFamily_exists_finset_of_mem_nhds
import Theorems.Thm_GlobalTheory_SmoothPointFamily_exists_holomorphic_family
import Theorems.Thm_GlobalTheory_exists_algIndep_tuple_near
import Theorems.Thm_GlobalTheory_generic_points_dense
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open Topology Filter
open GlobalTheory GlobalTheory.SmoothPointCover
namespace GlobalTheory.SmoothPointCover
theorem _root_.solution (K A : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.Smooth K A] (σ : K →+* ℂ) (φ₀ : A →+* ℂ) (h₀ : φ₀.comp (algebraMap K A) = σ) :
    ∃ (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (U : Set (A → ℂ)), U ∈ 𝓝 (φ₀ : A → ℂ) ∧
      IsOpen B ∧ (∀ b ∈ B, (φ b).comp (algebraMap K A) = σ) ∧
      (∀ a : A, DifferentiableOn ℂ (fun b => φ b a) B) ∧
      (∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → (ψ : A → ℂ) ∈ U → ∃ b ∈ B, φ b = ψ) ∧
      ∀ b ∈ B, ∀ a : A, a ≠ 0 → ∃ᶠ b' in 𝓝 b, φ b' a ≠ 0 := by
  classical
  obtain ⟨m, s, B, φ, S, ε, hB, hε, hφ, hd, hnear⟩ :=
    GlobalTheory.SmoothPointFamily.exists_holomorphic_family K A σ φ₀ h₀
  let U : Set (A → ℂ) := {f | ∀ a ∈ S, ‖f a - φ₀ a‖ < ε}
  have hU : IsOpen U := by
    have : U = ⋂ a ∈ S, {f : A → ℂ | ‖f a - φ₀ a‖ < ε} := by
      ext f; simp [U]
    rw [this]
    exact isOpen_biInter_finset fun a _ => isOpen_lt (by fun_prop) continuous_const
  have hc : ContinuousOn (fun b => (φ b : A → ℂ)) B := continuousOn_pi.2 fun a => (hd a).continuousOn
  refine ⟨m, B ∩ (fun b => (φ b : A → ℂ)) ⁻¹' U, φ, U, hU.mem_nhds (fun a _ => by simpa using hε),
    hc.isOpen_inter_preimage hB hU, fun b hb => (hφ b hb.1).1, fun a => (hd a).mono Set.inter_subset_left,
    fun ψ hψ hψU => ?_, fun b hb a ha => ?_⟩
  · obtain ⟨h1, h2⟩ := hnear ψ hψ hψU
    refine ⟨_, ⟨h1, ?_⟩, h2⟩
    rw [Set.mem_preimage, h2]
    exact hψU
  · rw [Filter.frequently_iff]
    intro V hV
    have hW : U ∩ (fun f : A → ℂ => fun i => f (s i)) ⁻¹' V ∈ 𝓝 (φ b : A → ℂ) := by
      refine Filter.inter_mem (hU.mem_nhds hb.2) ?_
      have hcs : Continuous (fun f : A → ℂ => fun i => f (s i)) := by fun_prop
      refine hcs.continuousAt.preimage_mem_nhds ?_
      have : (fun i => φ b (s i)) = b := funext (hφ b hb.1).2
      simpa only [this] using hV
    obtain ⟨S', δ, hδ, hS'⟩ := GlobalTheory.SmoothPointFamily.exists_finset_of_mem_nhds hW
    obtain ⟨P, hP, hPε⟩ := GlobalTheory.generic_points_dense GlobalTheory.exists_algIndep_tuple_near K A (FractionRing A) σ (φ b)
      (hφ b hb.1).1 S' δ hδ
    let ρ : A →+* ℂ := P.comp (algebraMap A (FractionRing A))
    have hρ : ρ.comp (algebraMap K A) = σ := RingHom.ext fun a => RingHom.congr_fun hP a
    obtain ⟨h3, h4⟩ := hS' ρ hPε
    refine ⟨_, h4, ?_⟩
    have h5 := (hnear ρ hρ h3).2
    change φ (fun i => ρ (s i)) a ≠ 0
    rw [h5]
    exact (map_ne_zero_iff ρ (P.injective.comp (IsFractionRing.injective A (FractionRing A)))).2 ha
end GlobalTheory.SmoothPointCover
