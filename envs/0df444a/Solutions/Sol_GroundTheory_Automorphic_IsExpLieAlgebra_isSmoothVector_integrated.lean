-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothVector_integrated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:33:07.04408+00:00
-- url     : https://prove2.me/submissions/f06a5c02-f827-4728-b529-9b64e031a2b6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Theorems.Thm_GroundTheory_Automorphic_secondCountableTopology_subgroup_units
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_iteratedFDeriv_param
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_IsTestFunction_continuous
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_contDiff_comp_expG_mul_expG
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_integrable_smul_orbit
import Theorems.Thm_GroundTheory_Automorphic_BanachRep_continuous_orbit
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expOrbit_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_contDiff_integral_of_iteratedFDeriv
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {f : G → ℂ} (hf : h.IsTestFunction f) (v : E) :
    h.IsSmoothVector π (π.integrated μ f v) := by
  haveI := secondCountableTopology_subgroup_units G
  rw [isSmoothVector_iff]

  set F : 𝔤 → G → E := fun Y g => f (h.expG (-Y) * g) • π g v with hFdef
  have hexp : h.expOrbit π (π.integrated μ f v) = fun Y => ∫ g, F Y g ∂μ := by
    funext Y
    rw [expOrbit_apply, BanachRep.integrated,
      ← (π (h.expG Y)).integral_comp_comm (h.integrable_smul_orbit π μ hf v)]
    rw [← integral_mul_left_eq_self (F Y) (h.expG Y)]
    congr 1
    funext g
    simp only [hFdef, ContinuousLinearMap.coe_restrictScalars', map_smul,
      ← BanachRep.map_mul_apply, expG_neg, inv_mul_cancel_left]
  rw [hexp]

  set ψ : 𝔤 → G → ℂ := fun Y g => f (h.expG (-Y) * g) with hψdef
  have hψ : ∀ g₀ : G, ContDiff ℝ ∞ (fun q : 𝔤 × 𝔤 => ψ q.1 (g₀ * h.expG q.2)) := by
    intro g₀
    have := h.contDiff_comp_expG_mul_expG hf.1 (contDiff_fst.neg) g₀ contDiff_snd
    simpa [hψdef, mul_assoc] using this
  have hψY : ∀ g : G, ContDiff ℝ ∞ (fun Y => ψ Y g) := by
    intro g
    have := h.contDiff_comp_expG_mul_expG hf.1 (contDiff_id.neg) g (contDiff_const (c := (0 : 𝔤)))
    simpa [hψdef] using this

  set Lw : G → ℂ →L[ℝ] E := fun g => (ContinuousLinearMap.lsmul ℝ ℂ).flip (π g v) with hLw
  have hLwc : Continuous Lw := (ContinuousLinearMap.continuous _).comp (π.continuous_orbit v)
  have hFL : ∀ g, (fun Y => F Y g) = Lw g ∘ fun Y => ψ Y g := by
    intro g; funext Y; simp [hFdef, hLw, hψdef]
  have hiter : ∀ (k : ℕ) (Y : 𝔤) (g : G), ParamIntegral.iter F k Y g =
      (Lw g).compContinuousMultilinearMap (iteratedFDeriv ℝ k (fun Y => ψ Y g) Y) := by
    intro k Y g
    rw [ParamIntegral.iter, hFL g]
    exact (Lw g).iteratedFDeriv_comp_left (hψY g).contDiffAt (by exact_mod_cast le_top)
  refine contDiff_integral_of_iteratedFDeriv F (fun g => ?_) (fun k => ?_) (fun Y₀ => ?_)
  · rw [hFL g]; exact (Lw g).contDiff.comp (hψY g)
  · simp_rw [hiter]
    have hc := h.continuous_iteratedFDeriv_param ψ hψ k
    have hB := ContinuousLinearMap.continuous₂ (𝕜 := ℝ) (E := ℂ →L[ℝ] E)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) ℂ)
      (G := ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) E)
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => 𝔤) ℂ E)
    exact hB.comp ((hLwc.comp continuous_snd).prodMk hc)
  ·
    refine ⟨closedBall Y₀ 1, closedBall_mem_nhds Y₀ one_pos,
      (fun p : 𝔤 × G => h.expG p.1 * p.2) '' (closedBall Y₀ 1 ×ˢ tsupport f), ?_, ?_⟩
    · exact ((isCompact_closedBall Y₀ 1).prod hf.2).image
        ((h.continuous_expG.comp continuous_fst).mul continuous_snd)
    · intro Y hY g hg
      simp only [hFdef]
      by_contra hne
      apply hg
      refine ⟨(Y, h.expG (-Y) * g), ⟨hY, subset_tsupport f ?_⟩, ?_⟩
      · intro h0; apply hne; simp [h0]
      · simp [expG_neg]
end GroundTheory.Automorphic.IsExpLieAlgebra
