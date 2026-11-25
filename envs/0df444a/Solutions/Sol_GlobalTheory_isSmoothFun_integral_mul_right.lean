-- Prove2me | solution 1 for GlobalTheory.isSmoothFun_integral_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:22:33.471673+00:00
-- url     : https://prove2.me/submissions/71df2003-2759-4bcd-9a1b-0f0f27d3838c

import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRight
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_IsTestFunction_continuous
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_contDiff_comp_expG_mul_expG
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_iteratedFDeriv_param
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_locallyCompactSpace
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_contDiff_integral_of_iteratedFDeriv
import Theorems.Thm_GroundTheory_Automorphic_secondCountableTopology_subgroup_units
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
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
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff Manifold
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] (K : Set G), IsCompact K → ν Kᶜ = 0 → ∀ κ : G → ℂ, h.IsSmoothFun κ → h.IsSmoothFun (fun z => ∫ y, κ (z * y) ∂ν) := by
  intro 𝔸 _ _ _ _ G 𝔤 h _ _ ν _ K hK hν κ hκ
  haveI := secondCountableTopology_subgroup_units G
  haveI := h.locallyCompactSpace
  obtain ⟨ψ, hψ1, -, hψc, -⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g
  have hae : ∀ᵐ y ∂ν, y ∈ K := by
    rw [ae_iff]; exact hν
  have e : (fun Y : 𝔤 => ∫ y, κ (g * h.expG Y * y) ∂ν) =
      fun Y => ∫ y, ((ψ y : ℝ) : ℂ) * κ (g * h.expG Y * y) ∂ν := by
    funext Y
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp [hψ1 hy]
  rw [e]
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hκg : ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (fun x : G => κ (g * x)) :=
    ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hκ (contMDiff_const.mul contMDiff_id)
  set Φ : 𝔤 → G → ℂ := fun Y y => κ (g * h.expG Y * y) with hΦdef
  have hΦ : ∀ y₀ : G, ContDiff ℝ ∞ (fun q : 𝔤 × 𝔤 => Φ q.1 (y₀ * h.expG q.2)) := by
    intro y₀
    have := h.contDiff_comp_expG_mul_expG hκg contDiff_fst y₀ contDiff_snd
    simpa [hΦdef, mul_assoc] using this
  have hΦY : ∀ y : G, ContDiff ℝ ∞ (fun Y => Φ Y y) := by
    intro y
    have := h.contDiff_comp_expG_mul_expG hκg contDiff_id y (contDiff_const (c := (0 : 𝔤)))
    simpa [hΦdef, mul_assoc] using this
  have hD : ∀ (k : ℕ) (Y : 𝔤) (y : G),
      iteratedFDeriv ℝ k (fun Y => ((ψ y : ℝ) : ℂ) * Φ Y y) Y =
        ((ψ y : ℝ) : ℂ) • iteratedFDeriv ℝ k (fun Y => Φ Y y) Y := by
    intro k Y y
    have e : (fun Y => ((ψ y : ℝ) : ℂ) * Φ Y y) = ((ψ y : ℝ) : ℂ) • fun Y => Φ Y y := by
      funext Y; simp [smul_eq_mul]
    rw [e, iteratedFDeriv_const_smul_apply ((hΦY y).contDiffAt.of_le (by exact_mod_cast le_top))]
  change ContDiff ℝ ∞ fun Y : 𝔤 => ∫ y, ((ψ y : ℝ) : ℂ) * Φ Y y ∂ν
  refine contDiff_integral_of_iteratedFDeriv (μ := ν) (fun (Y : 𝔤) (y : G) => ((ψ y : ℝ) : ℂ) * Φ Y y)
    (fun y => contDiff_const.mul (hΦY y)) (fun k => ?_) (fun Y₀ => ?_)
  · have hc := h.continuous_iteratedFDeriv_param Φ hΦ k
    refine (((Complex.continuous_ofReal.comp ψ.continuous).comp continuous_snd).smul hc).congr fun q => ?_
    exact (hD k q.1 q.2).symm
  · refine ⟨Set.univ, Filter.univ_mem, tsupport ψ, hψc, fun Y _ y hy => ?_⟩
    simp [image_eq_zero_of_notMem_tsupport hy]
end GlobalTheory
