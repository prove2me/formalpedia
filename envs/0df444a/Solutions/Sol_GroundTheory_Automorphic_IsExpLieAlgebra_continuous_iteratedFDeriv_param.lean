-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.continuous_iteratedFDeriv_param
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:04.147171+00:00
-- url     : https://prove2.me/submissions/befb23e8-3cef-494c-bf1a-23d3be429e70

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
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
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (ψ : P → G → E')
    (hψ : ∀ g₀ : G, ContDiff ℝ ∞ (fun q : P × 𝔤 => ψ q.1 (g₀ * h.expG q.2))) (k : ℕ) :
    Continuous (fun p : P × G => iteratedFDeriv ℝ k (fun Y => ψ Y p.2) p.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨Y₀, g₀⟩
  set Φ : P × 𝔤 → E' := fun q => ψ q.1 (g₀ * h.expG q.2) with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := hψ g₀
  set L := ContinuousLinearMap.inl ℝ P 𝔤
  set H : P × 𝔤 → ContinuousMultilinearMap ℝ (fun _ : Fin k => P) E' :=
    fun q => ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L) (iteratedFDeriv ℝ k Φ q)
  have hH : Continuous H :=
    (ContinuousLinearMap.continuous _).comp (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hpart : ∀ (Z : 𝔤) (Y : P), iteratedFDeriv ℝ k (fun Y => Φ (Y, Z)) Y = H (Y, Z) := by
    intro Z Y
    have e : (fun Y => Φ (Y, Z)) = (fun w => Φ (w + (0, Z))) ∘ L := by
      funext Y; simp [L]
    have hΦZ : ContDiff ℝ ∞ (fun w : P × 𝔤 => Φ (w + (0, Z))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, L.iteratedFDeriv_comp_right hΦZ Y (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp [H, L]
  letI := h.chartedSpace
  have hg₀ : g₀ ∈ (h.chart g₀).source := mem_chart_source 𝔤 g₀
  have hsrc : (h.chart g₀).source ∈ 𝓝 g₀ := (h.chart g₀).open_source.mem_nhds hg₀
  have hev : (fun p : P × G => iteratedFDeriv ℝ k (fun Y => ψ Y p.2) p.1) =ᶠ[𝓝 (Y₀, g₀)]
      fun p => H (p.1, h.chart g₀ p.2) := by
    filter_upwards [prod_mem_nhds univ_mem hsrc] with p hp
    have e : (fun Y => ψ Y p.2) = fun Y => Φ (Y, h.chart g₀ p.2) := by
      funext Y
      simp only [hΦdef]
      rw [show g₀ * h.expG (h.chart g₀ p.2) = p.2 from (h.chart g₀).left_inv hp.2]
    rw [e, hpart]
  refine ContinuousAt.congr ?_ hev.symm
  exact hH.continuousAt.comp (continuousAt_fst.prodMk
    (((h.chart g₀).continuousAt hg₀).comp continuousAt_snd))
end GroundTheory.Automorphic.IsExpLieAlgebra
