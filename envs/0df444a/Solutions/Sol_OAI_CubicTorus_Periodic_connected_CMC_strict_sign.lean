-- Prove2me | solution 1 for OAI.CubicTorus.Periodic.connected_CMC_strict_sign
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:58:36.356929+00:00
-- url     : https://prove2.me/submissions/6698dff2-dcc2-4527-bf6f-a62e2f09dab6

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_Periodic_profile_hessian_of_CMC
import Theorems.Thm_OAI_CubicTorus_antitoneOn_isoperimetricProfile_half
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_connected_curvature_integral_pos
import Theorems.Thm_OAI_CubicTorus_monotoneOn_isoperimetricProfile_half
import Theorems.Thm_OAI_CubicTorus_profile_upper_support_slope_nonneg
import Theorems.Thm_OAI_CubicTorus_profile_upper_support_slope_nonpos

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_TorusCoordinatePermute
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Reduction

lemma second_deriv_nonneg_of_right_min {f : ℝ → ℝ} {x : ℝ}
    (hc : ContinuousAt f x) (hd : deriv f x=0)
    (hmin : ∀ᶠ y in 𝓝 x,x<y → f x≤f y) : 0≤deriv (deriv f) x := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hd hc
  have he : ∀ᶠ y in 𝓝 x,x<y → f y=f x := by
    filter_upwards [hmin,hmax] with y hy hmy
    exact fun hxy ↦ le_antisymm hmy (hy hxy)
  have hn := deriv_neg_right_of_sign_deriv
    ((eventually_nhdsWithin_sign_eq_of_deriv_neg hneg hd).filter_mono nhdsWithin_le_nhds)
  have hfalse : ∀ᶠ y in 𝓝[>] x,False := by
    filter_upwards [he.eventually_nhds.filter_mono nhdsWithin_le_nhds,
      hn,self_mem_nhdsWithin] with y hy hny hxy
    have heq : f=ᶠ[𝓝 y](fun _ ↦ f x) := by
      filter_upwards [hy,Ioi_mem_nhds hxy] with z hz hxz
      exact hz hxz
    have hz := heq.deriv_eq
    simp only [deriv_const'] at hz
    exact hny.ne hz
  obtain ⟨y,hy⟩ := hfalse.exists
  exact hy

end Reduction
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Reduction

lemma second_deriv_nonneg_of_left_min {f : ℝ → ℝ} {x : ℝ}
    (hc : ContinuousAt f x) (hd : deriv f x=0)
    (hmin : ∀ᶠ y in 𝓝 x,y<x → f x≤f y) : 0≤deriv (deriv f) x := by
  by_contra! hneg
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hd hc
  have he : ∀ᶠ y in 𝓝 x,y<x → f y=f x := by
    filter_upwards [hmin,hmax] with y hy hmy
    exact fun hxy ↦ le_antisymm hmy (hy hxy)
  have hn := deriv_pos_left_of_sign_deriv
    ((eventually_nhdsWithin_sign_eq_of_deriv_neg hneg hd).filter_mono nhdsWithin_le_nhds)
  have hfalse : ∀ᶠ y in 𝓝[<] x,False := by
    filter_upwards [he.eventually_nhds.filter_mono nhdsWithin_le_nhds,
      hn,self_mem_nhdsWithin] with y hy hny hxy
    have heq : f=ᶠ[𝓝 y](fun _ ↦ f x) := by
      filter_upwards [hy,Iio_mem_nhds hxy] with z hz hxz
      exact hz hxz
    have hz := heq.deriv_eq
    simp only [deriv_const'] at hz
    exact hny.ne' hz
  obtain ⟨y,hy⟩ := hfalse.exists
  exact hy

end Reduction
namespace Periodic

theorem connected_support_of_CMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) :
    ∃ C : ℝ → ℝ,Reduction.UpperSupport isoperimetricProfile C V ∧
      deriv C V=H/2 ∧ deriv (deriv C) V<0 := by
  obtain ⟨N,C,hN,hp,hae,hs,hd,hdd⟩ := profile_hessian_of_CMC hV hE hmin hμ hCMC
  have hpos := isMinimizerAt_connected_curvature_integral_pos hV hE hmin hc hμ hN hp hae
  refine ⟨C,hs,hd,?_⟩
  have hprod : (isoperimetricProfile V)^2*deriv (deriv C) V<0 := by
    rw [hdd]; linarith
  by_contra! hnon
  exact (mul_nonneg (sq_nonneg _) hnon).not_gt hprod

theorem connected_CMC_strict_sign_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) :
    (V<1/2 → 0<H) ∧ (1/2<V → H<0) := by
  obtain ⟨C,hs,hd,hdd⟩ := connected_support_of_CMC hV hE hmin hc hμ hCMC
  constructor
  · intro hh
    have hn := profile_upper_support_slope_nonneg ⟨hV.1,hh⟩ hs
    have hp : 0<deriv C V := by
      apply lt_of_le_of_ne hn
      intro he
      have hr : ∀ᶠ W in 𝓝 V,V<W → C V≤C W := by
        filter_upwards [hs.above,Iio_mem_nhds hh] with W hW hWh hVW
        rw [hs.contact]
        exact (monotoneOn_isoperimetricProfile_half ⟨hV.1.le,hh.le⟩
          ⟨hV.1.le.trans hVW.le,hWh.le⟩ hVW.le).trans hW
      exact (Reduction.second_deriv_nonneg_of_right_min hs.smooth.continuousAt he.symm hr).not_gt hdd
    rw [hd] at hp
    linarith
  · intro hh
    have hn := profile_upper_support_slope_nonpos ⟨hh,hV.2⟩ hs
    have hp : deriv C V<0 := by
      apply lt_of_le_of_ne hn
      intro he
      have hr : ∀ᶠ W in 𝓝 V,W<V → C V≤C W := by
        filter_upwards [hs.above,Ioi_mem_nhds hh] with W hW hWh hWV
        rw [hs.contact]
        exact (antitoneOn_isoperimetricProfile_half
          ⟨hWh.le,hWV.le.trans hV.2.le⟩ ⟨hh.le,hV.2.le⟩ hWV.le).trans hW
      exact (Reduction.second_deriv_nonneg_of_left_min hs.smooth.continuousAt he hr).not_gt hdd
    rw [hd] at hp
    linarith

end Periodic
end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.Periodic.connected_CMC_strict_sign_oai := @OAI.CubicTorus.Periodic.connected_CMC_strict_sign_oai
