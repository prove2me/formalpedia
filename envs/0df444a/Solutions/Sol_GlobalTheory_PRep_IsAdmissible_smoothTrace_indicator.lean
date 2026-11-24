-- Prove2me | solution 1 for GlobalTheory.PRep.IsAdmissible.smoothTrace_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:35.25598+00:00
-- url     : https://prove2.me/submissions/ab448385-c290-4927-9ee1-589d38dc5725

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_finRankTrace_eq
import Theorems.Thm_GlobalTheory_OpTrace_eq_of_forall_dual
import Theorems.Thm_GlobalTheory_OpTrace_mem_fixed
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_mem_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace G]
variable [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  {ρ : Representation ℂ G V} {f f' : G → ℂ}
namespace GlobalTheory.OpTrace
namespace _root_.GlobalTheory.PRep.IsAdmissible
theorem _root_.solution [μ.IsMulLeftInvariant] (hρ : IsAdmissible ρ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) :
    smoothTrace ρ μ ((K : Set G).indicator fun _ => 1) =
      μ.real K * Module.finrank ℂ (fixed ρ K) := by
  have hf : IsLocallyConstant ((K : Set G).indicator fun _ => (1 : ℂ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    by_cases hg : g ∈ (K : Set G)
    · exact ⟨K, ho, hg, fun x hx => by simp only [Set.indicator_of_mem, hx, hg]⟩
    · exact ⟨(K : Set G)ᶜ, (K.isClosed_of_isOpen ho).isOpen_compl, hg, fun x hx => by
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hg]⟩
  have hc : HasCompactSupport ((K : Set G).indicator fun _ => (1 : ℂ)) :=
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _
  have := hρ.2 K ho hK
  have hm := hρ.1.smoothOp_mem_fixed (μ := μ) hf hc (K := K) fun k hk g => by
    by_cases hg : g ∈ (K : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (K.mul_mem hk hg)]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem fun h => hg ((K.mul_mem_cancel_left hk).1 h)]
  have key : ((smoothOp ρ μ ((K : Set G).indicator fun _ => 1)).restrict fun x _ => hm x :
      fixed ρ K →ₗ[ℂ] fixed ρ K) = (μ.real K : ℂ) • LinearMap.id := by
    ext v
    refine eq_of_forall_dual fun l => ?_
    have h1 : (fun g => (K : Set G).indicator (fun _ => (1 : ℂ)) g • l (ρ g v)) =
        (K : Set G).indicator fun _ => l v := by
      ext g
      by_cases hg : g ∈ (K : Set G)
      · simp [Set.indicator_of_mem hg, mem_fixed.1 v.2 g hg]
      · simp [Set.indicator_of_notMem hg]
    rw [LinearMap.restrict_coe_apply, hρ.1.map_smoothOp hf hc, h1,
      integral_indicator_const _ ho.measurableSet]
    simp
  rw [smoothTrace, finRankTrace_eq _ _ hm, key]
  simp
end _root_.GlobalTheory.PRep.IsAdmissible
end GlobalTheory.OpTrace
