-- Prove2me | solution 1 for GlobalTheory.OpTrace.isOpen_leftStabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:07.121528+00:00
-- url     : https://prove2.me/submissions/d4396706-5588-499a-bade-cb8779053647

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional

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
namespace GlobalTheory.OpTrace
theorem _root_.solution [IsTopologicalGroup G] {f : G → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) : IsOpen (leftStabilizer f : Set G) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h : ∀ᶠ k in nhds (1 : G), ∀ g ∈ tsupport f, f (k * g) = f g ∧ f (k⁻¹ * g) = f g := by
    refine hc.isCompact.eventually_forall_of_forall_eventually fun y _ => ?_
    have h1 := (hf.comp_continuous (continuous_fst.mul continuous_snd)).eventually_eq ((1 : G), y)
    have h2 := (hf.comp_continuous (continuous_fst.inv.mul continuous_snd)).eventually_eq
      ((1 : G), y)
    have h3 := (hf.comp_continuous (continuous_snd (X := G))).eventually_eq ((1 : G), y)
    filter_upwards [h1, h2, h3] with z a b c
    simp only [Function.comp_apply, Pi.mul_apply, Pi.inv_apply, one_mul, inv_one] at a b c
    exact ⟨a.trans c.symm, b.trans c.symm⟩
  filter_upwards [h] with k hk g
  by_cases hg : g ∈ tsupport f
  · exact (hk g hg).1
  · by_cases hg' : k * g ∈ tsupport f
    · simpa using (hk _ hg').2.symm
    · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hg']
end GlobalTheory.OpTrace
