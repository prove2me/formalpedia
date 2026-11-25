-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.repOp_convolution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:12.244804+00:00
-- url     : https://prove2.me/submissions/18203dfa-4913-4bd0-9f52-b2592eeeb852

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsHilbertSchmidt_smul
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_smul
import Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_isRepOp
import Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_repOp_apply

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
variable {G : Type*} [Group G] [TopologicalSpace G]
  {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [MeasurableSpace G]
variable {π : G →* (H →L[ℂ] H)} {μ : Measure G} {f f' : G → ℂ}
variable [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
namespace GlobalTheory.OpTrace
namespace IsUnitaryRep
theorem _root_.solution [IsTopologicalGroup G] [BorelSpace G] [μ.IsMulLeftInvariant]
    (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f)
    (hf' : Continuous f') (hc' : HasCompactSupport f') :
    IsRepOp π μ (fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ) (repOp π μ f ∘L repOp π μ f') := by
  intro v
  have hF : Continuous (Function.uncurry fun x y : G => (f x * f' (x⁻¹ * y)) • π y v) :=
    ((hf.comp continuous_fst).mul (hf'.comp (continuous_fst.inv.mul continuous_snd))).smul
      ((hπ.continuous_apply v).comp continuous_snd)
  have hK : IsCompact (tsupport f ×ˢ (tsupport f * tsupport f')) := hc.prod (hc.mul hc')
  have h0 : ∀ x y : G, (x, y) ∉ tsupport f ×ˢ (tsupport f * tsupport f') →
      f x * f' (x⁻¹ * y) = 0 := by
    intro x y h
    by_contra hne
    have h1 := subset_tsupport f (left_ne_zero_of_mul hne)
    have h2 := subset_tsupport f' (right_ne_zero_of_mul hne)
    exact h ⟨h1, x, h1, _, h2, by simp⟩
  have hFc : HasCompactSupport (Function.uncurry fun x y : G => (f x * f' (x⁻¹ * y)) • π y v) :=
    HasCompactSupport.intro hK fun p hp => by simp [Function.uncurry, h0 p.1 p.2 hp]
  have hcont : Continuous fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ := by
    refine continuousOn_univ.1 (continuousOn_integral_of_compact_support
      (f := fun y x => f x * f' (x⁻¹ * y)) (s := Set.univ) hc ?_ fun y x _ hx => ?_)
    · exact ((hf.comp continuous_snd).mul
        (hf'.comp (continuous_snd.inv.mul continuous_fst))).continuousOn
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hcs : HasCompactSupport fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ :=
    HasCompactSupport.intro (hc.mul hc') fun y hy => by
      simp [fun x => h0 x y fun h => hy h.2]
  refine ⟨(hπ.isRepOp hcont hcs v).1, ?_⟩
  simp only [← integral_smul_const]
  rw [← integral_integral_swap_of_hasCompactSupport hF hFc, comp_apply, hπ.repOp_apply hf hc,
    hπ.repOp_apply hf' hc']
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [mul_smul, integral_smul]
  rw [← (π x).integral_comp_comm (hπ.isRepOp hf' hc' v).1,
    ← integral_mul_left_eq_self (fun y => f' (x⁻¹ * y) • π y v) x]
  simp
end IsUnitaryRep
end GlobalTheory.OpTrace
