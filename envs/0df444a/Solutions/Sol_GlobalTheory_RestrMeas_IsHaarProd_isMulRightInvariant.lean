-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsHaarProd.isMulRightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:32:56.379161+00:00
-- url     : https://prove2.me/submissions/31638a54-4e28-44de-9956-ab1977298b3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
import Theorems.Thm_GlobalTheory_RestrMeas_IsRestrGroup_measurableSet_cyl
import Theorems.Thm_GlobalTheory_RestrMeas_IsHaarProd_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ μ' : Measure X}
variable [BorelSpace X] [∀ w, BorelSpace (Ya w)] [∀ v, BorelSpace (Yf v)] [IsTopologicalGroup X]
variable [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)]
variable [∀ w, SecondCountableTopology (Ya w)] [∀ v, IsTopologicalGroup (Yf v)] [∀ v, LocallyCompactSpace (Yf v)]
  [∀ v, SecondCountableTopology (Yf v)]
omit [∀ w, SecondCountableTopology (Ya w)] [∀ v, LocallyCompactSpace (Yf v)] [∀ v, SecondCountableTopology (Yf v)]
namespace GlobalTheory.RestrMeas
namespace IsHaarProd
theorem _root_.solution (h : IsHaarProd pa pf K μa μf μ) (hX : IsRestrGroup pa pf K)
    [∀ w, (μa w).IsMulRightInvariant] [∀ v, (μf v).IsMulRightInvariant] : μ.IsMulRightInvariant := by
  refine ⟨fun g => IsHaarProd.unique hX.isOpen_K hX.isCompact_K ?_ h⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually (h4.1.and (hX.eventually_mem g))
  refine ⟨h1, h2, inferInstance, isCylProd_of_large (fun v => (hX.isOpen_K v).measurableSet) S₀
    (fun v hv => (hS v hv).1) (fun _ _ => rfl) fun S hs A B hA hB => ?_⟩
  have e := h4.2 S (fun v hv => (hS v fun h' => hv (hs h')).1) (fun w => (· * pa w g) ⁻¹' A w)
    (fun v => (· * pf v g) ⁻¹' B v) (fun w => measurable_mul_const _ (hA w)) fun v hv => measurable_mul_const _ (hB v hv)
  simp only [measure_preimage_mul_right] at e
  rw [Measure.map_apply (measurable_mul_const g) (hX.measurableSet_cyl hA hB), ← e]
  refine congrArg μ (Set.ext fun x => ?_)
  simp only [mem_preimage, mem_cyl, map_mul]
  exact and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun v hv =>
    (K v).mul_mem_cancel_right (hS v fun h' => hv (hs h')).2
end IsHaarProd
end GlobalTheory.RestrMeas
