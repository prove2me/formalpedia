-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsRestrGroup.existsUnique_isHaarProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:28.633505+00:00
-- url     : https://prove2.me/submissions/d26cb2f5-7906-4105-87fd-3a753c79ffb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
import Theorems.Thm_GlobalTheory_RestrMeas_cyl_self
import Theorems.Thm_GlobalTheory_RestrMeas_IsCylProd_smul
import Theorems.Thm_GlobalTheory_RestrMeas_IsHaarProd_smul
import Theorems.Thm_GlobalTheory_RestrMeas_IsHaarProd_unique
import Theorems.Thm_GlobalTheory_RestrMeas_IsRestrGroup_exists_factor

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
namespace GlobalTheory.RestrMeas
namespace IsRestrGroup
theorem _root_.solution (h : IsRestrGroup pa pf K) (μa : ∀ w, Measure (Ya w))
    (μf : ∀ v, Measure (Yf v)) [ha : ∀ w, (μa w).IsHaarMeasure] [hf : ∀ v, (μf v).IsHaarMeasure]
    (h1 : ∀ᶠ v in cofinite, μf v (K v) = 1) : ∃! μ : Measure X, IsHaarProd pa pf K μa μf μ := by
  refine existsUnique_of_exists_of_unique ?_ fun _ _ => IsHaarProd.unique h.isOpen_K h.isCompact_K
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually h1
  let ν : Measure X := haar
  let C : ∀ w, TopologicalSpace.PositiveCompacts (Ya w) := fun w => Classical.arbitrary _
  let t := ν {x | (∀ w, pa w x ∈ C w) ∧ ∀ v, pf v x ∈ K v}
  let k := (∏ w, μa w (C w)) * ∏ v ∈ S₀, μf v (K v)
  have k0 : k ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => (measure_pos_of_nonempty_interior _ (C w).interior_nonempty).ne')
      (Finset.prod_ne_zero_iff.2 fun v _ => ((h.isOpen_K v).measure_pos _ ⟨1, one_mem _⟩).ne')
  have kt : k ≠ ∞ := ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => (C w).isCompact.measure_lt_top.ne)
      (ENNReal.prod_ne_top fun v _ => (h.isCompact_K v).measure_lt_top.ne)
  have tt : t ≠ ∞ := (h.isCompact_level (fun w => C w) fun w => (C w).isCompact).measure_lt_top.ne
  have t0 : t ≠ 0 := by
    choose a ha using fun w => (C w).interior_nonempty
    obtain ⟨x, hx1, hx2⟩ := h.exists_eq a 1 (Eventually.of_forall fun v => one_mem _)
    have ho : IsOpen ((⋂ w, pa w ⁻¹' interior (C w)) ∩ {x | ∀ v, pf v x ∈ K v}) :=
      (isOpen_iInter_of_finite fun w => isOpen_interior.preimage (h.continuous_pa w)).inter h.isOpen_level
    refine ne_bot_of_le_ne_bot (ho.measure_pos ν ⟨x, mem_iInter.2 fun w => ?_, fun v => ?_⟩).ne'
      (measure_mono fun y hy => ⟨fun w => interior_subset (mem_iInter.1 hy.1 w), hy.2⟩)
    · rw [mem_preimage, hx1]; exact ha w
    · rw [hx2]; exact one_mem _
  refine ⟨(k / t) • ν, ha, hf, IsHaarMeasure.smul ν (ENNReal.div_ne_zero.2 ⟨k0, tt⟩) (ENNReal.div_ne_top kt t0),
    isCylProd_of_large (fun v => (h.isOpen_K v).measurableSet) S₀ hS (fun _ _ => rfl) fun S hs A B hA hB => ?_⟩
  obtain ⟨c, hc⟩ := h.exists_factor μa μf ν S
  have e := hc (fun w => C w) (fun v => K v) (fun w => (C w).isCompact.measurableSet)
    fun v _ => (h.isOpen_K v).measurableSet
  rw [cyl_self, ← Finset.prod_subset hs fun v _ hv => hS v hv] at e
  have e' : k / t * c = 1 := by
    rw [div_eq_mul_inv, mul_right_comm, mul_comm k, ← show t = c * k from e, ENNReal.mul_inv_cancel t0 tt]
  rw [Measure.smul_apply, hc A B hA hB, smul_eq_mul, ← mul_assoc, e', one_mul]
end IsRestrGroup
end GlobalTheory.RestrMeas
