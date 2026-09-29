-- Prove2me | solution 1 for MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/97345e24-1b8f-50ad-9fd4-52b64bdff1ac

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant

set_option autoImplicit false

open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal NNReal Topology Pointwise

namespace P2mBruhat

variable {T : Type*} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  (S : Subgroup T) (hS : IsClosed (S : Set T)) [MeasurableSpace S] [BorelSpace S]
  (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]

theorem fibre_continuous (ψ : T → ℝ) (hψ : Continuous ψ) (t : T) : Continuous fun s : S => ψ ((s : T) * t) :=
  hψ.comp (continuous_subtype_val.mul continuous_const)

include hS in
theorem fibre_hasCompactSupport (ψ : T → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (t : T) :
    HasCompactSupport fun s : S => ψ ((s : T) * t) := by

  let K : Set T := (fun x => x * t⁻¹) '' tsupport ψ
  have hKc : IsCompact K := hψc.image (continuous_mul_right t⁻¹)
  have hKcl : IsClosed K := by
    have : K = (Homeomorph.mulRight t⁻¹) '' tsupport ψ := rfl
    rw [this]
    exact (Homeomorph.mulRight t⁻¹).isClosed_image.2 (isClosed_tsupport ψ)
  have hpre : IsCompact ((Subtype.val : S → T) ⁻¹' K) := hS.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  have hprecl : IsClosed ((Subtype.val : S → T) ⁻¹' K) := hKcl.preimage continuous_subtype_val
  refine IsCompact.of_isClosed_subset hpre isClosed_closure ?_
  refine closure_minimal (fun s hs => ?_) hprecl
  have hst : (s : T) * t ∈ tsupport ψ := subset_tsupport _ hs
  exact ⟨(s : T) * t, hst, by simp⟩

noncomputable def mass (ψ : T → ℝ) (t : T) : ℝ := ∫ s : S, ψ ((s : T) * t) ∂τS

include hS in
theorem mass_pos (ψ : T → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (t : T) (s₀ : S) (h1 : ψ ((s₀ : T) * t) ≠ 0) : 0 < mass S τS ψ t :=
  (fibre_continuous S ψ hψ t).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (fibre_hasCompactSupport S hS ψ hψ hψc t) (fun s => hψ0 _) h1

omit [LocallyCompactSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] in
theorem mass_mul_left (ψ : T → ℝ) (s' : S) (t : T) : mass S τS ψ ((s' : T) * t) = mass S τS ψ t := by
  unfold mass
  haveI : τS.IsMulRightInvariant := by
    have h := (inferInstance : (τS.inv).IsMulRightInvariant)
    rwa [Measure.inv_eq_self] at h
  have h := integral_mul_right_eq_self (μ := τS) (fun s : S => ψ ((s : T) * t)) s'
  simp only [Subgroup.coe_mul, mul_assoc] at h
  exact h

omit [τS.IsInvInvariant] in
include hS in

theorem mass_continuous (ψ : T → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψ1 : ∀ x, |ψ x| ≤ 1) :
    Continuous (mass S τS ψ) := by
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds t₀

  let L : Set T := tsupport ψ * N⁻¹
  have hLc : IsCompact L := hψc.mul hNc.inv
  have hpre : IsCompact ((Subtype.val : S → T) ⁻¹' L) := hS.isClosedEmbedding_subtypeVal.isCompact_preimage hLc
  obtain ⟨V, hVo, hLV, hVc⟩ := exists_isOpen_superset_and_isCompact_closure hpre
  have hVfin : τS V < ∞ := (measure_mono subset_closure).trans_lt hVc.measure_lt_top
  refine continuousAt_of_dominated (bound := V.indicator fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun t => (fibre_continuous S ψ hψ t).aestronglyMeasurable
  · filter_upwards [hN] with t ht
    refine Eventually.of_forall fun s => ?_
    by_cases hs : ψ ((s : T) * t) = 0
    · rw [hs, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · have hmem : s ∈ V := by
        apply hLV
        have hst : (s : T) * t ∈ tsupport ψ := subset_tsupport _ hs
        exact Set.mem_mul.2 ⟨(s : T) * t, hst, t⁻¹, Set.inv_mem_inv.2 ht, by simp⟩
      rw [Set.indicator_of_mem hmem, Real.norm_eq_abs]
      exact hψ1 _
  · exact (integrableOn_const hVfin.ne).integrable_indicator hVo.measurableSet
  · exact Eventually.of_forall fun s => (hψ.comp (continuous_const.mul continuous_id)).continuousAt

end P2mBruhat

theorem solution
    {T : Type*} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup T) (hS : IsClosed (S : Set T)) [MeasurableSpace S] [BorelSpace S]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (C : Set T) (hC : IsCompact C) (hSC : ∀ t : T, ∃ s : S, ∃ c ∈ C, t = (s : T) * c) :
    ∃ β : T → ℝ, Continuous β ∧ HasCompactSupport β ∧ (∀ t, 0 ≤ β t) ∧
      ∀ t : T, ∫ s : S, β ((s : T) * t) ∂τS = 1 := by

  obtain ⟨ψ, hψC, -, hψc, hψ01⟩ := exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => (hψ01 x).1
  have hψ1 : ∀ x, |ψ x| ≤ 1 := fun x => by rw [abs_of_nonneg (hψ0 x)]; exact (hψ01 x).2
  set m := P2mBruhat.mass S τS ψ with hm
  have hmpos : ∀ t, 0 < m t := by
    intro t
    obtain ⟨s₀, c, hc, rfl⟩ := hSC t
    refine P2mBruhat.mass_pos S hS τS ψ ψ.continuous hψc hψ0 _ s₀⁻¹ ?_
    rw [Subgroup.coe_inv, inv_mul_cancel_left, hψC hc]
    exact one_ne_zero
  have hmcont : Continuous m := P2mBruhat.mass_continuous S hS τS ψ ψ.continuous hψc hψ1
  refine ⟨fun t => ψ t / m t, ψ.continuous.div hmcont (fun t => (hmpos t).ne'), ?_, fun t => div_nonneg (hψ0 t) (hmpos t).le, fun t => ?_⟩
  · exact hψc.mono (fun x hx => by
      rw [Function.mem_support] at hx ⊢
      exact fun h0 => hx (by rw [h0, zero_div]))
  ·
    have hinv : ∀ s : S, m ((s : T) * t) = m t := fun s => P2mBruhat.mass_mul_left S τS ψ s t
    simp_rw [hinv]
    rw [integral_div, div_eq_one_iff_eq (hmpos t).ne']
    rfl

end S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant
end P2MW
export P2MW.S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_subgroup_mul_eq_one_of_isInvInvariant (solution)
