-- Prove2me | solution 1 for MeasureTheory.exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/be2beea5-2923-5a04-bb2a-ab8b1ee9c0e8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Topology Filter Set
open scoped Pointwise

namespace TSec25

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Average

variable (T : Subgroup G) [MeasurableSpace T] [BorelSpace T] (τ : Measure T)

theorem isClosedEmbedding_val_mul (hT : IsClosed (T : Set G)) (x : G) : IsClosedEmbedding fun t : T => (t : G) * x :=
  (Homeomorph.mulRight x).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal

noncomputable def avg (ψ : G → ℝ) (x : G) : ℝ := ∫ t : T, ψ ((t : G) * x) ∂τ

variable {T τ}

theorem avg_mul [τ.IsMulRightInvariant] (ψ : G → ℝ) (t₀ : T) (x : G) :
    avg T τ ψ ((t₀ : G) * x) = avg T τ ψ x := by
  unfold avg
  have : (fun t : T => ψ ((t : G) * ((t₀ : G) * x))) = fun t : T => (fun s : T => ψ ((s : G) * x)) (t * t₀) := by
    funext t
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [this, integral_mul_right_eq_self (fun s : T => ψ ((s : G) * x)) t₀]

theorem avg_nonneg {ψ : G → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (x : G) : 0 ≤ avg T τ ψ x :=
  integral_nonneg fun _ => hψ _

theorem avg_pos [LocallyCompactSpace G] (hT : IsClosed (T : Set G)) [τ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts τ] {ψ : G → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψ : ∀ x, 0 ≤ ψ x) {x : G} (hx : ψ x ≠ 0) : 0 < avg T τ ψ x := by
  unfold avg
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : T)) ?_ ?_ (fun t => hψ _) ?_
  · exact hψc.comp (isClosedEmbedding_val_mul T hT x).continuous
  · exact hψs.comp_isClosedEmbedding (isClosedEmbedding_val_mul T hT x)
  · simpa using hx

theorem continuous_avg [LocallyCompactSpace G] [SecondCountableTopology G] (hT : IsClosed (T : Set G))
    [IsLocallyFiniteMeasure τ] {ψ : G → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) :
    Continuous (avg T τ ψ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hN, hNx₀⟩ := exists_compact_mem_nhds x₀

  set s : Set T := ((↑) : T → G) ⁻¹' (tsupport ψ * N⁻¹) with hs
  have hsc : IsCompact s :=
    hT.isClosedEmbedding_subtypeVal.isCompact_preimage (hψs.mul hN.inv)
  have hF : Continuous (fun p : G × T => ψ ((p.2 : G) * p.1)) :=
    hψc.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have hcont : Continuous fun x => ∫ t in s, ψ ((t : G) * x) ∂τ :=
    continuous_parametric_integral_of_continuous (f := fun x (t : T) => ψ ((t : G) * x))
      (by exact hF) hsc
  have heq : ∀ x ∈ N, avg T τ ψ x = ∫ t in s, ψ ((t : G) * x) ∂τ := by
    intro x hx
    unfold avg
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    by_contra hne
    apply ht
    rw [hs, mem_preimage]
    have h1 : (t : G) * x ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hne)
    refine Set.mem_mul.mpr ⟨(t : G) * x, h1, x⁻¹, Set.inv_mem_inv.mpr hx, ?_⟩
    simp
  have hev : avg T τ ψ =ᶠ[𝓝 x₀] fun x => ∫ t in s, ψ ((t : G) * x) ∂τ :=
    Filter.eventually_of_mem hNx₀ heq
  exact (hcont.continuousAt.congr hev.symm)

end Average

theorem main [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ W : G → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable W ∧ HasCompactSupport W ∧ (∃ B : ℝ, ∀ x, W x ≤ B) ∧
      ∀ x : G, (∃ t : T, ∃ k ∈ Ω, x = (t : G) * k) → ∫ t : T, W ((t : G) * x) ∂τ = 1 := by
  by_cases hne : Ω.Nonempty
  swap
  · refine ⟨fun _ => 0, fun _ => le_rfl, measurable_const, ?_, ⟨0, fun _ => le_rfl⟩, ?_⟩
    · exact HasCompactSupport.zero
    · rintro x ⟨t, k, hk, -⟩
      exact absurd ⟨k, hk⟩ hne
  obtain ⟨ψ, hψC, -, hψs, hψ01⟩ := exists_continuous_one_zero_of_isCompact hΩ isClosed_empty
    (Set.disjoint_empty Ω)
  have hψc : Continuous ψ := ψ.continuous
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => (hψ01 x).1
  have hψ1 : ∀ x, ψ x ≤ 1 := fun x => (hψ01 x).2
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hΨc : Continuous (avg T τ ψ) := continuous_avg hT hψc hψs

  obtain ⟨k₀, hk₀, hmin⟩ := hΩ.exists_isMinOn hne hΨc.continuousOn
  set c : ℝ := avg T τ ψ k₀ with hc
  have hcpos : 0 < c := avg_pos hT hψc hψs hψ0 (by rw [hψC hk₀]; simp)
  refine ⟨fun x => ψ x / max (avg T τ ψ x) c, fun x => div_nonneg (hψ0 x) (hcpos.le.trans (le_max_right _ _)),
    hψc.measurable.div (hΨc.measurable.max measurable_const), ?_, ⟨1 / c, fun x => ?_⟩, ?_⟩
  · refine hψs.mono ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    exact fun h => hx (by simp [h])
  · have hm : c ≤ max (avg T τ ψ x) c := le_max_right _ _
    calc ψ x / max (avg T τ ψ x) c ≤ 1 / max (avg T τ ψ x) c :=
          div_le_div_of_nonneg_right (hψ1 x) (hcpos.le.trans hm)
      _ ≤ 1 / c := one_div_le_one_div_of_le hcpos hm
  · rintro x ⟨t₀, k, hk, rfl⟩
    have hk' : c ≤ avg T τ ψ k := hmin hk
    have hinv : ∀ t : T, max (avg T τ ψ ((t : G) * ((t₀ : G) * k))) c = avg T τ ψ k := by
      intro t
      rw [avg_mul ψ t, avg_mul ψ t₀, max_eq_left hk']
    simp_rw [hinv]
    rw [integral_div]
    show avg T τ ψ ((t₀ : G) * k) / avg T τ ψ k = 1
    rw [avg_mul ψ t₀ k]
    exact div_self (ne_of_gt (hcpos.trans_le hk'))

end TSec25

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (Ω : Set G) (hΩ : IsCompact Ω) :
    ∃ W : G → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable W ∧ HasCompactSupport W ∧ (∃ B : ℝ, ∀ x, W x ≤ B) ∧
      ∀ x : G, (∃ t : T, ∃ k ∈ Ω, x = (t : G) * k) → ∫ t : T, W ((t : G) * x) ∂τ = 1 :=
  TSec25.main T hT τ Ω hΩ

end S_MeasureTheory_exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact
end P2MW
export P2MW.S_MeasureTheory_exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact (solution)
