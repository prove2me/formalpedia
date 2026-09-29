-- Prove2me | solution 1 for MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0cc1bf43-5d98-5a02-ac23-98e53d44abd2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one

namespace K42Trunc

open MeasureTheory Topology
open scoped Pointwise

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

noncomputable def fibreIntegral [MeasurableSpace H] (τ : Measure H) (ι : H →* G) (g : G → ℝ) (x : G) : ℝ :=
  ∫ h, g (ι h * x) ∂τ

omit [TopologicalSpace G] [TopologicalSpace H] in
theorem fibreIntegral_mul_left [MeasurableSpace H] [MeasurableMul H] (τ : Measure H)
    [τ.IsMulRightInvariant] (ι : H →* G) (g : G → ℝ) (h₀ : H) (x : G) :
    fibreIntegral τ ι g (ι h₀ * x) = fibreIntegral τ ι g x := by
  show ∫ h, g (ι h * (ι h₀ * x)) ∂τ = ∫ h, g (ι h * x) ∂τ
  have hfun : (fun h => g (ι h * (ι h₀ * x))) = fun h => (fun s => g (ι s * x)) (h * h₀) := by
    funext h
    simp only [map_mul, mul_assoc]
  rw [hfun]
  exact integral_mul_right_eq_self (fun s => g (ι s * x)) h₀

theorem continuous_shifted [ContinuousMul G] {ι : H →* G} (hι : Continuous ι) {g : G → ℝ}
    (hg : Continuous g) (x : G) : Continuous fun h => g (ι h * x) :=
  hg.comp (hι.mul continuous_const)

theorem hasCompactSupport_shifted [ContinuousMul G] [T2Space G] [T2Space H] {ι : H →* G} (hι : IsClosedEmbedding ι)
    {g : G → ℝ} (hgc : HasCompactSupport g) (x : G) : HasCompactSupport fun h => g (ι h * x) := by
  refine HasCompactSupport.intro
    (hι.isCompact_preimage (hgc.image (continuous_id.mul (continuous_const (y := x⁻¹))))) fun t ht => ?_
  by_contra h
  exact ht ⟨ι t * x, subset_tsupport g h, by simp⟩

theorem continuous_fibreIntegral [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace H] [BorelSpace H] (τ : Measure H) [IsFiniteMeasureOnCompacts τ]
    {ι : H →* G} (hι : IsClosedEmbedding ι) {g : G → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (fibreIntegral τ ι g) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hN, hNx₀⟩ := exists_compact_mem_nhds x₀
  have hk : IsCompact (ι ⁻¹' (tsupport g * N⁻¹)) := hι.isCompact_preimage (hgc.mul hN.inv)
  have hcont : ContinuousOn (fun x => fibreIntegral τ ι g x) N := by
    refine continuousOn_integral_of_compact_support (f := fun x h => g (ι h * x)) hk ?_ ?_
    · exact (hg.comp ((hι.continuous.comp continuous_snd).mul continuous_fst)).continuousOn
    · intro p h hp hh
      by_contra hne
      exact hh ⟨ι h * p, subset_tsupport g hne, p⁻¹, Set.inv_mem_inv.mpr hp, by simp⟩
  exact hcont.continuousAt hNx₀

theorem fibreIntegral_pos [ContinuousMul G] [T2Space G] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (τ : Measure H) [τ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts τ] {ι : H →* G} (hι : IsClosedEmbedding ι)
    {g : G → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ y, 0 ≤ g y) {x : G}
    (hx : ∃ h : H, 0 < g (ι h * x)) : 0 < fibreIntegral τ ι g x := by
  obtain ⟨t, ht⟩ := hx
  refine (integral_pos_iff_support_of_nonneg (fun s => hg0 (ι s * x))
    ((continuous_shifted hι.continuous hg x).integrable_of_hasCompactSupport
      (hasCompactSupport_shifted hι hgc x))).mpr ?_
  exact (continuous_shifted hι.continuous hg x).isOpen_support.measure_pos τ ⟨t, ht.ne'⟩

end K42Trunc

set_option autoImplicit false

open MeasureTheory

theorem solution
    {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (τ : Measure H) [τ.IsHaarMeasure] [τ.IsMulRightInvariant]
    (ι : H →* G) (hι : Topology.IsClosedEmbedding ι)
    (K : Set G) (hK : IsCompact K) :
    ∃ w : G → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ g, 0 ≤ w g) ∧
      ∀ (h : H) (k : G), k ∈ K → ∫ h', w (ι h' * (ι h * k)) ∂τ = 1 := by
  classical
  obtain ⟨b, hbK, -, hbc, hb01⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  have hb0 : ∀ y, 0 ≤ b y := fun y => (hb01 y).1
  set β : G → ℝ := K42Trunc.fibreIntegral τ ι b with hβ
  have hβc : Continuous β := K42Trunc.continuous_fibreIntegral τ hι b.continuous hbc
  have hβinv : ∀ (h : H) (x : G), β (ι h * x) = β x := fun h x => K42Trunc.fibreIntegral_mul_left τ ι b h x
  have hβpos : ∀ k ∈ K, 0 < β k := fun k hk =>
    K42Trunc.fibreIntegral_pos τ hι b.continuous hbc hb0 ⟨1, by rw [map_one, one_mul, hbK hk]; exact one_pos⟩

  obtain ⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ k ∈ K, m ≤ β k := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun k hk => by simp [hKe] at hk⟩
    · obtain ⟨k₀, hk₀, hmin⟩ := hK.exists_isMinOn hKne hβc.continuousOn
      exact ⟨β k₀, hβpos k₀ hk₀, fun k hk => hmin hk⟩
  have hden : ∀ x, max (β x) m ≠ 0 := fun x => (lt_max_of_lt_right hm).ne'
  refine ⟨fun x => b x * (max (β x) m)⁻¹, ?_, ?_, ?_, ?_⟩
  · exact b.continuous.mul ((hβc.max continuous_const).inv₀ hden)
  · exact hbc.mul_right
  · intro g
    exact mul_nonneg (hb0 g) (inv_nonneg.mpr (le_max_of_le_right hm.le))
  · intro h k hk
    have hx : m ≤ β (ι h * k) := by rw [hβinv]; exact hmK k hk
    have hmax : ∀ h' : H, max (β (ι h' * (ι h * k))) m = β (ι h * k) := fun h' => by
      rw [hβinv, max_eq_left hx]
    simp_rw [hmax]
    rw [integral_mul_const]
    show β (ι h * k) * (β (ι h * k))⁻¹ = 1
    exact mul_inv_cancel₀ (lt_of_lt_of_le hm hx).ne'

end S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one
end P2MW
export P2MW.S_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one (solution)
