-- Prove2me | solution 1 for MeasureTheory.Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/dcce8244-026f-5d03-b84d-d8a17b1dc4bd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace INVCPT

open Set Filter Topology MulAction MeasureTheory.Measure

section fibreAverage

variable {L : Type*} [Group L] [MeasurableSpace L]

noncomputable def fib {S : Subgroup L} (μS : Measure S) (A : Set L) (l : L) : ℝ≥0∞ :=
  μS ((fun t : S => l * (t : L)) ⁻¹' A)

lemma fib_def {S : Subgroup L} (μS : Measure S) (A : Set L) (l : L) :
    fib μS A l = μS ((fun t : S => l * (t : L)) ⁻¹' A) := rfl

lemma measurable_coe_mul [TopologicalSpace L] [IsTopologicalGroup L] [BorelSpace L]
    (S : Subgroup L) (l : L) : Measurable (fun t : S => l * (t : L)) :=
  (continuous_const.mul continuous_subtype_val).measurable

lemma measurable_fib [TopologicalSpace L] [IsTopologicalGroup L] [BorelSpace L]
    [SecondCountableTopology L] {S : Subgroup L} (μS : Measure S) [SFinite μS]
    {A : Set L} (hA : MeasurableSet A) : Measurable (fib μS A) := by
  have hm : MeasurableSet ((fun p : L × S => p.1 * (p.2 : L)) ⁻¹' A) :=
    (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd)) hA
  exact measurable_measure_prodMk_left hm

lemma fib_mul_coe [TopologicalSpace L] [IsTopologicalGroup L] [BorelSpace L] {S : Subgroup L} (μS : Measure S) [μS.IsMulLeftInvariant] (A : Set L)
    (l : L) (s : S) : fib μS A (l * (s : L)) = fib μS A l := by
  unfold fib
  have : (fun t : S => l * (s : L) * (t : L)) ⁻¹' A =
      (fun t : S => s * t) ⁻¹' ((fun t : S => l * (t : L)) ⁻¹' A) := by
    ext t
    simp [mul_assoc]
  rw [this, measure_preimage_mul]

lemma lowerSemicontinuous_fib [TopologicalSpace L] [IsTopologicalGroup L] {S : Subgroup L} (μS : Measure S) [μS.Regular] {U : Set L}
    (hU : IsOpen U) : LowerSemicontinuous (fib μS U) := by
  intro l₀ c hc
  have hV : IsOpen ((fun t : S => l₀ * (t : L)) ⁻¹' U) :=
    hU.preimage (continuous_const.mul continuous_subtype_val)
  obtain ⟨K, hKV, hK, hcK⟩ := hV.exists_lt_isCompact hc
  have hK' : IsCompact ((fun t : S => l₀ * (t : L)) '' K) :=
    hK.image (continuous_const.mul continuous_subtype_val)
  have hsub : (fun t : S => l₀ * (t : L)) '' K ⊆ U := image_subset_iff.mpr hKV
  obtain ⟨V, hV1, hVU⟩ := compact_open_separated_mul_left hK' hU hsub
  have hev : ∀ᶠ l in 𝓝 l₀, K ⊆ (fun t : S => l * (t : L)) ⁻¹' U := by
    rw [← map_mul_right_nhds_one l₀, eventually_map]
    filter_upwards [hV1] with v hv
    intro t ht
    show v * l₀ * (t : L) ∈ U
    rw [mul_assoc]
    exact hVU (Set.mul_mem_mul hv (mem_image_of_mem _ ht))
  filter_upwards [hev] with l hl
  exact hcK.trans_le (measure_mono hl)

end fibreAverage

end INVCPT

open INVCPT Set Filter Topology MulAction in
theorem solution
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (μL : Measure L) [μL.IsHaarMeasure]
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MulAction L X] [ContinuousSMul L X] [MulAction.IsPretransitive L X]
    (x₀ : X) (hx₀ : IsCompact (MulAction.stabilizer L x₀ : Set L))
    (σ : Measure X) [IsFiniteMeasureOnCompacts σ]
    (hσ : ∀ g : L, σ.map (fun x : X => g • x) = σ) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ σ = c • μL.map (fun g : L => g • x₀) := by

  obtain ⟨S, hS⟩ : ∃ S : Subgroup L, S = MulAction.stabilizer L x₀ := ⟨_, rfl⟩
  have hmemS : ∀ {l : L}, l ∈ S ↔ l • x₀ = x₀ := by
    intro l; rw [hS, MulAction.mem_stabilizer_iff]
  have hScpt : IsCompact (S : Set L) := hS ▸ hx₀
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hScpt
  have hπc : Continuous (fun g : L => g • x₀) := by fun_prop
  have hπm : Measurable (fun g : L => g • x₀) := hπc.measurable
  have hSclosed : IsClosed (S : Set L) := by
    have : (S : Set L) = (fun g : L => g • x₀) ⁻¹' {x₀} := by
      ext l; simp [hmemS]
    rw [this]
    exact isClosed_singleton.preimage hπc
  haveI : LocallyCompactSpace S := hSclosed.locallyCompactSpace
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set L)

  let K₀ : TopologicalSpace.PositiveCompacts S :=
    { carrier := univ, isCompact' := isCompact_univ, interior_nonempty' := by simp }
  let μS : Measure S := Measure.haarMeasure K₀
  haveI : IsProbabilityMeasure μS := ⟨by
    have h := Measure.haarMeasure_self (K₀ := K₀)
    exact h⟩

  have hπo : IsOpenMap (fun g : L => g • x₀) := isOpenMap_smul_of_sigmaCompact x₀
  choose sec hsec using fun x : X => MulAction.exists_smul_eq L x₀ x

  have hfib : ∀ (x : X) (t : S), (sec x * (t : L)) • x₀ = x := by
    intro x t
    rw [mul_smul, hmemS.mp t.2, hsec]

  have hF_eq : ∀ (A : Set L) (l l' : L), l • x₀ = l' • x₀ → fib μS A l = fib μS A l' := by
    intro A l l' h
    have hs : l⁻¹ * l' ∈ S := by
      rw [hmemS, mul_smul, ← h, inv_smul_smul]
    have : l' = l * ((⟨l⁻¹ * l', hs⟩ : S) : L) := by simp
    rw [this, fib_mul_coe]
  have hF_sec : ∀ (A : Set L) (l : L), fib μS A (sec (l • x₀)) = fib μS A l :=
    fun A l => hF_eq A _ _ (hsec _)

  have hG_open : ∀ U : Set L, IsOpen U → Measurable (fun x => fib μS U (sec x)) := by
    intro U hU
    apply LowerSemicontinuous.measurable
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro c
    have hlsc := (lowerSemicontinuous_iff_isOpen_preimage.mp (lowerSemicontinuous_fib μS hU)) c
    have : (fun x => fib μS U (sec x)) ⁻¹' Ioi c = (fun g : L => g • x₀) '' (fib μS U ⁻¹' Ioi c) := by
      ext x
      constructor
      · intro hx
        exact ⟨sec x, hx, hsec x⟩
      · rintro ⟨l, hl, rfl⟩
        simp only [mem_preimage, mem_Ioi] at hl ⊢
        rwa [hF_sec]
    rw [this]
    exact hπo _ hlsc
  have hG : ∀ A : Set L, MeasurableSet A → Measurable (fun x => fib μS A (sec x)) := by
    intro A hA
    induction A, hA using MeasurableSpace.induction_on_inter
      (BorelSpace.measurable_eq (α := L)) isPiSystem_isOpen with
    | empty => simp [fib_def]
    | basic U hU => exact hG_open U hU
    | compl A hA ih =>
      have : (fun x => fib μS Aᶜ (sec x)) = fun x => 1 - fib μS A (sec x) := by
        funext x
        rw [fib_def, fib_def, preimage_compl, prob_compl_eq_one_sub ((measurable_coe_mul S _) hA)]
      rw [this]
      exact measurable_const.sub ih
    | iUnion f hdisj hfm ih =>
      have : (fun x => fib μS (⋃ i, f i) (sec x)) = fun x => ∑' i, fib μS (f i) (sec x) := by
        funext x
        rw [fib_def, preimage_iUnion, measure_iUnion]
        · rfl
        · exact fun i j hij => (hdisj hij).preimage _
        · exact fun i => (measurable_coe_mul S _) (hfm i)
      rw [this]
      exact Measurable.tsum ih

  let k : X → Measure L := fun x => μS.map (fun t : S => sec x * (t : L))
  have hk_apply : ∀ (x : X) (A : Set L), MeasurableSet A → k x A = fib μS A (sec x) :=
    fun x A hA => Measure.map_apply (measurable_coe_mul S _) hA
  have hk : Measurable k := by
    refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
    have : (fun x => k x A) = fun x => fib μS A (sec x) := funext fun x => hk_apply x A hA
    rw [this]
    exact hG A hA
  let ν : Measure L := σ.bind k
  have hν : ∀ A : Set L, MeasurableSet A → ν A = ∫⁻ x, fib μS A (sec x) ∂σ := by
    intro A hA
    rw [Measure.bind_apply hA hk.aemeasurable]
    exact lintegral_congr (fun x => hk_apply x A hA)

  haveI : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    have hK' : IsCompact (closure K) := hK.closure
    have hπK : IsCompact ((fun g : L => g • x₀) '' closure K) := hK'.image hπc
    refine (measure_mono subset_closure).trans_lt ?_
    rw [hν _ isClosed_closure.measurableSet]
    refine lt_of_le_of_lt ?_ (hπK.measure_lt_top (μ := σ))
    refine (lintegral_mono (fun x => ?_)).trans (lintegral_indicator_one_le _)
    by_cases hx : x ∈ (fun g : L => g • x₀) '' closure K
    · rw [indicator_of_mem hx, Pi.one_apply]
      exact prob_le_one
    · have : (fun t : S => sec x * (t : L)) ⁻¹' closure K = ∅ := by
        ext t
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        intro ht
        exact hx ⟨_, ht, hfib x t⟩
      rw [fib_def, this, measure_empty]
      exact zero_le⟩

  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    ext A hA
    have hgA : MeasurableSet ((fun h : L => g * h) ⁻¹' A) := (continuous_const_mul g).measurable hA
    rw [Measure.map_apply (continuous_const_mul g).measurable hA, hν _ hgA, hν A hA]
    have h1 : ∀ x, fib μS ((fun h : L => g * h) ⁻¹' A) (sec x) = fib μS A (sec (g • x)) := by
      intro x
      rw [show g • x = (g * sec x) • x₀ by rw [mul_smul, hsec], hF_sec]
      simp only [fib_def, preimage_preimage, mul_assoc]
    simp_rw [h1]
    calc ∫⁻ x, fib μS A (sec (g • x)) ∂σ
        = ∫⁻ x, fib μS A (sec x) ∂(σ.map (fun x : X => g • x)) :=
          (lintegral_map (hG A hA) (continuous_const_smul g).measurable).symm
      _ = ∫⁻ x, fib μS A (sec x) ∂σ := by rw [hσ g]⟩

  have hmap : ν.map (fun g : L => g • x₀) = σ := by
    ext B hB
    rw [Measure.map_apply hπm hB, hν _ (hπm hB)]
    have h1 : ∀ x, fib μS ((fun g : L => g • x₀) ⁻¹' B) (sec x) = B.indicator 1 x := by
      intro x
      by_cases hx : x ∈ B
      · have : (fun t : S => sec x * (t : L)) ⁻¹' ((fun g : L => g • x₀) ⁻¹' B) = univ := by
          ext t; simp [hfib x t, hx]
        rw [fib_def, this, measure_univ, indicator_of_mem hx, Pi.one_apply]
      · have : (fun t : S => sec x * (t : L)) ⁻¹' ((fun g : L => g • x₀) ⁻¹' B) = ∅ := by
          ext t; simp [hfib x t, hx]
        rw [fib_def, this, measure_empty, indicator_of_notMem hx]
    simp_rw [h1]
    exact lintegral_indicator_one hB

  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • μL :=
    ⟨Measure.haarScalarFactor ν μL, Measure.isMulLeftInvariant_eq_smul ν μL⟩
  refine ⟨(c : ℝ≥0∞), ENNReal.coe_ne_top, ?_⟩
  rw [← hmap, hc, Measure.map_smul]
  ext s hs
  simp

end S_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer
end P2MW
export P2MW.S_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer (solution)
