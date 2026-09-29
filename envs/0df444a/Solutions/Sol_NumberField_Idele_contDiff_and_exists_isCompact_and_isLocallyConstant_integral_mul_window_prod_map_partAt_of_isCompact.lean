-- Prove2me | solution 1 for NumberField.Idele.contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a2c6007e-df4c-5c7d-b21f-7133c451997f

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_NumberField_AdeleRing_isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside
import Theorems.Thm_MeasureTheory_contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

namespace R4X9

open NumberField Topology Filter MeasureTheory

theorem eventually_forall_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {Φ : X × Y → ℂ}
    (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) (b₀ : X) :
    ∀ᶠ b in 𝓝 b₀, ∀ y : Y, Φ (b, y) = Φ (b₀, y) := by
  have hK : IsCompact (Prod.snd '' tsupport Φ) := hcs.image continuous_snd
  have h1 : ∀ᶠ b in 𝓝 b₀, ∀ y ∈ Prod.snd '' tsupport Φ, Φ (b, y) = Φ (b₀, y) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have e1 : ∀ᶠ z : X × Y in 𝓝 (b₀, y), Φ z = Φ (b₀, y) :=
      ((IsLocallyConstant.iff_eventually_eq Φ).1 hlc) (b₀, y)
    have e2 : ∀ᶠ z : X × Y in 𝓝 (b₀, y), Φ (b₀, z.2) = Φ (b₀, y) := by
      have hc : Continuous fun z : X × Y => ((b₀, z.2) : X × Y) := continuous_const.prodMk continuous_snd
      have ht : Tendsto (fun z : X × Y => ((b₀, z.2) : X × Y)) (𝓝 (b₀, y)) (𝓝 (b₀, y)) := by
        have := hc.tendsto (b₀, y); simpa using this
      exact ht.eventually (((IsLocallyConstant.iff_eventually_eq Φ).1 hlc) (b₀, y))
    filter_upwards [e1, e2] with z hz1 hz2
    rw [hz2]; exact hz1
  filter_upwards [h1] with b hb y
  by_cases hy : y ∈ Prod.snd '' tsupport Φ
  · exact hb y hy
  · have h0 : ∀ b' : X, Φ (b', y) = 0 := fun b' =>
      image_eq_zero_of_notMem_tsupport fun hm => hy ⟨(b', y), hm, rfl⟩
    rw [h0, h0]

theorem tsupport_eq_support {X : Type*} [TopologicalSpace X] {Φ : X → ℂ} (hlc : IsLocallyConstant Φ) :
    tsupport Φ = Function.support Φ := by
  rw [tsupport, closure_eq_iff_isClosed]
  have : Function.support Φ = {x | Φ x = 0}ᶜ := by ext x; simp [Function.mem_support]
  rw [this]
  exact (hlc.isOpen_fiber 0).isClosed_compl

end R4X9

open Filter Topology

namespace R4X9

open NumberField Topology Filter MeasureTheory IsDedekindDomain

open scoped Classical in

theorem integrable_and_contDiff_fold
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (hξc : Continuous ξ)
    (G : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K → ℂ)
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (hGc : HasCompactSupport G)
    (Ca : Set (InfiniteAdeleRing K)ˣ) (hCa : IsCompact Ca)
    (hG0 : ∀ (x : mixedEmbedding.mixedSpace K) (y : InfiniteAdeleRing K),
      G (x, InfiniteAdeleRing.ringEquiv_mixedSpace K y) ≠ 0 → y ∈ Units.val '' Ca)
    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ S, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧
      ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0)
    (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) :
    (∀ x : mixedEmbedding.mixedSpace K,
      Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ξ zS *
          (G (x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)))
        (Measure.map (NumberField.Idele.partAt K S)
          (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : mixedEmbedding.mixedSpace K =>
      ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ξ zS *
          (G (x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
        ∂(Measure.map (NumberField.Idele.partAt K S)
          (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) := by
  classical
  set U : Set (AdeleRing (𝓞 K) K)ˣ := (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ) with hU
  set μS := Measure.map (NumberField.Idele.partAt K S) (ν.restrict U) with hμS
  set ρ := InfiniteAdeleRing.ringEquiv_mixedSpace K with hρ

  let Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K) := fun v => Prod.snd '' tsupport (Φf v)
  have hCf : ∀ v ∈ S, IsCompact (Cf v) := fun v hv => (hΦf v hv).2.1.image continuous_snd
  have hCf0 : ∀ v ∈ S, (0 : v.adicCompletion K) ∉ Cf v := by
    intro v hv ⟨p, hp, hp0⟩
    rw [tsupport_eq_support (hΦf v hv).1, Function.mem_support] at hp
    exact ((hΦf v hv).2.2 p hp).2 hp0

  set Box : Set (AdeleRing (𝓞 K) K)ˣ := {z : (AdeleRing (𝓞 K) K)ˣ |
      Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z ∈ Ca ∧
      ∀ v ∈ S, (((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v) ∈ Cf v} ∩ U with hBox
  have hBoxc : IsCompact Box :=
    NumberField.AdeleRing.isCompact_setOf_units_adeleArch_mem_and_apply_mem_inter_unitIdelesOutside K S Ca hCa Cf hCf hCf0
  set A : Set (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.partAt K S '' Box with hA
  have hAc : IsCompact A := hBoxc.image (NumberField.Idele.continuous_partAt K S)
  have hAm : MeasurableSet A := hAc.measurableSet

  have hpre : U ∩ NumberField.Idele.partAt K S ⁻¹' A = Box := by
    ext z
    constructor
    · rintro ⟨hzU, ⟨z', hz', hzz'⟩⟩
      refine ⟨⟨?_, fun v hv => ?_⟩, hzU⟩
      · have e : Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z = Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z' := by
          apply Units.ext
          show ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = ((z' : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1
          rw [← NumberField.Idele.partAt_fst K S z, ← NumberField.Idele.partAt_fst K S z', hzz']
        rw [e]; exact hz'.1.1
      · have e : ((z : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = ((z' : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v := by
          rw [← NumberField.Idele.partAt_snd_of_mem K S z hv, ← NumberField.Idele.partAt_snd_of_mem K S z' hv, hzz']
        rw [e]; exact hz'.1.2 v hv
    · intro hz
      exact ⟨hz.2, ⟨z, hz, rfl⟩⟩
  have hπm : Measurable (NumberField.Idele.partAt K S) := (NumberField.Idele.continuous_partAt K S).measurable
  have hμA : μS A < ⊤ := by
    rw [hμS, Measure.map_apply (hπm) hAm,
      Measure.restrict_apply (hAm.preimage (hπm)), Set.inter_comm, hpre]
    exact hBoxc.measure_lt_top

  obtain ⟨Mξ, hMξ⟩ := hAc.exists_bound_of_continuousOn hξc.continuousOn
  have hΦfb : ∀ v ∈ S, ∃ M : ℝ, 0 ≤ M ∧ ∀ p, ‖Φf v p‖ ≤ M := by
    intro v hv
    obtain ⟨M, hM⟩ := (hΦf v hv).2.1.exists_bound_of_continuous (hΦf v hv).1.continuous
    exact ⟨max M 0, le_max_right _ _, fun p => (hM p).trans (le_max_left _ _)⟩
  choose! Mf hMf0 hMf using hΦfb
  obtain ⟨MG, hMG⟩ := hGc.exists_bound_of_continuous hG.continuous

  let Pf : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun zS =>
    ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)
  let π : (AdeleRing (𝓞 K) K)ˣ → mixedEmbedding.mixedSpace K := fun zS =>
    ρ ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1
  have hPfc : Continuous Pf := by
    refine continuous_finset_prod _ fun v hv => ?_
    refine (hΦf v hv).1.continuous.comp (continuous_const.prodMk ?_)
    exact ((RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val))
  have hπc : Continuous π :=
    (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace K).comp (continuous_fst.comp Units.continuous_val)
  have hπ : Measurable π := hπc.measurable
  have hPfb : ∀ zS, ‖Pf zS‖ ≤ ∏ v ∈ S, Mf v := by
    intro zS
    simp only [Pf]
    rw [norm_prod]
    exact Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v hv => hMf v hv _

  let hw : (AdeleRing (𝓞 K) K)ˣ → ℂ := A.indicator fun zS => ξ zS * Pf zS
  have hwm : AEStronglyMeasurable hw μS :=
    (((hξc.mul hPfc).measurable).indicator hAm).aestronglyMeasurable
  have hwA : ∀ a ∈ A, ‖hw a‖ ≤ Mξ * ∏ v ∈ S, Mf v := by
    intro a ha
    simp only [hw, Set.indicator_of_mem ha, norm_mul]
    exact mul_le_mul (hMξ a ha) (hPfb a) (norm_nonneg _) ((norm_nonneg _).trans (hMξ a ha))
  have hw0 : ∀ a, a ∉ A → hw a = 0 := fun a ha => Set.indicator_of_notMem ha _

  have hae : ∀ x : mixedEmbedding.mixedSpace K,
      (fun zS : (AdeleRing (𝓞 K) K)ˣ => ξ zS * (G (x, π zS) * Pf zS)) =ᵐ[μS] fun zS => hw zS * G (x, π zS) := by
    intro x
    have hPm : MeasurableSet {w : (AdeleRing (𝓞 K) K)ˣ | ξ w * (G (x, π w) * Pf w) = hw w * G (x, π w)} := by
      refine measurableSet_eq_fun ?_ ?_
      · exact (hξc.mul ((hG.continuous.comp (continuous_const.prodMk hπc)).mul hPfc)).measurable
      · exact (((hξc.mul hPfc).measurable).indicator hAm).mul (hG.continuous.comp (continuous_const.prodMk hπc)).measurable
    rw [Filter.EventuallyEq, hμS, ae_map_iff (hπm).aemeasurable hPm]
    have hUo : IsOpen U := NumberField.Idele.isOpen_unitIdelesOutside K (↑S)
    filter_upwards [ae_restrict_mem hUo.measurableSet] with z hzU
    show ξ (NumberField.Idele.partAt K S z) * (G (x, π (NumberField.Idele.partAt K S z)) * Pf (NumberField.Idele.partAt K S z)) =
      hw (NumberField.Idele.partAt K S z) * G (x, π (NumberField.Idele.partAt K S z))
    by_cases hzA : NumberField.Idele.partAt K S z ∈ A
    · simp only [hw, Set.indicator_of_mem hzA]; ring
    · simp only [hw, Set.indicator_of_notMem hzA, zero_mul]
      by_contra hne
      have hG1 : G (x, π (NumberField.Idele.partAt K S z)) ≠ 0 := fun h => hne (by rw [h, zero_mul, mul_zero])
      have hP1 : Pf (NumberField.Idele.partAt K S z) ≠ 0 := fun h => hne (by rw [h, mul_zero, mul_zero])
      apply hzA
      refine ⟨z, ⟨⟨?_, fun v hv => ?_⟩, hzU⟩, rfl⟩
      · obtain ⟨u, hu, hueq⟩ := hG0 x _ hG1
        have e : Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z = u := by
          apply Units.ext
          show ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = (u : InfiniteAdeleRing K)
          rw [hueq, NumberField.Idele.partAt_fst]
        rw [e]; exact hu
      · have hv1 : Φf v (b v, (((NumberField.Idele.partAt K S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 :
            FiniteAdeleRing (𝓞 K) K) v) ≠ 0 := fun h => hP1 (Finset.prod_eq_zero hv h)
        rw [NumberField.Idele.partAt_snd_of_mem K S z hv] at hv1
        exact ⟨_, subset_tsupport _ hv1, rfl⟩

  have L := MeasureTheory.contDiff_and_hasCompactSupport_integral_mul_comp_of_contDiff_of_hasCompactSupport
    μS G hG hGc π hπ hw hwm A hAm hμA (Mξ * ∏ v ∈ S, Mf v) hwA hw0
  refine ⟨fun x => ?_, ?_⟩
  ·
    have hint : Integrable (fun zS => hw zS * G (x, π zS)) μS := by
      have hb : Integrable (A.indicator fun _ => (Mξ * ∏ v ∈ S, Mf v) * MG) μS :=
        (integrableOn_const hμA.ne).integrable_indicator hAm
      refine hb.mono' (hwm.mul (hG.continuous.comp (continuous_const.prodMk hπc)).measurable.aestronglyMeasurable)
        (Eventually.of_forall fun zS => ?_)
      by_cases hz : zS ∈ A
      · rw [Set.indicator_of_mem hz, norm_mul]
        exact mul_le_mul (hwA zS hz) (hMG _) (norm_nonneg _)
          ((norm_nonneg _).trans (hwA zS hz))
      · rw [Set.indicator_of_notMem hz, hw0 zS hz, zero_mul, norm_zero]
    exact hint.congr (hae x).symm
  · have e : (fun x : mixedEmbedding.mixedSpace K => ∫ zS, ξ zS * (G (x, π zS) * Pf zS) ∂μS) =
        fun x => ∫ zS, hw zS * G (x, π zS) ∂μS := funext fun x => integral_congr_ae (hae x)
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : mixedEmbedding.mixedSpace K => ∫ zS, ξ zS * (G (x, π zS) * Pf zS) ∂μS)
    rw [e]
    exact L.1

end R4X9

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (Φa : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ) (hΦa : ContDiff ℝ (⊤ : ℕ∞) Φa) (hΦac : HasCompactSupport Φa)
    (Ca : Set (InfiniteAdeleRing K)ˣ) (hCa : IsCompact Ca)
    (hΦa0 : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φa p ≠ 0 →
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1) ∈ Units.val '' Ca)
    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ S, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧
      ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) :
    (∀ b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K,
      ContDiff ℝ (⊤ : ℕ∞) fun x : mixedEmbedding.mixedSpace K =>
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) ∧
    (∃ C : Set (mixedEmbedding.mixedSpace K), IsCompact C ∧
      ∀ (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) (x : mixedEmbedding.mixedSpace K), x ∉ C →
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) = 0) ∧
    (∀ x : mixedEmbedding.mixedSpace K,
      IsLocallyConstant fun b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K =>
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) ∧
    (∃ Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K), (∀ v ∈ S, IsCompact (Cf v) ∧ (0 : v.adicCompletion K) ∉ Cf v) ∧
      ∀ (x : mixedEmbedding.mixedSpace K) (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K),
        (∃ v ∈ S, b v ∉ Cf v) →
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) = 0)  := by
  classical

  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro b
    let e := (ContinuousLinearEquiv.finTwoArrow ℝ (mixedEmbedding.mixedSpace K)).symm
    have hGe : (fun p : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K => Φa ![p.1, p.2]) = Φa ∘ e := by
      funext p
      simp only [Function.comp_apply, e, ContinuousLinearEquiv.finTwoArrow_symm_apply]
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun p : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K => Φa ![p.1, p.2]) := by
      rw [hGe]; exact hΦa.comp e.contDiff
    have hGc : HasCompactSupport (fun p : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K => Φa ![p.1, p.2]) := by
      rw [hGe]; exact hΦac.comp_homeomorph e.toHomeomorph
    have hG0 : ∀ (x : mixedEmbedding.mixedSpace K) (y : InfiniteAdeleRing K),
        (fun p : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K => Φa ![p.1, p.2])
          (x, InfiniteAdeleRing.ringEquiv_mixedSpace K y) ≠ 0 → y ∈ Units.val '' Ca := by
      intro x y h
      obtain ⟨u, hu, hueq⟩ := hΦa0 _ h
      refine ⟨u, hu, ?_⟩
      rw [hueq]
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply y
    exact (R4X9.integrable_and_contDiff_fold K ν S (fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) hξc
      (fun p => Φa ![p.1, p.2]) hG hGc Ca hCa hG0 Φf hΦf b).2
  ·
    refine ⟨(fun p : Fin 2 → mixedEmbedding.mixedSpace K => p 0) '' tsupport Φa, hΦac.image (continuous_apply 0),
      fun b x hx => ?_⟩
    have h0 : ∀ y : mixedEmbedding.mixedSpace K, Φa ![x, y] = 0 := fun y =>
      image_eq_zero_of_notMem_tsupport fun hm => hx ⟨_, hm, rfl⟩
    simp only [h0, zero_mul, mul_zero, integral_zero]
  ·
    intro x
    rw [IsLocallyConstant.iff_eventually_eq]
    intro b₀
    have hev : ∀ᶠ b in 𝓝 b₀, ∀ v ∈ S, ∀ y : v.adicCompletion K, Φf v (b v, y) = Φf v (b₀ v, y) := by
      refine Filter.eventually_all_finset S |>.mpr fun v hv => ?_
      exact ((continuous_apply v).tendsto b₀).eventually (R4X9.eventually_forall_eq (hΦf v hv).1 (hΦf v hv).2.1 (b₀ v))
    filter_upwards [hev] with b hb
    refine integral_congr_ae (Eventually.of_forall fun zS => ?_)
    show _ * (_ * _) = _ * (_ * _)
    rw [Finset.prod_congr rfl fun v hv => hb v hv _]
  ·
    refine ⟨fun v => Prod.fst '' tsupport (Φf v), fun v hv => ⟨(hΦf v hv).2.1.image continuous_fst, fun h0 => ?_⟩,
      fun x b hb => ?_⟩
    · obtain ⟨p, hp, hp0⟩ := h0
      rw [R4X9.tsupport_eq_support (hΦf v hv).1, Function.mem_support] at hp
      exact ((hΦf v hv).2.2 p hp).1 hp0
    · obtain ⟨v, hv, hbv⟩ := hb
      have h0 : ∀ y : v.adicCompletion K, Φf v (b v, y) = 0 := fun y =>
        image_eq_zero_of_notMem_tsupport fun hm => hbv ⟨_, hm, rfl⟩
      have hprod : ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
          ∏ w ∈ S, Φf w (b w, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) = 0 :=
        fun zS => Finset.prod_eq_zero hv (h0 _)
      simp only [hprod, mul_zero, integral_zero]

end S_NumberField_Idele_contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
end P2MW
export P2MW.S_NumberField_Idele_contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact (solution)
