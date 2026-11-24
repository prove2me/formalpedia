-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.ModulusAction.exists_continuous_modulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:17:20.685701+00:00
-- url     : https://prove2.me/submissions/bde84513-9b50-45b7-a4e1-285e5718c74b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GroupActionHaarScalingContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.ModulusAction
namespace GlobalTheory.CompanionTheory.Adelic.ModulusAction
theorem _root_.solution :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
      [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (μ : Measure V) [μ.IsAddHaarMeasure] (T : Type) [Group T] [TopologicalSpace T]
      [FirstCountableTopology T] [LocallyCompactSpace T] (a : T → V →+ V),
      (Continuous fun p : T × V => a p.1 p.2) → Continuous (fun t : T => t⁻¹) →
      (∀ y, a 1 y = y) → (∀ s t y, a (s * t) y = a s (a t y)) →
      ∃ χ : T →* ℝ≥0, Continuous χ ∧ ∀ t, μ.map (a t) = χ t • μ := by
  intro V _ _ _ _ _ _ _ _ μ _ T _ _ _ _ a ha hinv h1 hmul
  have hat : ∀ t, Continuous (a t) := fun t => by
    have h := ha.comp (continuous_const.prodMk (continuous_id (X := V)) :
      Continuous fun y : V => (t, y))
    exact h
  have hleft : ∀ t y, a t⁻¹ (a t y) = y := by
    intro t y
    rw [← hmul, inv_mul_cancel, h1]
  have hright : ∀ t y, a t (a t⁻¹ y) = y := by
    intro t y
    rw [← hmul, mul_inv_cancel, h1]
  have hfin : ∀ t, IsFiniteMeasureOnCompacts (μ.map (a t)) := by
    intro t
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply (hat t).measurable hK.isClosed.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) ((hK.image (hat t⁻¹)).measure_lt_top)
    intro y hy
    exact ⟨a t y, hy, hleft t y⟩
  have hinvar : ∀ t, (μ.map (a t)).IsAddLeftInvariant := by
    intro t
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_add g) (hat t).measurable]
    have e : (fun x => g + x) ∘ a t = a t ∘ fun x => a t⁻¹ g + x := by
      funext x
      simp only [Function.comp_apply, map_add, hright]
    rw [e, ← Measure.map_map (hat t).measurable (measurable_const_add _),
      map_add_left_eq_self]
  have hscale : ∀ t, ∃ c : ℝ≥0, μ.map (a t) = c • μ := by
    intro t
    haveI := hfin t
    haveI := hinvar t
    exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ⟩
  choose c hc using hscale
  obtain ⟨f, hfc, hf0, hfx⟩ := exists_continuous_nonneg_pos (0 : V)
  have hI : 0 < ∫ y, f y ∂μ :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hfx
  have hint : ∀ t (g : V → ℝ), Continuous g →
      ∫ y, g (a t y) ∂μ = (c t : ℝ) * ∫ y, g y ∂μ := by
    intro t g hg
    rw [← integral_map (hat t).measurable.aemeasurable hg.aestronglyMeasurable, hc t,
      integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hform : ∀ t, (c t : ℝ) * ∫ y, f y ∂μ = ∫ y, f (a t y) ∂μ := fun t =>
    (hint t f f.continuous).symm
  have hone : c 1 = 1 := by
    apply NNReal.coe_injective
    apply mul_right_cancel₀ hI.ne'
    rw [hform, NNReal.coe_one, one_mul]
    simp only [h1]
  have hmulc : ∀ s t, c (s * t) = c s * c t := by
    intro s t
    apply NNReal.coe_injective
    apply mul_right_cancel₀ hI.ne'
    rw [hform, NNReal.coe_mul]
    calc ∫ y, f (a (s * t) y) ∂μ = ∫ y, f (a s (a t y)) ∂μ := by simp only [hmul]
      _ = (c t : ℝ) * ∫ y, f (a s y) ∂μ := hint t (fun z => f (a s z)) (f.continuous.comp (hat s))
      _ = (c s : ℝ) * (c t : ℝ) * ∫ y, f y ∂μ := by rw [← hform s]; ring
  have hF : Continuous fun t => ∫ y, f (a t y) ∂μ := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    obtain ⟨N, hN, hNn⟩ := exists_compact_mem_nhds t₀
    set s : Set V := (fun p : T × V => a p.1 p.2) '' (((fun t => t⁻¹) '' N) ×ˢ tsupport f)
      with hsdef
    have hs : IsCompact s := ((hN.image hinv).prod hfc.isCompact).image ha
    have hG : Continuous fun t => ∫ y in s, f (a t y) ∂μ := by
      refine continuous_parametric_integral_of_continuous ?_ hs
      exact f.continuous.comp ha
    refine hG.continuousAt.congr (Filter.eventually_of_mem hNn fun t ht => ?_)
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    by_contra hne
    exact hy ⟨(t⁻¹, a t y), ⟨⟨t, ht, rfl⟩, subset_tsupport _ hne⟩, hleft t y⟩
  have hcreal : (fun t => (c t : ℝ)) = fun t => (∫ y, f (a t y) ∂μ) / ∫ y, f y ∂μ :=
    funext fun t => eq_div_of_mul_eq hI.ne' (hform t)
  refine ⟨{ toFun := c, map_one' := hone, map_mul' := hmulc }, ?_, hc⟩
  show Continuous c
  have hcont : Continuous fun t => (c t : ℝ) := by
    rw [hcreal]
    exact hF.div_const _
  exact Continuous.subtype_mk hcont fun t => (c t).2
end GlobalTheory.CompanionTheory.Adelic.ModulusAction
