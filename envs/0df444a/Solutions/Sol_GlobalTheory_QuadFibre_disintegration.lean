-- Prove2me | solution 1 for GlobalTheory.QuadFibre.disintegration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:07.651709+00:00
-- url     : https://prove2.me/submissions/db1cf4b6-f7f1-4c08-b182-e2041c9b6721

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HaarDisintegrationAveragedFibreMeasures
import Theorems.Thm_GlobalTheory_QuadFibre_avg_div_eq
import Theorems.Thm_GlobalTheory_QuadFibre_fibOf_ne
import Theorems.Thm_GlobalTheory_QuadFibre_fibOf_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped Pointwise ENNReal NNReal
open GlobalTheory GlobalTheory.QuadFibre
namespace GlobalTheory.QuadFibre
theorem _root_.solution (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K)
    (hq : Continuous q) (hq2 : ∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x)
    (U : Set K) (s : K → K) (hU : IsSqrtOn U s)
    (hμ : ∀ c : K, ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ)
    (h0 : μ {x | q x = 0} = 0) (φ : V → ENNReal) (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂μ = ∫⁻ t, ∫⁻ x, φ x ∂(fibOf μ ν q U s t) ∂ν := by
  obtain ⟨hUo, hUc, h1U, hmulU, hinvU, hnormU, hs, hsq⟩ := hU
  have hUm : MeasurableSet U := hUo.measurableSet
  have hνU0 : ν U ≠ 0 := hUo.measure_ne_zero ν ⟨1, h1U⟩
  have hνUt : ν U ≠ ∞ := hUc.measure_lt_top.ne
  have hqm : Measurable q := hq.measurable
  have hsm : Measurable s := hs.measurable
  have h0U : (0 : K) ∉ U := fun h => by simpa using hnormU 0 h
  have hdiv : Measurable (fun p : K × K => p.1 / p.2) := by
    simp_rw [div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv
  have hself : ∀ t : K, t ∈ t • U := fun t => by simpa using Set.smul_mem_smul_set (a := t) h1U

  have hstab : ∀ u ∈ U, u • U = U := by
    intro u hu
    have hu0 : u ≠ 0 := fun h => h0U (h ▸ hu)
    ext v
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hu0, smul_eq_mul]
    constructor
    · intro h
      have := hmulU _ hu _ h
      rwa [← mul_assoc, mul_inv_cancel₀ hu0, one_mul] at this
    · intro h
      exact hmulU _ (hinvU _ hu) _ h
  have hshift : ∀ t : K, ∀ t' ∈ t • U, t' • U = t • U := by
    intro t t' ht'
    obtain ⟨u, hu, rfl⟩ := ht'
    change (t • u) • U = t • U
    rw [smul_eq_mul, ← smul_smul, hstab u hu]
  have hmem : ∀ t : K, t ≠ 0 → ∀ y : K, y ∈ t • U ↔ t / y ∈ U := by
    intro t ht y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht, smul_eq_mul]
    constructor
    · intro h
      have := hinvU _ h
      rwa [mul_inv, inv_inv, ← div_eq_mul_inv] at this
    · intro h
      have := hinvU _ h
      rwa [inv_div, div_eq_inv_mul] at this
  have hpos : ∀ t : K, t ≠ 0 → ν (t • U) ≠ 0 := fun t ht =>
    (hUo.smul₀ ht).measure_ne_zero ν ⟨t, hself t⟩

  have hmeas : Measurable (fun t : K => ν (t • U)) := by
    refine measurable_of_continuousOn_compl_singleton 0 ?_
    intro t ht
    have ht0 : t ≠ 0 := ht
    refine ContinuousAt.continuousWithinAt ?_
    have hnb : t • U ∈ 𝓝 t := (hUo.smul₀ ht0).mem_nhds (hself t)
    have hev : (fun _ : K => ν (t • U)) =ᶠ[𝓝 t] fun t' => ν (t' • U) := by
      filter_upwards [hnb] with t' ht'
      rw [hshift t t' ht']
    exact continuousAt_const.congr hev

  have hGm : Measurable (fun p : K × V => (ν (p.1 • U))⁻¹ *
      {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) p) := by
    refine (hmeas.comp measurable_fst).inv.mul (Measurable.indicator ?_ ?_)
    · exact hφ.comp ((hsm.comp (hdiv.comp (measurable_fst.prodMk (hqm.comp measurable_snd)))).smul
        measurable_snd)
    · exact (hdiv.comp (measurable_fst.prodMk (hqm.comp measurable_snd))) hUm

  have hA : ∀ t : K, ∫⁻ x, φ x ∂(fibOf μ ν q U s t) = ∫⁻ x, (ν (t • U))⁻¹ *
      {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂μ := by
    intro t
    by_cases ht : t = 0
    · subst ht
      rw [fibOf_zero, lintegral_zero_measure]
      simp [h0U]
    · have hfm : Measurable (fun x : V => s (t / q x) • x) :=
        (hsm.comp (hdiv.comp (measurable_const.prodMk hqm))).smul measurable_id
      have hSm : MeasurableSet (q ⁻¹' (t • U)) := hqm (hUo.smul₀ ht).measurableSet
      rw [fibOf_ne μ ν q U s ht, lintegral_smul_measure, smul_eq_mul, lintegral_map hφ hfm,
        ← lintegral_indicator hSm, ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (hpos t ht))]
      refine lintegral_congr fun x => ?_
      by_cases h : t / q x ∈ U
      · rw [Set.indicator_of_mem (show x ∈ q ⁻¹' (t • U) from (hmem t ht (q x)).mpr h),
          Set.indicator_of_mem (show (t, x) ∈ {p : K × V | p.1 / q p.2 ∈ U} from h)]
      · rw [Set.indicator_of_notMem (show x ∉ q ⁻¹' (t • U) from fun h' => h ((hmem t ht (q x)).mp h')),
          Set.indicator_of_notMem (show (t, x) ∉ {p : K × V | p.1 / q p.2 ∈ U} from h)]

  have hC : ∀ x : V, q x ≠ 0 → ∫⁻ t, (ν (t • U))⁻¹ *
      {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂ν =
      (ν U)⁻¹ * ∫⁻ u, U.indicator (fun u => φ (s u • x)) u ∂ν := by
    intro x hx
    have hset : {r : K | r / q x ∈ U} = q x • U := by
      ext r
      rw [Set.mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀ hx, smul_eq_mul, div_eq_inv_mul]
    have hpt : ∀ t : K, (ν (t • U))⁻¹ *
        {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) =
        (ν {r : K | r / q x ∈ U})⁻¹ * U.indicator (fun u => φ (s u • x)) (t / q x) := by
      intro t
      by_cases h : t / q x ∈ U
      · have ht' : t ∈ q x • U := by
          rw [Set.mem_smul_set_iff_inv_smul_mem₀ hx, smul_eq_mul, ← div_eq_inv_mul]
          exact h
        rw [Set.indicator_of_mem (show (t, x) ∈ {p : K × V | p.1 / q p.2 ∈ U} from h),
          Set.indicator_of_mem h, hset, hshift (q x) t ht']
      · rw [Set.indicator_of_notMem (show (t, x) ∉ {p : K × V | p.1 / q p.2 ∈ U} from h),
          Set.indicator_of_notMem h, mul_zero, mul_zero]
    have hgm : Measurable (U.indicator (fun u => φ (s u • x))) :=
      (hφ.comp (hsm.smul measurable_const)).indicator hUm
    have hne : ν {r : K | r / q x ∈ U} ≠ 0 := by
      rw [hset]
      exact hpos _ hx
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hne)]
    exact avg_div_eq ν hx hUm hgm

  have hunit : ∀ u ∈ U, ∫⁻ x, φ (s u • x) ∂μ = ∫⁻ x, φ x ∂μ := by
    intro u hu
    have hn : ‖s u‖ = 1 := by
      have h := congrArg norm (hsq u hu)
      rw [norm_pow, hnormU u hu] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
    calc ∫⁻ x, φ (s u • x) ∂μ = ∫⁻ x, φ x ∂(Measure.map (fun x : V => s u • x) μ) :=
          (lintegral_map hφ (measurable_const_smul (s u))).symm
      _ = ∫⁻ x, φ x ∂μ := by rw [hμ _ hn]
  have hae : ∀ᵐ x ∂μ, q x ≠ 0 := by
    rw [ae_iff]
    simpa using h0
  have hM2 : Measurable (Function.uncurry fun (u : K) (x : V) => U.indicator (fun u => φ (s u • x)) u) := by
    have : (Function.uncurry fun (u : K) (x : V) => U.indicator (fun u => φ (s u • x)) u) =
        (Prod.fst ⁻¹' U).indicator (fun p : K × V => φ (s p.1 • p.2)) := by
      funext p
      by_cases h : p.1 ∈ U
      · rw [Function.uncurry_apply_pair, Set.indicator_of_mem h,
          Set.indicator_of_mem (show p ∈ Prod.fst ⁻¹' U from h)]
      · rw [Function.uncurry_apply_pair, Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show p ∉ Prod.fst ⁻¹' U from h)]
    rw [this]
    exact (hφ.comp ((hsm.comp measurable_fst).smul measurable_snd)).indicator (measurable_fst hUm)
  calc ∫⁻ x, φ x ∂μ = (ν U)⁻¹ * (ν U * ∫⁻ x, φ x ∂μ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hνU0 hνUt, one_mul]
    _ = (ν U)⁻¹ * ∫⁻ u, U.indicator (fun _ => ∫⁻ x, φ x ∂μ) u ∂ν := by
        rw [lintegral_indicator_const hUm, mul_comm (ν U)]
    _ = (ν U)⁻¹ * ∫⁻ u, ∫⁻ x, U.indicator (fun u => φ (s u • x)) u ∂μ ∂ν := by
        congr 1
        refine lintegral_congr fun u => ?_
        by_cases hu : u ∈ U
        · simp [hu, hunit u hu]
        · simp [hu]
    _ = (ν U)⁻¹ * ∫⁻ x, ∫⁻ u, U.indicator (fun u => φ (s u • x)) u ∂ν ∂μ := by
        rw [lintegral_lintegral_swap hM2.aemeasurable]
    _ = ∫⁻ x, (ν U)⁻¹ * ∫⁻ u, U.indicator (fun u => φ (s u • x)) u ∂ν ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hνU0)]
    _ = ∫⁻ x, ∫⁻ t, (ν (t • U))⁻¹ *
          {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂ν ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with x hx
        exact (hC x hx).symm
    _ = ∫⁻ t, ∫⁻ x, (ν (t • U))⁻¹ *
          {p : K × V | p.1 / q p.2 ∈ U}.indicator (fun p => φ (s (p.1 / q p.2) • p.2)) (t, x) ∂μ ∂ν :=
        (lintegral_lintegral_swap hGm.aemeasurable).symm
    _ = ∫⁻ t, ∫⁻ x, φ x ∂(fibOf μ ν q U s t) ∂ν := lintegral_congr fun t => (hA t).symm
end GlobalTheory.QuadFibre
