-- Prove2me | solution 1 for GlobalTheory.finiteDimensional_of_uniformly_almost_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:40.644035+00:00
-- url     : https://prove2.me/submissions/93881aad-f73d-4b7c-9727-df3ef9226237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalOfUniformlyAlmostInvariant
import Theorems.Thm_GlobalTheory_norm_sq_toLp_two_eq_integral_norm_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)),
      (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K),
      (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) →
      FiniteDimensional ℂ E := by
  intro K _ _ _ _ _ _ _ μ _ _ _ E hE U hU hinv
  classical
  obtain ⟨β, hβ1, -, hβU, hβ01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_singleton (x := (1 : K))) isOpen_interior
    (Set.singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hU))
  have hβ0 : ∀ x, 0 ≤ β x := fun x => (hβ01 x).1
  have hβU' : ∀ u, β u ≠ 0 → u ∈ U := fun u hu =>
    interior_subset (hβU (subset_tsupport _ hu))
  set c : ℝ := ∫ u, β u ∂μ with hc
  have hcpos : 0 < c := β.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := 1) (HasCompactSupport.of_compactSpace _) hβ0 (by simp [hβ1 (Set.mem_singleton _)])
  set L := ContinuousMap.toLp (α := K) (E := ℂ) 2 μ ℂ with hL

  let b : C(K, C(K, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × K => (β (p.1⁻¹ * p.2) : ℂ), by fun_prop⟩
  have hb : Continuous fun x => L (b x) := L.continuous.comp b.continuous
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x : K => (fun y => L (b y)) ⁻¹' Metric.ball (L (b x)) (c / 4))
    (fun x _ => hb.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity)))
  let ι : E →ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun f => ⟨f.1, hE f.1 f.2⟩
      map_add' := fun f g => by ext; simp
      map_smul' := fun a f => by ext; simp }
  let Φ : E →ₗ[ℂ] (t → ℂ) := LinearMap.pi fun j : t =>
    (innerSL ℂ (L (b j.1))).toLinearMap ∘ₗ L.toLinearMap ∘ₗ ι
  refine FiniteDimensional.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  have hf0 : ∀ j ∈ t, inner ℂ (L (b j)) (L (ι f)) = 0 := fun j hj => by
    simpa [Φ] using congrFun hf ⟨j, hj⟩
  set g : C(K, ℂ) := ι f with hg
  let R : C(K, C(K, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × K => g (p.2 * p.1), by fun_prop⟩
  have hint : ∀ {V : Type} [NormedAddCommGroup V] {F : K → V}, Continuous F → Integrable F μ :=
    fun hF => hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun u => β u • R u) μ := hint (by fun_prop)
  set T : C(K, ℂ) := ∫ u, β u • R u ∂μ with hT
  have hTx : ∀ x, T x = inner ℂ (L (b x)) (L g) := fun x => by
    rw [hT, ContinuousMap.integral_apply hi1, hL, ContinuousMap.inner_toLp,
      ← integral_mul_left_eq_self (μ := μ) (fun z => g z * (starRingEnd ℂ) (b x z)) x]
    congr 1
    ext u
    simp [R, b, mul_comm]
  have hTb : ∀ x, ‖T x‖ ≤ c / 4 * ‖L g‖ := fun x => by
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    have hx' : ‖L (b x) - L (b j)‖ ≤ c / 4 := by
      rw [← dist_eq_norm]; exact le_of_lt hx
    have : T x = inner ℂ (L (b x) - L (b j)) (L g) := by
      rw [inner_sub_left, hf0 j hj, sub_zero, hTx]
    rw [this]
    exact (norm_inner_le_norm _ _).trans (by gcongr)
  have hLT : ‖L T‖ ≤ c / 4 * ‖L g‖ := by
    have := Lp.norm_le_of_ae_bound (f := L T) (C := c / 4 * ‖L g‖) (by positivity)
      (by
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ T] with x hx
        rw [hL, hx]; exact hTb x)
    simpa [measureUnivNNReal] using this
  have hmove : ∀ u ∈ U, ‖L (R u) - L g‖ ≤ 1 / 2 * ‖L g‖ := fun u hu => by
    have h1 := hinv f.1 f.2 u hu
    have h2 : ‖L (R u - g)‖ ^ 2 ≤ (1 / 2 * ‖L g‖) ^ 2 := by
      rw [mul_pow, hL, norm_sq_toLp_two_eq_integral_norm_sq, norm_sq_toLp_two_eq_integral_norm_sq]
      norm_num
      simpa [R, hg, ι] using h1
    rw [← map_sub]
    exact le_of_sq_le_sq h2 (by positivity)
  have hdiff : L T - c • L g = ∫ u, β u • (L (R u) - L g) ∂μ := by
    rw [hT, ← L.integral_comp_comm hi1, hc, ← integral_smul_const, ← integral_sub]
    · congr 1
      ext1 u
      rw [smul_sub, L.map_smul_of_tower]
    · exact L.integrable_comp hi1
    · exact hint (by fun_prop)
  have hdn : ‖L T - c • L g‖ ≤ c * (1 / 2 * ‖L g‖) := by
    rw [hdiff, hc, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hint (by fun_prop)) (Eventually.of_forall fun u => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hβ0 u)]
    by_cases hu : β u = 0
    · simp [hu]
    · exact mul_le_mul_of_nonneg_left (hmove u (hβU' u hu)) (hβ0 u)
  have hfin : c * ‖L g‖ ≤ c / 4 * ‖L g‖ + c * (1 / 2 * ‖L g‖) := by
    have : ‖c • L g‖ ≤ ‖L T‖ + ‖L T - c • L g‖ := by
      simpa using norm_sub_le (L T) (L T - c • L g)
    rw [norm_smul, Real.norm_of_nonneg hcpos.le] at this
    linarith
  have hg0 : ‖L g‖ = 0 := by
    have := norm_nonneg (L g)
    nlinarith
  have hg1 : g = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ
    (by rw [map_zero]; exact norm_eq_zero.1 hg0)
  ext x
  simpa [hg, ι] using congrArg (fun h : C(K, ℂ) => h x) hg1
end GlobalTheory
