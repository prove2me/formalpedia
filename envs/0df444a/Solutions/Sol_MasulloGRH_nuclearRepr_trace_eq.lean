-- Prove2me | solution 1 for MasulloGRH.nuclearRepr_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:24:18.33165+00:00
-- url     : https://prove2.me/submissions/da3989a3-8f2e-460b-aef9-49830d296212

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_NuclearMap
import Definitions.Def_TopologicalTensorProduct_ApproximationProperty

open Filter Topology TopologicalTensorProduct
set_option autoImplicit false

namespace Sol_MasulloGRH_nuclearRepr_trace_eq

/-- For a summable nonnegative sequence `a` there are positive weights `d n → 0` such that
`a n / d n` is still summable. -/
theorem exists_pos_tendsto_zero_summable_div {a : ℕ → ℝ} (ha : Summable a)
    (ha₀ : ∀ n, 0 ≤ a n) :
    ∃ d : ℕ → ℝ, (∀ n, 0 < d n) ∧ Tendsto d atTop (𝓝 0) ∧
      Summable (fun n ↦ a n / d n) := by
  let b (n : ℕ) := a n + (1 / 2 : ℝ) ^ n
  have hb : Summable b := ha.add (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hb₀ (n : ℕ) : 0 < b n := add_pos_of_nonneg_of_pos (ha₀ n) (by positivity)
  let t (n : ℕ) := ∑' k : ℕ, b (k + n)
  have ht (n : ℕ) : 0 < t n :=
    ((summable_nat_add_iff n).mpr hb).tsum_pos (fun k ↦ (hb₀ (k + n)).le) 0 (hb₀ (0 + n))
  have ht_add (n : ℕ) : t n = b n + t (n + 1) := by
    simpa only [t, zero_add, Nat.add_right_comm, Nat.add_assoc] using
      ((summable_nat_add_iff n).mpr hb).tsum_eq_zero_add
  let s (n : ℕ) := Real.sqrt (t n)
  have hs : Tendsto s atTop (𝓝 0) := by
    simpa only [s, t, Real.sqrt_zero] using (tendsto_sum_nat_add b).sqrt
  let d (n : ℕ) := s n + s (n + 1)
  have hd (n : ℕ) : 0 < d n := add_pos (Real.sqrt_pos_of_pos (ht _)) (Real.sqrt_pos_of_pos (ht _))
  refine ⟨d, hd, ?_, ?_⟩
  · simpa only [d, Function.comp_apply, zero_add] using hs.add (hs.comp (tendsto_add_atTop_nat 1))
  · refine summable_of_sum_range_le (c := s 0) (fun n ↦ div_nonneg (ha₀ n) (hd n).le) fun N ↦ ?_
    calc
      _ ≤ ∑ n ∈ Finset.range N, (s n - s (n + 1)) := by
        refine Finset.sum_le_sum fun n _ ↦ (div_le_iff₀ (hd n)).mpr ?_
        dsimp [d, s]
        nlinarith [Real.mul_self_sqrt (ht n).le, Real.mul_self_sqrt (ht (n + 1)).le,
          ht_add n, show a n ≤ b n from le_add_of_nonneg_right (by positivity)]
      _ ≤ s 0 := by
        rw [Finset.sum_range_sub']
        exact sub_le_self _ (Real.sqrt_nonneg _)

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- An equicontinuous sequence of functionals is uniformly small near `0`. -/
theorem eventually_norm_lt {φ : ℕ → StrongDual ℂ E}
    (hφ : Equicontinuous (fun (n : ℕ) (x : E) => φ n x)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 (0 : E), ∀ n, ‖φ n y‖ < ε := by
  filter_upwards [(Metric.equicontinuousAt_iff_right.mp (hφ 0)) ε hε] with y hy n
  have h := hy n
  simpa [dist_zero_left] using h

/-- Points of a bounded set multiplied by scalars tending to `0` tend to `0`. -/
theorem tendsto_smul_zero {B : Set E} (hB : Bornology.IsVonNBounded ℂ B) {x : ℕ → E}
    (hx : ∀ n, x n ∈ B) {d : ℕ → ℝ} (hd : ∀ n, 0 < d n) (hd0 : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => ((d n : ℂ)) • x n) atTop (𝓝 0) := by
  intro V hV
  obtain ⟨r, hr, hrV⟩ := (hB hV).exists_pos
  have hev : ∀ᶠ n in atTop, d n < r⁻¹ := hd0 (Iio_mem_nhds (inv_pos.mpr hr))
  refine Filter.mem_map.mpr ?_
  filter_upwards [hev] with n hn
  have hdn := hd n
  have hle : r ≤ ‖((d n : ℂ))⁻¹‖ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hdn.le]
    rw [lt_inv_comm₀ hdn hr] at hn
    exact hn.le
  obtain ⟨v, hv, hvx⟩ := hrV _ hle (hx n)
  show (d n : ℂ) • x n ∈ V
  rw [← hvx, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hdn.ne'), one_smul]
  exact hv

/-- The diagonal series of a nuclear representation converges absolutely. -/
theorem summable_norm_diag {c : ℕ → ℂ} {φ : ℕ → StrongDual ℂ E} {x : ℕ → E} {B : Set E}
    (hc : Summable (fun n => ‖c n‖)) (hφ : Equicontinuous (fun (n : ℕ) (x : E) => φ n x))
    (hB : Bornology.IsVonNBounded ℂ B) (hx : ∀ n, x n ∈ B) :
    Summable (fun m => ‖c m * φ m (x m)‖) := by
  have hV := eventually_norm_lt hφ one_pos
  obtain ⟨r, hr, hrV⟩ := (hB hV).exists_pos
  have hbound : ∀ m, ‖φ m (x m)‖ ≤ r := by
    intro m
    have hle : r ≤ ‖(r : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
    obtain ⟨v, hv, hvx⟩ := hrV _ hle (hx m)
    rw [← hvx, map_smul, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have h1 : ‖φ m v‖ < 1 := hv m
    nlinarith [norm_nonneg (φ m v)]
  refine (hc.mul_right r).of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound m) (norm_nonneg _)

omit [Module ℂ E] in
/-- The union of the ranges of two null sequences is pre-compact. -/
theorem isPrecompact_union_range {z z' : ℕ → E} (hz : Tendsto z atTop (𝓝 0))
    (hz' : Tendsto z' atTop (𝓝 0)) : IsPrecompact (Set.range z ∪ Set.range z') := by
  classical
  intro U hU
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hz.eventually_mem hU).and (hz'.eventually_mem hU))
  refine ⟨insert 0 ((Finset.range N).image z ∪ (Finset.range N).image z'), ?_⟩
  have h0 : (0 : E) ∈ U := mem_of_mem_nhds hU
  rintro y (⟨n, rfl⟩ | ⟨n, rfl⟩)
  · rw [Set.mem_iUnion₂]
    by_cases hn : n < N
    · refine ⟨z n, ?_, ?_⟩
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem z
          (Finset.mem_range.mpr hn)))
      · show z n - z n ∈ U
        rw [sub_self]; exact h0
    · refine ⟨0, Finset.mem_insert_self _ _, ?_⟩
      show z n - 0 ∈ U
      rw [sub_zero]; exact (hN n (not_lt.mp hn)).1
  · rw [Set.mem_iUnion₂]
    by_cases hn : n < N
    · refine ⟨z' n, ?_, ?_⟩
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem z'
          (Finset.mem_range.mpr hn)))
      · show z' n - z' n ∈ U
        rw [sub_self]; exact h0
    · refine ⟨0, Finset.mem_insert_self _ _, ?_⟩
      show z' n - 0 ∈ U
      rw [sub_zero]; exact (hN n (not_lt.mp hn)).2

/-- Inserting a finite-rank approximation of the identity into a nuclear representation: the
diagonal series differs from `∑ᵢ ψᵢ(A wᵢ)` by at most `δ ∑ₙ |cₙ| / dₙ`. -/
theorem norm_tsum_sub_le {A : E →L[ℂ] E} {c : ℕ → ℂ} {φ : ℕ → StrongDual ℂ E} {x : ℕ → E}
    (hsum : Summable (fun n => c n * φ n (x n)))
    (hA : ∀ y : E, HasSum (fun n => (c n * φ n y) • x n) (A y))
    {d : ℕ → ℝ} (hd : ∀ n, 0 < d n) (hcd : Summable (fun n => ‖c n‖ / d n))
    {δ : ℝ} {N : ℕ} (ψ : Fin N → StrongDual ℂ E) (w : Fin N → E)
    (hδ : ∀ n, ‖φ n ((d n : ℂ) • x n - ∑ i, ψ i ((d n : ℂ) • x n) • w i)‖ ≤ δ) :
    ‖∑' n, c n * φ n (x n) - ∑ i, ψ i (A (w i))‖ ≤ (∑' n, ‖c n‖ / d n) * δ := by
  have h1 : HasSum (fun n => c n * φ n (∑ i, ψ i (x n) • w i)) (∑ i, ψ i (A (w i))) := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin N)),
        HasSum (fun n => (c n * φ n (w i)) * ψ i (x n)) (ψ i (A (w i))) := by
      intro i _
      have h := (ψ i).hasSum (hA (w i))
      simpa only [map_smul, smul_eq_mul] using h
    have h := hasSum_sum hi
    convert h using 1
    funext n
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 := hsum.hasSum.sub h1
  refine h2.norm_le_of_bounded (hcd.hasSum.mul_right δ) ?_
  intro n
  have hdn : (d n : ℂ) ≠ 0 := by exact_mod_cast (hd n).ne'
  have key : c n * φ n (x n) - c n * φ n (∑ i, ψ i (x n) • w i)
      = (c n / (d n : ℂ)) * φ n ((d n : ℂ) • x n - ∑ i, ψ i ((d n : ℂ) • x n) • w i) := by
    simp only [map_sub, map_smul, map_sum, smul_eq_mul, mul_assoc]
    rw [← Finset.mul_sum]
    field_simp
  rw [key, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (hd n).le]
  exact mul_le_mul_of_nonneg_left (hδ n) (div_nonneg (norm_nonneg _) (hd n).le)

end Sol_MasulloGRH_nuclearRepr_trace_eq

open MasulloGRH Sol_MasulloGRH_nuclearRepr_trace_eq in
theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (hAP : HasApproximationProperty ℂ E) (A : E →L[ℂ] E)
    (c c' : ℕ → ℂ) (φ φ' : ℕ → StrongDual ℂ E) (x x' : ℕ → E)
    (h : IsNuclearRepr A c φ x) (h' : IsNuclearRepr A c' φ' x') :
    Summable (fun m => ‖c m * φ m (x m)‖) ∧
      ∑' m, c m * φ m (x m) = ∑' m, c' m * φ' m (x' m) := by
  obtain ⟨hc, hφ, ⟨B, hB, hxB⟩, hA⟩ := h
  obtain ⟨hc', hφ', ⟨B', hB', hxB'⟩, hA'⟩ := h'
  have hs : Summable (fun m => ‖c m * φ m (x m)‖) := summable_norm_diag hc hφ hB.2.1 hxB
  have hs' : Summable (fun m => ‖c' m * φ' m (x' m)‖) :=
    summable_norm_diag hc' hφ' hB'.2.1 hxB'
  refine ⟨hs, ?_⟩
  obtain ⟨d, hd, hd0, hcd⟩ := exists_pos_tendsto_zero_summable_div hc (fun n => norm_nonneg _)
  obtain ⟨d', hd', hd0', hcd'⟩ :=
    exists_pos_tendsto_zero_summable_div hc' (fun n => norm_nonneg _)
  have hz := tendsto_smul_zero hB.2.1 hxB hd hd0
  have hz' := tendsto_smul_zero hB'.2.1 hxB' hd' hd0'
  have hK := isPrecompact_union_range hz hz'
  set T := ∑' m, c m * φ m (x m) with hT
  set T' := ∑' m, c' m * φ' m (x' m) with hT'
  set C := ∑' n, ‖c n‖ / d n with hC
  set C' := ∑' n, ‖c' n‖ / d' n with hC'
  have hC0 : 0 ≤ C := tsum_nonneg fun n => div_nonneg (norm_nonneg _) (hd n).le
  have hC0' : 0 ≤ C' := tsum_nonneg fun n => div_nonneg (norm_nonneg _) (hd' n).le
  have key : ∀ δ : ℝ, 0 < δ → ‖T - T'‖ ≤ C * δ + C' * δ := by
    intro δ hδ
    have hU := (eventually_norm_lt hφ hδ).and (eventually_norm_lt hφ' hδ)
    obtain ⟨N, ψ, w, hw⟩ := hAP _ hK _ hU
    have h1 := norm_tsum_sub_le hs.of_norm hA hd hcd ψ w
      (fun n => ((hw _ (Or.inl ⟨n, rfl⟩)).1 n).le)
    have h2 := norm_tsum_sub_le hs'.of_norm hA' hd' hcd' ψ w
      (fun n => ((hw _ (Or.inr ⟨n, rfl⟩)).2 n).le)
    calc ‖T - T'‖ = ‖(T - ∑ i, ψ i (A (w i))) - (T' - ∑ i, ψ i (A (w i)))‖ := by
          congr 1; ring
      _ ≤ ‖T - ∑ i, ψ i (A (w i))‖ + ‖T' - ∑ i, ψ i (A (w i))‖ := norm_sub_le _ _
      _ ≤ C * δ + C' * δ := add_le_add h1 h2
  by_contra hne
  have hpos : 0 < ‖T - T'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set ε := ‖T - T'‖ with hε
  have hδ : 0 < ε / (C + C' + 1) := div_pos hpos (by linarith)
  have hk := key _ hδ
  have : C * (ε / (C + C' + 1)) + C' * (ε / (C + C' + 1)) < ε := by
    rw [← add_mul]
    calc (C + C') * (ε / (C + C' + 1)) < (C + C' + 1) * (ε / (C + C' + 1)) :=
          mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε := mul_div_cancel₀ _ (by linarith)
  linarith
