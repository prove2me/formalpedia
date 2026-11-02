-- Prove2me | solution 1 for IsodiamVar.Simplex.center_in_hull
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:43:51.20064+00:00
-- url     : https://prove2.me/submissions/144b5ae7-3e90-408a-a490-2bb972c60361

import Mathlib
import Definitions.Def_IsodiamVar_Simplex_Defs


open MeasureTheory

open IsodiamVar.Simplex in
theorem solution {n : ℕ} (K : Set (E n)) (hK : IsCompact K)
    (v : ℝ → ℝ) (hv0 : ∀ t, 0 ≤ t → 0 ≤ v t)
    (hvconv : ConvexOn ℝ (Set.Ici 0) v) (hvmono : StrictMonoOn v (Set.Ici 0))
    (μ : Measure (E n)) (hμ : InP K μ)
    (hmax : ∀ ν : Measure (E n), InP K ν →
      varV (fun x => v ‖x‖) ν ≤ varV (fun x => v ‖x‖) μ) (zs : E n)
    (hzs : IsMinOn (fun z => ∫ x, v ‖x - z‖ ∂μ) Set.univ zs) :
    zs ∈ closedConvexHull ℝ μ.support := by
  classical
  have := hμ.1
  by_contra hc
  have hvmon : MonotoneOn v (Set.Ici 0) := hvmono.monotoneOn
  -- measurability and integrability
  set vt : ℝ → ℝ := fun t => v (max t 0) with hvt
  have hvt_mono : Monotone vt := by
    intro a b hab
    exact hvmon (Set.mem_Ici.mpr (le_max_right _ _)) (Set.mem_Ici.mpr (le_max_right _ _))
      (max_le_max hab le_rfl)
  have hmeas : ∀ z : E n, Measurable (fun x : E n => v ‖x - z‖) := by
    intro z
    have : (fun x : E n => v ‖x - z‖) = vt ∘ (fun x => ‖x - z‖) := by
      ext x; simp [hvt, max_eq_left (norm_nonneg _)]
    rw [this]
    exact hvt_mono.measurable.comp (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
  have hKae : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hμ.2
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  have hint : ∀ z, Integrable (fun x => v ‖x - z‖) μ := by
    intro z
    refine Integrable.mono' (integrable_const (v (B + ‖z‖))) (hmeas z).aestronglyMeasurable ?_
    filter_upwards [hKae] with x hx
    rw [Real.norm_of_nonneg (hv0 _ (norm_nonneg _))]
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB x hx)
    apply hvmon (Set.mem_Ici.mpr (norm_nonneg _)) (Set.mem_Ici.mpr (by positivity))
    calc ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ B + ‖z‖ := by linarith [hB x hx]
  -- separation of zs from the closed convex hull of the support
  obtain ⟨f, u, w, hfu, huw, hfw⟩ := geometric_hahn_banach_compact_closed
    (convex_singleton zs) isCompact_singleton (convex_closedConvexHull (𝕜 := ℝ))
    isClosed_closedConvexHull (Set.disjoint_singleton_left.mpr hc)
  have hfz := hfu zs rfl
  set δ := w - u with hδ
  have hδpos : 0 < δ := by linarith
  set g : E n := (InnerProductSpace.toDual ℝ (E n)).symm f with hg
  have hgf : ∀ x, inner ℝ g x = f x := fun x => InnerProductSpace.toDual_symm_apply
  set G := ‖g‖ with hG
  set t := δ / (G ^ 2 + 1) with ht
  have htpos : 0 < t := by positivity
  have htG : t * G ^ 2 < δ := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  set z := zs + t • g with hz
  -- every point of the support is strictly closer to z than to zs
  have hcloser : ∀ a ∈ μ.support, ‖a - z‖ < ‖a - zs‖ := by
    intro a ha
    have h1 : δ < f a - f zs := by
      have := hfw a (subset_closedConvexHull ha); linarith
    have hexp : ‖a - z‖ ^ 2 = ‖a - zs‖ ^ 2 - 2 * t * inner ℝ (a - zs) g + t ^ 2 * G ^ 2 := by
      have e : a - z = (a - zs) - t • g := by rw [hz]; abel
      rw [e, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg htpos.le]; ring
    have hin : inner ℝ (a - zs) g = f a - f zs := by rw [real_inner_comm, hgf, map_sub]
    have hlt : ‖a - z‖ ^ 2 < ‖a - zs‖ ^ 2 := by
      rw [hexp, hin]; nlinarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hlt
  -- hence the integral at z is strictly smaller
  set h : E n → ℝ := fun x => v ‖x - zs‖ - v ‖x - z‖ with hh
  have hpos : ∀ a ∈ μ.support, 0 < h a := by
    intro a ha
    have := hvmono (Set.mem_Ici.mpr (norm_nonneg _)) (Set.mem_Ici.mpr (norm_nonneg _))
      (hcloser a ha)
    simp only [hh]; linarith
  have hsupp : ∀ᵐ x ∂μ, x ∈ μ.support := Measure.support_mem_ae
  have hnn : 0 ≤ᵐ[μ] h := by
    filter_upwards [hsupp] with x hx; exact (hpos x hx).le
  have hhint : Integrable h μ := (hint zs).sub (hint z)
  have hIpos : 0 < ∫ x, h x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hhint]
    have hsub : μ.support ⊆ Function.support h := fun a ha => (hpos a ha).ne'
    have h1 : μ μ.support = 1 := by
      have := measure_inter_conull (μ := μ) (s := Set.univ) (t := μ.support)
        Measure.measure_compl_support
      rw [Set.univ_inter, measure_univ] at this; exact this
    calc (0 : ENNReal) < 1 := one_pos
      _ = μ μ.support := h1.symm
      _ ≤ μ (Function.support h) := measure_mono hsub
  have hI : ∫ x, h x ∂μ = ∫ x, v ‖x - zs‖ ∂μ - ∫ x, v ‖x - z‖ ∂μ := integral_sub (hint zs) (hint z)
  have hmin := hzs (Set.mem_univ z)
  simp only [Set.mem_setOf_eq] at hmin
  linarith
