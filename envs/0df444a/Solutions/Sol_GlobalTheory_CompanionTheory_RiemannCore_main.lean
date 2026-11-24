-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:05:37.455071+00:00
-- url     : https://prove2.me/submissions/fd3f6e28-a78c-4e6d-a236-88e4e13a823e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_tile_sum_estimate
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_exists_nhds_close
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_mem_tile
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_measurableSet_tile
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_measure_tile
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_tile_disjoint
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_tile_cover
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_finite_lattice_points
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_scaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RiemannCore
namespace GlobalTheory.CompanionTheory.RiemannCore
theorem _root_.solution : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (Λ : AddSubgroup G) [Countable Λ] (D K₀ : Set G) (R : Finset G) (T : ℝ → G →+ G) (M : ℕ), MeasurableSet D → IsCompact K₀ → D ⊆ K₀ → μ D = 1 → (∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) → (∀ ε : ℝ, 0 < ε → Continuous (T ε)) → (∀ ε : ℝ, 0 < ε → ∀ y, T ε⁻¹ (T ε y) = y ∧ T ε (T ε⁻¹ y) = y) → (∀ ε : ℝ, 0 < ε → Measure.map (T ε) μ = ENNReal.ofReal ((ε ^ M)⁻¹) • μ) → (∀ B : Set G, IsCompact B → ∀ U ∈ 𝓝 (0 : G), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ B, T ε b ∈ U) → ∀ (x0 : G) (φ : G → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun l : Λ => φ (T ε (x0 + l))) ∧ Tendsto (fun ε : ℝ => ε ^ M * ∑' l : Λ, φ (T ε (x0 + l))) (𝓝[>] 0) (𝓝 ((R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ)) := by
  intro G _ _ _ _ _ _ _ _ μ _ Λ _ D K₀ R T M hD hK hDK hD1 ht hcont hinv hscale hshrink x0 φ hφc hφs
  let τ : ∀ ε : ℝ, 0 < ε → G ≃ₜ G := fun ε hε =>
    { toFun := T ε
      invFun := T ε⁻¹
      left_inv := fun y => (hinv ε hε y).1
      right_inv := fun y => (hinv ε hε y).2
      continuous_toFun := hcont ε hε
      continuous_invFun := hcont ε⁻¹ (inv_pos.2 hε) }
  have hsummable : ∀ ε : ℝ, 0 < ε → Summable fun l : Λ => φ (T ε (x0 + l)) := by
    intro ε hε
    have hfin := finite_lattice_points μ hD hK hDK hD1 R Λ ht x0 (C := T ε⁻¹ '' tsupport φ)
      (IsCompact.image hφs (hcont _ (inv_pos.2 hε)))
    refine summable_of_finite_support (hfin.subset ?_)
    intro l hl
    exact ⟨T ε (x0 + l), subset_tsupport _ hl, (hinv ε hε _).1⟩
  refine ⟨hsummable, ?_⟩
  obtain ⟨W, hWc, hW⟩ := exists_compact_mem_nhds (0 : G)
  set C : Set G := (fun p : G × G => p.1 - p.2) '' (tsupport φ ×ˢ W) with hC
  have hCc : IsCompact C := (IsCompact.prod hφs hWc).image (by fun_prop)
  have hCm : MeasurableSet C := hCc.measurableSet
  set B : Set G := (fun p : G × G => x0 - p.1 - p.2) '' ((R : Set G) ×ˢ K₀) with hB
  have hBc : IsCompact B := (R.finite_toSet.isCompact.prod hK).image (by fun_prop)
  have hRpos : (0 : ℝ) < R.card := by
    obtain ⟨⟨r, l⟩, ⟨hr, -, -⟩, -⟩ := ht 0
    exact_mod_cast Finset.card_pos.2 ⟨r, hr⟩
  have hφi : Integrable φ μ := hφc.integrable_of_hasCompactSupport hφs
  have hCi : Integrable (C.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hCm).2 (integrableOn_const hCc.measure_lt_top.ne)
  have hkey : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      |ε ^ M * ∑' l : Λ, φ (T ε (x0 + l)) - (R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ| ≤
        δ * (μ.real C / R.card) := by
    intro δ hδ
    obtain ⟨V₁, hV₁, hclose⟩ := exists_nhds_close φ hφc hφs hδ
    filter_upwards [hshrink B hBc (V₁ ∩ W) (inter_mem hV₁ hW), self_mem_nhdsWithin]
      with ε hε hpos
    have hpos' : 0 < ε := hpos
    have hpow : 0 < ε ^ M := pow_pos hpos' M
    have hemb : MeasurableEmbedding (T ε) := (τ ε hpos').measurableEmbedding
    obtain ⟨hi1, he1⟩ := scaling μ hemb (inv_nonneg.2 hpow.le) (hscale ε hpos') hφi
    obtain ⟨hi2, he2⟩ := scaling μ hemb (inv_nonneg.2 hpow.le) (hscale ε hpos') hCi
    have est := tile_sum_estimate μ (fun l : Λ => tile D R (l : G))
      (fun l => measurableSet_tile hD R _) (tile_disjoint ht) (tile_cover ht) R.card
      (fun l => measure_tile μ hD hD1 R Λ ht _) (fun l : Λ => φ (T ε (x0 + l)))
      (hsummable ε hpos') (fun y => φ (T ε y))
      (fun y => δ * C.indicator (fun _ => (1 : ℝ)) (T ε y)) hi1 (hi2.const_mul δ) (by
        intro l y hy
        obtain ⟨r, hr, hyd⟩ := mem_tile.1 hy
        have hb : x0 + (l : G) - y ∈ B :=
          ⟨(r, y - r - l), ⟨hr, hDK hyd⟩, by simp only; abel⟩
        have hTU := hε _ hb
        rw [map_sub] at hTU
        generalize T ε (x0 + (l : G)) = a at hTU ⊢
        generalize T ε y = b at hTU ⊢
        by_cases hbC : b ∈ C
        · rw [Set.indicator_of_mem hbC]
          simpa using (hclose a b hTU.1).le
        · have hb0 : φ b = 0 := by
            by_contra h
            exact hbC ⟨(b, 0), ⟨subset_tsupport _ h, mem_of_mem_nhds hW⟩, by simp⟩
          have ha0 : φ a = 0 := by
            by_contra h
            exact hbC ⟨(a, a - b), ⟨subset_tsupport _ h, hTU.2⟩, by simp⟩
          rw [Set.indicator_of_notMem hbC]
          simp [ha0, hb0])
    rw [he1, integral_const_mul, he2, integral_indicator_const _ hCm] at est
    simp only [smul_eq_mul, mul_one] at est
    have hid : ε ^ M * ∑' l : Λ, φ (T ε (x0 + l)) - (R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ =
        (ε ^ M / R.card) * ((R.card : ℝ) * ∑' l : Λ, φ (T ε (x0 + l)) -
          (ε ^ M)⁻¹ * ∫ y, φ y ∂μ) := by
      field_simp
    rw [hid, abs_mul, abs_of_pos (div_pos hpow hRpos)]
    calc ε ^ M / R.card * _ ≤ ε ^ M / R.card * (δ * ((ε ^ M)⁻¹ * μ.real C)) :=
          mul_le_mul_of_nonneg_left est (div_pos hpow hRpos).le
      _ = δ * (μ.real C / R.card) := by field_simp
  rw [Metric.tendsto_nhds]
  intro η hη
  have hK0 : 0 ≤ μ.real C / R.card := div_nonneg measureReal_nonneg hRpos.le
  set L := μ.real C / R.card with hL
  have hδ : 0 < η / (L + 1) := by positivity
  filter_upwards [hkey _ hδ] with ε hε
  rw [Real.dist_eq]
  refine lt_of_le_of_lt hε ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith
end GlobalTheory.CompanionTheory.RiemannCore
