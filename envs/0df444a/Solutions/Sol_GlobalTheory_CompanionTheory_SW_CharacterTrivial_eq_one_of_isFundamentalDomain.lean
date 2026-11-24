-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:12:16.094702+00:00
-- url     : https://prove2.me/submissions/908ef1a4-12c6-4c44-9fde-ff5a3147f8c5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModularCharacterTrivialFiniteCovolume
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Averaging_setLIntegral_mul_right_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatticeUnimod_unimodular_of_isFundamentalDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CharacterTrivial
namespace GlobalTheory.CompanionTheory.SW.CharacterTrivial
theorem _root_.solution :
    ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
      [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
      (Γ₁ : Subgroup G₁) [Countable Γ₁] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁),
      IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → ∀ δ : G₁ →* ℝ≥0, Measurable δ →
        (∀ γ ∈ Γ₁, δ γ = 1) → ∀ u, δ u = 1 := by
  intro G₁ _ _ _ _ _ _ _ _ Γ₁ _ μ₁ _ 𝓕₁ h𝓕₁ hfin δ hδ hγ
  obtain ⟨h0, hR, -⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin
  have hinv : ∀ u, δ u * δ u⁻¹ = 1 := fun u => by rw [← map_mul, mul_inv_cancel, map_one]
  have hpos : ∀ u, 0 < (δ u : ℝ) := by
    intro u
    have h : δ u ≠ 0 := left_ne_zero_of_mul_eq_one (hinv u)
    exact_mod_cast pos_iff_ne_zero.2 h
  have hδr : Measurable (fun u => (δ u : ℝ)) := measurable_coe_nnreal_real.comp hδ
  have hind : ∀ (A B : Set G₁) (x y : G₁), (x ∈ A ↔ y ∈ B) →
      A.indicator (1 : G₁ → ℝ≥0∞) x = B.indicator (1 : G₁ → ℝ≥0∞) y := by
    intro A B x y h
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (h.1 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun hy => hx (h.2 hy))]
  have hbig : ∀ u₀, 1 < δ u₀ → False := by
    intro u₀ ht
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = δ u₀ := ⟨_, rfl⟩
    have ht1 : 1 < t := by rw [htdef]; exact_mod_cast ht
    have ht0 : 0 < t := by linarith
    let C : ℤ → Set G₁ := fun n => (fun u => (δ u : ℝ)) ⁻¹' Set.Ico (t ^ n) (t ^ (n + 1))
    have hCm : ∀ n, MeasurableSet (C n) := fun n => hδr measurableSet_Ico
    have hmem : ∀ n u, u * u₀ ∈ C (n + 1) ↔ u ∈ C n := by
      intro n u
      have e : (δ (u * u₀) : ℝ) = δ u * t := by rw [map_mul, htdef]; push_cast; rfl
      simp only [C, Set.mem_preimage, Set.mem_Ico, e]
      rw [zpow_add_one₀ ht0.ne' n, zpow_add_one₀ ht0.ne' (n + 1),
        mul_le_mul_iff_of_pos_right ht0, mul_lt_mul_iff_of_pos_right ht0, zpow_add_one₀ ht0.ne' n]
    have hshift : ∀ n, (μ₁.restrict 𝓕₁) (C n) = (μ₁.restrict 𝓕₁) (C (n + 1)) := by
      intro n
      have hinvar : ∀ γ ∈ Γ₁, ∀ u, (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) (γ * u) =
          (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) u := by
        intro γ hg u
        have e : γ * u ∈ C (n + 1) ↔ u ∈ C (n + 1) := by
          simp only [C, Set.mem_preimage, map_mul, hγ γ hg, one_mul]
        exact hind _ _ _ _ e
      have e := GlobalTheory.CompanionTheory.SW.Averaging.setLIntegral_mul_right_eq μ₁ Γ₁ 𝓕₁ h𝓕₁
        ((C (n + 1)).indicator 1) hinvar u₀
      have e' : (fun u => (C (n + 1)).indicator (1 : G₁ → ℝ≥0∞) (u * u₀)) =
          (C n).indicator 1 := by
        funext u
        exact hind _ _ _ _ (hmem n u)
      rw [e', lintegral_indicator_one (hCm n), lintegral_indicator_one (hCm (n + 1))] at e
      exact e
    have hconst : ∀ n, (μ₁.restrict 𝓕₁) (C n) = (μ₁.restrict 𝓕₁) (C 0) := by
      intro n
      induction n using Int.induction_on with
      | zero => rfl
      | succ i ih => rw [← hshift]; exact ih
      | pred i ih =>
        rw [← ih, hshift (-(i : ℤ) - 1)]
        congr 2
        ring
    have hU : ⋃ n, C n = Set.univ := by
      refine Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ?_
      obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (hpos u) ht1
      exact ⟨n, hn⟩
    have hdisj : Pairwise (Function.onFun Disjoint C) := by
      intro m n hmn
      refine Set.disjoint_left.2 fun u h₁ h₂ => hmn ?_
      have a : t ^ n < t ^ (m + 1) := lt_of_le_of_lt h₂.1 h₁.2
      have b : t ^ m < t ^ (n + 1) := lt_of_le_of_lt h₁.1 h₂.2
      have a' := (zpow_lt_zpow_iff_right₀ ht1).1 a
      have b' := (zpow_lt_zpow_iff_right₀ ht1).1 b
      omega
    have hsum : μ₁ 𝓕₁ = ∑' _ : ℤ, (μ₁.restrict 𝓕₁) (C 0) := by
      rw [← Measure.restrict_apply_univ 𝓕₁, ← hU, measure_iUnion hdisj hCm]
      exact tsum_congr hconst
    by_cases hz : (μ₁.restrict 𝓕₁) (C 0) = 0
    · rw [hz, tsum_zero] at hsum
      exact h0 hsum
    · rw [ENNReal.tsum_const_eq_top_of_ne_zero hz] at hsum
      exact hfin.ne hsum
  intro u
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine hbig u⁻¹ ?_
    by_contra hle
    have h1 : δ u * δ u⁻¹ < 1 * 1 :=
      mul_lt_mul'' hlt (lt_of_le_of_ne (not_lt.1 hle) ?_) zero_le zero_le
    · rw [hinv u, one_mul] at h1
      exact lt_irrefl _ h1
    · intro e
      have := hinv u
      rw [e, mul_one] at this
      exact hne this
  · exact hbig u hgt
end GlobalTheory.CompanionTheory.SW.CharacterTrivial
