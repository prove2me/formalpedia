-- Prove2me | solution 1 for GlobalTheory.fourierCoeff_mul_char_conv_and_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:43.984902+00:00
-- url     : https://prove2.me/submissions/92037c49-7a3f-4344-a36d-4a86696c6356

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MeanSquareAddFundamentalDomainOfCocompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierCoeffMulCharConvAndHasDerivAt
import Theorems.Thm_GlobalTheory_measure_addFundamentalDomain_lt_top_of_cocompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
namespace GlobalTheory
open MeasureTheory in
open scoped Pointwise in
private lemma exists_norm_le_of_continuous_periodic_compact_cover {G : Type} [AddCommGroup G] [TopologicalSpace G]
    (Γ : AddSubgroup G) {K : Set G} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    {Φ : G → ℂ} (hΦ : Continuous Φ) (hper : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) :
    ∃ M, ∀ x, ‖Φ x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image hΦ.norm).bddAbove
  refine ⟨M, fun x => ?_⟩
  obtain ⟨γ, hγ, hx⟩ := hcov x
  rw [← hper γ hγ x]
  exact hM ⟨_, hx, rfl⟩
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open MeasureTheory
open scoped Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ χ : G → ℂ, Continuous χ → (∀ x y, χ (x + y) = χ x * χ y) → (∀ x, ‖χ x‖ = 1) → (∀ γ ∈ Γ, χ γ = 1) → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ z, (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ z = ∫ y in 𝓕, Φ (z + y) * starRingEnd ℂ (χ y) ∂μ) ∧ ∀ (L : ℝ →+ G) (Φ' : G → ℂ), Continuous Φ' → (∀ γ ∈ Γ, ∀ x, Φ' (γ + x) = Φ' x) → (∀ x, HasDerivAt (fun t : ℝ => Φ (x + L t)) (Φ' x) 0) → ∀ x, HasDerivAt (fun t : ℝ => (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ (x + L t)) ((∫ y in 𝓕, Φ' y * starRingEnd ℂ (χ y) ∂μ) * χ x) 0 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov μ 𝓕 hμ h𝓕 χ hχ hmul hnorm hχΓ Φ hΦ hper
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hcc : ∀ x, starRingEnd ℂ (χ x) * χ x = 1 := by
    intro x
    rw [Complex.conj_mul', hnorm x]
    simp
  have conv : ∀ Ψ : G → ℂ, (∀ γ ∈ Γ, ∀ x, Ψ (γ + x) = Ψ x) → ∀ z,
      (∫ y in 𝓕, Ψ y * starRingEnd ℂ (χ y) ∂μ) * χ z = ∫ y in 𝓕, Ψ (z + y) * starRingEnd ℂ (χ y) ∂μ := by
    intro Ψ hΨ z
    set g : G → ℂ := fun y => Ψ y * starRingEnd ℂ (χ y) with hg
    have hgper : ∀ (γ : Γ) (y : G), g (γ +ᵥ y) = g y := by
      intro γ y
      simp only [hg, AddSubgroup.vadd_def, vadd_eq_add, hmul, map_mul, hχΓ γ γ.2, map_one, one_mul,
        hΨ γ γ.2]
    have hpt : ∀ y, Ψ (z + y) * starRingEnd ℂ (χ y) = g (z + y) * χ z := by
      intro y
      simp only [hg, hmul, map_mul]
      linear_combination -(Ψ (z + y) * starRingEnd ℂ (χ y)) * hcc z
    have hS : IsAddFundamentalDomain Γ ((fun y => -z + y) ⁻¹' 𝓕) μ := by
      have hset : (fun y => -z + y) ⁻¹' 𝓕 = z +ᵥ 𝓕 := by
        ext y
        simp only [Set.mem_preimage, Set.mem_vadd_set, vadd_eq_add]
        constructor
        · intro h
          exact ⟨_, h, add_neg_cancel_left z y⟩
        · rintro ⟨w, hw, rfl⟩
          simpa using hw
      rw [hset]
      exact h𝓕.vadd_of_comm z
    have hpre : (fun y => z + y) ⁻¹' ((fun y => -z + y) ⁻¹' 𝓕) = 𝓕 := by
      ext y; simp
    calc (∫ y in 𝓕, g y ∂μ) * χ z
        = (∫ y in (fun y => -z + y) ⁻¹' 𝓕, g y ∂μ) * χ z := by rw [h𝓕.setIntegral_eq hS hgper]
      _ = (∫ y in 𝓕, g (z + y) ∂μ) * χ z := by
          rw [← (measurePreserving_add_left μ z).setIntegral_preimage_emb
            (measurableEmbedding_addLeft z), hpre]
      _ = ∫ y in 𝓕, g (z + y) * χ z ∂μ := (integral_mul_const _ _).symm
      _ = ∫ y in 𝓕, Ψ (z + y) * starRingEnd ℂ (χ y) ∂μ := by simp_rw [hpt]
  refine ⟨conv Φ hper, ?_⟩
  intro L Φ' hΦ' hper' hderiv x
  obtain ⟨M, hM⟩ := exists_norm_le_of_continuous_periodic_compact_cover Γ hK hcov hΦ hper
  obtain ⟨M', hM'⟩ := exists_norm_le_of_continuous_periodic_compact_cover Γ hK hcov hΦ' hper'
  have hfin : μ 𝓕 < ⊤ := _root_.GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.mpr hfin.ne
  have hfun : (fun t : ℝ => (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ y) ∂μ) * χ (x + L t)) =
      fun t : ℝ => ∫ y in 𝓕, Φ (x + L t + y) * starRingEnd ℂ (χ y) ∂μ := by
    funext t; exact conv Φ hper (x + L t)
  rw [hfun, conv Φ' hper' x]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ)
    (F := fun (t : ℝ) y => Φ (x + L t + y) * starRingEnd ℂ (χ y))
    (F' := fun (t : ℝ) y => Φ' (x + L t + y) * starRingEnd ℂ (χ y)) (x₀ := 0) (s := Set.univ)
    (bound := fun _ => M') Filter.univ_mem
    (Filter.Eventually.of_forall fun t => by fun_prop)
    (Integrable.of_bound (by fun_prop) M (Filter.Eventually.of_forall fun y => by
      simp [hnorm, hM]))
    (by fun_prop)
    (Filter.Eventually.of_forall fun y t _ => by simp [hnorm, hM'])
    (integrable_const _)
    (Filter.Eventually.of_forall fun y t _ => by
      have h := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hderiv (x + L t + y))
      have h' : HasDerivAt (fun s : ℝ => Φ (x + L s + y)) (Φ' (x + L t + y)) t := by
        have e : (fun s : ℝ => Φ (x + L s + y)) = fun s : ℝ => Φ (x + L t + y + L (s - t)) := by
          funext s
          congr 1
          rw [show L s = L t + L (s - t) by rw [← map_add]; congr 1; ring]
          abel
        rw [e]
        exact h
      exact h'.mul_const _)
  simpa using key.2
end _root_.GlobalTheory
end GlobalTheory
