-- Prove2me | solution 1 for NumberField.sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3d984c32-d885-556a-ae05-e21d134d162f

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]

    (C : ℝ) (hC : 0 < C)
    (hCl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ENNReal, Measurable g →
        ∫⁻ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          ENNReal.ofReal C *
            ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hCi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
        (Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)))
            (HaarQuotient.measure νZL N1 μN) ↔
          IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          C * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)

    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))

    (F : (AdeleRing (𝓞 K) K)ˣ → ℂ) (hFm : Measurable F)
    (hFi : ∀ ξ ∈ Ξ, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * F z) νZK)
    (hF0 : ∀ z : (AdeleRing (𝓞 K) K)ˣ, z ∉ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm → F z = 0) :
    (Ξ.Nonempty → Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
          F ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)))
      (HaarQuotient.measure νZL N1 μN)) ∧
    ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * F z ∂νZK =
      ((Ξ.card : ℂ) / (C : ℂ)) *
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
          ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            F ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)) ∂(HaarQuotient.measure νZL N1 μN) := by
  classical
  set Nrm := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hNrm
  have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  by_cases hne : Ξ.Nonempty
  swap
  ·
    have hempty : Ξ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun h => absurd h hne, ?_⟩
    rw [hempty, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_div, zero_mul]
  obtain ⟨ξ₁, hξ₁⟩ := hne
  obtain ⟨hξ₁c, -, hξ₁N⟩ := (hΞ ξ₁).mp hξ₁

  set g : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun z => ((ξ₁ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * F z with hg
  have hgm : Measurable g := hξ₁c.measurable.mul hFm
  have hg0 : ∀ z : (AdeleRing (𝓞 K) K)ˣ, z ∉ Set.range Nrm → g z = 0 := by
    intro z hz
    simp only [hg, hF0 z hz, mul_zero]

  have hgN : (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
        g (Nrm (wq.out : (AdeleRing (𝓞 L) L)ˣ))) =
      fun wq => ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
        F (Nrm (wq.out : (AdeleRing (𝓞 L) L)ˣ)) := by
    funext wq
    simp only [hg]
    rw [hξ₁N]
  obtain ⟨hiff, hint⟩ := hCi g hgm

  have hsame : ∀ ξ ∈ Ξ,
      ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * F z ∂νZK =
        ∫ z : (AdeleRing (𝓞 K) K)ˣ, g z ∂νZK := by
    intro ξ hξ
    obtain ⟨-, -, hξN⟩ := (hΞ ξ).mp hξ
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show _ = g z
    dsimp only
    by_cases hz : z ∈ Set.range Nrm
    · obtain ⟨w, rfl⟩ := hz
      simp only [hg]
      rw [hξN w, hξ₁N w]
    · rw [hg0 z hz, hF0 z hz, mul_zero]
  refine ⟨fun _ => ?_, ?_⟩
  ·
    rw [← hgN]
    exact hiff.mpr (hFi ξ₁ hξ₁).integrableOn
  · rw [Finset.sum_congr rfl hsame, Finset.sum_const, nsmul_eq_mul, ← hgN, hint,
      setIntegral_eq_integral_of_forall_compl_eq_zero hg0]
    field_simp

end S_NumberField_sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range
end P2MW
export P2MW.S_NumberField_sum_integral_mul_eq_card_div_mul_integral_haarQuotient_ker_idelicNorm_of_forall_eq_zero_of_not_mem_range (solution)
