-- Prove2me | solution 1 for LanglandsTunnell.exists_forall_norm_a_le_of_formalBaseChange_agrees_liftTraceSeed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/679d6e9e-60fd-5392-bfca-526daa20f318

import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Theorems.Thm_AutomorphicForm_satakePow_add_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_forall_norm_a_le_of_formalBaseChange_agrees_liftTraceSeed

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

private theorem seedBound_roots (s t : ℂ) : ∃ α β : ℂ, α + β = s ∧ α * β = t := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_eq_mul_self (s ^ 2 - 4 * t)
  refine ⟨(s + δ) / 2, (s - δ) / 2, by ring, ?_⟩
  linear_combination (1 / 4 : ℂ) * hδ

private theorem seedBound_ordered (α β : ℂ) (f : ℕ) (hf : f ≠ 0) (C D : ℝ)
    (hord : ‖β‖ ≤ ‖α‖) (hC : ‖α ^ f + β ^ f‖ ≤ C) (hDf : ‖(α * β) ^ f‖ ≤ D) :
    ‖α + β‖ ≤ max (C + 2) (2 * D) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  by_cases hβ : ‖β‖ ≤ 1
  ·
    refine le_trans ?_ (le_max_left _ _)
    have hαf : ‖α‖ ^ f ≤ C + 1 := by
      have h1 : ‖α ^ f‖ ≤ ‖α ^ f + β ^ f‖ + ‖β ^ f‖ := by
        have := norm_sub_le (α ^ f + β ^ f) (β ^ f)
        rwa [add_sub_cancel_right] at this
      have h2 : ‖β ^ f‖ ≤ 1 := by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hβ
      rw [norm_pow] at h1
      linarith
    have hα : ‖α‖ ≤ C + 1 := by
      by_cases hα1 : ‖α‖ ≤ 1
      · linarith
      · exact (le_self_pow₀ (not_le.1 hα1).le hf).trans hαf
    calc ‖α + β‖ ≤ ‖α‖ + ‖β‖ := norm_add_le α β
      _ ≤ (C + 1) + 1 := add_le_add hα hβ
      _ = C + 2 := by ring
  ·
    have hβ1 : 1 < ‖β‖ := not_le.1 hβ
    refine le_trans ?_ (le_max_right _ _)
    have hprod : ‖α‖ * ‖β‖ ≤ D := by
      have h1 : 1 ≤ ‖α‖ * ‖β‖ := by nlinarith
      have h2 : ‖α‖ * ‖β‖ ≤ (‖α‖ * ‖β‖) ^ f := le_self_pow₀ h1 hf
      rw [norm_pow, norm_mul] at hDf
      exact h2.trans hDf
    have hα : ‖α‖ ≤ D := by
      have h1 : ‖α‖ ≤ ‖α‖ * ‖β‖ := le_mul_of_one_le_right (norm_nonneg _) hβ1.le
      exact h1.trans hprod
    calc ‖α + β‖ ≤ ‖α‖ + ‖β‖ := norm_add_le α β
      _ ≤ D + D := add_le_add hα (hord.trans hα)
      _ = 2 * D := by ring

private theorem seedBound_symm (α β : ℂ) (f : ℕ) (hf : f ≠ 0) (C D : ℝ)
    (hC : ‖α ^ f + β ^ f‖ ≤ C) (hDf : ‖(α * β) ^ f‖ ≤ D) : ‖α + β‖ ≤ max (C + 2) (2 * D) := by
  rcases le_total ‖β‖ ‖α‖ with hord | hord
  · exact seedBound_ordered α β f hf C D hord hC hDf
  · rw [add_comm]
    refine seedBound_ordered β α f hf C D hord ?_ ?_
    · rwa [add_comm]
    · rwa [mul_comm]

private theorem seedBound_satake (s t : ℂ) (f : ℕ) (hf : f ≠ 0) (C D : ℝ)
    (hC : ‖satakePow f s t‖ ≤ C) (hDf : ‖t ^ f‖ ≤ D) : ‖s‖ ≤ max (C + 2) (2 * D) := by
  obtain ⟨α, β, rfl, rfl⟩ := seedBound_roots s t
  rw [satakePow_add_pow] at hC
  exact seedBound_symm α β f hf C D hC hDf

private theorem seedBound_under {L : Type} [Field L] [NumberField L] (E : IntermediateField ℚ L)
    (p : HeightOneSpectrum (𝓞 ℚ)) : ∃ w : HeightOneSpectrum (𝓞 ↥E), w.under (𝓞 ℚ) = p := by
  haveI := p.isMaximal
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 ↥E) p.asIdeal
    (by rw [NumberField.RingOfIntegers.ker_algebraMap_eq_bot ℚ ↥E]; exact bot_le)
  have hQb : Q ≠ ⊥ := by
    rintro rfl
    exact p.ne_bot (hQp.symm.trans (Ideal.comap_bot_of_injective (algebraMap (𝓞 ℚ) (𝓞 ↥E))
      (NumberField.RingOfIntegers.algebraMap.injective ℚ ↥E)))
  exact ⟨⟨Q, hQ.isPrime, hQb⟩, HeightOneSpectrum.ext hQp⟩

private theorem seedBound_inertiaDeg {L : Type} [Field L] [NumberField L] (E : IntermediateField ℚ L)
    (w : HeightOneSpectrum (𝓞 ↥E)) : (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal ≠ 0 := by
  haveI : (w.under (𝓞 ℚ)).asIdeal.IsMaximal := (w.under (𝓞 ℚ)).isMaximal
  haveI : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  exact (Ideal.inertiaDeg'_pos _ _).ne'

private theorem seedBound_finite (φ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) → ℂ) :
    ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Set.finite_range fun g => ‖φ g‖).bddAbove
  exact ⟨C, fun g => hC ⟨g, rfl⟩⟩

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (H : Subgroup (L ≃ₐ[ℚ] L))
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hagree : AutomorphicForm.HeckeEigensystem.AgreesAwayFromFinite
      (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld H) Φ)
      ((LanglandsTunnell.P2.liftTraceSeed e H).map AutomorphicForm.iotaZsqrtdNegTwo)) :
    ∃ C : ℝ, ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), ‖Φ.a p‖ ≤ C := by
  classical
  obtain ⟨S, hS⟩ := hagree

  obtain ⟨C₀, hC₀⟩ := seedBound_finite
    fun g => iotaZsqrtdNegTwo (LanglandsTunnell.P2.liftOf g).trace
  obtain ⟨D₀, hD₀⟩ := seedBound_finite
    fun g => iotaZsqrtdNegTwo (LanglandsTunnell.P2.liftOf g).det

  set SQ : Finset (HeightOneSpectrum (𝓞 ℚ)) := S.image fun w => w.under (𝓞 ℚ) with hSQ
  refine ⟨max (C₀ + 2) (2 * D₀) + ∑ q ∈ SQ, ‖Φ.a q‖, fun p => ?_⟩
  have hsum_nonneg : 0 ≤ ∑ q ∈ SQ, ‖Φ.a q‖ := Finset.sum_nonneg fun q _ => norm_nonneg _
  have hC₀0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ 1)
  have hmax_nonneg : 0 ≤ max (C₀ + 2) (2 * D₀) := le_trans (by linarith) (le_max_left (C₀ + 2) (2 * D₀))
  by_cases hp : p ∈ SQ
  ·
    have h1 : ‖Φ.a p‖ ≤ ∑ q ∈ SQ, ‖Φ.a q‖ :=
      Finset.single_le_sum (f := fun q => ‖Φ.a q‖) (fun q _ => norm_nonneg _) hp
    linarith
  ·
    refine le_trans ?_ (le_add_of_nonneg_right hsum_nonneg)
    obtain ⟨w, hw⟩ := seedBound_under (LanglandsTunnell.fixFld H) p
    have hwS : w ∉ S := fun h => hp (by rw [hSQ]; exact Finset.mem_image.2 ⟨w, h, hw⟩)
    obtain ⟨ha, hb⟩ := hS w hwS
    rw [formalBaseChange_a, HeckeEigensystem.map_a] at ha
    rw [formalBaseChange_b, HeckeEigensystem.map_b] at hb
    rw [← hw]
    refine seedBound_satake (Φ.a (w.under (𝓞 ℚ))) (Φ.b (w.under (𝓞 ℚ)))
      ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal) (seedBound_inertiaDeg (LanglandsTunnell.fixFld H) w)
      C₀ D₀ ?_ ?_
    · rw [ha]
      exact hC₀ (e (LanglandsTunnell.P2.seedFrob H w))
    · rw [hb]
      exact hD₀ (e (LanglandsTunnell.P2.seedFrob H w))

#print axioms solution

end S_LanglandsTunnell_exists_forall_norm_a_le_of_formalBaseChange_agrees_liftTraceSeed
end P2MW
export P2MW.S_LanglandsTunnell_exists_forall_norm_a_le_of_formalBaseChange_agrees_liftTraceSeed (solution)
