-- Prove2me | solution 1 for GlobalTheory.JR.fourB_indicator_intLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:03:03.33781+00:00
-- url     : https://prove2.me/submissions/fb66b3da-e8e8-46d4-9d9b-6a3e1359c865

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierIndicatorHermitianIntegralLattice
import Theorems.Thm_GlobalTheory_T_unramifiedStandardAddChar_conductor_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) (B : A.L → A.L → ℂ), (∀ y' y, B y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) → IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} → ∀ μ : Measure A.L, μ.IsAddHaarMeasure → ∀ y, fourB μ B (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1) y = ((μ {y : A.L | ∀ i, ‖j y i‖ ≤ 1}).toReal : ℂ) * Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} 1 y := by
  intro F E _ _ _ _ hU A ψ hψ r j B hB hO _hC μ hμ y
  haveI := hU.ultraE
  set Λ : Set A.L := {y : A.L | ∀ i, ‖j y i‖ ≤ 1} with hΛ
  have key : ∀ z : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * z)) = 1) ↔ ‖z‖ ≤ 1 :=
    ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  have hmem_add : ∀ a x, a ∈ Λ → (a + x ∈ Λ ↔ x ∈ Λ) := by
    intro a x ha
    constructor
    · intro h i
      have e1 : j x i = j (a + x) i + -(j a i) := by simp
      rw [e1]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h i) (by rw [norm_neg]; exact ha i))
    · intro h i
      rw [map_add, Pi.add_apply]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (h i))
  have hBadd : ∀ a x, B (a + x) y = B a y * B x y := by
    intro a x
    rw [hB, hB, hB, map_add, star_add, add_dotProduct, map_add, AddChar.map_add_eq_mul]
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  unfold fourB
  by_cases hy : y ∈ Λ
  · have h1 : ∀ x, Set.indicator Λ 1 x * B x y = Set.indicator Λ (fun _ => (1:ℂ)) x := by
      intro x
      by_cases hx : x ∈ Λ
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, hB]
        simp only [dotProduct, Pi.star_apply, map_sum]
        refine Finset.sum_induction _ (fun t => ψ t = 1) (fun u v hu hv => by
          rw [AddChar.map_add_eq_mul, hu, hv, one_mul]) (AddChar.map_zero_eq_one ψ) fun i _ => ?_
        exact (key (j y i)).2 (hy i) _ (by rw [hU.norm_star]; exact hx i)
      · simp [hx]
    simp_rw [h1]
    rw [integral_indicator_const _ hO.measurableSet, Set.indicator_of_mem hy, Pi.one_apply, mul_one]
    simp [Measure.real]
  · obtain ⟨i, hi⟩ : ∃ i, ¬ ‖j y i‖ ≤ 1 := by
      by_contra h
      push_neg at h
      exact hy h
    obtain ⟨e, he, hne⟩ : ∃ e : E, ‖e‖ ≤ 1 ∧ ψ (Algebra.trace F E (e * j y i)) ≠ 1 := by
      by_contra h
      push_neg at h
      exact hi ((key _).1 h)
    set a := j.symm (Pi.single i (star e)) with ha_def
    have hja : j a = Pi.single i (star e) := by simp [ha_def]
    have ha : a ∈ Λ := by
      intro k
      rw [hja]
      by_cases hk : k = i
      · subst hk; simp [hU.norm_star, he]
      · simp [Pi.single_eq_of_ne hk]
    have hst : star (Pi.single i (star e) : Fin r → E) = Pi.single i e := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    have hBa : B a y = ψ (Algebra.trace F E (e * j y i)) := by
      rw [hB, hja, hst, single_dotProduct]
    have hint : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = B a y * ∫ x, Set.indicator Λ 1 x * B x y ∂μ := by
      rw [← integral_const_mul]
      calc ∫ x, Set.indicator Λ 1 x * B x y ∂μ
          = ∫ x, Set.indicator Λ 1 (a + x) * B (a + x) y ∂μ :=
            (integral_add_left_eq_self (fun x => Set.indicator Λ 1 x * B x y) a).symm
        _ = ∫ x, B a y * (Set.indicator Λ 1 x * B x y) ∂μ := by
            congr 1; ext x
            rw [hBadd]
            by_cases hx : x ∈ Λ
            · rw [Set.indicator_of_mem ((hmem_add a x ha).2 hx), Set.indicator_of_mem hx, Pi.one_apply, Pi.one_apply]; ring
            · have hx' : a + x ∉ Λ := fun h => hx ((hmem_add a x ha).1 h)
              simp [hx, hx']
    have h0 : ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0 := by
      have : (1 - B a y) * ∫ x, Set.indicator Λ 1 x * B x y ∂μ = 0 := by
        rw [sub_mul, one_mul, ← hint, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by rw [hBa] at h; exact (sub_eq_zero.1 h).symm) hne
      · exact h
    rw [h0]
    simp [hy]
end GlobalTheory.JR
