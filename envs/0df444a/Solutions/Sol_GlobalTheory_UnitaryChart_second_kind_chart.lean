-- Prove2me | solution 1 for GlobalTheory.UnitaryChart.second_kind_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:17.465193+00:00
-- url     : https://prove2.me/submissions/b7782a0a-b559-4aa0-97de-d991ee673f56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne
import Theorems.Thm_GlobalTheory_UnitaryChart_hasStrictFDerivAt_ofFn_prod
import Theorems.Thm_GlobalTheory_UnitaryChart_unitary_list_prod
import Theorems.Thm_GlobalTheory_UnitaryChart_eq_of_skew_eq
import Theorems.Thm_GlobalTheory_UnitaryChart_exists_skew_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnitaryChart
open Topology Filter
namespace GlobalTheory.UnitaryChart
theorem _root_.solution : ∀ (E : Type) [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E) (N : ℕ) (e : Fin N → E) (c : Fin N → ℝ → E), (∀ a, σ (σ a) = a) → (∀ a b, σ (a * b) = σ b * σ a) → σ 1 = 1 → LinearIndependent ℝ e → (∀ i, σ (e i) = -e i) → (∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) → (∀ i, c i 0 = 1 ∧ HasStrictDerivAt (c i) (e i) 0 ∧ ∀ t, σ (c i t) * c i t = 1 ∧ c i t * σ (c i t) = 1) → ∃ (s S K : ℝ) (W : Set E), 0 < s ∧ 0 ≤ K ∧ W ∈ nhds (1 : E) ∧ ∀ x ∈ W, σ x * x = 1 → x * σ x = 1 → ∃ f : (Fin N → ℝ) → (Fin N → ℝ), (∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖f t‖ ≤ S ∧ (List.ofFn fun i => c i (f t i)).prod * x = (List.ofFn fun i => c i (t i)).prod) ∧ ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∀ t' ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖t - t'‖ ≤ K * ‖f t - f t'‖ := by
  intro E _ _ _ σ N e c hσ hm h1 hli he hsp hc
  set Θ : (Fin N → ℝ) → E := fun t => (List.ofFn fun i => c i (t i)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact (hc i).2.2 _)
  let T : (Fin N → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp (ContinuousLinearMap.proj i)
  have hT : ∀ t, T t = ∑ i, t i • e i := fun t => by simp [T]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    hasStrictFDerivAt_ofFn_prod N (fun i (t : Fin N → ℝ) => c i (t i)) _ (fun i =>
      ⟨(hc i).1, HasStrictFDerivAt.comp (0 : Fin N → ℝ) (g := c i)
        (hc i).2.1.hasStrictFDerivAt
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i).hasStrictFDerivAt⟩)
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_skew_coord σ e hσ hli he hsp
  have hΨ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hΨ0 : P (Θ 0) = 0 := by rw [h0]; exact hP2 _ h1
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  obtain ⟨U₁, hU₁, hA⟩ := hΨ.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
  obtain ⟨L, U₂, hU₂, hL⟩ := hD.exists_lipschitzOnWith
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := by fun_prop
    exact this.eventually_le_const (by simp [h1])
  have hΘt : Tendsto Θ (𝓝 0) (𝓝 1) := h0 ▸ hD.continuousAt
  let U : Set (Fin N → ℝ) := U₁ ∩ U₂ ∩ {t | ‖1 - σ (Θ t)‖ ≤ 1 / 2} ∩ Metric.closedBall 0 1
  have hUn : U ∈ 𝓝 0 :=
    inter_mem (inter_mem (inter_mem hU₁ hU₂) (hΘt.eventually hnear))
      (Metric.closedBall_mem_nhds _ one_pos)
  have hV : (fun t => P (Θ t)) '' U ∈ 𝓝 (0 : Fin N → ℝ) := by
    have := hΨ.map_nhds_eq_of_equiv
    rw [hΨ0] at this
    rw [← this]
    exact image_mem_map hUn
  have hM : Tendsto (fun p : (Fin N → ℝ) × E => Θ p.1 * σ p.2) (𝓝 0 ×ˢ 𝓝 1) (𝓝 1) := by
    have a : Tendsto σ (𝓝 1) (𝓝 1) := by
      simpa [h1] using hσc.tendsto 1
    simpa using (hΘt.comp tendsto_fst).mul (a.comp tendsto_snd)
  have hPM : Tendsto (fun p : (Fin N → ℝ) × E => P (Θ p.1 * σ p.2)) (𝓝 0 ×ˢ 𝓝 1) (𝓝 0) := by
    have a : Tendsto P (𝓝 1) (𝓝 0) := by
      simpa [hP2 _ h1] using P.continuous.tendsto 1
    exact a.comp hM
  obtain ⟨A, hAn, W, hWn, hAW⟩ := Filter.mem_prod_iff.mp ((hM.eventually hnear).and (hPM hV))
  obtain ⟨s, hs, hsA⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (inter_mem hAn hU₁)
  have hcube : ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), t ∈ A ∩ U₁ := by
    intro t ht
    apply hsA
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hs.le]
    intro i
    have := ht i (Set.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  refine ⟨s, 1, 2 * (‖P‖ * (L * (‖(1 : E)‖ + 1))), W ∩ Metric.closedBall 1 1, hs, by positivity,
    inter_mem hWn (Metric.closedBall_mem_nhds _ one_pos), fun x hx hx1 hx2 => ?_⟩
  have hxn : ‖x‖ ≤ ‖(1 : E)‖ + 1 := norm_le_of_mem_closedBall hx.2
  have key : ∀ t : Fin N → ℝ, ∃ y : Fin N → ℝ, t ∈ A → y ∈ U ∧ Θ y * x = Θ t := by
    intro t
    by_cases ht : t ∈ A
    · obtain ⟨k1, y, hy, k2⟩ := hAW (Set.mk_mem_prod ht hx.1)
      refine ⟨y, fun _ => ⟨hy, ?_⟩⟩
      have hv : Θ t * σ x * σ (Θ t * σ x) = 1 := by
        rw [hm, hσ]
        calc Θ t * σ x * (x * σ (Θ t)) = Θ t * (σ x * x) * σ (Θ t) := by noncomm_ring
          _ = 1 := by rw [hx1, mul_one, (hU t).2]
      have := eq_of_skew_eq (hU y).1 hv (hP3 _ _ k2) hy.1.2 k1
      rw [this, mul_assoc, hx1, mul_one]
    · exact ⟨0, fun h => absurd h ht⟩
  choose f hf using key
  refine ⟨f, fun t ht => ?_, fun t ht t' ht' => ?_⟩
  · obtain ⟨a, b⟩ := hf t (hcube t ht).1
    exact ⟨mem_closedBall_zero_iff.mp a.2, b⟩
  · obtain ⟨a, b⟩ := hf t (hcube t ht).1
    obtain ⟨a', b'⟩ := hf t' (hcube t' ht').1
    have k1 := hA t (hcube t ht).2 t' (hcube t' ht').2
    have k2 : ‖t - t'‖ ≤ 2 * ‖P (Θ t) - P (Θ t')‖ := by
      have k3 : ‖t - t'‖ ≤ ‖P (Θ t) - P (Θ t')‖ + ‖P (Θ t) - P (Θ t') - (t - t')‖ := by
        have := norm_sub_le (P (Θ t) - P (Θ t')) (P (Θ t) - P (Θ t') - (t - t'))
        simpa using this
      have k4 : ‖P (Θ t) - P (Θ t') - (t - t')‖ ≤ 1 / 2 * ‖t - t'‖ := by simpa using k1
      linarith
    have k5 : ‖Θ (f t) - Θ (f t')‖ ≤ L * ‖f t - f t'‖ := by
      simpa [dist_eq_norm] using hL.dist_le_mul _ a.1.1.2 _ a'.1.1.2
    have k6 : ‖P (Θ t) - P (Θ t')‖ ≤ ‖P‖ * (L * ‖f t - f t'‖ * (‖(1 : E)‖ + 1)) := by
      rw [← map_sub, ← b, ← b', ← sub_mul]
      refine (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact (norm_mul_le _ _).trans (mul_le_mul k5 hxn (norm_nonneg _) (by positivity))
    calc ‖t - t'‖ ≤ 2 * (‖P‖ * (L * ‖f t - f t'‖ * (‖(1 : E)‖ + 1))) := by linarith
      _ = _ := by ring
end GlobalTheory.UnitaryChart
