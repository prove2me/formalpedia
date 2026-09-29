-- Prove2me | solution 1 for MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/25e45e52-0af4-5b6c-aa09-4aa47548afa4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero

set_option autoImplicit false

open MeasureTheory

namespace TorusUnifAux

noncomputable abbrev P1 : Measure (AddCircle (1 : ℝ)) := AddCircle.haarAddCircle

noncomputable abbrev P (d : ℕ) : Measure (Fin d → AddCircle (1 : ℝ)) := Measure.pi fun _ => P1

scoped instance (d : ℕ) : IsProbabilityMeasure (P d) := by
  unfold P; infer_instance

theorem haar_eq_volume (s : Set (AddCircle (1 : ℝ))) : P1 s = volume s := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

theorem haar_ball_le (x : AddCircle (1 : ℝ)) (r : ℝ) :
    P1 (Metric.ball x r) ≤ ENNReal.ofReal (2 * r) := by
  calc P1 (Metric.ball x r) ≤ P1 (Metric.closedBall x r) := measure_mono Metric.ball_subset_closedBall
    _ = volume (Metric.closedBall x r) := haar_eq_volume _
    _ = ENNReal.ofReal (min 1 (2 * r)) := AddCircle.volume_closedBall (T := 1) r
    _ ≤ ENNReal.ofReal (2 * r) := ENNReal.ofReal_le_ofReal (min_le_right _ _)

theorem integral_fourier_haar (n : ℤ) :
    ∫ x : AddCircle (1 : ℝ), fourier n x ∂P1 = if n = 0 then (1 : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp only [fourier_zero, integral_const, probReal_univ, one_smul]
  · have h := integral_eq_zero_of_add_right_eq_neg (μ := (P1 : Measure (AddCircle (1 : ℝ))))
      (fourier_add_half_inv_index hn one_pos)
    simpa using h

theorem integrable_continuousMap (d : ℕ) (g : C((Fin d → AddCircle (1 : ℝ)), ℂ)) :
    Integrable g (P d) :=
  g.continuous.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

noncomputable def μP (d : ℕ) : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ θ, g θ ∂(P d)
      map_add' := fun g h => by
        simpa only [ContinuousMap.coe_add, Pi.add_apply] using
          integral_add (integrable_continuousMap d g) (integrable_continuousMap d h)
      map_smul' := fun c g => by
        simp only [ContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
    1 (fun g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      calc ‖∫ θ, g θ ∂(P d)‖ ≤ ‖g‖ * (P d).real Set.univ :=
            norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun θ => g.norm_coe_le_norm θ)
        _ = ‖g‖ := by rw [probReal_univ, mul_one])

theorem μP_apply (d : ℕ) (g : C((Fin d → AddCircle (1 : ℝ)), ℂ)) : μP d g = ∫ θ, g θ ∂(P d) := rfl

end TorusUnifAux
p2m_reactivate "P2MW.S_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero.TorusUnifAux"

open TorusUnifAux in
theorem solution
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) → μ e = ∏ i : Fin d, (if n i = 0 then (1 : ℂ) else 0) := by
  classical
  refine ⟨μP d, ?_, ?_⟩
  ·
    intro τ ε hε
    obtain ⟨i₀⟩ : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    set r : ℝ := ε / 4 with hr
    have hr0 : 0 < r := by positivity
    refine ⟨fun i => Metric.ball (τ i) r, fun i => ⟨Metric.isOpen_ball, Metric.mem_ball_self hr0⟩, ?_⟩
    intro g hg0 hg1
    set B : Set (Fin d → AddCircle (1 : ℝ)) := Set.pi Set.univ fun i => Metric.ball (τ i) r with hB
    have hBm : MeasurableSet B := MeasurableSet.univ_pi fun i => measurableSet_ball
    have hoff : ∀ θ, θ ∉ B → g θ = 0 := by
      intro θ hθ
      apply hg0
      simpa [hB, Set.mem_univ_pi] using hθ
    have hPB : P d B ≤ ENNReal.ofReal (2 * r) := by
      rw [hB, Measure.pi_pi]
      calc ∏ i, P1 (Metric.ball (τ i) r)
          = P1 (Metric.ball (τ i₀) r) * ∏ i ∈ Finset.univ.erase i₀, P1 (Metric.ball (τ i) r) :=
            (Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)).symm
        _ ≤ P1 (Metric.ball (τ i₀) r) * 1 := by
            gcongr
            exact Finset.prod_le_one' fun i _ => prob_le_one
        _ = P1 (Metric.ball (τ i₀) r) := mul_one _
        _ ≤ ENNReal.ofReal (2 * r) := haar_ball_le _ _
    rw [μP_apply, ← setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
    calc ‖∫ θ in B, g θ ∂(P d)‖ ≤ 1 * (P d).real B :=
          norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun θ _ => hg1 θ
      _ ≤ 2 * r := by
          rw [one_mul]
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) hPB
      _ < ε := by rw [hr]; linarith
  ·
    intro n e he
    rw [μP_apply]
    have hfun : (fun θ : Fin d → AddCircle (1 : ℝ) => e θ) = fun θ => ∏ i, fourier (n i) (θ i) :=
      funext he
    rw [hfun, integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun i (x : AddCircle (1 : ℝ)) => fourier (n i) x)]
    exact Finset.prod_congr rfl fun i _ => integral_fourier_haar (n i)

end S_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero
end P2MW
export P2MW.S_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_ite_eq_zero (solution)
