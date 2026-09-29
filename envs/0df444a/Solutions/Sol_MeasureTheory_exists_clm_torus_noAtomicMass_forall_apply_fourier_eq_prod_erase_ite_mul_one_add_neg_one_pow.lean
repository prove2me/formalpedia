-- Prove2me | solution 1 for MeasureTheory.exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/286ddd8d-ff1d-514e-808d-6057c24ebacb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow

set_option autoImplicit false

open MeasureTheory

namespace TorusEdgeAux

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

theorem pi_univ_le (d : ℕ) (U : Fin d → Set (AddCircle (1 : ℝ))) (i₀ : Fin d) :
    P d (Set.pi Set.univ U) ≤ P1 (U i₀) := by
  rw [Measure.pi_pi]
  calc ∏ i, P1 (U i) = P1 (U i₀) * ∏ i ∈ Finset.univ.erase i₀, P1 (U i) :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)).symm
    _ ≤ P1 (U i₀) * 1 := by
        gcongr
        exact Finset.prod_le_one' fun i _ => prob_le_one
    _ = P1 (U i₀) := mul_one _

def setCoord (d : ℕ) (p : Fin d) (a : AddCircle (1 : ℝ)) (θ : Fin d → AddCircle (1 : ℝ)) :
    Fin d → AddCircle (1 : ℝ) := fun i => if i = p then a else θ i

theorem continuous_setCoord (d : ℕ) (p : Fin d) (a : AddCircle (1 : ℝ)) : Continuous (setCoord d p a) := by
  refine continuous_pi fun i => ?_
  by_cases h : i = p
  · simp only [setCoord, h, if_true]; exact continuous_const
  · simp only [setCoord, h, if_false]; exact continuous_apply i

noncomputable def preSet (d : ℕ) (p : Fin d) (a : AddCircle (1 : ℝ)) (g : C((Fin d → AddCircle (1 : ℝ)), ℂ)) :
    C((Fin d → AddCircle (1 : ℝ)), ℂ) := g.comp ⟨setCoord d p a, continuous_setCoord d p a⟩

theorem preSet_apply (d : ℕ) (p : Fin d) (a : AddCircle (1 : ℝ)) (g : C((Fin d → AddCircle (1 : ℝ)), ℂ))
    (θ : Fin d → AddCircle (1 : ℝ)) : preSet d p a g θ = g (setCoord d p a θ) := rfl

theorem integrable_comp_setCoord (d : ℕ) (p : Fin d) (a : AddCircle (1 : ℝ))
    (g : C((Fin d → AddCircle (1 : ℝ)), ℂ)) : Integrable (fun θ => g (setCoord d p a θ)) (P d) :=
  integrable_continuousMap d (preSet d p a g)

noncomputable def halfPt (q : ℕ) : AddCircle (1 : ℝ) := (((q : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ))

noncomputable def μE (d : ℕ) (p : Fin d) (q : ℕ) : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ θ, (g (setCoord d p 0 θ) + g (setCoord d p (halfPt q) θ)) ∂(P d)
      map_add' := fun g h => by
        have hg' : Integrable (fun θ => g (setCoord d p 0 θ) + g (setCoord d p (halfPt q) θ)) (P d) :=
          (integrable_comp_setCoord d p 0 g).add (integrable_comp_setCoord d p (halfPt q) g)
        have hh' : Integrable (fun θ => h (setCoord d p 0 θ) + h (setCoord d p (halfPt q) θ)) (P d) :=
          (integrable_comp_setCoord d p 0 h).add (integrable_comp_setCoord d p (halfPt q) h)
        simp only [ContinuousMap.coe_add, Pi.add_apply]
        rw [← integral_add hg' hh']
        congr 1; funext θ; ring
      map_smul' := fun c g => by
        simp only [ContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; funext θ; ring }
    2 (fun g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ θ, (g (setCoord d p 0 θ) + g (setCoord d p (halfPt q) θ)) ∂(P d)‖
            ≤ (‖g‖ + ‖g‖) * (P d).real Set.univ :=
            norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun θ =>
              (norm_add_le _ _).trans (add_le_add (g.norm_coe_le_norm _) (g.norm_coe_le_norm _)))
        _ = 2 * ‖g‖ := by rw [probReal_univ, mul_one, two_mul])

theorem μE_apply (d : ℕ) (p : Fin d) (q : ℕ) (g : C((Fin d → AddCircle (1 : ℝ)), ℂ)) :
    μE d p q g = ∫ θ, (g (setCoord d p 0 θ) + g (setCoord d p (halfPt q) θ)) ∂(P d) := rfl

theorem neg_one_zpow_eq_pow_natAbs (k : ℤ) : (-1 : ℂ) ^ k = (-1 : ℂ) ^ k.natAbs := by
  rcases Int.natAbs_eq k with h | h
  · conv_lhs => rw [h]
    exact zpow_natCast _ _
  · conv_lhs => rw [h]
    rw [zpow_neg, zpow_natCast]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow])

theorem fourier_halfPt (n : ℤ) (q : ℕ) : fourier n (halfPt q) = (-1 : ℂ) ^ (q * n.natAbs) := by
  rw [halfPt, fourier_coe_apply]
  have : (2 * Real.pi * Complex.I * n * (((q : ℝ) / 2 : ℝ) : ℂ) / (1 : ℝ) : ℂ) =
      ((n * q : ℤ) : ℂ) * (Real.pi * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I, neg_one_zpow_eq_pow_natAbs, Int.natAbs_mul,
    Int.natAbs_natCast, mul_comm]

end TorusEdgeAux
p2m_reactivate "P2MW.S_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow.TorusEdgeAux"

open TorusEdgeAux in
theorem solution
    (d : ℕ) (hd : 2 ≤ d) (p : Fin d) (q : ℕ) :
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) →
          μ e = (∏ i ∈ Finset.univ.erase p, (if n i = 0 then (1 : ℂ) else 0)) *
            (1 + (-1 : ℂ) ^ (q * (n p).natAbs)) := by
  classical
  refine ⟨μE d p q, ?_, ?_⟩
  ·
    intro τ ε hε
    let i₀ : Fin d := ⟨if p.val = 0 then 1 else 0, by split_ifs <;> omega⟩
    have hi₀ : i₀ ≠ p := by
      intro h
      have hv : i₀.val = p.val := congrArg Fin.val h
      simp only [i₀] at hv
      split_ifs at hv <;> omega
    set r : ℝ := ε / 8 with hr
    have hr0 : 0 < r := by positivity
    refine ⟨fun i => Metric.ball (τ i) r, fun i => ⟨Metric.isOpen_ball, Metric.mem_ball_self hr0⟩, ?_⟩
    intro g hg0 hg1

    set U' : Fin d → Set (AddCircle (1 : ℝ)) := fun i => if i = p then Set.univ else Metric.ball (τ i) r with hU'
    set B : Set (Fin d → AddCircle (1 : ℝ)) := Set.pi Set.univ U' with hB
    have hBm : MeasurableSet B :=
      MeasurableSet.univ_pi fun i => by
        by_cases h : i = p
        · simp only [hU', h, if_true]; exact MeasurableSet.univ
        · simp only [hU', h, if_false]; exact measurableSet_ball
    have hoff : ∀ (a : AddCircle (1 : ℝ)) (θ : Fin d → AddCircle (1 : ℝ)), θ ∉ B → g (setCoord d p a θ) = 0 := by
      intro a θ hθ
      apply hg0
      simp only [hB, Set.mem_univ_pi, not_forall] at hθ
      obtain ⟨i, hi⟩ := hθ
      refine ⟨i, ?_⟩
      by_cases h : i = p
      · exact absurd (by simp only [hU', h, if_true]; exact Set.mem_univ _) hi
      · simp only [hU', h, if_false] at hi
        simpa only [setCoord, h, if_false] using hi
    have hPB : P d B ≤ ENNReal.ofReal (2 * r) := by
      rw [hB]
      refine (pi_univ_le d U' i₀).trans ?_
      simp only [hU', hi₀, if_false]
      exact haar_ball_le _ _
    have hbound : ∀ a : AddCircle (1 : ℝ), ‖∫ θ, g (setCoord d p a θ) ∂(P d)‖ ≤ 2 * r := by
      intro a
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hoff a)]
      calc ‖∫ θ in B, g (setCoord d p a θ) ∂(P d)‖ ≤ 1 * (P d).real B :=
            norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun θ _ => hg1 _
        _ ≤ 2 * r := by
            rw [one_mul]
            exact ENNReal.toReal_le_of_le_ofReal (by positivity) hPB
    rw [μE_apply, integral_add (integrable_comp_setCoord d p 0 g) (integrable_comp_setCoord d p (halfPt q) g)]
    calc ‖(∫ θ, g (setCoord d p 0 θ) ∂(P d)) + ∫ θ, g (setCoord d p (halfPt q) θ) ∂(P d)‖
        ≤ 2 * r + 2 * r := (norm_add_le _ _).trans (add_le_add (hbound _) (hbound _))
      _ < ε := by rw [hr]; linarith
  ·
    intro n e he
    have key : ∀ a : AddCircle (1 : ℝ), ∫ θ, e (setCoord d p a θ) ∂(P d) =
        fourier (n p) a * ∏ i ∈ Finset.univ.erase p, (if n i = 0 then (1 : ℂ) else 0) := by
      intro a
      have hfun : (fun θ : Fin d → AddCircle (1 : ℝ) => e (setCoord d p a θ)) =
          fun θ => ∏ i, (fun (i : Fin d) (x : AddCircle (1 : ℝ)) => fourier (n i) (if i = p then a else x)) i (θ i) := by
        funext θ
        rw [he]
        rfl
      rw [hfun, integral_fintype_prod_eq_prod (𝕜 := ℂ)
        (fun (i : Fin d) (x : AddCircle (1 : ℝ)) => fourier (n i) (if i = p then a else x)),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
      simp only [if_true, integral_const, probReal_univ, one_smul]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Finset.mem_erase] at hi
      simp only [hi.1, if_false]
      exact integral_fourier_haar (n i)
    rw [μE_apply, integral_add (integrable_comp_setCoord d p 0 e) (integrable_comp_setCoord d p (halfPt q) e),
      key, key, fourier_eval_zero, fourier_halfPt]
    ring

end S_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow
end P2MW
export P2MW.S_MeasureTheory_exists_clm_torus_noAtomicMass_forall_apply_fourier_eq_prod_erase_ite_mul_one_add_neg_one_pow (solution)
