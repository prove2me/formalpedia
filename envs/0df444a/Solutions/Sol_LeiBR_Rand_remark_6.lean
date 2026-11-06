-- Prove2me | solution 1 for LeiBR.Rand.remark_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:47:22.938879+00:00
-- url     : https://prove2.me/submissions/3ec540a7-6546-409d-861d-4edf5436096e

import Theorems.Thm_LeiBR_Rand_lemma_5
open MeasureTheory ProbabilityTheory
open LeiBR.Rand

theorem solution {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (hA2 : Assumption2 G mu) (xstar : LeiBR.Sync.Profile n) (hNE : G.IsNE xstar) (hN : 0 < N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (p : Fin N → ℝ)
    (χ : Fin N → ℕ → Ω → ℕ) (w : ∀ i, ℕ → Ω → LeiBR.Sync.Strat n i) (x0 : LeiBR.Sync.Profile n)
    (x : ℕ → Ω → LeiBR.Sync.Profile n) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (C : ℝ) (hC : ∀ i, ‖x0 i - xstar i‖ ≤ C)
    (hrun : IsAlg2Run G xhat P F p χ w (fun i k ω => η ^ (beta χ i k ω + 1)) x0 x)
    (q : ℝ) (hq : ctil p (contrFactor G mu) η < q) (hq1 : q < 1) (k : ℕ) :
    ∫ ω, blockNorm (x k ω - xstar) ∂P ≤ Real.sqrt (pmax p) * ∫ ω, wnorm p (x k ω - xstar) ∂P ∧
    Real.sqrt (pmax p) * ∫ ω, wnorm p (x k ω - xstar) ∂P ≤
      Real.sqrt (N * pmax p) * (Ctil p C + Dtil p (contrFactor G mu) η q) * q ^ k := by
  have hp0 := hrun.p_pos
  have i0 : Fin N := ⟨0, hN⟩
  have hpmax : ∀ i, p i ≤ pmax p := fun i => le_ciSup (Finite.bddAbove_range p) i
  have hpmax0 : 0 < pmax p := (hp0 i0).trans_le (hpmax i0)
  -- feasibility and measurability of the iterates
  have hfeas : ∀ k ω, G.Feasible (x k ω) := by
    intro k
    induction k with
    | zero => intro ω; rw [hrun.init ω]; exact hrun.x0_feas
    | succ k ih =>
      intro ω i
      rw [hrun.step k ω i]
      split_ifs
      · exact hrun.w_mem i k ω
      · exact ih ω i
  have hxm : ∀ k, Measurable (x k) := by
    intro k
    induction k with
    | zero =>
      have : x 0 = fun _ => x0 := funext hrun.init
      rw [this]; exact measurable_const
    | succ k ih =>
      have : x (k + 1) = fun ω i => if χ i k ω = 1 then w i k ω else x k ω i := by
        funext ω i; exact hrun.step k ω i
      rw [this]
      refine measurable_pi_lambda _ fun i => ?_
      have hs : MeasurableSet {ω | χ i k ω = 1} :=
        ((hrun.coin_meas i k).mono (F.le _) le_rfl) (measurableSet_singleton 1)
      exact Measurable.ite hs (((hrun.w_meas i k).mono (F.le _)).measurable)
        ((measurable_pi_apply i).comp ih)
  have hxs : G.Feasible xstar := hNE.1
  have hbd : ∀ i (a b : LeiBR.Sync.Strat n i), a ∈ G.X i → b ∈ G.X i →
      ‖a - b‖ ^ 2 ≤ Metric.diam (G.X i) ^ 2 := by
    intro i a b ha hb
    have := Metric.dist_le_diam_of_mem (hA1.compact i).isBounded ha hb
    rw [dist_eq_norm] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hwm : Measurable fun ω => wnorm p (x k ω - xstar) := by
    unfold wnorm
    refine Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun i _ => ?_)
    exact ((((measurable_pi_apply i).comp (hxm k)).sub_const _).norm.pow_const 2).div_const _
  have hwi : Integrable (fun ω => wnorm p (x k ω - xstar)) P := by
    refine Integrable.of_bound hwm.aestronglyMeasurable
      (Real.sqrt (∑ i, Metric.diam (G.X i) ^ 2 / p i)) (ae_of_all _ fun ω => ?_)
    unfold wnorm
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    exact div_le_div_of_nonneg_right (hbd i _ _ (hfeas k ω i) (hxs i)) (hp0 i).le
  have hpt : ∀ v : LeiBR.Sync.Profile n, blockNorm v ≤ Real.sqrt (pmax p) * wnorm p v := by
    intro v
    unfold blockNorm wnorm
    rw [← Real.sqrt_mul hpmax0.le]
    refine Real.sqrt_le_sqrt ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_div_assoc', le_div_iff₀ (hp0 i)]
    rw [mul_comm (pmax p)]
    exact mul_le_mul_of_nonneg_left (hpmax i) (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · rw [← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun ω => Real.sqrt_nonneg _)
      (hwi.const_mul _) (ae_of_all _ fun ω => hpt _)
  · have h5 := lemma_5 G μξ ψ gψ M hA1 mu hmu xhat hxhat hA2 xstar hNE hN P F p χ w x0 x η hη0 hη1
      C hC hrun q hq hq1 k
    rw [Real.sqrt_mul (Nat.cast_nonneg N), mul_comm (Real.sqrt (N : ℝ)) (Real.sqrt (pmax p)),
      mul_assoc (Real.sqrt (pmax p)), mul_assoc (Real.sqrt (pmax p))]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    simpa [mul_assoc] using h5
