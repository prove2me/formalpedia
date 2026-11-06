-- Prove2me | solution 1 for LeiBR.Rand.eqB1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:50:18.879191+00:00
-- url     : https://prove2.me/submissions/ad5eba92-52a6-4dc3-8826-101d0fbb9e12

import Theorems.Thm_LeiBR_Rand_eqA3
open MeasureTheory ProbabilityTheory
open LeiBR.Rand

theorem solution {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (hA2 : Assumption2 G mu) (xstar : LeiBR.Sync.Profile n) (hNE : G.IsNE xstar)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (k : ℕ) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (xk : Ω → LeiBR.Sync.Profile n) (hxk_meas : StronglyMeasurable[F k] xk)
    (hxk_feas : ∀ ω, G.Feasible (xk ω))
    (χ : Fin N → Ω → ℕ) (hχ1 : ∀ i ω, χ i ω ≤ 1) (hχ_meas : ∀ i, Measurable (χ i))
    (hχ_prob : ∀ i, P {ω | χ i ω = 1} = ENNReal.ofReal (p i))
    (hχ_indep : ∀ i, Indep (MeasurableSpace.comap (χ i) inferInstance) (F k) P) :
    P[fun ω => wnorm p ((fun i => xk ω i + (χ i ω : ℝ) • (xhat (xk ω) i - xk ω i)) - xstar) ^ 2 | F k]
      ≤ᵐ[P] fun ω => (1 - pmin p * (1 - contrFactor G mu ^ 2)) * wnorm p (xk ω - xstar) ^ 2 := by
  have hA3 := eqA3 G μξ ψ gψ M hA1 mu hmu xhat hxhat hA2 xstar hNE P F k p hp hp1 xk hxk_meas
    hxk_feas χ hχ1 hχ_meas hχ_prob hχ_indep
  refine hA3.trans (ae_of_all _ fun ω => ?_)
  have ha0 : 0 ≤ contrFactor G mu := norm_nonneg _
  have ha1 : 0 ≤ 1 - contrFactor G mu ^ 2 := by
    have : contrFactor G mu < 1 := hA2
    nlinarith
  have hpmin : ∀ i, pmin p ≤ p i := fun i => ciInf_le (Finite.bddBelow_range p) i
  set v := xk ω - xstar
  have hw : wnorm p v ^ 2 = ∑ i, ‖v i‖ ^ 2 / p i := by
    unfold wnorm
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hp i).le)
  have hb : blockNorm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
    unfold blockNorm
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hcmp : pmin p * wnorm p v ^ 2 ≤ blockNorm v ^ 2 := by
    rw [hw, hb, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_div_assoc', div_le_iff₀ (hp i)]
    rw [mul_comm (‖v i‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hpmin i) (sq_nonneg _)
  have := mul_le_mul_of_nonneg_left hcmp ha1
  show wnorm p v ^ 2 - (1 - contrFactor G mu ^ 2) * blockNorm v ^ 2 ≤
    (1 - pmin p * (1 - contrFactor G mu ^ 2)) * wnorm p v ^ 2
  nlinarith
