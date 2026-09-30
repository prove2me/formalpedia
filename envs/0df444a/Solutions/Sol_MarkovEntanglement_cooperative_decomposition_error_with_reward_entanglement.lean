-- Prove2me | solution 1 for MarkovEntanglement.cooperative_decomposition_error_with_reward_entanglement
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:50:17.708022+00:00
-- url     : https://prove2.me/submissions/b0216ae2-75b3-4f99-964f-37da7988ba2f

import Definitions.Def_markov_entanglement_multi

set_option autoImplicit false
set_option maxHeartbeats 2000000

/- The three private helpers below are copied verbatim from tianyipeng's accepted
   submission2fb66d88-a605-4460-853e-5c106f1d4c80 for multi_agent_decomposition_error.
   The main proof adds the actual reward residual and uses marginal identities
   directly, so no platform theorem imports are required. -/

open scoped BigOperators
open MarkovEntanglement

/-- A Bellman solution is bounded by the reward bound over `1 - γ`. -/
private theorem bellman_sup_bound {ι : Type*} [Fintype ι] [Nonempty ι] (A : Matrix ι ι ℝ)
    (hA : IsTransitionMatrix A) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (ρ : ι → ℝ) (c : ℝ) (hρ : ∀ s, |ρ s| ≤ c) (V : ι → ℝ)
    (hV : IsBellmanQ A ρ γ V) : ∀ s, |V s| ≤ c / (1 - γ) := by
  classical
  obtain ⟨s0, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun s => |V s|)
      ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have hstep : |V s0| ≤ c + γ * |V s0| := by
    calc |V s0| = |ρ s0 + γ * ∑ t, A s0 t * V t| := by rw [← hV s0]
      _ ≤ |ρ s0| + |γ * ∑ t, A s0 t * V t| := abs_add_le _ _
      _ = |ρ s0| + γ * |∑ t, A s0 t * V t| := by rw [abs_mul, abs_of_nonneg hγ]
      _ ≤ c + γ * ∑ t, |A s0 t * V t| := by
          have h1 : |∑ t, A s0 t * V t| ≤ ∑ t, |A s0 t * V t| :=
            Finset.abs_sum_le_sum_abs _ _
          have := mul_le_mul_of_nonneg_left h1 hγ
          linarith [hρ s0]
      _ = c + γ * ∑ t, A s0 t * |V t| := by
          congr 2
          exact Finset.sum_congr rfl (fun t _ => by rw [abs_mul, abs_of_nonneg (hA.1 s0 t)])
      _ ≤ c + γ * ∑ t, A s0 t * |V s0| := by
          have : ∑ t, A s0 t * |V t| ≤ ∑ t, A s0 t * |V s0| :=
            Finset.sum_le_sum (fun t _ =>
              mul_le_mul_of_nonneg_left (hmax t (Finset.mem_univ t)) (hA.1 s0 t))
          linarith [mul_le_mul_of_nonneg_left this hγ]
      _ = c + γ * |V s0| := by rw [← Finset.sum_mul, hA.2 s0, one_mul]
  have hb : |V s0| ≤ c / (1 - γ) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  exact fun s => le_trans (hmax s (Finset.mem_univ s)) hb

/-- A stationary weight makes the transition matrix a contraction in `μ`-norm. -/
private theorem muNorm_apply_le {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (hA : IsTransitionMatrix A) (μ : ι → ℝ) (hμ0 : ∀ i, 0 ≤ μ i)
    (hstat : IsStationary A μ) (x : ι → ℝ) :
    muNorm μ (fun p => ∑ q, A p q * x q) ≤ muNorm μ x := by
  classical
  calc muNorm μ (fun p => ∑ q, A p q * x q)
      = ∑ p, μ p * |∑ q, A p q * x q| := rfl
    _ ≤ ∑ p, μ p * ∑ q, A p q * |x q| := by
        refine Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left ?_ (hμ0 p))
        calc |∑ q, A p q * x q| ≤ ∑ q, |A p q * x q| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ q, A p q * |x q| :=
              Finset.sum_congr rfl (fun q _ => by rw [abs_mul, abs_of_nonneg (hA.1 p q)])
    _ = ∑ p, ∑ q, μ p * (A p q * |x q|) :=
        Finset.sum_congr rfl (fun p _ => Finset.mul_sum _ _ _)
    _ = ∑ q, ∑ p, μ p * (A p q * |x q|) := Finset.sum_comm
    _ = ∑ q, (∑ p, μ p * A p q) * |x q| := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = muNorm μ x := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [hstat q]

/-- Pairing a joint transition with a function of one agent's coordinate. -/
private theorem sum_mul_coord {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)]
    [∀ i, DecidableEq (S i)] (i : Fin N) (P : Matrix (Joint S) (Joint S) ℝ)
    (p : Joint S) (g : S i → ℝ) :
    ∑ q : Joint S, P p q * g (q i) = ∑ t : S i, marginalN i P p t * g t := by
  classical
  simp only [marginalN, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Finset.sum_eq_single (q i)]
  · simp
  · intro t _ ht
    exact if_neg (fun h => ht h.symm)
  · intro h; exact absurd (Finset.mem_univ _) h


theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : Joint S → ℝ) (rl : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (Pl : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (hr : ∀ i s, |rl i s| ≤ rmax i)
    (hrl : muNorm μ (fun p => r p - ∑ i, rl i (p i)) = rewardEntanglement μ r)
    (hQ : IsBellmanQ P r γ Q)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hopt : ∀ i, muAgentTVDistN i μ P (Pl i) = entanglementN i μ P)
    (hQi : ∀ i, IsBellmanQ (Pl i) (rl i) γ (Qi i)) :
    muNorm μ (fun p => Q p - ∑ i, Qi i (p i))
      ≤ rewardEntanglement μ r / (1 - γ)
        + 4 * γ * (∑ i, entanglementN i μ P * rmax i) / (1 - γ) ^ 2 := by
  classical
  have hμ0 : ∀ p, 0 ≤ μ p := fun p => (hμ.1 p).le
  have hne : Nonempty (Joint S) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    have h := hμ.2
    simp at h
  haveI : ∀ i, Nonempty (S i) := fun i => ⟨(Classical.arbitrary (Joint S)) i⟩
  have hrmax0 : ∀ i, 0 ≤ rmax i :=
    fun i => le_trans (abs_nonneg _) (hr i (Classical.arbitrary (S i)))
  have hg1 : (0 : ℝ) < 1 - γ := by linarith
  have hQib : ∀ i s, |Qi i s| ≤ rmax i / (1 - γ) :=
    fun i => bellman_sup_bound (Pl i) (hPl i) γ hγ hγ1
      (rl i) (rmax i) (hr i) (Qi i) (hQi i)
  have hEnt0 : ∀ i, 0 ≤ entanglementN i μ P := by
    intro i
    rw [← hopt i, muAgentTVDistN]
    refine Finset.sum_nonneg (fun p _ => mul_nonneg (hμ0 p) ?_)
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun t _ => abs_nonneg _))
  set X : ℝ := ∑ i, entanglementN i μ P * rmax i with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun i _ => mul_nonneg (hEnt0 i) (hrmax0 i))
  let W : Joint S → ℝ := fun p => ∑ i, Qi i (p i)
  let D : Joint S → ℝ := fun p => Q p - W p
  let R : Joint S → ℝ := fun p => r p - ∑ i, rl i (p i)
  let E : Joint S → ℝ := fun p =>
    ∑ i, ∑ t : S i, (marginalN i P p t - Pl i (p i) t) * Qi i t
  have hWbell (p : Joint S) :
      W p = (∑ i, rl i (p i)) + γ * ∑ i, ∑ t : S i, Pl i (p i) t * Qi i t := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hQi i (p i))
  have hPW (p : Joint S) :
      ∑ q, P p q * W q = ∑ i, ∑ t : S i, marginalN i P p t * Qi i t := by
    calc ∑ q, P p q * W q
        = ∑ q, ∑ i, P p q * Qi i (q i) :=
          Finset.sum_congr rfl (fun q _ => Finset.mul_sum _ _ _)
      _ = ∑ i, ∑ q, P p q * Qi i (q i) := Finset.sum_comm
      _ = ∑ i, ∑ t : S i, marginalN i P p t * Qi i t :=
          Finset.sum_congr rfl (fun i _ => sum_mul_coord i P p (Qi i))
  have hEeq (p : Joint S) :
      E p = (∑ q, P p q * W q) - ∑ i, ∑ t : S i, Pl i (p i) t * Qi i t := by
    rw [hPW, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  have hDeq (p : Joint S) : D p = R p + γ * (∑ q, P p q * D q) + γ * E p := by
    have hPD : ∑ q, P p q * D q = (∑ q, P p q * Q q) - ∑ q, P p q * W q := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun q _ => by dsimp [D]; ring)
    rw [hPD, hEeq]
    dsimp [D, R]
    linarith [hQ p, hWbell p]
  have hmuAdd : ∀ x y : Joint S → ℝ,
      muNorm μ (fun p => x p + y p) ≤ muNorm μ x + muNorm μ y := by
    intro x y
    rw [muNorm, muNorm, muNorm, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun p _ => ?_)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (hμ0 p)
  have hmuSmul : ∀ (c : ℝ) (x : Joint S → ℝ), 0 ≤ c →
      muNorm μ (fun p => c * x p) = c * muNorm μ x := by
    intro c x hc
    rw [muNorm, muNorm, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by rw [abs_mul, abs_of_nonneg hc]; ring)
  have hmis : muNorm μ E ≤ (2 / (1 - γ)) * X := by
    calc muNorm μ E
        = ∑ p : Joint S, μ p *
            |∑ i, ∑ t : S i, (marginalN i P p t - Pl i (p i) t) * Qi i t| := rfl
      _ ≤ ∑ p : Joint S, μ p *
            ∑ i, (rmax i / (1 - γ)) * ∑ t : S i, |marginalN i P p t - Pl i (p i) t| := by
          refine Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left ?_ (hμ0 p))
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i _ => ?_))
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum (fun t _ => ?_)
          rw [abs_mul, mul_comm (rmax i / (1 - γ))]
          exact mul_le_mul_of_nonneg_left (hQib i t) (abs_nonneg _)
      _ = ∑ i, ∑ p : Joint S,
            μ p * ((rmax i / (1 - γ)) * ∑ t : S i, |marginalN i P p t - Pl i (p i) t|) := by
          rw [← Finset.sum_comm]
          exact Finset.sum_congr rfl (fun p _ => Finset.mul_sum _ _ _)
      _ = ∑ i, (rmax i / (1 - γ)) * (2 * muAgentTVDistN i μ P (Pl i)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [muAgentTVDistN, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by ring)
      _ = (2 / (1 - γ)) * X := by
          rw [hX, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by rw [← hopt i]; ring)
  have hcontr : muNorm μ (fun p => ∑ q, P p q * D q) ≤ muNorm μ D :=
    muNorm_apply_le P hP μ hμ0 hstat D
  have hmain : muNorm μ D ≤ rewardEntanglement μ r
      + γ * muNorm μ D + γ * ((2 / (1 - γ)) * X) := by
    calc muNorm μ D
        = muNorm μ (fun p => R p + γ * (∑ q, P p q * D q) + γ * E p) := by
          congr 1
          funext p
          exact hDeq p
      _ ≤ muNorm μ (fun p => R p + γ * (∑ q, P p q * D q))
            + muNorm μ (fun p => γ * E p) := hmuAdd _ _
      _ ≤ (muNorm μ R + muNorm μ (fun p => γ * (∑ q, P p q * D q)))
            + muNorm μ (fun p => γ * E p) := add_le_add (hmuAdd _ _) le_rfl
      _ = rewardEntanglement μ r + γ * muNorm μ (fun p => ∑ q, P p q * D q)
            + γ * muNorm μ E := by
          rw [hmuSmul γ _ hγ, hmuSmul γ _ hγ]
          change muNorm μ (fun p => r p - ∑ i, rl i (p i)) + _ + _ = _
          rw [hrl]
      _ ≤ rewardEntanglement μ r + γ * muNorm μ D + γ * ((2 / (1 - γ)) * X) := by
          have h1 := mul_le_mul_of_nonneg_left hcontr hγ
          have h2 := mul_le_mul_of_nonneg_left hmis hγ
          linarith
  have hne1 : (1 : ℝ) - γ ≠ 0 := ne_of_gt hg1
  have hfinal : muNorm μ D ≤ rewardEntanglement μ r / (1 - γ)
      + 2 * γ * X / (1 - γ) ^ 2 := by
    have hkey : (1 - γ) * muNorm μ D ≤ rewardEntanglement μ r
        + γ * ((2 / (1 - γ)) * X) := by linarith
    have hstep := mul_le_mul_of_nonneg_right hkey hg1.le
    have hexp : (rewardEntanglement μ r + γ * ((2 / (1 - γ)) * X)) * (1 - γ)
        = rewardEntanglement μ r * (1 - γ) + 2 * γ * X := by field_simp
    rw [hexp] at hstep
    have hdiv : muNorm μ D ≤
        (rewardEntanglement μ r * (1 - γ) + 2 * γ * X) / (1 - γ) ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 - γ) ^ 2)]
      nlinarith [hstep]
    convert hdiv using 1 <;> field_simp <;> ring
  have hle : 2 * γ * X / (1 - γ) ^ 2 ≤ 4 * γ * X / (1 - γ) ^ 2 := by
    exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _)
  exact hfinal.trans (add_le_add le_rfl hle)

#print axioms solution
