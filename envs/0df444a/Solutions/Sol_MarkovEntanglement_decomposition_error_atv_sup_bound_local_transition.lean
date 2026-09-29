-- Prove2me | solution 1 for MarkovEntanglement.decomposition_error_atv_sup_bound_local_transition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-09T01:33:05.23137+00:00
-- url     : https://prove2.me/submissions/be259896-1e3c-4ee2-87a3-96a504bd917a

import Definitions.Def_markov_entanglement_multi_atv

open scoped BigOperators

namespace MarkovEntanglement

variable {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]


/-! ## μ-norm toolkit -/

lemma muNorm_nonneg {ι : Type*} [Fintype ι] (μ x : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    0 ≤ muNorm μ x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (abs_nonneg _)

lemma muNorm_le_sum {ι : Type*} [Fintype ι] (μ x c : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (h : ∀ i, |x i| ≤ c i) : muNorm μ x ≤ ∑ i, μ i * c i :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hμ i)

lemma muNorm_add_le {ι : Type*} [Fintype ι] (μ a b : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    muNorm μ (fun i => a i + b i) ≤ muNorm μ a + muNorm μ b := by
  unfold muNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (hμ i)

lemma muNorm_const_smul {ι : Type*} [Fintype ι] (μ a : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    muNorm μ (fun i => c * a i) = c * muNorm μ a := by
  unfold muNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_mul, abs_of_nonneg hc]; ring

/-- A transition matrix is a contraction for the `μ`-norm of its stationary distribution:
`‖P x‖_μ ≤ ‖x‖_μ`.  This is the inequality `μᵀ|Px| ≤ μᵀP|x| = μᵀ|x|` from the proof of
Theorem 5, and the only place stationarity of `μ` is used. -/
lemma muNorm_mulVec_le {ι : Type*} [Fintype ι] (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (P : Matrix ι ι ℝ) (hP : IsTransitionMatrix P) (hstat : IsStationary P μ) (x : ι → ℝ) :
    muNorm μ (fun i => ∑ j, P i j * x j) ≤ muNorm μ x := by
  unfold muNorm
  have step1 : ∀ i : ι, μ i * |∑ j, P i j * x j| ≤ μ i * ∑ j, P i j * |x j| := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (hμ i)
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_mul, abs_of_nonneg (hP.1 i j)]
  refine (Finset.sum_le_sum fun i _ => step1 i).trans_eq ?_
  have swap : ∑ i, μ i * ∑ j, P i j * |x j| = ∑ j, (∑ i, μ i * P i j) * |x j| := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [swap]
  exact Finset.sum_congr rfl fun j _ => by rw [hstat j]

/-! ## Sup bound on a value function -/

/-- The value function of a discounted chain with rewards bounded by `B` is bounded by
`B / (1 - γ)`. -/
lemma bellman_abs_le {ι : Type*} [Fintype ι] [Nonempty ι] (P : Matrix ι ι ℝ)
    (hP : IsTransitionMatrix P) (r Q : ι → ℝ) (γ B : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ i, |r i| ≤ B) (hQ : IsBellmanQ P r γ Q) (i : ι) :
    |Q i| ≤ B / (1 - γ) := by
  obtain ⟨m, hm⟩ := Finite.exists_max (fun i => |Q i|)
  have hcontr : |∑ j, P m j * Q j| ≤ |Q m| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ j ∈ Finset.univ, |P m j * Q j| ≤ P m j * |Q m| := by
      intro j _
      rw [abs_mul, abs_of_nonneg (hP.1 m j)]
      exact mul_le_mul_of_nonneg_left (hm j) (hP.1 m j)
    refine (Finset.sum_le_sum this).trans_eq ?_
    rw [← Finset.sum_mul, hP.2 m, one_mul]
  have key : |Q m| ≤ B + γ * |Q m| := by
    calc |Q m| = |r m + γ * ∑ j, P m j * Q j| := by rw [hQ m]
      _ ≤ |r m| + |γ * ∑ j, P m j * Q j| := abs_add_le _ _
      _ ≤ B + γ * |Q m| := by
          have : |γ * ∑ j, P m j * Q j| = γ * |∑ j, P m j * Q j| := by
            rw [abs_mul, abs_of_nonneg hγ]
          rw [this]
          exact add_le_add (hr m) (mul_le_mul_of_nonneg_left hcontr hγ)
  have hpos : (0:ℝ) < 1 - γ := by linarith
  have : (1 - γ) * |Q m| ≤ B := by nlinarith
  calc |Q i| ≤ |Q m| := hm i
    _ ≤ B / (1 - γ) := by rw [le_div_iff₀ hpos]; nlinarith

/-! ## Coordinate regrouping -/

/-- Applying a joint transition to a function of a single agent's coordinate is the same as
applying that agent's marginal. -/
lemma sum_apply_coord (P : Matrix (Joint S) (Joint S) ℝ) (i : Fin N) (f : S i → ℝ)
    (p : Joint S) :
    ∑ q : Joint S, P p q * f (q i) = ∑ t : S i, marginalN i P p t * f t := by
  simp only [marginalN, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp

/-- The tensor product of local transitions acts on a function of agent `i`'s coordinate
through agent `i`'s local transition alone (Lemma 6 with a single term). -/
lemma tensor_apply_coord (Pl : ∀ i, Matrix (S i) (S i) ℝ)
    (hPl : ∀ i, IsTransitionMatrix (Pl i)) (i : Fin N) (f : S i → ℝ) (p : Joint S) :
    ∑ q : Joint S, tensorProdN Pl p q * f (q i) = ∑ t : S i, Pl i (p i) t * f t := by
  classical
  set F : ∀ j, S j → ℝ := fun j u => Pl j (p j) u with hF
  set g : ∀ j, S j → ℝ := Function.update F i (fun u => F i u * f u) with hg
  have hgi : g i = fun u => F i u * f u := by rw [hg, Function.update_self]
  have hgj : ∀ j, j ≠ i → g j = F j := fun j hj => by rw [hg, Function.update_of_ne hj]
  have hprod : ∀ q : Joint S, ∏ j, g j (q j) = (∏ j, F j (q j)) * f (q i) := by
    intro q
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin N)) (fun j => g j (q j))
          (Finset.mem_univ i),
        ← Finset.mul_prod_erase (Finset.univ : Finset (Fin N)) (fun j => F j (q j))
          (Finset.mem_univ i)]
    have he : ∏ j ∈ Finset.univ.erase i, g j (q j) = ∏ j ∈ Finset.univ.erase i, F j (q j) :=
      Finset.prod_congr rfl fun j hj => by rw [hgj j (Finset.ne_of_mem_erase hj)]
    rw [he, hgi]
    ring
  have hconv : ∀ q : Joint S, tensorProdN Pl p q * f (q i) = ∏ j, g j (q j) := by
    intro q
    rw [hprod q, hF]
    rfl
  calc ∑ q : Joint S, tensorProdN Pl p q * f (q i)
      = ∑ q : Joint S, ∏ j, g j (q j) := Finset.sum_congr rfl fun q _ => hconv q
    _ = ∏ j, ∑ u : S j, g j u := (Fintype.prod_sum fun j u => g j u).symm
    _ = ∑ t : S i, Pl i (p i) t * f t := by
        rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin N))
              (fun j => ∑ u : S j, g j u) (Finset.mem_univ i)]
        have hone : ∏ j ∈ Finset.univ.erase i, ∑ u : S j, g j u = 1 := by
          refine Finset.prod_eq_one fun j hj => ?_
          rw [hgj j (Finset.ne_of_mem_erase hj)]
          exact (hPl j).2 (p j)
        rw [hone, mul_one, hgi, hF]

/-! ## The perturbation core -/

/-- **Perturbation bound in `μ`-norm.**  If `Q` solves the Bellman equation for `(P, r)` and
`W` solves it for `(T, r')`, then the gap is controlled by the reward gap plus the
one-step transition gap applied to `W`.  This is the engine behind Theorems 5, 6 and 8 and
Proposition 4; stationarity of `μ` enters only through `muNorm_mulVec_le`. -/
lemma muNorm_bellman_diff_le {ι : Type*} [Fintype ι] (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (P T : Matrix ι ι ℝ) (hP : IsTransitionMatrix P) (hstat : IsStationary P μ)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (r r' Q W : ι → ℝ) (hQ : IsBellmanQ P r γ Q) (hW : IsBellmanQ T r' γ W) :
    (1 - γ) * muNorm μ (fun i => Q i - W i)
      ≤ muNorm μ (fun i => r i - r' i)
        + γ * muNorm μ (fun i => ∑ j, (P i j - T i j) * W j) := by
  have hd : ∀ i, Q i - W i = (r i - r' i) + (γ * (∑ j, P i j * (Q j - W j))
      + γ * (∑ j, (P i j - T i j) * W j)) := by
    intro i
    have e : (∑ j, P i j * (Q j - W j)) + ∑ j, (P i j - T i j) * W j
        = (∑ j, P i j * Q j) - ∑ j, T i j * W j := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hQ i, hW i, ← mul_add, e]
    ring
  have hle : muNorm μ (fun i => Q i - W i)
      ≤ muNorm μ (fun i => r i - r' i)
        + (γ * muNorm μ (fun i => Q i - W i)
          + γ * muNorm μ (fun i => ∑ j, (P i j - T i j) * W j)) := by
    calc muNorm μ (fun i => Q i - W i)
        = muNorm μ (fun i => (r i - r' i) + (γ * (∑ j, P i j * (Q j - W j))
            + γ * (∑ j, (P i j - T i j) * W j))) := congrArg (muNorm μ) (funext hd)
      _ ≤ muNorm μ (fun i => r i - r' i)
            + muNorm μ (fun i => γ * (∑ j, P i j * (Q j - W j))
              + γ * (∑ j, (P i j - T i j) * W j)) := muNorm_add_le _ _ _ hμ
      _ ≤ muNorm μ (fun i => r i - r' i)
            + (γ * muNorm μ (fun i => Q i - W i)
              + γ * muNorm μ (fun i => ∑ j, (P i j - T i j) * W j)) := by
          have inner : muNorm μ (fun i => γ * (∑ j, P i j * (Q j - W j))
                  + γ * (∑ j, (P i j - T i j) * W j))
              ≤ γ * muNorm μ (fun i => Q i - W i)
                + γ * muNorm μ (fun i => ∑ j, (P i j - T i j) * W j) := by
            calc muNorm μ (fun i => γ * (∑ j, P i j * (Q j - W j))
                    + γ * (∑ j, (P i j - T i j) * W j))
                ≤ muNorm μ (fun i => γ * (∑ j, P i j * (Q j - W j)))
                  + muNorm μ (fun i => γ * (∑ j, (P i j - T i j) * W j)) :=
                  muNorm_add_le _ _ _ hμ
              _ = γ * muNorm μ (fun i => ∑ j, P i j * (Q j - W j))
                  + γ * muNorm μ (fun i => ∑ j, (P i j - T i j) * W j) := by
                  rw [muNorm_const_smul _ _ _ hγ, muNorm_const_smul _ _ _ hγ]
              _ ≤ γ * muNorm μ (fun i => Q i - W i)
                  + γ * muNorm μ (fun i => ∑ j, (P i j - T i j) * W j) := by
                  have := mul_le_mul_of_nonneg_left
                    (muNorm_mulVec_le μ hμ P hP hstat (fun j => Q j - W j)) hγ
                  linarith
          linarith
  linarith

/-- **Perturbation bound in sup norm**, the unweighted counterpart of
`muNorm_bellman_diff_le`.  No stationary distribution is involved. -/
lemma sup_bellman_diff_le {ι : Type*} [Fintype ι] [Nonempty ι] (P T : Matrix ι ι ℝ)
    (hP : IsTransitionMatrix P) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (r r' Q W : ι → ℝ) (hQ : IsBellmanQ P r γ Q) (hW : IsBellmanQ T r' γ W)
    (a b : ℝ) (ha : ∀ i, |r i - r' i| ≤ a)
    (hb : ∀ i, |∑ j, (P i j - T i j) * W j| ≤ b) (i : ι) :
    |Q i - W i| ≤ (a + γ * b) / (1 - γ) := by
  obtain ⟨m, hm⟩ := Finite.exists_max (fun i => |Q i - W i|)
  have hd : ∀ i, Q i - W i = (r i - r' i) + (γ * (∑ j, P i j * (Q j - W j))
      + γ * (∑ j, (P i j - T i j) * W j)) := by
    intro i
    have e : (∑ j, P i j * (Q j - W j)) + ∑ j, (P i j - T i j) * W j
        = (∑ j, P i j * Q j) - ∑ j, T i j * W j := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hQ i, hW i, ← mul_add, e]
    ring
  have hcontr : |∑ j, P m j * (Q j - W j)| ≤ |Q m - W m| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ j ∈ Finset.univ, |P m j * (Q j - W j)| ≤ P m j * |Q m - W m| := by
      intro j _
      rw [abs_mul, abs_of_nonneg (hP.1 m j)]
      exact mul_le_mul_of_nonneg_left (hm j) (hP.1 m j)
    refine (Finset.sum_le_sum h1).trans_eq ?_
    rw [← Finset.sum_mul, hP.2 m, one_mul]
  have key : |Q m - W m| ≤ a + (γ * |Q m - W m| + γ * b) := by
    calc |Q m - W m| = |(r m - r' m) + (γ * (∑ j, P m j * (Q j - W j))
            + γ * (∑ j, (P m j - T m j) * W j))| := by rw [hd m]
      _ ≤ |r m - r' m| + |γ * (∑ j, P m j * (Q j - W j))
            + γ * (∑ j, (P m j - T m j) * W j)| := abs_add_le _ _
      _ ≤ |r m - r' m| + (|γ * (∑ j, P m j * (Q j - W j))|
            + |γ * (∑ j, (P m j - T m j) * W j)|) := by
          have := abs_add_le (γ * (∑ j, P m j * (Q j - W j)))
            (γ * (∑ j, (P m j - T m j) * W j))
          linarith
      _ ≤ a + (γ * |Q m - W m| + γ * b) := by
          have e1 : |γ * (∑ j, P m j * (Q j - W j))| = γ * |∑ j, P m j * (Q j - W j)| := by
            rw [abs_mul, abs_of_nonneg hγ]
          have e2 : |γ * (∑ j, (P m j - T m j) * W j)|
              = γ * |∑ j, (P m j - T m j) * W j| := by
            rw [abs_mul, abs_of_nonneg hγ]
          rw [e1, e2]
          exact add_le_add (ha m)
            (add_le_add (mul_le_mul_of_nonneg_left hcontr hγ)
              (mul_le_mul_of_nonneg_left (hb m) hγ))
  have hpos : (0:ℝ) < 1 - γ := by linarith
  calc |Q i - W i| ≤ |Q m - W m| := hm i
    _ ≤ (a + γ * b) / (1 - γ) := by rw [le_div_iff₀ hpos]; nlinarith

/-! ## From the tensor-product chain to the agent-wise entanglement -/

/-- The sum of the agents' local value functions solves the Bellman equation for the
tensor-product transition with the additive reward.  This is what makes the separable
matrix `⊗ᵢ Pl i` the right comparison point. -/
lemma isBellmanQ_tensorProdN (Pl : ∀ i, Matrix (S i) (S i) ℝ)
    (hPl : ∀ i, IsTransitionMatrix (Pl i)) (rl : ∀ i, S i → ℝ) (γ : ℝ)
    (Qi : ∀ i, S i → ℝ) (hQi : ∀ i, IsBellmanQ (Pl i) (rl i) γ (Qi i)) :
    IsBellmanQ (tensorProdN Pl) (fun p => ∑ i, rl i (p i)) γ (fun p => ∑ i, Qi i (p i)) := by
  intro p
  have hsum : ∑ q : Joint S, tensorProdN Pl p q * (∑ i, Qi i (q i))
      = ∑ i, ∑ t : S i, Pl i (p i) t * Qi i t := by
    have e : ∑ q : Joint S, tensorProdN Pl p q * (∑ i, Qi i (q i))
        = ∑ i, ∑ q : Joint S, tensorProdN Pl p q * Qi i (q i) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [e]
    exact Finset.sum_congr rfl fun i _ => tensor_apply_coord Pl hPl i (Qi i) p
  show ∑ i, Qi i (p i)
      = (∑ i, rl i (p i)) + γ * ∑ q : Joint S, tensorProdN Pl p q * (∑ i, Qi i (q i))
  rw [hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hQi i (p i)

/-- The one-step gap between the joint transition and the tensor product of the local ones,
applied to a sum of local value functions, splits agent by agent into the gap between the
joint marginal and the local transition. -/
lemma joint_minus_tensor_apply (P : Matrix (Joint S) (Joint S) ℝ)
    (Pl : ∀ i, Matrix (S i) (S i) ℝ) (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (Qi : ∀ i, S i → ℝ) (p : Joint S) :
    ∑ q : Joint S, (P p q - tensorProdN Pl p q) * (∑ i, Qi i (q i))
      = ∑ i, ∑ t : S i, (marginalN i P p t - Pl i (p i) t) * Qi i t := by
  have e : ∑ q : Joint S, (P p q - tensorProdN Pl p q) * (∑ i, Qi i (q i))
      = ∑ i, ∑ q : Joint S, (P p q - tensorProdN Pl p q) * Qi i (q i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∑ q : Joint S, (P p q - tensorProdN Pl p q) * Qi i (q i)
      = (∑ q : Joint S, P p q * Qi i (q i))
        - ∑ q : Joint S, tensorProdN Pl p q * Qi i (q i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [h1, sum_apply_coord, tensor_apply_coord Pl hPl, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

lemma abs_joint_minus_tensor_le (P : Matrix (Joint S) (Joint S) ℝ)
    (Pl : ∀ i, Matrix (S i) (S i) ℝ) (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (Qi : ∀ i, S i → ℝ) (B : Fin N → ℝ) (hB : ∀ i t, |Qi i t| ≤ B i) (p : Joint S) :
    |∑ q : Joint S, (P p q - tensorProdN Pl p q) * (∑ i, Qi i (q i))|
      ≤ ∑ i, B i * ∑ t : S i, |marginalN i P p t - Pl i (p i) t| := by
  rw [joint_minus_tensor_apply P Pl hPl Qi p]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [abs_mul, mul_comm (B i)]
  exact mul_le_mul_of_nonneg_left (hB i t) (abs_nonneg _)

/-- The `μ`-norm of the one-step gap is at most `∑ᵢ Bᵢ · 2 dᵢ`, where `dᵢ` is agent `i`'s
`μ`-weighted agent-wise total variation distance. -/
lemma muNorm_transition_gap_le (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (Pl : ∀ i, Matrix (S i) (S i) ℝ)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (Qi : ∀ i, S i → ℝ) (B : Fin N → ℝ) (hB : ∀ i t, |Qi i t| ≤ B i) :
    muNorm μ (fun p => ∑ q : Joint S, (P p q - tensorProdN Pl p q) * (∑ i, Qi i (q i)))
      ≤ ∑ i, B i * (2 * muAgentTVDistN i μ P (Pl i)) := by
  refine (muNorm_le_sum μ _
    (fun p => ∑ i, B i * ∑ t : S i, |marginalN i P p t - Pl i (p i) t|) hμ
    (fun p => abs_joint_minus_tensor_le P Pl hPl Qi B hB p)).trans ?_
  have swap : ∑ p : Joint S, μ p * (∑ i, B i * ∑ t : S i, |marginalN i P p t - Pl i (p i) t|)
      = ∑ i, B i * (∑ p : Joint S, μ p * ∑ t : S i, |marginalN i P p t - Pl i (p i) t|) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
  rw [swap]
  refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
  congr 1
  unfold muAgentTVDistN
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring



/-- **The `μ`-norm decomposition-error core.**  With `Q` the joint value function for an
arbitrary reward `r`, and `Qi i` the value function of agent `i`'s candidate local chain
`Pl i` with local reward `rl i`, the decomposition error splits into a reward-gap term and
an agent-wise transition-gap term. -/
theorem decomposition_error_mu_core
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : Joint S → ℝ) (rl : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (Pl : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (hr : ∀ i s, |rl i s| ≤ rmax i)
    (hQ : IsBellmanQ P r γ Q)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hQi : ∀ i, IsBellmanQ (Pl i) (rl i) γ (Qi i)) :
    muNorm μ (fun p => Q p - ∑ i, Qi i (p i))
      ≤ muNorm μ (fun p => r p - ∑ i, rl i (p i)) / (1 - γ)
        + 2 * γ * (∑ i, muAgentTVDistN i μ P (Pl i) * rmax i) / (1 - γ) ^ 2 := by
  have hpos : (0:ℝ) < 1 - γ := by linarith
  have hμ0 : ∀ p, 0 ≤ μ p := fun p => (hμ.1 p).le
  have hne : Nonempty (Joint S) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := hμ.2
    simp at h1
  haveI : ∀ i, Nonempty (S i) := fun i => ⟨(Classical.arbitrary (Joint S)) i⟩
  have hB : ∀ i t, |Qi i t| ≤ rmax i / (1 - γ) := fun i t =>
    bellman_abs_le (Pl i) (hPl i) (rl i) (Qi i) γ (rmax i) hγ hγ1 (hr i) (hQi i) t
  have hW := isBellmanQ_tensorProdN Pl hPl rl γ Qi hQi
  have hcore : (1 - γ) * muNorm μ (fun p => Q p - ∑ i, Qi i (p i))
      ≤ muNorm μ (fun p => r p - ∑ i, rl i (p i))
        + γ * muNorm μ (fun p =>
            ∑ q : Joint S, (P p q - tensorProdN Pl p q) * (∑ i, Qi i (q i))) :=
    muNorm_bellman_diff_le μ hμ0 P (tensorProdN Pl) hP hstat γ hγ hγ1
      r (fun p => ∑ i, rl i (p i)) Q (fun p => ∑ i, Qi i (p i)) hQ hW
  have hgap := muNorm_transition_gap_le P μ hμ0 Pl hPl Qi (fun i => rmax i / (1 - γ)) hB
  have hX : (1 - γ) * (∑ i, rmax i / (1 - γ) * (2 * muAgentTVDistN i μ P (Pl i)))
      = 2 * ∑ i, muAgentTVDistN i μ P (Pl i) * rmax i := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  set MD := muNorm μ (fun p => Q p - ∑ i, Qi i (p i)) with hMD
  set A := muNorm μ (fun p => r p - ∑ i, rl i (p i)) with hA
  set MG := muNorm μ (fun p =>
    ∑ q : Joint S, (P p q - tensorProdN Pl p q) * (∑ i, Qi i (q i))) with hMGdef
  set SS := ∑ i, muAgentTVDistN i μ P (Pl i) * rmax i with hSS
  set X := ∑ i, rmax i / (1 - γ) * (2 * muAgentTVDistN i μ P (Pl i)) with hXdef
  have e1 := mul_le_mul_of_nonneg_left hcore hpos.le
  have e3 : γ * ((1 - γ) * MG) ≤ γ * (2 * SS) := by
    rw [← hX]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgap hpos.le) hγ
  have step : (1 - γ) ^ 2 * MD ≤ A * (1 - γ) + 2 * γ * SS := by nlinarith [e1, e3]
  have hrw : A / (1 - γ) + 2 * γ * SS / (1 - γ) ^ 2
      = (A * (1 - γ) + 2 * γ * SS) / (1 - γ) ^ 2 := by
    field_simp
  rw [hrw, le_div_iff₀ (pow_pos hpos 2)]
  nlinarith [step]


/-! ## The true (marginalized) local chain -/

lemma sum_coord_regroup (μ : Joint S → ℝ) (i : Fin N) (f : S i → ℝ) :
    ∑ p : Joint S, μ p * f (p i) = ∑ s : S i, marginalDist i μ s * f s := by
  simp only [marginalDist, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

lemma marginalDist_nonneg (μ : Joint S → ℝ) (hμ : ∀ p, 0 ≤ μ p) (i : Fin N) (s : S i) :
    0 ≤ marginalDist i μ s :=
  Finset.sum_nonneg fun p _ => by by_cases h : p i = s <;> simp [h, hμ p]

lemma marginalDist_pos [Nonempty (Joint S)] (μ : Joint S → ℝ) (hμ : IsPositiveDist μ)
    (i : Fin N) (s : S i) : 0 < marginalDist i μ s := by
  classical
  obtain ⟨q⟩ := ‹Nonempty (Joint S)›
  have hpi : (Function.update q i s) i = s := by simp
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum
    (f := fun p : Joint S => if p i = s then μ p else 0)
    (fun x _ => by by_cases h : x i = s <;> simp [h, (hμ.1 x).le])
    (Finset.mem_univ (Function.update q i s)))
  simp [hpi, hμ.1 (Function.update q i s)]

/-- **Leg (II) of the paper's proof, per row.**  The true marginalized chain `Ptrue` differs
from a candidate `Pi` by at most the `μ`-weighted deviation of the joint marginal from `Pi`,
restricted to the fibre over `s`.  This is the inequality behind `‖P^π_i − P_i‖ ≤ 2 Eᵢ`. -/
lemma localTransition_row_diff_le (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (i : Fin N) (Pi Ptrue : Matrix (S i) (S i) ℝ)
    (htrue : IsLocalTransitionN i P μ Ptrue) (s : S i) :
    marginalDist i μ s * ∑ t : S i, |Ptrue s t - Pi s t|
      ≤ ∑ p : Joint S,
          (if p i = s then μ p * ∑ t : S i, |marginalN i P p t - Pi (p i) t| else 0) := by
  have key : ∀ t : S i, marginalDist i μ s * |Ptrue s t - Pi s t|
      ≤ ∑ p : Joint S, (if p i = s then μ p * |marginalN i P p t - Pi (p i) t| else 0) := by
    intro t
    have hid : marginalDist i μ s * (Ptrue s t - Pi s t)
        = ∑ p : Joint S,
            (if p i = s then μ p * (marginalN i P p t - Pi (p i) t) else 0) := by
      have hPi : marginalDist i μ s * Pi s t
          = ∑ p : Joint S, (if p i = s then μ p else 0) * Pi s t := by
        rw [marginalDist, Finset.sum_mul]
      rw [mul_sub, htrue s t, hPi, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases h : p i = s
      · simp [h, mul_sub]
      · simp [h]
    calc marginalDist i μ s * |Ptrue s t - Pi s t|
        = |marginalDist i μ s * (Ptrue s t - Pi s t)| := by
          rw [abs_mul, abs_of_nonneg (marginalDist_nonneg μ hμ i s)]
      _ = |∑ p : Joint S,
            (if p i = s then μ p * (marginalN i P p t - Pi (p i) t) else 0)| := by rw [hid]
      _ ≤ ∑ p : Joint S,
            |if p i = s then μ p * (marginalN i P p t - Pi (p i) t) else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ p : Joint S,
            (if p i = s then μ p * |marginalN i P p t - Pi (p i) t| else 0) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases h : p i = s
          · simp [h, abs_mul, abs_of_nonneg (hμ p)]
          · simp [h]
  calc marginalDist i μ s * ∑ t : S i, |Ptrue s t - Pi s t|
      = ∑ t : S i, marginalDist i μ s * |Ptrue s t - Pi s t| := Finset.mul_sum _ _ _
    _ ≤ ∑ t : S i, ∑ p : Joint S,
          (if p i = s then μ p * |marginalN i P p t - Pi (p i) t| else 0) :=
        Finset.sum_le_sum fun t _ => key t
    _ = ∑ p : Joint S,
          (if p i = s then μ p * ∑ t : S i, |marginalN i P p t - Pi (p i) t| else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : p i = s
        · simp [h, Finset.mul_sum]
        · simp [h]

/-- **The `μ`-weighted bridging bound.**  The joint marginal deviates from the *true* local
chain by at most twice its deviation from any candidate.  With the candidate the optimizer,
this is `d_i(P, P^π_i) ≤ 2 Eᵢ` — the step the mission's error bounds are missing. -/
lemma muAgentTVDistN_localTransition_le (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (i : Fin N) (Pi Ptrue : Matrix (S i) (S i) ℝ)
    (htrue : IsLocalTransitionN i P μ Ptrue) :
    muAgentTVDistN i μ P Ptrue ≤ 2 * muAgentTVDistN i μ P Pi := by
  have hloc : ∑ s : S i, marginalDist i μ s * ∑ t : S i, |Ptrue s t - Pi s t|
      ≤ ∑ p : Joint S, μ p * ∑ t : S i, |marginalN i P p t - Pi (p i) t| := by
    refine (Finset.sum_le_sum fun s _ =>
      localTransition_row_diff_le P μ hμ i Pi Ptrue htrue s).trans ?_
    rw [Finset.sum_comm]
    exact le_of_eq (Finset.sum_congr rfl fun p _ => by simp)
  have hlift : ∑ p : Joint S, μ p * ∑ t : S i, |Ptrue (p i) t - Pi (p i) t|
      = ∑ s : S i, marginalDist i μ s * ∑ t : S i, |Ptrue s t - Pi s t| :=
    sum_coord_regroup μ i (fun s => ∑ t : S i, |Ptrue s t - Pi s t|)
  unfold muAgentTVDistN
  have tri : ∀ p : Joint S,
      μ p * ((1 / 2) * ∑ t : S i, |marginalN i P p t - Ptrue (p i) t|)
        ≤ μ p * ((1 / 2) * ∑ t : S i, |marginalN i P p t - Pi (p i) t|)
          + μ p * ((1 / 2) * ∑ t : S i, |Ptrue (p i) t - Pi (p i) t|) := by
    intro p
    have hsum : ∑ t : S i, |marginalN i P p t - Ptrue (p i) t|
        ≤ (∑ t : S i, |marginalN i P p t - Pi (p i) t|)
          + ∑ t : S i, |Ptrue (p i) t - Pi (p i) t| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun t _ => ?_
      calc |marginalN i P p t - Ptrue (p i) t|
          = |(marginalN i P p t - Pi (p i) t) + -(Ptrue (p i) t - Pi (p i) t)| := by
            congr 1; ring
        _ ≤ |marginalN i P p t - Pi (p i) t| + |-(Ptrue (p i) t - Pi (p i) t)| :=
            abs_add_le _ _
        _ = |marginalN i P p t - Pi (p i) t| + |Ptrue (p i) t - Pi (p i) t| := by
            rw [abs_neg]
    nlinarith [hμ p, hsum]
  refine (Finset.sum_le_sum fun p _ => tri p).trans ?_
  rw [Finset.sum_add_distrib]
  have hhalf : ∑ p : Joint S, μ p * ((1 / 2) * ∑ t : S i, |Ptrue (p i) t - Pi (p i) t|)
      ≤ ∑ p : Joint S, μ p * ((1 / 2) * ∑ t : S i, |marginalN i P p t - Pi (p i) t|) := by
    have e1 : ∑ p : Joint S, μ p * ((1 / 2) * ∑ t : S i, |Ptrue (p i) t - Pi (p i) t|)
        = (1 / 2) * ∑ p : Joint S, μ p * ∑ t : S i, |Ptrue (p i) t - Pi (p i) t| := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    have e2 : ∑ p : Joint S, μ p * ((1 / 2) * ∑ t : S i, |marginalN i P p t - Pi (p i) t|)
        = (1 / 2) * ∑ p : Joint S, μ p * ∑ t : S i, |marginalN i P p t - Pi (p i) t| := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    rw [e1, e2, hlift]
    linarith [hloc]
  linarith [hhalf]
/-! ## Sup-norm core and the faithful Theorem 8 -/

theorem decomposition_error_sup_core
    (P : Matrix (Joint S) (Joint S) ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ) (Pl : ∀ i, Matrix (S i) (S i) ℝ)
    (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hr : ∀ i s, |r i s| ≤ rmax i)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hQi : ∀ i, IsBellmanQ (Pl i) (r i) γ (Qi i)) (p : Joint S) :
    |Q p - ∑ i, Qi i (p i)|
      ≤ 2 * γ * (∑ i, agentTVDistN i P (Pl i) * rmax i) / (1 - γ) ^ 2 := by
  have hpos : (0:ℝ) < 1 - γ := by linarith
  haveI : Nonempty (Joint S) := ⟨p⟩
  haveI : ∀ i, Nonempty (S i) := fun i => ⟨p i⟩
  have hrmax : ∀ i, 0 ≤ rmax i := fun i => le_trans (abs_nonneg _) (hr i (p i))
  have hB : ∀ i t, |Qi i t| ≤ rmax i / (1 - γ) := fun i t =>
    bellman_abs_le (Pl i) (hPl i) (r i) (Qi i) γ (rmax i) hγ hγ1 (hr i) (hQi i) t
  have hW := isBellmanQ_tensorProdN Pl hPl r γ Qi hQi
  have hsup : ∀ (i : Fin N) (q : Joint S),
      (1 / 2 : ℝ) * ∑ t : S i, |marginalN i P q t - Pl i (q i) t|
        ≤ agentTVDistN i P (Pl i) := by
    intro i q
    exact le_ciSup (f := fun w : Joint S =>
      (1 / 2 : ℝ) * ∑ t : S i, |marginalN i P w t - Pl i (w i) t|)
      (Finite.bddAbove_range _) q
  have hb : ∀ q : Joint S,
      |∑ q' : Joint S, (P q q' - tensorProdN Pl q q') * (∑ i, Qi i (q' i))|
        ≤ ∑ i, rmax i / (1 - γ) * (2 * agentTVDistN i P (Pl i)) := by
    intro q
    refine (abs_joint_minus_tensor_le P Pl hPl Qi (fun i => rmax i / (1 - γ)) hB q).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hsup i q])
      (div_nonneg (hrmax i) hpos.le)
  have ha : ∀ q : Joint S, |(∑ i, r i (q i)) - ∑ i, r i (q i)| ≤ 0 := by intro q; simp
  have key := sup_bellman_diff_le P (tensorProdN Pl) hP γ hγ hγ1
    (fun q => ∑ i, r i (q i)) (fun q => ∑ i, r i (q i)) Q (fun q => ∑ i, Qi i (q i))
    hQ hW 0 (∑ i, rmax i / (1 - γ) * (2 * agentTVDistN i P (Pl i))) ha hb p
  have hbrw : (1 - γ) * (∑ i, rmax i / (1 - γ) * (2 * agentTVDistN i P (Pl i)))
      = 2 * ∑ i, agentTVDistN i P (Pl i) * rmax i := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have hbval : (∑ i, rmax i / (1 - γ) * (2 * agentTVDistN i P (Pl i)))
      = 2 * (∑ i, agentTVDistN i P (Pl i) * rmax i) / (1 - γ) := by
    rw [eq_div_iff (ne_of_gt hpos)]
    linarith [hbrw]
  rw [hbval] at key
  refine key.trans (le_of_eq ?_)
  field_simp
  ring

lemma agentTVDistN_localTransition_le [Nonempty (Joint S)]
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (hμ : IsPositiveDist μ)
    (i : Fin N) (Pi Ptrue : Matrix (S i) (S i) ℝ)
    (htrue : IsLocalTransitionN i P μ Ptrue) :
    agentTVDistN i P Ptrue ≤ 2 * agentTVDistN i P Pi := by
  have hμ0 : ∀ p, 0 ≤ μ p := fun p => (hμ.1 p).le
  have hsup : ∀ q : Joint S,
      (1 / 2 : ℝ) * ∑ t : S i, |marginalN i P q t - Pi (q i) t| ≤ agentTVDistN i P Pi := by
    intro q
    exact le_ciSup (f := fun w : Joint S =>
      (1 / 2 : ℝ) * ∑ t : S i, |marginalN i P w t - Pi (w i) t|)
      (Finite.bddAbove_range _) q
  have hrow : ∀ s : S i, ∑ t : S i, |Ptrue s t - Pi s t| ≤ 2 * agentTVDistN i P Pi := by
    intro s
    have h1 := localTransition_row_diff_le P μ hμ0 i Pi Ptrue htrue s
    have h2 : ∑ p : Joint S,
        (if p i = s then μ p * ∑ t : S i, |marginalN i P p t - Pi (p i) t| else 0)
        ≤ marginalDist i μ s * (2 * agentTVDistN i P Pi) := by
      rw [marginalDist, Finset.sum_mul]
      refine Finset.sum_le_sum fun p _ => ?_
      by_cases h : p i = s
      · rw [if_pos h, if_pos h]
        exact mul_le_mul_of_nonneg_left (by linarith [hsup p]) (hμ0 p)
      · simp [h]
    exact le_of_mul_le_mul_left (le_trans h1 h2) (marginalDist_pos μ hμ i s)
  have hall : ∀ q : Joint S, (1 / 2 : ℝ) * ∑ t : S i, |marginalN i P q t - Ptrue (q i) t|
      ≤ 2 * agentTVDistN i P Pi := by
    intro q
    have h3 : ∑ t : S i, |marginalN i P q t - Ptrue (q i) t|
        ≤ (∑ t : S i, |marginalN i P q t - Pi (q i) t|)
          + ∑ t : S i, |Ptrue (q i) t - Pi (q i) t| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun t _ => ?_
      calc |marginalN i P q t - Ptrue (q i) t|
          = |(marginalN i P q t - Pi (q i) t) + -(Ptrue (q i) t - Pi (q i) t)| := by
            congr 1; ring
        _ ≤ |marginalN i P q t - Pi (q i) t| + |-(Ptrue (q i) t - Pi (q i) t)| := abs_add_le _ _
        _ = |marginalN i P q t - Pi (q i) t| + |Ptrue (q i) t - Pi (q i) t| := by rw [abs_neg]
    linarith [hsup q, hrow (q i), h3]
  exact ciSup_le hall


end MarkovEntanglement

open MarkovEntanglement

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (Pl Ptrue : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (hr : ∀ i s, |r i s| ≤ rmax i)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hopt : ∀ i, agentTVDistN i P (Pl i) = agentEntanglementWith i (agentTVDistN i) P)
    (hPtrue : ∀ i, IsTransitionMatrix (Ptrue i))
    (htrue : ∀ i, IsLocalTransitionN i P μ (Ptrue i))
    (hQi : ∀ i, IsBellmanQ (Ptrue i) (r i) γ (Qi i)) (p : Joint S) :
    |Q p - ∑ i, Qi i (p i)|
      ≤ 4 * γ * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) / (1 - γ) ^ 2 := by
  have hpos : (0:ℝ) < 1 - γ := by linarith
  haveI : Nonempty (Joint S) := ⟨p⟩
  have hrmax : ∀ i, 0 ≤ rmax i := fun i => le_trans (abs_nonneg _) (hr i (p i))
  have hcore := decomposition_error_sup_core P γ rmax r Q Ptrue Qi hγ hγ1 hP hr hQ hPtrue hQi p
  have hsum : ∑ i, agentTVDistN i P (Ptrue i) * rmax i
      ≤ 2 * ∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hb := agentTVDistN_localTransition_le P μ hμ i (Pl i) (Ptrue i) (htrue i)
    rw [hopt i] at hb
    nlinarith [hrmax i]
  have hnum : 2 * γ * (∑ i, agentTVDistN i P (Ptrue i) * rmax i)
      ≤ 4 * γ * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) := by
    nlinarith [hsum, hγ]
  have hdiv : 2 * γ * (∑ i, agentTVDistN i P (Ptrue i) * rmax i) / (1 - γ) ^ 2
      ≤ 4 * γ * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) / (1 - γ) ^ 2 := by
    rw [div_le_div_iff_of_pos_right (pow_pos hpos 2)]
    exact hnum
  linarith [hcore, hdiv]
