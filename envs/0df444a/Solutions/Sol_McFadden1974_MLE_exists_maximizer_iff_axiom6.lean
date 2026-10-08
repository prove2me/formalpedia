-- Prove2me | solution 1 for McFadden1974.MLE.exists_maximizer_iff_axiom6
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:56:40.507454+00:00
-- url     : https://prove2.me/submissions/87345c75-d2d1-4c1c-a58c-b2feeedabb55

/-
McFadden (1974), Lemma 3: for conditional logit data satisfying the full-rank Axiom 5, the
log-likelihood has a global maximizer iff Axiom 6 holds.

(⇐) Under Axiom 6 the finite maximum `b` of the forms `S_in ⟪z_jn − z_in, ·⟫` is positive on the
unit sphere, hence bounded below by some `c > 0` there; since `log ∑ exp ≥ max` and every summand of
`C − L` is nonnegative, `L(θ) ≤ C − c‖θ‖`. So `{L ≥ L 0}` is compact and `L` is continuous.
(⇒) A direction `γ` with all `S_in ⟪z_jn − z_in, γ⟫ ≤ 0` can only increase `L`; at a maximizer it
cannot increase it, so every logarithm is unchanged, which forces `⟪z_jn − z_in, γ⟫ = 0` whenever
`S_in > 0`; this makes `γ` orthogonal to all rows of the Axiom 5 matrix, so `γ = 0`.
-/
import Mathlib
import Definitions.Def_McFadden1974_MLE_Model
import Definitions.Def_McFadden1974_MLE_Axioms

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace McfProof

open McFadden1974.MLE

variable {K : ℕ} (d : Data K)

/-- `log ∑_j exp ⟪z_jn − z_in, θ⟫`. -/
noncomputable def F (n : Fin d.N) (i : Fin (d.J n)) (θ : EuclideanSpace ℝ (Fin K)) : ℝ :=
  Real.log (∑ j, Real.exp ⟪d.z n j - d.z n i, θ⟫)

theorem L_eq (θ : EuclideanSpace ℝ (Fin K)) :
    d.L θ = d.C - ∑ n, ∑ i, (d.S n i : ℝ) * F d n i θ := rfl

theorem one_le_sum (n : Fin d.N) (i : Fin (d.J n)) (θ : EuclideanSpace ℝ (Fin K)) :
    1 ≤ ∑ j, Real.exp ⟪d.z n j - d.z n i, θ⟫ := by
  calc (1 : ℝ) = Real.exp ⟪d.z n i - d.z n i, θ⟫ := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun j => Real.exp ⟪d.z n j - d.z n i, θ⟫)
        (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

theorem sum_pos (n : Fin d.N) (i : Fin (d.J n)) (θ : EuclideanSpace ℝ (Fin K)) :
    0 < ∑ j, Real.exp ⟪d.z n j - d.z n i, θ⟫ :=
  lt_of_lt_of_le one_pos (one_le_sum d n i θ)

theorem F_nonneg (n : Fin d.N) (i : Fin (d.J n)) (θ : EuclideanSpace ℝ (Fin K)) :
    0 ≤ F d n i θ := Real.log_nonneg (one_le_sum d n i θ)

theorem inner_le_F (n : Fin d.N) (i j : Fin (d.J n)) (θ : EuclideanSpace ℝ (Fin K)) :
    ⟪d.z n j - d.z n i, θ⟫ ≤ F d n i θ := by
  unfold F
  rw [Real.le_log_iff_exp_le (sum_pos d n i θ)]
  exact Finset.single_le_sum (f := fun j => Real.exp ⟪d.z n j - d.z n i, θ⟫)
    (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ j)

theorem F_le_of_nonpos (n : Fin d.N) (i : Fin (d.J n)) (θ γ : EuclideanSpace ℝ (Fin K))
    (h : ∀ j, ⟪d.z n j - d.z n i, γ⟫ ≤ 0) : F d n i (θ + γ) ≤ F d n i θ := by
  unfold F
  refine Real.log_le_log (sum_pos d n i (θ + γ)) (Finset.sum_le_sum fun j _ => ?_)
  apply Real.exp_le_exp.mpr
  rw [inner_add_right]
  linarith [h j]

theorem inner_eq_zero_of_F_eq (n : Fin d.N) (i : Fin (d.J n)) (θ γ : EuclideanSpace ℝ (Fin K))
    (h : ∀ j, ⟪d.z n j - d.z n i, γ⟫ ≤ 0) (heq : F d n i (θ + γ) = F d n i θ) :
    ∀ j, ⟪d.z n j - d.z n i, γ⟫ = 0 := by
  unfold F at heq
  have hs : ∑ j, Real.exp ⟪d.z n j - d.z n i, θ + γ⟫ = ∑ j, Real.exp ⟪d.z n j - d.z n i, θ⟫ :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (sum_pos d n i (θ + γ)))
      (Set.mem_Ioi.mpr (sum_pos d n i θ)) heq
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin (d.J n))),
      Real.exp ⟪d.z n j - d.z n i, θ + γ⟫ ≤ Real.exp ⟪d.z n j - d.z n i, θ⟫ := by
    intro j _
    apply Real.exp_le_exp.mpr
    rw [inner_add_right]
    linarith [h j]
  have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  intro j
  have := Real.exp_injective (hall j (Finset.mem_univ j))
  rw [inner_add_right] at this
  linarith

theorem sum_pos' (n : Fin d.N) (i : Fin (d.J n)) (θ : EuclideanSpace ℝ (Fin K)) :
    0 < ∑ j, Real.exp ⟪d.z n j, θ⟫ :=
  Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩

theorem eq_zero_of_rank {m : Type*} [Fintype m] (A : Matrix m (Fin K) ℝ) (hr : A.rank = K)
    (v : Fin K → ℝ) (hv : A.mulVec v = 0) : v = 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h2 : Module.finrank ℝ (LinearMap.range A.mulVecLin) = K := hr
  simp only [Module.finrank_fin_fun] at h1
  have h3 : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 0 := by omega
  have h4 : LinearMap.ker A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h3
  have h5 : v ∈ LinearMap.ker A.mulVecLin := by simpa using hv
  rw [h4] at h5
  simpa using h5

theorem zbar_inner (n : Fin d.N) (θ γ : EuclideanSpace ℝ (Fin K)) (i : Fin (d.J n))
    (hconst : ∀ j, ⟪d.z n j, γ⟫ = ⟪d.z n i, γ⟫) :
    ⟪d.zbar n θ, γ⟫ = ⟪d.z n i, γ⟫ := by
  unfold Data.zbar
  rw [sum_inner]
  have hsum : ∑ j, d.P n j θ = 1 := by
    unfold Data.P
    rw [← Finset.sum_div]
    exact div_self (sum_pos' d n i θ).ne'
  calc ∑ j, ⟪d.P n j θ • d.z n j, γ⟫ = ∑ j, d.P n j θ * ⟪d.z n i, γ⟫ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [real_inner_smul_left, hconst j]
    _ = ⟪d.z n i, γ⟫ := by rw [← Finset.sum_mul, hsum, one_mul]

theorem axiom6_of_exists_max (h5 : d.Axiom5) (hmax : ∃ θhat, ∀ θ, d.L θ ≤ d.L θhat) :
    d.Axiom6 := by
  obtain ⟨θh, hθh⟩ := hmax
  intro γ hγ
  have hnonpos : ∀ n i, 0 < d.S n i → ∀ j, ⟪d.z n j - d.z n i, γ⟫ ≤ 0 := by
    intro n i hpos j
    have h := hγ n i j
    have hSpos : (0 : ℝ) < d.S n i := by exact_mod_cast hpos
    by_contra hcon
    push_neg at hcon
    exact absurd h (not_le.mpr (mul_pos hSpos hcon))
  have hterm : ∀ n i, (d.S n i : ℝ) * F d n i (θh + γ) ≤ (d.S n i : ℝ) * F d n i θh := by
    intro n i
    rcases Nat.eq_zero_or_pos (d.S n i) with h0 | hpos
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (F_le_of_nonpos d n i θh γ (hnonpos n i hpos))
        (by positivity)
  have hsum_le : ∑ n, ∑ i, (d.S n i : ℝ) * F d n i (θh + γ) ≤
      ∑ n, ∑ i, (d.S n i : ℝ) * F d n i θh :=
    Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun i _ => hterm n i
  have hL1 := hθh (θh + γ)
  rw [L_eq, L_eq] at hL1
  have hEq : ∑ n, ∑ i, (d.S n i : ℝ) * F d n i (θh + γ) =
      ∑ n, ∑ i, (d.S n i : ℝ) * F d n i θh := le_antisymm hsum_le (by linarith)
  have houter := (Finset.sum_eq_sum_iff_of_le
    (fun n _ => Finset.sum_le_sum fun i _ => hterm n i)).mp hEq
  have hinner : ∀ n i, (d.S n i : ℝ) * F d n i (θh + γ) = (d.S n i : ℝ) * F d n i θh :=
    fun n i => (Finset.sum_eq_sum_iff_of_le (fun i _ => hterm n i)).mp
      (houter n (Finset.mem_univ n)) i (Finset.mem_univ i)
  have hconst : ∀ n (i : Fin (d.J n)), 0 < d.S n i → ∀ j, ⟪d.z n j - d.z n i, γ⟫ = 0 := by
    intro n i hpos
    have hSne : (d.S n i : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    exact inner_eq_zero_of_F_eq d n i θh γ (hnonpos n i hpos)
      (mul_left_cancel₀ hSne (hinner n i))
  have hzero : ∀ n (i : Fin (d.J n)), ⟪d.z n i - d.zbar n θh, γ⟫ = 0 := by
    intro n i
    obtain ⟨i0, _, hi0⟩ := Finset.sum_pos_iff.mp (d.observed n)
    have hall : ∀ j, ⟪d.z n j, γ⟫ = ⟪d.z n i0, γ⟫ := by
      intro j
      have := hconst n i0 hi0 j
      rw [inner_sub_left] at this
      linarith
    rw [inner_sub_left, zbar_inner d n θh γ i0 hall, hall i]
    ring
  have hvec : (d.designMatrix θh).mulVec (fun k => γ k) = 0 := by
    ext ⟨n, i⟩
    have := hzero n i
    simp only [Matrix.mulVec, dotProduct, Data.designMatrix, Pi.zero_apply]
    simpa [PiLp.inner_apply, mul_comm] using this
  have := eq_zero_of_rank (d.designMatrix θh) (h5 θh) _ hvec
  ext k
  simpa using congrFun this k


/-- The index type of the double maximum in `b`. -/
abbrev T (d : Data K) := Σ n : Fin d.N, Fin (d.J n) × Fin (d.J n)

/-- The linear form `S_in ⟪z_jn − z_in, θ⟫`. -/
noncomputable def f (x : T d) (θ : EuclideanSpace ℝ (Fin K)) : ℝ :=
  (d.S x.1 x.2.1 : ℝ) * ⟪d.z x.1 x.2.2 - d.z x.1 x.2.1, θ⟫

theorem T_nonempty : Nonempty (T d) := by
  have hN := d.trials
  let n : Fin d.N := ⟨0, hN⟩
  obtain ⟨i, _, _⟩ := Finset.sum_pos_iff.mp (d.observed n)
  exact ⟨⟨n, i, i⟩⟩

theorem f_cont (x : T d) : Continuous (f d x) := by
  unfold f
  exact continuous_const.mul (continuous_const.inner continuous_id)

theorem f_smul (x : T d) (t : ℝ) (γ : EuclideanSpace ℝ (Fin K)) :
    f d x (t • γ) = t * f d x γ := by
  unfold f
  rw [inner_smul_right]
  ring

theorem f_zero (x : T d) : f d x 0 = 0 := by simp [f]

/-- Under Axiom 6 some linear form `f x` is at least `c ‖θ‖`. -/
theorem coercive (h6 : d.Axiom6) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ : EuclideanSpace ℝ (Fin K), ∃ x : T d, c * ‖θ‖ ≤ f d x θ := by
  classical
  have := T_nonempty d
  by_cases hsph : ∃ γ : EuclideanSpace ℝ (Fin K), ‖γ‖ = 1
  · set m : EuclideanSpace ℝ (Fin K) → ℝ :=
      fun γ => Finset.univ.sup' Finset.univ_nonempty (fun x : T d => f d x γ) with hm
    have hmc : Continuous m :=
      Continuous.finset_sup'_apply Finset.univ_nonempty (fun x _ => f_cont d x)
    have hpos : ∀ γ : EuclideanSpace ℝ (Fin K), ‖γ‖ = 1 → 0 < m γ := by
      intro γ hγ
      have hne : γ ≠ 0 := by
        intro h
        rw [h] at hγ
        simp at hγ
      by_contra hcon
      push_neg at hcon
      apply hne
      apply h6
      intro n i j
      have : f d ⟨n, i, j⟩ γ ≤ m γ :=
        Finset.le_sup' (fun x : T d => f d x γ) (Finset.mem_univ _)
      exact this.trans hcon
    obtain ⟨γ0, hγ0, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin K)) 1).exists_isMinOn
      (by obtain ⟨γ, hγ⟩ := hsph; exact ⟨γ, by simpa using hγ⟩) hmc.continuousOn
    have hγ0n : ‖γ0‖ = 1 := by simpa using hγ0
    refine ⟨m γ0, hpos γ0 hγ0n, fun θ => ?_⟩
    by_cases hθ : θ = 0
    · obtain ⟨x⟩ := ‹Nonempty (T d)›
      exact ⟨x, by simp [hθ, f_zero]⟩
    · have hnpos : 0 < ‖θ‖ := norm_pos_iff.mpr hθ
      obtain ⟨γ, hγdef⟩ : ∃ γ : EuclideanSpace ℝ (Fin K), γ = (‖θ‖⁻¹) • θ := ⟨_, rfl⟩
      have hγn : ‖γ‖ = 1 := by rw [hγdef]; exact norm_smul_inv_norm hθ
      have hmγ : m γ0 ≤ m γ := hmin (by simpa using hγn)
      obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun x : T d => f d x γ)
      have hθeq : θ = ‖θ‖ • γ := by
        rw [hγdef, smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul]
      have hfx : f d x θ = ‖θ‖ * f d x γ := by
        rw [← f_smul d x ‖θ‖ γ, ← hθeq]
      refine ⟨x, ?_⟩
      have hmx : m γ = f d x γ := hx
      calc m γ0 * ‖θ‖ ≤ m γ * ‖θ‖ := mul_le_mul_of_nonneg_right hmγ hnpos.le
        _ = ‖θ‖ * f d x γ := by rw [hmx]; ring
        _ = f d x θ := hfx.symm
  · refine ⟨1, one_pos, fun θ => ?_⟩
    have hθ : θ = 0 := by
      by_contra hne
      exact hsph ⟨(‖θ‖⁻¹) • θ, norm_smul_inv_norm hne⟩
    obtain ⟨x⟩ := T_nonempty d
    exact ⟨x, by simp [hθ, f_zero]⟩

theorem coercive_L (c : ℝ) (hc : ∀ θ : EuclideanSpace ℝ (Fin K), ∃ x : T d, c * ‖θ‖ ≤ f d x θ)
    (θ : EuclideanSpace ℝ (Fin K)) : c * ‖θ‖ ≤ d.C - d.L θ := by
  obtain ⟨⟨n, i, j⟩, hx⟩ := hc θ
  have h1 : f d ⟨n, i, j⟩ θ ≤ (d.S n i : ℝ) * F d n i θ :=
    mul_le_mul_of_nonneg_left (inner_le_F d n i j θ) (Nat.cast_nonneg _)
  have h2 : (d.S n i : ℝ) * F d n i θ ≤ ∑ i', (d.S n i' : ℝ) * F d n i' θ :=
    Finset.single_le_sum (f := fun i' => (d.S n i' : ℝ) * F d n i' θ)
      (fun i' _ => mul_nonneg (Nat.cast_nonneg _) (F_nonneg d n i' θ)) (Finset.mem_univ i)
  have h3 : ∑ i', (d.S n i' : ℝ) * F d n i' θ ≤ ∑ n', ∑ i', (d.S n' i' : ℝ) * F d n' i' θ :=
    Finset.single_le_sum (f := fun n' => ∑ i', (d.S n' i' : ℝ) * F d n' i' θ)
      (fun n' _ => Finset.sum_nonneg fun i' _ =>
        mul_nonneg (Nat.cast_nonneg _) (F_nonneg d n' i' θ)) (Finset.mem_univ n)
  have : d.C - d.L θ = ∑ n', ∑ i', (d.S n' i' : ℝ) * F d n' i' θ := by
    rw [L_eq]; ring
  rw [this]
  exact hx.trans (h1.trans (h2.trans h3))

theorem L_continuous : Continuous (d.L : EuclideanSpace ℝ (Fin K) → ℝ) := by
  have : (d.L : EuclideanSpace ℝ (Fin K) → ℝ) =
      fun θ => d.C - ∑ n, ∑ i, (d.S n i : ℝ) * F d n i θ := funext fun θ => L_eq d θ
  rw [this]
  refine continuous_const.sub (continuous_finsetSum _ fun n _ =>
    continuous_finsetSum _ fun i _ => continuous_const.mul ?_)
  unfold F
  refine Continuous.log (continuous_finsetSum _ fun j _ => Real.continuous_exp.comp
    (continuous_const.inner continuous_id)) fun θ => (sum_pos d n i θ).ne'

theorem exists_max_of_axiom6 (h6 : d.Axiom6) :
    ∃ θhat : EuclideanSpace ℝ (Fin K), ∀ θ, d.L θ ≤ d.L θhat := by
  obtain ⟨c, hc, hco⟩ := coercive d h6
  set A : Set (EuclideanSpace ℝ (Fin K)) := {θ | d.L 0 ≤ d.L θ} with hA
  have hAclosed : IsClosed A := isClosed_le continuous_const (L_continuous d)
  have hAbdd : Bornology.IsBounded A := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin K)))
      (r := (d.C - d.L 0) / c)).subset ?_
    intro θ hθ
    rw [mem_closedBall_zero_iff]
    have h1 := coercive_L d c hco θ
    have h2 : d.L 0 ≤ d.L θ := hθ
    rw [le_div_iff₀ hc]
    linarith
  have hAcompact : IsCompact A := Metric.isCompact_of_isClosed_isBounded hAclosed hAbdd
  obtain ⟨θh, hθhA, hθh⟩ := hAcompact.exists_isMaxOn ⟨0, by simp [hA]⟩ (L_continuous d).continuousOn
  refine ⟨θh, fun θ => ?_⟩
  by_cases hθ : θ ∈ A
  · exact hθh hθ
  · have : d.L θ < d.L 0 := by simpa [hA] using hθ
    exact this.le.trans hθhA

end McfProof

open McFadden1974.MLE in
theorem solution {K : ℕ} (d : Data K) (h5 : d.Axiom5) :
    (∃ θhat : EuclideanSpace ℝ (Fin K), ∀ θ, d.L θ ≤ d.L θhat) ↔ d.Axiom6 :=
  ⟨McfProof.axiom6_of_exists_max d h5, McfProof.exists_max_of_axiom6 d⟩
