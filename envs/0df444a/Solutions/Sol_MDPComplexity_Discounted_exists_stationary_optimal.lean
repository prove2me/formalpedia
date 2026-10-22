-- Prove2me | solution 1 for MDPComplexity.Discounted.exists_stationary_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T17:48:57.64299+00:00
-- url     : https://prove2.me/submissions/f0f21bb3-17f7-48fd-85b4-a834d9129ea4

import Mathlib
import Definitions.Def_MDPComplexity_Discounted_Model

open MDPComplexity.Discounted Finset Filter

section
variable {S : Type} [Fintype S] [DecidableEq S]

noncomputable def bel (M : DetMDP S) (β : ℝ) (V : S → ℝ) : S → ℝ := fun s =>
  Finset.univ.inf' Finset.univ_nonempty (fun d : M.D s => M.c s d + β * V (M.next s d))

theorem bel_le (M : DetMDP S) (β : ℝ) (V : S → ℝ) (s : S) (d : M.D s) :
    bel M β V s ≤ M.c s d + β * V (M.next s d) :=
  Finset.inf'_le _ (Finset.mem_univ d)

theorem bel_ex (M : DetMDP S) (β : ℝ) (V : S → ℝ) (s : S) :
    ∃ d : M.D s, bel M β V s = M.c s d + β * V (M.next s d) := by
  obtain ⟨d, -, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun d : M.D s => M.c s d + β * V (M.next s d))
  exact ⟨d, h⟩

theorem bel_lip (M : DetMDP S) (β : ℝ) (hβ : 0 ≤ β) (V W : S → ℝ) :
    dist (bel M β V) (bel M β W) ≤ β * dist V W := by
  rw [dist_pi_le_iff (by positivity)]
  intro s
  have key : ∀ (V W : S → ℝ), bel M β V s ≤ bel M β W s + β * dist V W := by
    intro V W
    obtain ⟨d, hd⟩ := bel_ex M β W s
    have h1 := bel_le M β V s d
    have h2 : V (M.next s d) - W (M.next s d) ≤ dist V W := by
      have := dist_le_pi_dist V W (M.next s d)
      rw [Real.dist_eq] at this
      exact (le_abs_self _).trans this
    rw [hd]
    nlinarith
  have k1 := key V W
  have k2 := key W V
  rw [dist_comm W V] at k2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

theorem bel_fix (M : DetMDP S) (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    ∃ V : S → ℝ, bel M β V = V := by
  have hK : ((Real.toNNReal β : NNReal) : ℝ) = β := Real.coe_toNNReal β hβ.1.le
  have hc : ContractingWith (Real.toNNReal β) (bel M β) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun V W => ?_⟩
    · rw [← NNReal.coe_lt_coe, hK]; simpa using hβ.2
    · rw [hK]; exact bel_lip M β hβ.1.le V W
  exact ⟨ContractingWith.fixedPoint (bel M β) hc, ContractingWith.fixedPoint_isFixedPt hc⟩

theorem bel_ineq (M : DetMDP S) (β : ℝ) (hβ : 0 ≤ β) (V : S → ℝ) (hV : bel M β V = V)
    (s₀ : S) (δ : M.Policy) : ∀ T, V s₀ ≤ ∑ t ∈ range T, β ^ t * M.stageCost s₀ δ t +
      β ^ T * V (M.path s₀ δ T) := by
  intro T
  induction T with
  | zero => simp [DetMDP.path]
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have h := bel_le M β V (M.path s₀ δ T) (δ (M.path s₀ δ T) T)
    rw [hV] at h
    have hp : M.path s₀ δ (T+1) = M.next (M.path s₀ δ T) (δ (M.path s₀ δ T) T) := rfl
    rw [hp]
    have hs : M.stageCost s₀ δ T = M.c (M.path s₀ δ T) (δ (M.path s₀ δ T) T) := rfl
    rw [hs]
    have hb : 0 ≤ β ^ T := pow_nonneg hβ T
    have := mul_le_mul_of_nonneg_left h hb
    calc V s₀ ≤ _ := ih
      _ ≤ _ := by rw [pow_succ]; nlinarith

theorem bel_eq (M : DetMDP S) (β : ℝ) (V : S → ℝ) (hV : bel M β V = V)
    (s₀ : S) (δ : M.Policy) (hδ : ∀ s t, V s = M.c s (δ s t) + β * V (M.next s (δ s t))) :
    ∀ T, V s₀ = ∑ t ∈ range T, β ^ t * M.stageCost s₀ δ t + β ^ T * V (M.path s₀ δ T) := by
  intro T
  induction T with
  | zero => simp [DetMDP.path]
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have h := hδ (M.path s₀ δ T) T
    have hp : M.path s₀ δ (T+1) = M.next (M.path s₀ δ T) (δ (M.path s₀ δ T) T) := rfl
    rw [hp]
    have hs : M.stageCost s₀ δ T = M.c (M.path s₀ δ T) (δ (M.path s₀ δ T) T) := rfl
    rw [hs]
    conv_lhs => rw [ih, h]
    rw [pow_succ]
    ring

theorem bel_lim (M : DetMDP S) (β : ℝ) (hβ : 0 < β ∧ β < 1) (V : S → ℝ) (s₀ : S)
    (δ : M.Policy) :
    Tendsto (fun T => ∑ t ∈ range T, β ^ t * M.stageCost s₀ δ t + β ^ T * V (M.path s₀ δ T))
      atTop (nhds (M.discCost β s₀ δ)) := by
  set cm : ℝ := ∑ p : (Σ s : S, M.D s), |M.c p.1 p.2|
  have hcm : ∀ s d, |M.c s d| ≤ cm := fun s d =>
    Finset.single_le_sum (f := fun p : (Σ s : S, M.D s) => |M.c p.1 p.2|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ ⟨s, d⟩)
  set CV : ℝ := ∑ s, |V s|
  have hCV : ∀ s, |V s| ≤ CV := fun s =>
    Finset.single_le_sum (f := fun s => |V s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  have hsum : Summable (fun t => β ^ t * M.stageCost s₀ δ t) := by
    apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ.1.le hβ.2).mul_right cm)
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ.1.le t)]
    exact mul_le_mul_of_nonneg_left (hcm _ _) (pow_nonneg hβ.1.le t)
  have h1 := hsum.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun T => β ^ T * V (M.path s₀ δ T)) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun T => β ^ T * CV)
    · intro T
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ.1.le T)]
      exact mul_le_mul_of_nonneg_left (hCV _) (pow_nonneg hβ.1.le T)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.1.le hβ.2).mul_const CV
  have := h1.add h2
  rw [add_zero] at this
  exact this
end

theorem solution {S : Type} [Fintype S] [DecidableEq S] (M : DetMDP S) (s₀ : S)
    (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    ∃ δ : M.Policy, M.IsStationary δ ∧ ∀ δ' : M.Policy, M.discCost β s₀ δ ≤ M.discCost β s₀ δ' := by
  obtain ⟨V, hV⟩ := bel_fix M β hβ
  let g : (s : S) → M.D s := fun s => Classical.choose (bel_ex M β V s)
  have hg : ∀ s, V s = M.c s (g s) + β * V (M.next s (g s)) := fun s => by
    have := Classical.choose_spec (bel_ex M β V s)
    exact (congrFun hV s).symm.trans this
  refine ⟨fun s _ => g s, fun s t => rfl, fun δ' => ?_⟩
  have e1 : M.discCost β s₀ (fun s _ => g s) = V s₀ := by
    have hl := bel_lim M β hβ V s₀ (fun s _ => g s)
    have heq := bel_eq M β V hV s₀ (fun s _ => g s) (fun s _ => hg s)
    have hl2 : Tendsto (fun T => ∑ t ∈ range T, β ^ t * M.stageCost s₀ (fun s _ => g s) t +
        β ^ T * V (M.path s₀ (fun s _ => g s) T)) atTop (nhds (V s₀)) := by
      simp_rw [← heq]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hl hl2
  rw [e1]
  exact ge_of_tendsto' (bel_lim M β hβ V s₀ δ') (bel_ineq M β hβ.1.le V hV s₀ δ')
