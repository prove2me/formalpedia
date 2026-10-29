-- Prove2me | solution 1 for KallenbergLP.Bias.four_characterizations
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T23:50:53.658012+00:00
-- url     : https://prove2.me/submissions/74fb2a10-3724-480a-81ec-3afb76fc4bc7

import Mathlib
import Definitions.Def_KallenbergLP_Bias_Stationary

set_option autoImplicit false

open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace KB68

variable {n : Type} [Fintype n] [DecidableEq n]

lemma markov_pow (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (k : ℕ) :
    IsMarkovMatrix (P ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp [Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  | succ k ih =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih.1 i l) (hP.1 l j)
    · rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hP.2, mul_one]
      exact ih.2 i

lemma markov_le_one (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (i j : n) : P i j ≤ 1 := by
  rw [← hP.2 i]
  exact Finset.single_le_sum (fun l _ => hP.1 i l) (Finset.mem_univ j)

lemma cesaro_mem (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (N : ℕ) (i j : n) :
    cesaroMean P N i j ∈ Set.Icc (0 : ℝ) 1 := by
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  simp only [cesaroMean, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  constructor
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun k _ => (markov_pow P hP k).1 i j)
  · rw [inv_mul_le_iff₀ hpos]
    calc ∑ k ∈ Finset.range (N + 1), (P ^ k) i j ≤ ∑ k ∈ Finset.range (N + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => markov_le_one _ (markov_pow P hP k) i j
      _ = (N : ℝ) + 1 := by simp
      _ = ((N : ℝ) + 1) * 1 := by ring

lemma cesaro_mul_sub (P : Matrix n n ℝ) (N : ℕ) :
    cesaroMean P N * (1 - P) = ((N : ℝ) + 1)⁻¹ • (1 - P ^ (N + 1)) := by
  simp only [cesaroMean, Matrix.smul_mul]
  congr 1
  rw [Finset.sum_mul]
  induction N with
  | zero => simp [mul_sub]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, mul_sub, mul_one, ← pow_succ]; abel

lemma sub_mul_cesaro (P : Matrix n n ℝ) (N : ℕ) :
    (1 - P) * cesaroMean P N = ((N : ℝ) + 1)⁻¹ • (1 - P ^ (N + 1)) := by
  simp only [cesaroMean, Matrix.mul_smul]
  congr 1
  rw [Finset.mul_sum]
  induction N with
  | zero => simp [sub_mul]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, sub_mul, one_mul, ← pow_succ']; abel

/-- bounded matrices scaled by `1/(N+1)` tend to zero -/
lemma tendsto_inv_smul_bdd (A : ℕ → Matrix n n ℝ) (B : ℝ) (hA : ∀ N i j, |A N i j| ≤ B) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ • A N) atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * B) atTop (𝓝 0) := by
    simpa using h1.mul_const B
  refine squeeze_zero_norm (fun N => ?_) h2
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < ((N:ℝ)+1)⁻¹)]
  exact mul_le_mul_of_nonneg_left (hA N i j) (by positivity)

lemma one_sub_pow_bdd (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (N : ℕ) (i j : n) :
    |(1 - P ^ (N + 1)) i j| ≤ 2 := by
  have h1 := (markov_pow P hP (N+1)).1 i j
  have h2 := markov_le_one _ (markov_pow P hP (N+1)) i j
  simp only [Matrix.sub_apply, Matrix.one_apply]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma eq_of_mapClusterPt_tendsto {X : Type} [TopologicalSpace X] [T2Space X]
    {u : ℕ → X} {x y : X} (hx : MapClusterPt x atTop u) (hy : Tendsto u atTop (𝓝 y)) :
    x = y := by
  have : ClusterPt x (𝓝 y) := ClusterPt.mono hx hy
  exact eq_of_nhds_neBot this

theorem cesaro_tendsto (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) :
    Tendsto (cesaroMean P) atTop (𝓝 (limitMatrix P)) ∧
      P * limitMatrix P = limitMatrix P ∧ limitMatrix P * P = limitMatrix P ∧
      limitMatrix P * limitMatrix P = limitMatrix P := by
  set K : Set (Matrix n n ℝ) := Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1)
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ N, cesaroMean P N ∈ K := fun N i _ j _ => cesaro_mem P hP N i j
  have hL : Tendsto (fun N => cesaroMean P N * (1 - P)) atTop (𝓝 0) := by
    simp_rw [cesaro_mul_sub]; exact tendsto_inv_smul_bdd _ 2 (one_sub_pow_bdd P hP)
  have hR : Tendsto (fun N => (1 - P) * cesaroMean P N) atTop (𝓝 0) := by
    simp_rw [sub_mul_cesaro]; exact tendsto_inv_smul_bdd _ 2 (one_sub_pow_bdd P hP)
  -- properties of any cluster point
  have hcl : ∀ Q, MapClusterPt Q atTop (cesaroMean P) → P * Q = Q ∧ Q * P = Q := by
    intro Q hQ
    have h1 : MapClusterPt (Q * (1 - P)) atTop (fun N => cesaroMean P N * (1 - P)) :=
      hQ.continuousAt_comp (f := fun X => X * (1 - P)) (by fun_prop)
    have h2 : MapClusterPt ((1 - P) * Q) atTop (fun N => (1 - P) * cesaroMean P N) :=
      hQ.continuousAt_comp (f := fun X => (1 - P) * X) (by fun_prop)
    have e1 := eq_of_mapClusterPt_tendsto h1 hL
    have e2 := eq_of_mapClusterPt_tendsto h2 hR
    rw [mul_sub, mul_one, sub_eq_zero] at e1
    rw [sub_mul, one_mul, sub_eq_zero] at e2
    exact ⟨e2.symm, e1.symm⟩
  have hfix : ∀ Q, P * Q = Q → Q * P = Q → ∀ N, cesaroMean P N * Q = Q ∧ Q * cesaroMean P N = Q := by
    intro Q h1 h2 N
    have hp : ∀ k : ℕ, P ^ k * Q = Q ∧ Q * P ^ k = Q := by
      intro k; induction k with
      | zero => simp
      | succ k ih => exact ⟨by rw [pow_succ, Matrix.mul_assoc, h1, ih.1],
                            by rw [pow_succ', ← Matrix.mul_assoc, h2, ih.2]⟩
    have hpos : ((N : ℝ) + 1) ≠ 0 := by positivity
    constructor
    · simp only [cesaroMean, Matrix.smul_mul, Finset.sum_mul, (hp _).1, Finset.sum_const,
        Finset.card_range]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add, Nat.cast_one, inv_mul_cancel₀ hpos,
        one_smul]
    · simp only [cesaroMean, Matrix.mul_smul, Finset.mul_sum, (hp _).2, Finset.sum_const,
        Finset.card_range]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add, Nat.cast_one, inv_mul_cancel₀ hpos,
        one_smul]
  have huniq : ∀ Q Q', MapClusterPt Q atTop (cesaroMean P) → MapClusterPt Q' atTop (cesaroMean P) →
      Q = Q' := by
    intro Q Q' hQ hQ'
    obtain ⟨a1, a2⟩ := hcl Q hQ
    obtain ⟨b1, b2⟩ := hcl Q' hQ'
    -- Q' * Q = Q (cluster of C_N * Q = Q)
    have e1 : Q' * Q = Q := by
      have h := hQ'.continuousAt_comp (f := fun X => X * Q) (by fun_prop)
      have hc : (fun N => cesaroMean P N * Q) = fun _ => Q := funext fun N => (hfix Q a1 a2 N).1
      have : Tendsto ((fun X => X * Q) ∘ cesaroMean P) atTop (𝓝 Q) := by
        show Tendsto (fun N => cesaroMean P N * Q) atTop (𝓝 Q); rw [hc]; exact tendsto_const_nhds
      exact eq_of_mapClusterPt_tendsto h this
    have e2 : Q' * Q = Q' := by
      have h := hQ.continuousAt_comp (f := fun X => Q' * X) (by fun_prop)
      have hc : (fun N => Q' * cesaroMean P N) = fun _ => Q' := funext fun N => (hfix Q' b1 b2 N).2
      have : Tendsto ((fun X => Q' * X) ∘ cesaroMean P) atTop (𝓝 Q') := by
        show Tendsto (fun N => Q' * cesaroMean P N) atTop (𝓝 Q'); rw [hc]; exact tendsto_const_nhds
      exact eq_of_mapClusterPt_tendsto h this
    rw [← e1, e2]
  obtain ⟨Q0, -, hQ0⟩ := hK.exists_mapClusterPt (f := atTop) (u := cesaroMean P)
    (by rw [Filter.le_principal_iff, Filter.mem_map]; exact Filter.Eventually.of_forall hmem)
  have ht : Tendsto (cesaroMean P) atTop (𝓝 Q0) :=
    hK.tendsto_nhds_of_unique_mapClusterPt (Filter.Eventually.of_forall hmem)
      (fun x _ hx => huniq x Q0 hx hQ0)
  have hlim : limitMatrix P = Q0 := ht.limUnder_eq
  obtain ⟨c1, c2⟩ := hcl Q0 hQ0
  refine ⟨hlim ▸ ht, hlim ▸ c1, hlim ▸ c2, ?_⟩
  rw [hlim]
  have := ht.const_mul Q0
  have hc : (fun N => Q0 * cesaroMean P N) = fun _ => Q0 := funext fun N => (hfix Q0 c1 c2 N).2
  rw [hc] at this
  exact tendsto_nhds_unique this tendsto_const_nhds

lemma fund_unit (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) :
    IsUnit (1 - P + limitMatrix P).det := by
  obtain ⟨ht, h1, h2, h3⟩ := cesaro_tendsto P hP
  set Q := limitMatrix P
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hQA : Q * (1 - P + Q) = Q := by
    rw [mul_add, mul_sub, mul_one, h2, h3]; abel
  have hQx : Q *ᵥ x = 0 := by
    rw [← hQA, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have hPx : P *ᵥ x = x := by
    have : (1 - P + Q) *ᵥ x = x - P *ᵥ x + Q *ᵥ x := by
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hx, hQx, add_zero] at this
    exact (sub_eq_zero.1 this.symm).symm
  have hpow : ∀ k : ℕ, (P ^ k) *ᵥ x = x := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hPx, ih]
  have hC : ∀ N, cesaroMean P N *ᵥ x = x := by
    intro N
    have hpos : ((N : ℝ) + 1) ≠ 0 := by positivity
    simp only [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec, hpow, Finset.sum_const,
      Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add, Nat.cast_one, inv_mul_cancel₀ hpos,
      one_smul]
  have hlim : Tendsto (fun N => cesaroMean P N *ᵥ x) atTop (𝓝 (Q *ᵥ x)) :=
    ((continuous_id.matrix_mulVec continuous_const).tendsto Q).comp ht
  simp_rw [hC] at hlim
  have : x = Q *ᵥ x := tendsto_nhds_unique tendsto_const_nhds hlim
  exact hx0 (this.trans hQx)

/-- the exact Laurent identity -/
lemma laurent_identity (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (β : ℝ) (hβ : β ≠ 1)
    (hu : IsUnit (1 - β • (P - limitMatrix P)).det) :
    (1 - β • P)⁻¹ = (1 - β)⁻¹ • limitMatrix P + (1 - β • (P - limitMatrix P))⁻¹ - limitMatrix P := by
  obtain ⟨-, h1, h2, h3⟩ := cesaro_tendsto P hP
  set Q := limitMatrix P
  set X := (1 - β • (P - Q))⁻¹
  apply Matrix.inv_eq_right_inv
  have hX : (1 - β • (P - Q)) * X = 1 := Matrix.mul_nonsing_inv _ hu
  have hQX : Q * X = Q := by
    have hQ : Q * (1 - β • (P - Q)) = Q := by
      rw [mul_sub, mul_one, Matrix.mul_smul, mul_sub, h2, h3, sub_self, smul_zero, sub_zero]
    calc Q * X = Q * (1 - β • (P - Q)) * X := by rw [hQ]
      _ = Q := by rw [Matrix.mul_assoc, hX, mul_one]
  have hsplit : (1 - β • P) = (1 - β • (P - Q)) - β • Q := by
    rw [smul_sub]; abel
  have hb : (1 - β) ≠ 0 := sub_ne_zero.2 (Ne.symm hβ)
  have e1 : (1 - β • P) * Q = (1 - β) • Q := by
    rw [sub_mul, one_mul, Matrix.smul_mul, h1, sub_smul, one_smul]
  have e2 : (1 - β • P) * X = 1 - β • Q := by
    rw [hsplit, sub_mul, hX, Matrix.smul_mul, hQX]
  rw [mul_sub, mul_add, Matrix.mul_smul, e1, e2, smul_smul, inv_mul_cancel₀ hb, one_smul,
    sub_smul, one_smul]
  abel

lemma pow_mulVec_bdd (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (r : n → ℝ) (k : ℕ) (i : n) :
    |(P ^ k *ᵥ r) i| ≤ ∑ l, |r l| := by
  have hk := markov_pow P hP k
  simp only [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul, abs_of_nonneg (hk.1 i l)]
  exact mul_le_of_le_one_left (abs_nonneg _) (markov_le_one _ hk i l)

lemma geom_tsum (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (r : n → ℝ) (i : n) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (Y : Matrix n n ℝ) (hY : (1 - β • P) * Y = 1) :
    ∑' k : ℕ, β ^ k * (P ^ k *ᵥ r) i = (Y *ᵥ r) i := by
  have hY' : Y * (1 - β • P) = 1 := mul_eq_one_comm.1 hY
  set C := ∑ l, |r l|
  have hsum : Summable (fun k : ℕ => β ^ k * (P ^ k *ᵥ r) i) := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => β ^ k * C)
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_right C) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (pow_mulVec_bdd P hP r k i) (pow_nonneg hβ0 k)
  -- partial sums
  have hpart : ∀ T : ℕ, ∑ k ∈ Finset.range T, β ^ k * (P ^ k *ᵥ r) i =
      (Y *ᵥ r) i - β ^ T * ((Y * P ^ T) *ᵥ r) i := by
    intro T
    have hS : (∑ k ∈ Finset.range T, β ^ k • P ^ k) = Y - β ^ T • (Y * P ^ T) := by
      have h1 : (1 - β • P) * (∑ k ∈ Finset.range T, β ^ k • P ^ k) = 1 - β ^ T • P ^ T := by
        induction T with
        | zero => simp
        | succ T ih =>
          rw [Finset.sum_range_succ, mul_add, ih, sub_mul, one_mul, Matrix.smul_mul,
            Matrix.mul_smul, smul_smul, ← pow_succ', ← pow_succ']; abel
      calc (∑ k ∈ Finset.range T, β ^ k • P ^ k)
          = Y * ((1 - β • P) * (∑ k ∈ Finset.range T, β ^ k • P ^ k)) := by
            rw [← Matrix.mul_assoc, hY', one_mul]
        _ = Y - β ^ T • (Y * P ^ T) := by rw [h1, mul_sub, mul_one, Matrix.mul_smul]
    have := congrArg (fun A : Matrix n n ℝ => (A *ᵥ r) i) hS
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Finset.sum_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
    exact this
  have hlim : Tendsto (fun T : ℕ => ∑ k ∈ Finset.range T, β ^ k * (P ^ k *ᵥ r) i) atTop
      (𝓝 ((Y *ᵥ r) i)) := by
    simp_rw [hpart]
    conv => rhs; rw [← sub_zero ((Y *ᵥ r) i)]
    refine tendsto_const_nhds.sub ?_
    set B := ∑ j, |Y i j| * ∑ l, |r l|
    have hb : ∀ T : ℕ, |((Y * P ^ T) *ᵥ r) i| ≤ B := by
      intro T
      rw [← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct] at *
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (pow_mulVec_bdd P hP r T j) (abs_nonneg _)
    have hg : Tendsto (fun T : ℕ => β ^ T * B) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const B
    refine squeeze_zero_norm (fun T => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T)]
    exact mul_le_mul_of_nonneg_left (hb T) (pow_nonneg hβ0 T)
  exact tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim

/-- vector Laurent expansion near `β = 1` -/
theorem laurent_tendsto (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (r : n → ℝ) (i : n) :
    Tendsto (fun β : ℝ => (∑' k : ℕ, β ^ k * (P ^ k *ᵥ r) i) - (1 - β)⁻¹ * (limitMatrix P *ᵥ r) i)
      (𝓝[<] 1) (𝓝 ((((1 - P + limitMatrix P)⁻¹ - limitMatrix P) *ᵥ r) i)) := by
  set Q := limitMatrix P
  have hZ := fund_unit P hP
  have hcont : Continuous fun β : ℝ => 1 - β • (P - Q) := by fun_prop
  have h1 : (1 : Matrix n n ℝ) - (1 : ℝ) • (P - Q) = 1 - P + Q := by rw [one_smul]; abel
  have hdet : ∀ᶠ β in 𝓝 (1 : ℝ), IsUnit (1 - β • (P - Q)).det := by
    have hc : ContinuousAt (fun β : ℝ => (1 - β • (P - Q)).det) 1 :=
      (hcont.matrix_det).continuousAt
    have hne : (fun β : ℝ => (1 - β • (P - Q)).det) 1 ≠ 0 := by
      show (1 - (1 : ℝ) • (P - Q)).det ≠ 0
      rw [h1]; exact hZ.ne_zero
    filter_upwards [hc.eventually_ne hne] with β hβ
    exact isUnit_iff_ne_zero.2 hβ
  have hinv : Tendsto (fun β : ℝ => (1 - β • (P - Q))⁻¹) (𝓝 1) (𝓝 (1 - P + Q)⁻¹) := by
    have hca : ContinuousAt Inv.inv (1 - P + Q) := by
      apply continuousAt_matrix_inv
      rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
      exact continuousAt_inv₀ hZ.ne_zero
    have h2 := hcont.tendsto 1
    rw [h1] at h2
    exact hca.tendsto.comp h2
  have hev : ∀ᶠ β in 𝓝[<] (1 : ℝ),
      (∑' k : ℕ, β ^ k * (P ^ k *ᵥ r) i) - (1 - β)⁻¹ * (Q *ᵥ r) i =
        (((1 - β • (P - Q))⁻¹ - Q) *ᵥ r) i := by
    have hpos : ∀ᶠ β in 𝓝[<] (1 : ℝ), β ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hpos, nhdsWithin_le_nhds hdet] with β hβ hu
    have hβ1 : β ≠ 1 := hβ.2.ne
    have hL := laurent_identity P hP β hβ1 hu
    have hdetU : IsUnit (1 - β • P).det := by
      by_contra hn
      have hz : (1 - β • P).det = 0 := by simpa [isUnit_iff_ne_zero] using hn
      have hYr : (1 - β • P) * ((1 - β)⁻¹ • Q + (1 - β • (P - Q))⁻¹ - Q) = 1 := by
        obtain ⟨-, c1, c2, c3⟩ := cesaro_tendsto P hP
        have hX : (1 - β • (P - Q)) * (1 - β • (P - Q))⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
        have hQX : Q * (1 - β • (P - Q))⁻¹ = Q := by
          have hQ : Q * (1 - β • (P - Q)) = Q := by
            rw [mul_sub, mul_one, Matrix.mul_smul, mul_sub, c2, c3, sub_self, smul_zero, sub_zero]
          calc Q * (1 - β • (P - Q))⁻¹ = Q * (1 - β • (P - Q)) * (1 - β • (P - Q))⁻¹ := by rw [hQ]
            _ = Q := by rw [Matrix.mul_assoc, hX, mul_one]
        have hb : (1 - β) ≠ 0 := sub_ne_zero.2 (Ne.symm hβ1)
        have e1 : (1 - β • P) * Q = (1 - β) • Q := by
          rw [sub_mul, one_mul, Matrix.smul_mul, c1, sub_smul, one_smul]
        have e2 : (1 - β • P) * (1 - β • (P - Q))⁻¹ = 1 - β • Q := by
          have hsplit : (1 - β • P) = (1 - β • (P - Q)) - β • Q := by rw [smul_sub]; abel
          rw [hsplit, sub_mul, hX, Matrix.smul_mul, hQX]
        rw [mul_sub, mul_add, Matrix.mul_smul, e1, e2, smul_smul, inv_mul_cancel₀ hb, one_smul,
          sub_smul, one_smul]
        abel
      have := congrArg Matrix.det hYr
      rw [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    have hYY : (1 - β • P) * (1 - β • P)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdetU
    rw [geom_tsum P hP r i β hβ.1.le hβ.2 _ hYY, hL]
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have := ((hinv.sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds :
    Tendsto (fun β : ℝ => (1 - β • (P - Q))⁻¹ - Q) (𝓝[<] 1) (𝓝 ((1 - P + Q)⁻¹ - Q)))
  exact (((continuous_id.matrix_mulVec continuous_const).tendsto _).comp this |>.apply_nhds i)

/-- the EReal trichotomy criterion -/
lemma ereal_crit {ι : Type} {l : Filter ι} [NeBot l] (x g ε : ι → ℝ) (a b : ℝ)
    (hg : Tendsto g l atTop) (hε : Tendsto ε l (𝓝 0)) (hx : ∀ᶠ t in l, x t = g t * a + b + ε t) :
    (∃ L : EReal, Tendsto (fun t => (x t : EReal)) l (𝓝 L) ∧ 0 ≤ L) ↔ (0 < a ∨ (a = 0 ∧ 0 ≤ b)) := by
  have hbe : Tendsto (fun t => b + ε t) l (𝓝 b) := by simpa using hε.const_add b
  have hx' : ∀ᶠ t in l, x t = g t * a + (b + ε t) := by
    filter_upwards [hx] with t ht; rw [ht]; ring
  rcases lt_trichotomy a 0 with ha | ha | ha
  · -- limit is ⊥
    have hbot : Tendsto (fun t => (x t : EReal)) l (𝓝 ⊥) := by
      rw [EReal.tendsto_nhds_bot_iff_real]
      intro y
      have h1 : Tendsto (fun t => g t * a) l atBot := hg.atTop_mul_const_of_neg ha
      have h2 : Tendsto (fun t => g t * a + (b + ε t)) l atBot := h1.atBot_add hbe
      filter_upwards [h2.eventually_lt_atBot y, hx'] with t ht hxt
      rw [hxt]; exact_mod_cast ht
    constructor
    · rintro ⟨L, hL, h0⟩
      have := tendsto_nhds_unique hL hbot
      rw [this] at h0; exact absurd h0 (by simp)
    · rintro (h | ⟨h, -⟩) <;> linarith
  · subst ha
    have hb : Tendsto (fun t => (x t : EReal)) l (𝓝 (b : EReal)) := by
      apply EReal.tendsto_coe.2
      refine hbe.congr' ?_
      filter_upwards [hx'] with t ht; rw [ht]; ring
    constructor
    · rintro ⟨L, hL, h0⟩
      have := tendsto_nhds_unique hL hb
      rw [this] at h0
      exact Or.inr ⟨rfl, by exact_mod_cast h0⟩
    · rintro (h | ⟨-, h⟩)
      · exact absurd h (lt_irrefl 0)
      · exact ⟨b, hb, by exact_mod_cast h⟩
  · have htop : Tendsto (fun t => (x t : EReal)) l (𝓝 ⊤) := by
      rw [EReal.tendsto_nhds_top_iff_real]
      intro y
      have h1 : Tendsto (fun t => g t * a) l atTop := hg.atTop_mul_const ha
      have h2 : Tendsto (fun t => g t * a + (b + ε t)) l atTop := h1.atTop_add hbe
      filter_upwards [h2.eventually_gt_atTop y, hx'] with t ht hxt
      rw [hxt]; exact_mod_cast ht
    exact ⟨fun _ => Or.inl ha, fun _ => ⟨⊤, htop, le_top⟩⟩

lemma fund_props (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) :
    (1 - P) * ((1 - P + limitMatrix P)⁻¹ - limitMatrix P) = 1 - limitMatrix P ∧
      limitMatrix P * ((1 - P + limitMatrix P)⁻¹ - limitMatrix P) = 0 := by
  obtain ⟨-, h1, h2, h3⟩ := cesaro_tendsto P hP
  set Q := limitMatrix P
  have hZ := fund_unit P hP
  set Z := (1 - P + Q)⁻¹
  have hZ1 : (1 - P + Q) * Z = 1 := Matrix.mul_nonsing_inv _ hZ
  have hQZ : Q * Z = Q := by
    have hQ : Q * (1 - P + Q) = Q := by rw [mul_add, mul_sub, mul_one, h2, h3]; abel
    calc Q * Z = Q * (1 - P + Q) * Z := by rw [hQ]
      _ = Q := by rw [Matrix.mul_assoc, hZ1, mul_one]
  constructor
  · have e : (1 - P) * Z = 1 - Q * Z := by
      have h := hZ1; rw [add_mul] at h; exact eq_sub_of_add_eq h
    rw [mul_sub, e, hQZ, sub_mul, one_mul, h1, sub_self, sub_zero]
  · rw [mul_sub, hQZ, h3, sub_self]

/-- cumulative identity `∑_{s<m} P^s = m Q + D - P^m D` -/
lemma cumul_identity (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (m : ℕ) :
    ∑ s ∈ Finset.range m, P ^ s = (m : ℝ) • limitMatrix P +
      ((1 - P + limitMatrix P)⁻¹ - limitMatrix P) -
      P ^ m * ((1 - P + limitMatrix P)⁻¹ - limitMatrix P) := by
  obtain ⟨-, h1, h2, h3⟩ := cesaro_tendsto P hP
  obtain ⟨hD, -⟩ := fund_props P hP
  set Q := limitMatrix P
  set D := (1 - P + Q)⁻¹ - Q
  have hpQ : ∀ s : ℕ, P ^ s * Q = Q := by
    intro s; induction s with
    | zero => simp
    | succ s ih => rw [pow_succ, Matrix.mul_assoc, h1, ih]
  have htel : (∑ s ∈ Finset.range m, P ^ s) * (1 - P) = 1 - P ^ m := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, add_mul, ih, mul_sub, mul_one, ← pow_succ]; abel
  have key : (∑ s ∈ Finset.range m, P ^ s) * (1 - Q) = (1 - P ^ m) * D := by
    rw [← hD, ← Matrix.mul_assoc, htel]
  have hsQ : (∑ s ∈ Finset.range m, P ^ s) * Q = (m : ℝ) • Q := by
    rw [Finset.sum_mul]; simp_rw [hpQ]
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [mul_sub, mul_one, hsQ, sub_mul, one_mul] at key
  rw [add_sub_assoc, ← key]; abel

/-- shifted Cesàro averages of `P^{t+1} w` converge to `Q w` -/
lemma shifted_cesaro (P : Matrix n n ℝ) (hP : IsMarkovMatrix P) (w : n → ℝ) (i : n) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, (P ^ (t + 1) *ᵥ w) i) atTop
      (𝓝 ((limitMatrix P *ᵥ w) i)) := by
  obtain ⟨ht, -⟩ := cesaro_tendsto P hP
  have hC : Tendsto (fun T : ℕ => (cesaroMean P T *ᵥ w) i) atTop (𝓝 ((limitMatrix P *ᵥ w) i)) :=
    (((continuous_id.matrix_mulVec continuous_const).tendsto _).comp ht).apply_nhds i
  have hinv : Tendsto (fun T : ℕ => (T : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun T : ℕ => (1 + (T : ℝ)⁻¹) * (cesaroMean P T *ᵥ w) i - (T : ℝ)⁻¹ * w i)
      atTop (𝓝 ((limitMatrix P *ᵥ w) i)) := by
    have := (((tendsto_const_nhds (x := (1:ℝ))).add hinv).mul hC).sub (hinv.mul_const (w i))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  have hpos : ((T : ℝ) + 1) ≠ 0 := by positivity
  have hsum : ((T : ℝ) + 1) * (cesaroMean P T *ᵥ w) i =
      ∑ t ∈ Finset.range T, (P ^ (t + 1) *ᵥ w) i + w i := by
    simp only [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    rw [← mul_assoc, mul_inv_cancel₀ hpos, one_mul, Finset.sum_range_succ']
    simp
  have : (1 + (T : ℝ)⁻¹) = (T : ℝ)⁻¹ * ((T : ℝ) + 1) := by field_simp
  rw [this, mul_assoc, hsum]; ring

end KB68

open Filter Topology Matrix BlackwellDiscreteDP.NearOne KallenbergLP.Bias

namespace KF68

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

lemma hist_ext {n : ℕ} {h h' : History N α n} (hs : h.states = h'.states)
    (hc : h.chosen = h'.chosen) : h = h' := by
  cases h; cases h'; cases hs; cases hc; rfl

def hext {n : ℕ} (h : History N α n) (a : α) (j : Fin N) : History N α (n + 1) where
  states := fun i => if hi : i.val < n + 1 then h.states ⟨i.val, hi⟩ else j
  chosen := fun i => if hi : i.val < n then h.chosen ⟨i.val, hi⟩ else a

def htrunc {n : ℕ} (h : History N α (n + 1)) : History N α n where
  states := fun i => h.states ⟨i.val, by omega⟩
  chosen := fun i => h.chosen ⟨i.val, by omega⟩

def histEquiv (n : ℕ) : History N α (n + 1) ≃ History N α n × α × Fin N where
  toFun h := (htrunc h, h.chosen (Fin.last n), h.last)
  invFun p := hext p.1 p.2.1 p.2.2
  left_inv h := by
    apply hist_ext
    · funext i
      simp only [hext, htrunc, History.last]
      split_ifs with hi
      · rfl
      · congr 1; ext; simp only; omega
    · funext i
      simp only [hext, htrunc]
      split_ifs with hi
      · rfl
      · congr 1; ext; simp only [Fin.val_last]; omega
  right_inv p := by
    obtain ⟨h, a, j⟩ := p
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · apply hist_ext
      · funext i; simp only [hext, htrunc]; rw [dif_pos (by omega)]
      · funext i; simp only [hext, htrunc]; rw [dif_pos (by omega)]
    · simp [hext]
    · simp [hext, History.last]

def hist0Equiv : History N α 0 ≃ Fin N where
  toFun h := h.last
  invFun j := ⟨fun _ => j, fun i => i.elim0⟩
  left_inv h := by
    apply hist_ext
    · funext i
      have : i = ⟨0, by omega⟩ := Fin.ext (by have := i.isLt; omega)
      subst this; rfl
    · funext i; exact i.elim0
  right_inv j := rfl

lemma hext_prefix_castSucc {n : ℕ} (h : History N α n) (a : α) (j : Fin N) (k : Fin n) :
    (hext h a j).prefix k.castSucc = h.prefix k := by
  apply hist_ext
  · funext i
    simp only [History.prefix, hext]
    rw [dif_pos (by have hi := i.isLt; have hk := k.isLt; simp only [Fin.val_castSucc] at hi; omega)]
  · funext i
    simp only [History.prefix, hext]
    rw [dif_pos (by have hi := i.isLt; have hk := k.isLt; simp only [Fin.val_castSucc] at hi; omega)]

lemma hext_prefix_last {n : ℕ} (h : History N α n) (a : α) (j : Fin N) :
    (hext h a j).prefix (Fin.last n) = h := by
  apply hist_ext
  · funext i
    simp only [History.prefix, hext]
    rw [dif_pos (by have hi := i.isLt; simp only [Fin.val_last] at hi; omega)]; rfl
  · funext i
    simp only [History.prefix, hext]
    rw [dif_pos (by have hi := i.isLt; simp only [Fin.val_last] at hi; omega)]; rfl

variable (M : MDP N α)

lemma historyProb_hext (R : Policy M) (i : Fin N) {n : ℕ} (h : History N α n) (a : α)
    (j : Fin N) :
    historyProb M R i (n + 1) (hext h a j) =
      historyProb M R i n h * (R.choose n h a * M.transition h.last a j) := by
  unfold historyProb
  rw [Fin.prod_univ_castSucc]
  have h0 : (hext h a j).states ⟨0, by omega⟩ = h.states ⟨0, by omega⟩ := by
    simp only [hext]; rw [dif_pos (by omega)]
  have hp : ∀ k : Fin n,
      R.choose (k.castSucc : Fin (n + 1)).val ((hext h a j).prefix k.castSucc)
          ((hext h a j).chosen k.castSucc) *
        M.transition ((hext h a j).states ⟨(k.castSucc : Fin (n + 1)).val, by omega⟩)
          ((hext h a j).chosen k.castSucc)
          ((hext h a j).states ⟨(k.castSucc : Fin (n + 1)).val + 1, by omega⟩) =
      R.choose k (h.prefix k) (h.chosen k) *
        M.transition (h.states ⟨k.val, by omega⟩) (h.chosen k) (h.states ⟨k.val + 1, by omega⟩) := by
    intro k
    rw [hext_prefix_castSucc]
    simp only [hext, Fin.val_castSucc]
    rw [dif_pos (show k.val < n + 1 by omega), dif_pos (show k.val + 1 < n + 1 by omega),
      dif_pos k.isLt]
  have hl : R.choose (Fin.last n).val ((hext h a j).prefix (Fin.last n))
        ((hext h a j).chosen (Fin.last n)) *
      M.transition ((hext h a j).states ⟨(Fin.last n).val, by omega⟩)
        ((hext h a j).chosen (Fin.last n))
        ((hext h a j).states ⟨(Fin.last n).val + 1, by omega⟩) =
      R.choose n h a * M.transition h.last a j := by
    rw [hext_prefix_last]
    simp only [hext, Fin.val_last, History.last]
    rw [dif_neg (lt_irrefl n), dif_pos (by omega), dif_neg (by omega)]
  rw [h0, Finset.prod_congr rfl (fun k _ => hp k), hl]
  ring

lemma historyProb_nonneg (R : Policy M) (i : Fin N) (n : ℕ) (h : History N α n) :
    0 ≤ historyProb M R i n h := by
  unfold historyProb
  refine mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun k _ => ?_)
  by_cases ha : h.chosen k ∈ M.actions (h.states ⟨k.val, by omega⟩)
  · exact mul_nonneg (R.choose_nonneg _ _ _) (M.transition_nonneg _ _ _ ha)
  · rw [R.choose_outside _ _ _ ha, zero_mul]

/-- state marginal -/
noncomputable def stateProb (R : Policy M) (i : Fin N) (n : ℕ) (j : Fin N) : ℝ :=
  ∑ h : History N α n, if h.last = j then historyProb M R i n h else 0

lemma occ_nonneg (R : Policy M) (i j : Fin N) (a : α) (n : ℕ) :
    0 ≤ occupancy M R i j a n := by
  unfold occupancy
  refine Finset.sum_nonneg fun h _ => ?_
  split_ifs
  · exact mul_nonneg (historyProb_nonneg M R i n h) (R.choose_nonneg _ _ _)
  · exact le_rfl

lemma occ_outside (R : Policy M) (i j : Fin N) (a : α) (n : ℕ) (ha : a ∉ M.actions j) :
    occupancy M R i j a n = 0 := by
  unfold occupancy
  refine Finset.sum_eq_zero fun h _ => ?_
  split_ifs with hj
  · rw [R.choose_outside _ _ _ (hj ▸ ha), mul_zero]
  · rfl

lemma sum_occ (R : Policy M) (i j : Fin N) (n : ℕ) :
    ∑ a, occupancy M R i j a n = stateProb M R i n j := by
  unfold occupancy stateProb
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs
  · rw [← Finset.mul_sum, R.choose_sum_one, mul_one]
  · simp

lemma stateProb_zero (R : Policy M) (i j : Fin N) :
    stateProb M R i 0 j = if j = i then 1 else 0 := by
  unfold stateProb
  rw [← (hist0Equiv (α := α)).symm.sum_comp]
  simp only [hist0Equiv, Equiv.coe_fn_symm_mk, History.last, historyProb]
  simp [Finset.sum_ite_eq', eq_comm]

lemma stateProb_succ (R : Policy M) (i : Fin N) (n : ℕ) (j : Fin N) :
    stateProb M R i (n + 1) j =
      ∑ k, ∑ a, occupancy M R i k a n * M.transition k a j := by
  have hs : ∀ p : History N α n × α × Fin N,
      (histEquiv (α := α) n).symm p = hext p.1 p.2.1 p.2.2 := fun p => rfl
  have hl : ∀ (h : History N α n) (a : α) (j' : Fin N), (hext h a j').last = j' := by
    intro h a j'; simp [hext, History.last]
  have lhs : stateProb M R i (n + 1) j = ∑ h : History N α n, ∑ a,
      historyProb M R i n h * (R.choose n h a * M.transition h.last a j) := by
    unfold stateProb
    rw [← (histEquiv (α := α) n).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, hs, hl, historyProb_hext, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [lhs]
  symm
  calc _ = ∑ a, ∑ k, ∑ h : History N α n, (if h.last = k then
          historyProb M R i n h * R.choose n h a * M.transition k a j else 0) := by
          unfold occupancy; simp only [Finset.sum_mul, ite_mul, zero_mul]; exact Finset.sum_comm
    _ = ∑ a, ∑ h : History N α n, ∑ k, (if h.last = k then
          historyProb M R i n h * R.choose n h a * M.transition k a j else 0) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ h : History N α n, ∑ a, ∑ k, (if h.last = k then
          historyProb M R i n h * R.choose n h a * M.transition k a j else 0) := Finset.sum_comm
    _ = _ := by
          refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ, if_true]; ring

lemma stateProb_nonneg (R : Policy M) (i : Fin N) (n : ℕ) (j : Fin N) :
    0 ≤ stateProb M R i n j := by
  rw [← sum_occ]; exact Finset.sum_nonneg fun a _ => occ_nonneg M R i j a n

lemma stateProb_sum (R : Policy M) (i : Fin N) (n : ℕ) :
    ∑ j, stateProb M R i n j = 1 := by
  induction n with
  | zero => simp [stateProb_zero]
  | succ n ih =>
    simp only [stateProb_succ]
    rw [Finset.sum_comm]
    rw [← ih]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm, ← sum_occ]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.mul_sum]
    by_cases ha : a ∈ M.actions k
    · rw [M.transition_sum_one k a ha, mul_one]
    · rw [occ_outside M R i k a n ha, zero_mul]

lemma stateProb_le_one (R : Policy M) (i : Fin N) (n : ℕ) (j : Fin N) :
    stateProb M R i n j ≤ 1 := by
  rw [← stateProb_sum M R i n]
  exact Finset.single_le_sum (fun k _ => stateProb_nonneg M R i n k) (Finset.mem_univ j)

lemma occ_le_one (R : Policy M) (i j : Fin N) (a : α) (n : ℕ) :
    occupancy M R i j a n ≤ 1 := by
  refine le_trans ?_ (stateProb_le_one M R i n j)
  rw [← sum_occ]
  exact Finset.single_le_sum (fun b _ => occ_nonneg M R i j b n) (Finset.mem_univ a)

lemma periodReward_bdd (R : Policy M) (i : Fin N) (n : ℕ) :
    |periodReward M R i n| ≤ ∑ j, ∑ a, |M.reward j a| := by
  unfold periodReward
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul, abs_of_nonneg (occ_nonneg M R i j a n)]
  exact mul_le_of_le_one_left (abs_nonneg _) (occ_le_one M R i j a n)

/-! pure policies -/

lemma occ_pure (f : PureRule M) (i j : Fin N) (a : α) (n : ℕ) :
    occupancy M (purePolicy M f) i j a n =
      stateProb M (purePolicy M f) i n j * (if a = f.choose j then 1 else 0) := by
  unfold occupancy stateProb
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs with h1 h2 h2 <;> simp_all [purePolicy]

lemma stationary_markov (f : PureRule M) : IsMarkovMatrix (stationaryMatrix M f) :=
  ⟨fun i j => M.transition_nonneg _ _ _ (f.admissible i),
   fun i => M.transition_sum_one _ _ (f.admissible i)⟩

lemma stateProb_pure (f : PureRule M) (i : Fin N) (n : ℕ) (j : Fin N) :
    stateProb M (purePolicy M f) i n j = (stationaryMatrix M f ^ n) i j := by
  induction n generalizing j with
  | zero =>
    rw [stateProb_zero, pow_zero, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij)]
  | succ n ih =>
    rw [stateProb_succ, pow_succ, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [occ_pure, ih, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, stationaryMatrix]

lemma periodReward_pure (f : PureRule M) (i : Fin N) (n : ℕ) :
    periodReward M (purePolicy M f) i n =
      ((stationaryMatrix M f ^ n) *ᵥ stationaryReward M f) i := by
  unfold periodReward
  simp only [occ_pure, stateProb_pure, Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, stationaryReward]

/-! discounted telescoping and optimality over all policies -/

lemma summable_geom_bdd (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (u : ℕ → ℝ) (C : ℝ)
    (hu : ∀ n, |u n| ≤ C) : Summable (fun n => β ^ n * u n) :=
  Summable.of_norm_bounded (g := fun n : ℕ => β ^ n * C)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right C) (fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n)]
      exact mul_le_mul_of_nonneg_left (hu n) (pow_nonneg hβ0 n))

lemma W_bdd (R : Policy M) (i : Fin N) (v : Fin N → ℝ) (n : ℕ) :
    |∑ j, stateProb M R i n j * v j| ≤ ∑ j, |v j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg (stateProb_nonneg M R i n j)]
  exact mul_le_of_le_one_left (abs_nonneg _) (stateProb_le_one M R i n j)

noncomputable def bellGap (β : ℝ) (v : Fin N → ℝ) (j : Fin N) (a : α) : ℝ :=
  M.reward j a + β * ∑ k, M.transition j a k * v k - v j

lemma gap_identity (R : Policy M) (i : Fin N) (β : ℝ) (v : Fin N → ℝ) (n : ℕ) :
    ∑ j, ∑ a, occupancy M R i j a n * bellGap M β v j a =
      periodReward M R i n + β * ∑ k, stateProb M R i (n + 1) k * v k -
        ∑ j, stateProb M R i n j * v j := by
  have e1 : ∀ j, ∑ a, occupancy M R i j a n * (β * ∑ k, M.transition j a k * v k) =
      ∑ k, ∑ a, β * (occupancy M R i j a n * M.transition j a k * v k) := by
    intro j; simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_; ring
  have t2 : ∑ j, ∑ a, occupancy M R i j a n * (β * ∑ k, M.transition j a k * v k) =
      β * ∑ k, stateProb M R i (n + 1) k * v k := by
    rw [Finset.sum_congr rfl fun j _ => e1 j, Finset.sum_comm]
    simp only [stateProb_succ, Finset.sum_mul, Finset.mul_sum]
  have t3 : ∑ j, ∑ a, occupancy M R i j a n * v j = ∑ j, stateProb M R i n j * v j := by
    simp only [← sum_occ, Finset.sum_mul]
  have e : ∀ j a, occupancy M R i j a n * bellGap M β v j a =
      occupancy M R i j a n * M.reward j a +
        occupancy M R i j a n * (β * ∑ k, M.transition j a k * v k) -
        occupancy M R i j a n * v j := by
    intro j a; unfold bellGap; ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [t2, t3]
  rfl

lemma gap_summable (R : Policy M) (i : Fin N) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (v : Fin N → ℝ) :
    Summable (fun n => β ^ n * ∑ j, ∑ a, occupancy M R i j a n * bellGap M β v j a) := by
  refine summable_geom_bdd β hβ0 hβ1 _ (∑ j, ∑ a, |bellGap M β v j a|) fun n => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul, abs_of_nonneg (occ_nonneg M R i j a n)]
  exact mul_le_of_le_one_left (abs_nonneg _) (occ_le_one M R i j a n)

noncomputable def Wv (R : Policy M) (i : Fin N) (v : Fin N → ℝ) (n : ℕ) : ℝ :=
  ∑ j, stateProb M R i n j * v j

lemma disc_telescope (R : Policy M) (i : Fin N) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (v : Fin N → ℝ) :
    discountedReward M R i β = v i +
      ∑' n : ℕ, β ^ n * ∑ j, ∑ a, occupancy M R i j a n * bellGap M β v j a := by
  have hW0 : Wv M R i v 0 = v i := by
    unfold Wv; simp only [stateProb_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']; simp
  have hs1 : Summable (fun n => β ^ n * periodReward M R i n) :=
    summable_geom_bdd β hβ0 hβ1 _ _ (periodReward_bdd M R i)
  have hs2 : Summable (fun n => β ^ n * Wv M R i v n) :=
    summable_geom_bdd β hβ0 hβ1 _ _ (W_bdd M R i v)
  have hs3 : Summable (fun n => β ^ (n + 1) * Wv M R i v (n + 1)) :=
    (summable_nat_add_iff (f := fun n => β ^ n * Wv M R i v n) 1).2 hs2
  have hz : ∑' n : ℕ, β ^ n * Wv M R i v n =
      β ^ 0 * Wv M R i v 0 + ∑' n : ℕ, β ^ (n + 1) * Wv M R i v (n + 1) :=
    hs2.tsum_eq_zero_add
  have hterm : ∀ n, β ^ n * ∑ j, ∑ a, occupancy M R i j a n * bellGap M β v j a =
      (β ^ n * periodReward M R i n + β ^ (n + 1) * Wv M R i v (n + 1)) -
        β ^ n * Wv M R i v n := by
    intro n; rw [gap_identity]; unfold Wv; ring
  have hfun : (fun n : ℕ => β ^ n * ∑ j, ∑ a, occupancy M R i j a n * bellGap M β v j a) =
      fun n => (β ^ n * periodReward M R i n + β ^ (n + 1) * Wv M R i v (n + 1)) -
        β ^ n * Wv M R i v n := funext hterm
  rw [hfun, Summable.tsum_sub (hs1.add hs3) hs2, Summable.tsum_add hs1 hs3, hz, hW0,
    pow_zero, one_mul]
  unfold discountedReward
  ring

lemma periodReward_pure_succ (f : PureRule M) (j : Fin N) (n : ℕ) :
    periodReward M (purePolicy M f) j (n + 1) =
      ∑ k, M.transition j (f.choose j) k * periodReward M (purePolicy M f) k n := by
  simp only [periodReward_pure]
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

lemma bellman_pure (f : PureRule M) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (j : Fin N) :
    discountedReward M (purePolicy M f) j β =
      M.reward j (f.choose j) +
        β * ∑ k, M.transition j (f.choose j) k * discountedReward M (purePolicy M f) k β := by
  have hs : ∀ k, Summable (fun n => β ^ n * periodReward M (purePolicy M f) k n) :=
    fun k => summable_geom_bdd β hβ0 hβ1 _ _ (periodReward_bdd M _ k)
  unfold discountedReward
  rw [(hs j).tsum_eq_zero_add]
  have h0 : periodReward M (purePolicy M f) j 0 = M.reward j (f.choose j) := by
    rw [periodReward_pure, pow_zero, Matrix.one_mulVec]; rfl
  have hstep : ∀ n, β ^ (n + 1) * periodReward M (purePolicy M f) j (n + 1) =
      ∑ k, β * (M.transition j (f.choose j) k *
        (β ^ n * periodReward M (purePolicy M f) k n)) := by
    intro n; rw [periodReward_pure_succ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  simp only [hstep, pow_zero, one_mul, h0]
  rw [Summable.tsum_finsetSum (fun k _ => ((hs k).mul_left _).mul_left _)]
  simp only [tsum_mul_left, Finset.mul_sum]

lemma bellGap_pure_zero (f : PureRule M) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (l : Fin N) :
    bellGap M β (fun k => discountedReward M (purePolicy M f) k β) l (f.choose l) = 0 := by
  unfold bellGap; rw [← bellman_pure M f β hβ0 hβ1 l]; ring

lemma pureRule_finite : Finite (PureRule M) :=
  Finite.of_injective (fun f : PureRule M => f.choose) (by
    intro f g h; cases f; cases g; simp only [PureRule.mk.injEq]; exact h)

lemma pureRule_nonempty : Nonempty (PureRule M) :=
  ⟨⟨fun i => (M.actions_nonempty i).choose, fun i => (M.actions_nonempty i).choose_spec⟩⟩

lemma exists_disc_opt (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ f : PureRule M, ∀ (R : Policy M) (i : Fin N),
      discountedReward M R i β ≤ discountedReward M (purePolicy M f) i β := by
  have := pureRule_finite M; have := pureRule_nonempty M
  obtain ⟨f, hf⟩ := Finite.exists_max
    (fun f : PureRule M => ∑ i, discountedReward M (purePolicy M f) i β)
  refine ⟨f, ?_⟩
  set v : Fin N → ℝ := fun k => discountedReward M (purePolicy M f) k β with hv
  have hgap : ∀ j a, a ∈ M.actions j → bellGap M β v j a ≤ 0 := by
    intro j a ha
    by_contra hpos
    push Not at hpos
    let g : PureRule M := ⟨Function.update f.choose j a, fun k => by
      by_cases hk : k = j
      · subst hk; simp [ha]
      · simp [hk, f.admissible k]⟩
    have hg0 : ∀ l, 0 ≤ bellGap M β v l (g.choose l) := by
      intro l
      by_cases hl : l = j
      · subst hl; simp only [g, Function.update_self]; exact hpos.le
      · have : g.choose l = f.choose l := by simp [g, hl]
        rw [this, hv, bellGap_pure_zero M f β hβ0 hβ1 l]
    have hterm : ∀ k n, 0 ≤ β ^ n * ∑ l, ∑ b,
        occupancy M (purePolicy M g) k l b n * bellGap M β v l b := by
      intro k n
      refine mul_nonneg (pow_nonneg hβ0 n) (Finset.sum_nonneg fun l _ =>
        Finset.sum_nonneg fun b _ => ?_)
      rw [occ_pure]
      by_cases hb : b = g.choose l
      · rw [if_pos hb, mul_one, hb]
        exact mul_nonneg (stateProb_nonneg M _ k n l) (hg0 l)
      · rw [if_neg hb, mul_zero, zero_mul]
    have hVg : ∀ k, v k ≤ discountedReward M (purePolicy M g) k β := by
      intro k
      rw [disc_telescope M _ k β hβ0 hβ1 v]
      have ht : 0 ≤ ∑' n : ℕ, β ^ n * ∑ l, ∑ b,
          occupancy M (purePolicy M g) k l b n * bellGap M β v l b := tsum_nonneg (hterm k)
      linarith
    have hVj : v j < discountedReward M (purePolicy M g) j β := by
      rw [disc_telescope M _ j β hβ0 hβ1 v]
      have h0 := (gap_summable M (purePolicy M g) j β hβ0 hβ1 v).le_tsum 0
        (fun m _ => hterm j m)
      have hz : β ^ 0 * ∑ l, ∑ b, occupancy M (purePolicy M g) j l b 0 * bellGap M β v l b =
          bellGap M β v j a := by
        simp [occ_pure, stateProb_zero, g]
      linarith
    have hlt : ∑ i, v i < ∑ i, discountedReward M (purePolicy M g) i β :=
      Finset.sum_lt_sum (fun k _ => hVg k) ⟨j, Finset.mem_univ _, hVj⟩
    exact absurd (hf g) (not_le.2 hlt)
  intro R i
  rw [disc_telescope M R i β hβ0 hβ1 v]
  have : ∑' n : ℕ, β ^ n * ∑ j, ∑ a, occupancy M R i j a n * bellGap M β v j a ≤ 0 := by
    refine tsum_nonpos fun n => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ0 n)
      (Finset.sum_nonpos fun j _ => Finset.sum_nonpos fun a _ => ?_)
    by_cases ha : a ∈ M.actions j
    · exact mul_nonpos_of_nonneg_of_nonpos (occ_nonneg M R i j a n) (hgap j a ha)
    · rw [occ_outside M R i j a n ha, zero_mul]
  linarith

lemma optDisc_eq (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ f : PureRule M, ∀ i : Fin N,
      optimalDiscounted M i β = discountedReward M (purePolicy M f) i β ∧
      ∀ R : Policy M, discountedReward M R i β ≤ discountedReward M (purePolicy M f) i β := by
  obtain ⟨f, hf⟩ := exists_disc_opt M β hβ0 hβ1
  refine ⟨f, fun i => ⟨?_, fun R => hf R i⟩⟩
  unfold optimalDiscounted
  apply IsGreatest.csSup_eq
  exact ⟨⟨purePolicy M f, rfl⟩, by rintro x ⟨R, rfl⟩; exact hf R i⟩

end KF68

namespace KA68

open KallenbergLP.Bias

lemma crit_lower {ι : Type} {l : Filter ι} [NeBot l] (x g ε y : ι → ℝ) (a b : ℝ)
    (hg : Tendsto g l atTop) (hε : Tendsto ε l (𝓝 0)) (hy : Tendsto y l (𝓝 0))
    (hx : ∀ t, x t = g t * a + b + ε t) (hxy : ∀ᶠ t in l, y t ≤ x t) :
    0 < a ∨ (a = 0 ∧ 0 ≤ b) := by
  have hbe : Tendsto (fun t => b + ε t) l (𝓝 b) := by simpa using hε.const_add b
  rcases lt_trichotomy a 0 with ha | ha | ha
  · exfalso
    have h1 : Tendsto (fun t => g t * a) l atBot := hg.atTop_mul_const_of_neg ha
    have h2 : Tendsto x l atBot := by
      have := h1.atBot_add hbe
      refine this.congr' (Eventually.of_forall fun t => ?_)
      simp only [hx]; ring
    obtain ⟨t, ht1, ht2, ht3⟩ := ((h2.eventually (eventually_lt_atBot (-1))).and
      ((hy.eventually (lt_mem_nhds (show (-1:ℝ) < 0 by norm_num))).and hxy)).exists
    linarith
  · right
    refine ⟨ha, le_of_tendsto_of_tendsto hy hbe ?_⟩
    filter_upwards [hxy] with t ht
    rw [hx, ha] at ht
    simpa using ht
  · left; exact ha

lemma crit_upper {ι : Type} {l : Filter ι} (x g ε : ι → ℝ) (a b : ℝ)
    (hg : Tendsto g l atTop) (hε : Tendsto ε l (𝓝 0))
    (hx : ∀ t, x t = g t * a + b + ε t) (hab : 0 < a ∨ (a = 0 ∧ 0 ≤ b)) (δ : ℝ)
    (hδ : 0 < δ) : ∀ᶠ t in l, -δ ≤ x t := by
  have hbe : Tendsto (fun t => b + ε t) l (𝓝 b) := by simpa using hε.const_add b
  rcases hab with ha | ⟨ha, hb⟩
  · have h1 : Tendsto (fun t => g t * a) l atTop := hg.atTop_mul_const ha
    have h2 : Tendsto x l atTop := by
      have := h1.atTop_add hbe
      refine this.congr' (Eventually.of_forall fun t => ?_)
      simp only [hx]; ring
    filter_upwards [h2.eventually (eventually_ge_atTop (-δ))] with t ht using ht
  · filter_upwards [hbe.eventually (lt_mem_nhds (show b - δ < b by linarith))] with t ht
    rw [hx, ha]
    simp only [mul_zero, zero_add]
    linarith

lemma one_sub_tendsto : Tendsto (fun β : ℝ => 1 - β) (𝓝[<] 1) (𝓝 0) := by
  have : Tendsto (fun β : ℝ => 1 - β) (𝓝 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub tendsto_id
  rw [sub_self] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma inv_one_sub_tendsto : Tendsto (fun β : ℝ => (1 - β)⁻¹) (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun β : ℝ => 1 - β) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ one_sub_tendsto ?_
    filter_upwards [self_mem_nhdsWithin] with β hβ
    simp only [Set.mem_Ioi, sub_pos]
    exact hβ
  exact tendsto_inv_nhdsGT_zero.comp h1

lemma abel_lower (c : ℕ → ℝ) (K : ℝ) (hc : ∀ n, |c n| ≤ K) (a : ℝ) (T0 : ℕ)
    (hS : ∀ T ≥ T0, a * T ≤ ∑ n ∈ Finset.range T, c n) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ β in 𝓝[<] (1 : ℝ), a - δ ≤ (1 - β) * ∑' n : ℕ, β ^ n * c n := by
  set K' : ℝ := K + |a| with hK'
  have hd : ∀ n, |c n - a| ≤ K' := fun n => (abs_sub _ _).trans (add_le_add (hc n) le_rfl)
  have hK'0 : 0 ≤ K' := (abs_nonneg _).trans (hd 0)
  set D : ℕ → ℝ := fun T => ∑ n ∈ Finset.range T, (c n - a) with hDdef
  have hD : ∀ T, |D T| ≤ T * K' := by
    intro T
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun n _ => hd n).trans ?_)
    simp
  have hD0 : ∀ T ≥ T0, 0 ≤ D T := by
    intro T hT
    have := hS T hT
    simp only [D, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith
  set B : ℝ := T0 * (T0 * K') with hB
  have hlim : Tendsto (fun β : ℝ => (1 - β) ^ 2 * B) (𝓝[<] 1) (𝓝 0) := by
    have := (one_sub_tendsto.pow 2).mul_const B
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds hδ), Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)]
    with β hβB hβ
  obtain ⟨hβ0, hβ1⟩ := hβ
  have hβn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  have hsc : Summable (fun n => β ^ n * c n) := KF68.summable_geom_bdd β hβ0.le hβ1 c K hc
  have hsD : Summable (fun n => β ^ n * D n) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => ((n : ℝ) ^ 1 * β ^ n) * K')
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hβn).mul_right K') (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 n), pow_one]
    nlinarith [hD n, pow_pos hβ0 n]
  have hsD1 : Summable (fun n => β ^ n * D (n + 1)) := by
    have h := ((summable_nat_add_iff (f := fun n => β ^ n * D n) 1).2 hsD).mul_left β⁻¹
    refine h.congr fun n => ?_
    simp only [pow_succ]
    field_simp
  have hgeo : ∑' n : ℕ, β ^ n = (1 - β)⁻¹ := tsum_geometric_of_lt_one hβ0.le hβ1
  have hsg := summable_geometric_of_lt_one hβ0.le hβ1
  -- ∑' β^n c_n = a/(1-β) + (1-β) ∑' β^n D(n+1)
  have hDz : ∑' n : ℕ, β ^ n * D n = β * ∑' n : ℕ, β ^ n * D (n + 1) := by
    rw [hsD.tsum_eq_zero_add]
    simp only [D, Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_succ]
    rw [← tsum_mul_left]
    congr 1; funext n; ring
  have hcd : ∀ n, β ^ n * c n = a * β ^ n + (β ^ n * D (n + 1) - β ^ n * D n) := by
    intro n
    simp only [D, Finset.sum_range_succ]
    ring
  have hsum : ∑' n : ℕ, β ^ n * c n =
      a * (1 - β)⁻¹ + (1 - β) * ∑' n : ℕ, β ^ n * D (n + 1) := by
    rw [tsum_congr hcd, Summable.tsum_add (hsg.mul_left a) (hsD1.sub hsD),
      Summable.tsum_sub hsD1 hsD, tsum_mul_left, hgeo, hDz]
    ring
  have hne : (1 - β) ≠ 0 := by linarith
  have hlow : -B ≤ ∑' n : ℕ, β ^ n * D (n + 1) := by
    have h1 := hsD1.sum_le_tsum (Finset.range T0) (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      exact mul_nonneg (pow_pos hβ0 n).le (hD0 (n + 1) (by omega)))
    refine le_trans ?_ h1
    have hterm : ∀ n ∈ Finset.range T0, -((T0 : ℝ) * K') ≤ β ^ n * D (n + 1) := by
      intro n hn
      simp only [Finset.mem_range] at hn
      have hb : |β ^ n * D (n + 1)| ≤ (T0 : ℝ) * K' := by
        rw [abs_mul, abs_of_pos (pow_pos hβ0 n)]
        have hpow : β ^ n ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
        have hn' : ((n + 1 : ℕ) : ℝ) ≤ T0 := by exact_mod_cast hn
        calc β ^ n * |D (n + 1)| ≤ 1 * (((n + 1 : ℕ) : ℝ) * K') :=
              mul_le_mul hpow (hD (n + 1)) (abs_nonneg _) zero_le_one
          _ ≤ T0 * K' := by rw [one_mul]; exact mul_le_mul_of_nonneg_right hn' hK'0
      exact (abs_le.1 hb).1
    calc -B = ∑ n ∈ Finset.range T0, -((T0 : ℝ) * K') := by
          simp [hB]
      _ ≤ _ := Finset.sum_le_sum hterm
  rw [hsum, mul_add, ← mul_assoc, mul_comm (1 - β) a, mul_assoc, mul_inv_cancel₀ hne, mul_one,
    ← mul_assoc, ← pow_two]
  have : (1 - β) ^ 2 * (-B) ≤ (1 - β) ^ 2 * ∑' n : ℕ, β ^ n * D (n + 1) :=
    mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
  linarith

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α] (M : MDP N α)

lemma disc_pure_eq (f : PureRule M) (i : Fin N) (β : ℝ) :
    discountedReward M (purePolicy M f) i β =
      ∑' k : ℕ, β ^ k * ((stationaryMatrix M f) ^ k *ᵥ stationaryReward M f) i := by
  unfold discountedReward; simp only [KF68.periodReward_pure]

lemma laurent_pure (f : PureRule M) (i : Fin N) :
    Tendsto (fun β : ℝ => discountedReward M (purePolicy M f) i β - (1 - β)⁻¹ * gain M f i)
      (𝓝[<] 1) (𝓝 (bias M f i)) := by
  simp only [disc_pure_eq]
  exact KB68.laurent_tendsto _ (KF68.stationary_markov M f) _ i

lemma disc_diff (f g : PureRule M) (i : Fin N) :
    Tendsto (fun β : ℝ =>
      (discountedReward M (purePolicy M f) i β - (1 - β)⁻¹ * gain M f i - bias M f i) -
      (discountedReward M (purePolicy M g) i β - (1 - β)⁻¹ * gain M g i - bias M g i))
      (𝓝[<] 1) (𝓝 0) := by
  have hf := tendsto_sub_nhds_zero_iff.2 (laurent_pure M f i)
  have hg := tendsto_sub_nhds_zero_iff.2 (laurent_pure M g i)
  simpa using hf.sub hg

lemma clause2_iff (fStar f : PureRule M) (i : Fin N) :
    (∃ L : EReal,
      Tendsto (fun β : ℝ => ((discountedReward M (purePolicy M fStar) i β -
        discountedReward M (purePolicy M f) i β : ℝ) : EReal))
        (nhdsWithin 1 (Set.Iio 1)) (nhds L) ∧ 0 ≤ L) ↔
      (0 < gain M fStar i - gain M f i ∨
        (gain M fStar i - gain M f i = 0 ∧ 0 ≤ bias M fStar i - bias M f i)) := by
  refine KB68.ereal_crit (fun β => discountedReward M (purePolicy M fStar) i β -
    discountedReward M (purePolicy M f) i β) (fun β : ℝ => (1 - β)⁻¹) _ _ _
    inv_one_sub_tendsto (disc_diff M fStar f i) (Eventually.of_forall fun β => ?_)
  ring

lemma sum_range_succ_cast (T : ℕ) :
    ∑ t ∈ Finset.range T, ((t : ℝ) + 1) = (T : ℝ) * (T + 1) / 2 := by
  induction T with
  | zero => simp
  | succ T ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma cumul_pure (f : PureRule M) (i : Fin N) (m : ℕ) :
    ∑ s ∈ Finset.range m, periodReward M (purePolicy M f) i s =
      (m : ℝ) * gain M f i + bias M f i -
        ((stationaryMatrix M f) ^ m *ᵥ
          (deviationMatrix (stationaryMatrix M f) *ᵥ stationaryReward M f)) i := by
  have key : ∀ (A B C : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ),
      (((m : ℝ) • A + B - C * B) *ᵥ v) i =
        (m : ℝ) * (A *ᵥ v) i + (B *ᵥ v) i - (C *ᵥ (B *ᵥ v)) i := by
    intro A B C v
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hs : ∑ s ∈ Finset.range m, ((stationaryMatrix M f ^ s) *ᵥ stationaryReward M f) i =
      ((∑ s ∈ Finset.range m, stationaryMatrix M f ^ s) *ᵥ stationaryReward M f) i := by
    simp only [Matrix.sum_mulVec, Finset.sum_apply]
  simp only [KF68.periodReward_pure]
  rw [hs, KB68.cumul_identity _ (KF68.stationary_markov M f) m, key]
  rfl

lemma limit_dev_zero (f : PureRule M) (i : Fin N) :
    (limitMatrix (stationaryMatrix M f) *ᵥ
      (deviationMatrix (stationaryMatrix M f) *ᵥ stationaryReward M f)) i = 0 := by
  rw [Matrix.mulVec_mulVec]
  unfold deviationMatrix
  rw [(KB68.fund_props _ (KF68.stationary_markov M f)).2]
  simp

lemma clause4_iff (fStar f : PureRule M) (i : Fin N) :
    (∃ L : EReal,
      Tendsto (fun T : ℕ => (cesaroRewardDifference M fStar f i T : EReal)) atTop (nhds L) ∧
        0 ≤ L) ↔
      (0 < gain M fStar i - gain M f i ∨
        (gain M fStar i - gain M f i = 0 ∧ 0 ≤ bias M fStar i - bias M f i)) := by
  have hS := KB68.shifted_cesaro _ (KF68.stationary_markov M fStar)
    (deviationMatrix (stationaryMatrix M fStar) *ᵥ stationaryReward M fStar) i
  have hP := KB68.shifted_cesaro _ (KF68.stationary_markov M f)
    (deviationMatrix (stationaryMatrix M f) *ᵥ stationaryReward M f) i
  rw [limit_dev_zero] at hS hP
  have hpt : ∀ t : ℕ, ∑ s ∈ Finset.range (t + 1),
      (periodReward M (purePolicy M fStar) i s - periodReward M (purePolicy M f) i s) =
      ((t : ℝ) + 1) * (gain M fStar i - gain M f i) + (bias M fStar i - bias M f i) +
        (((stationaryMatrix M f) ^ (t + 1) *ᵥ
          (deviationMatrix (stationaryMatrix M f) *ᵥ stationaryReward M f)) i -
         ((stationaryMatrix M fStar) ^ (t + 1) *ᵥ
          (deviationMatrix (stationaryMatrix M fStar) *ᵥ stationaryReward M fStar)) i) := by
    intro t
    rw [Finset.sum_sub_distrib, cumul_pure, cumul_pure]
    push_cast; ring
  refine KB68.ereal_crit (fun T => cesaroRewardDifference M fStar f i T)
    (fun T : ℕ => ((T : ℝ) + 1) / 2) _ _ _ ?_ ((hP.sub hS).trans (by rw [sub_zero])) ?_
  · exact Tendsto.atTop_div_const (by norm_num)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    unfold cesaroRewardDifference
    simp only [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, sum_range_succ_cast,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_sub_distrib]
    field_simp

lemma avg_pure (f : PureRule M) (i : Fin N) :
    averageReward M (purePolicy M f) i = gain M f i := by
  unfold averageReward
  apply Tendsto.liminf_eq
  simp only [KF68.periodReward_pure]
  obtain ⟨ht, -⟩ := KB68.cesaro_tendsto _ (KF68.stationary_markov M f)
  have hC : Tendsto (fun T : ℕ => (cesaroMean (stationaryMatrix M f) T *ᵥ
      stationaryReward M f) i) atTop
      (𝓝 ((limitMatrix (stationaryMatrix M f) *ᵥ stationaryReward M f) i)) :=
    (((continuous_id.matrix_mulVec continuous_const).tendsto _).comp ht).apply_nhds i
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hC.congr (fun T => ?_)
  unfold cesaroMean
  simp only [Matrix.smul_mulVec, Matrix.sum_mulVec, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  push_cast
  rfl

lemma gain_le_max (i : Fin N) : ∃ f0 : PureRule M, ∀ f : PureRule M, gain M f i ≤ gain M f0 i := by
  have := KF68.pureRule_finite M
  have := KF68.pureRule_nonempty M
  exact Finite.exists_max (fun f : PureRule M => gain M f i)

lemma avg_le (R : Policy M) (i : Fin N) (f0 : PureRule M)
    (hf0 : ∀ f : PureRule M, gain M f i ≤ gain M f0 i) :
    averageReward M R i ≤ gain M f0 i := by
  by_contra hlt
  push Not at hlt
  set A := averageReward M R i with hA
  set G := gain M f0 i with hG
  set ε := (A - G) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set K := ∑ j, ∑ a, |M.reward j a| with hK
  have hc : ∀ n, |periodReward M R i n| ≤ K := KF68.periodReward_bdd M R i
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hc 0)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun T : ℕ => (T : ℝ)⁻¹ * ∑ n ∈ Finset.range T, periodReward M R i n) := by
    refine isBoundedUnder_of ⟨-K, fun T => ?_⟩
    have : |(T : ℝ)⁻¹ * ∑ n ∈ Finset.range T, periodReward M R i n| ≤ K := by
      rw [abs_mul, abs_inv, Nat.abs_cast]
      rcases Nat.eq_zero_or_pos T with h | h
      · subst h; simp [hK0]
      · rw [inv_mul_le_iff₀ (by exact_mod_cast h)]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun n _ => hc n).trans ?_)
        simp
    exact (abs_le.1 this).1
  have hev := eventually_lt_of_lt_liminf (show A - ε < liminf (fun T : ℕ => (T : ℝ)⁻¹ *
      ∑ n ∈ Finset.range T, periodReward M R i n) atTop from by
        rw [hA]; unfold averageReward; linarith) hbdd
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 hev
  have hS : ∀ T ≥ max T0 1, (A - ε) * T ≤ ∑ n ∈ Finset.range T, periodReward M R i n := by
    intro T hT
    have h1 := hT0 T (le_of_max_le_left hT)
    have hTpos : (0 : ℝ) < T := by
      have : 1 ≤ T := le_of_max_le_right hT
      exact_mod_cast this
    rw [inv_mul_eq_div, lt_div_iff₀ hTpos] at h1
    linarith
  have hab := abel_lower (fun n => periodReward M R i n) K hc (A - ε) (max T0 1) hS ε hεpos
  have hup : ∀ f : PureRule M, ∀ᶠ β in 𝓝[<] (1:ℝ),
      (1 - β) * discountedReward M (purePolicy M f) i β ≤ gain M f i + ε := by
    intro f
    have h2 := one_sub_tendsto.mul (laurent_pure M f i)
    rw [zero_mul] at h2
    filter_upwards [h2.eventually (gt_mem_nhds hεpos), self_mem_nhdsWithin] with β hβ hβ1
    have hne : 1 - β ≠ 0 := by
      have : β < 1 := hβ1
      linarith
    have e1 : (1 - β) * ((1 - β)⁻¹ * gain M f i) = gain M f i := by
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    have : (1 - β) * discountedReward M (purePolicy M f) i β = gain M f i +
        (1 - β) * (discountedReward M (purePolicy M f) i β - (1 - β)⁻¹ * gain M f i) := by
      rw [mul_sub, e1]; ring
    linarith
  have hall : ∀ᶠ β in 𝓝[<] (1:ℝ), ∀ f : PureRule M,
      (1 - β) * discountedReward M (purePolicy M f) i β ≤ gain M f i + ε := by
    have := KF68.pureRule_finite M
    exact Filter.eventually_all.2 hup
  obtain ⟨β, hβa, hβall, hβ01⟩ :=
    (hab.and (hall.and (Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)))).exists
  obtain ⟨fβ, hfβ⟩ := KF68.exists_disc_opt M β hβ01.1.le hβ01.2
  have h1 := hfβ R i
  have h2 := hβall fβ
  have h3 := hf0 fβ
  have hpos : 0 < 1 - β := by linarith [hβ01.2]
  have h4 : (1 - β) * discountedReward M R i β ≤
      (1 - β) * discountedReward M (purePolicy M fβ) i β := mul_le_mul_of_nonneg_left h1 hpos.le
  have h5 : (1 - β) * ∑' n : ℕ, β ^ n * periodReward M R i n =
      (1 - β) * discountedReward M R i β := rfl
  linarith

lemma optAvg (i : Fin N) : (∀ f : PureRule M, gain M f i ≤ optimalAverage M i) ∧
    ∃ f0 : PureRule M, gain M f0 i = optimalAverage M i := by
  obtain ⟨f0, hf0⟩ := gain_le_max M i
  have hG : IsGreatest {x : ℝ | ∃ R : Policy M, x = averageReward M R i} (gain M f0 i) :=
    ⟨⟨purePolicy M f0, (avg_pure M f0 i).symm⟩, by
      rintro x ⟨R, rfl⟩; exact avg_le M R i f0 hf0⟩
  have h := hG.csSup_eq
  unfold optimalAverage
  rw [h]
  exact ⟨hf0, f0, rfl⟩

lemma clause3_iff (fStar : PureRule M) :
    ((∀ i : Fin N, gain M fStar i = optimalAverage M i) ∧
      ∀ (i : Fin N) (f : PureRule M),
        gain M f i = optimalAverage M i → bias M f i ≤ bias M fStar i) ↔
      ∀ (f : PureRule M) (i : Fin N), (0 < gain M fStar i - gain M f i ∨
        (gain M fStar i - gain M f i = 0 ∧ 0 ≤ bias M fStar i - bias M f i)) := by
  constructor
  · rintro ⟨h1, h2⟩ f i
    have hle := (optAvg M i).1 f
    rw [← h1 i] at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · left; linarith
    · right
      refine ⟨by linarith, ?_⟩
      have := h2 i f (by rw [heq, h1 i])
      linarith
  · intro hG
    have hg : ∀ i, gain M fStar i = optimalAverage M i := by
      intro i
      obtain ⟨hb, f0, hf0⟩ := optAvg M i
      have h1 := hb fStar
      rcases hG f0 i with h | ⟨h, -⟩ <;> linarith
    refine ⟨hg, fun i f hf => ?_⟩
    rcases hG f i with h | ⟨-, h⟩
    · linarith [hg i]
    · linarith

lemma clause1_iff (fStar : PureRule M) :
    IsBiasOptimal M (purePolicy M fStar) ↔
      ∀ (f : PureRule M) (i : Fin N), (0 < gain M fStar i - gain M f i ∨
        (gain M fStar i - gain M f i = 0 ∧ 0 ≤ bias M fStar i - bias M f i)) := by
  have hrep : ∀ (f : PureRule M) (i : Fin N) (β : ℝ),
      discountedReward M (purePolicy M fStar) i β - discountedReward M (purePolicy M f) i β =
      (1 - β)⁻¹ * (gain M fStar i - gain M f i) + (bias M fStar i - bias M f i) +
      ((discountedReward M (purePolicy M fStar) i β - (1 - β)⁻¹ * gain M fStar i -
          bias M fStar i) -
        (discountedReward M (purePolicy M f) i β - (1 - β)⁻¹ * gain M f i - bias M f i)) := by
    intros; ring
  have hev01 : ∀ᶠ β in 𝓝[<] (1:ℝ), β ∈ Set.Ioo 0 1 := Ioo_mem_nhdsLT (by norm_num)
  constructor
  · intro hB f i
    refine crit_lower
      (fun β => discountedReward M (purePolicy M fStar) i β -
        discountedReward M (purePolicy M f) i β)
      (fun β : ℝ => (1 - β)⁻¹) _
      (fun β => discountedReward M (purePolicy M fStar) i β - optimalDiscounted M i β) _ _
      inv_one_sub_tendsto (disc_diff M fStar f i) (hB i) (hrep f i) ?_
    filter_upwards [hev01] with β hβ
    obtain ⟨fβ, hfβ⟩ := KF68.optDisc_eq M β hβ.1.le hβ.2
    rw [(hfβ i).1]
    have := (hfβ i).2 (purePolicy M f)
    linarith
  · intro hG i
    rw [tendsto_order]
    refine ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
    · have hall : ∀ᶠ β in 𝓝[<] (1:ℝ), ∀ f : PureRule M,
          -(-(a' / 2)) ≤ discountedReward M (purePolicy M fStar) i β -
            discountedReward M (purePolicy M f) i β := by
        have := KF68.pureRule_finite M
        refine Filter.eventually_all.2 fun f => ?_
        exact crit_upper
          (fun β => discountedReward M (purePolicy M fStar) i β -
            discountedReward M (purePolicy M f) i β)
          (fun β : ℝ => (1 - β)⁻¹) _ _ _ inv_one_sub_tendsto (disc_diff M fStar f i)
          (hrep f i) (hG f i) (-(a' / 2)) (by linarith)
      filter_upwards [hall, hev01] with β hβ hβ01
      obtain ⟨fβ, hfβ⟩ := KF68.optDisc_eq M β hβ01.1.le hβ01.2
      rw [(hfβ i).1]
      have := hβ fβ
      linarith
    · filter_upwards [hev01] with β hβ01
      obtain ⟨fβ, hfβ⟩ := KF68.optDisc_eq M β hβ01.1.le hβ01.2
      rw [(hfβ i).1]
      have := (hfβ i).2 (purePolicy M fStar)
      linarith

lemma pairwise4 {p1 p2 p3 p4 G : Prop} (h1 : p1 ↔ G) (h2 : p2 ↔ G) (h3 : p3 ↔ G)
    (h4 : p4 ↔ G) : [p1, p2, p3, p4].Pairwise (· ↔ ·) := by
  rw [propext h1, propext h2, propext h3, propext h4]
  simp
  exact fun a h => h.symm

end KA68

open KallenbergLP.Bias Filter in
theorem solution {N : ℕ} {α : Type}
    [Fintype α] [DecidableEq α] (M : MDP N α) (fStar : PureRule M) :
    [
      IsBiasOptimal M (purePolicy M fStar),
      (∀ (f : PureRule M) (i : Fin N),
        ∃ L : EReal,
          Tendsto (fun β : ℝ =>
            ((discountedReward M (purePolicy M fStar) i β -
              discountedReward M (purePolicy M f) i β : ℝ) : EReal))
            (nhdsWithin 1 (Set.Iio 1)) (nhds L) ∧ 0 ≤ L),
      ((∀ i : Fin N, gain M fStar i = optimalAverage M i) ∧
        ∀ (i : Fin N) (f : PureRule M),
          gain M f i = optimalAverage M i → bias M f i ≤ bias M fStar i),
      (∀ (f : PureRule M) (i : Fin N),
        ∃ L : EReal,
          Tendsto (fun T : ℕ => (cesaroRewardDifference M fStar f i T : EReal))
            atTop (nhds L) ∧ 0 ≤ L)
    ].Pairwise (· ↔ ·) := by
  exact KA68.pairwise4 (KA68.clause1_iff M fStar)
    (forall_congr' fun f => forall_congr' fun i => KA68.clause2_iff M fStar f i)
    (KA68.clause3_iff M fStar)
    (forall_congr' fun f => forall_congr' fun i => KA68.clause4_iff M fStar f i)
