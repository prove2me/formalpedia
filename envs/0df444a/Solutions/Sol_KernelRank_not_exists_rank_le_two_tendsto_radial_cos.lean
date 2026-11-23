-- Prove2me | solution 1 for KernelRank.not_exists_rank_le_two_tendsto_radial_cos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:48:27.4701+00:00
-- url     : https://prove2.me/submissions/28ab60ae-b56c-49f7-bed2-b9151468c995

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same


section
open Complex Polynomial
open scoped Topology
namespace KernelRank
section LowerSemicontinuity
private lemma isSumOfProducts_mono {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X : ι → Type*} [Nonempty ι] {K : (∀ i, X i) → 𝕜} {m n : ℕ} (hmn : m ≤ n)
    (hK : IsSumOfProducts K m) : IsSumOfProducts K n := by
  obtain ⟨f, hf⟩ := hK
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨fun k i x => if h : (k : ℕ) < m then f ⟨k, h⟩ i x else 0, fun x => ?_⟩
  have h1 : (∑ k : Fin n, ∏ i : ι,
      (if h : (k : ℕ) < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜))) =
      ∑ k ∈ Finset.range n, ∏ i : ι, (if h : k < m then f ⟨k, h⟩ i (x i) else 0) :=
    Fin.sum_univ_eq_sum_range
      (fun k => ∏ i : ι, if h : k < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜)) n
  have h2 : (∑ k ∈ Finset.range m, ∏ i : ι,
      (if h : k < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜))) =
      ∑ k ∈ Finset.range n, ∏ i : ι, (if h : k < m then f ⟨k, h⟩ i (x i) else 0) := by
    refine Finset.sum_subset (Finset.range_mono hmn) fun k _ hk => ?_
    have hnot : ¬ k < m := by simpa using hk
    simp only [hnot, ↓reduceDIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) rfl
  have h3 : (∑ k : Fin m, ∏ i : ι, f k i (x i)) =
      ∑ k ∈ Finset.range m, ∏ i : ι, (if h : k < m then f ⟨k, h⟩ i (x i) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => ∏ i : ι, if h : k < m then f ⟨k, h⟩ i (x i) else (0 : 𝕜)) m]
    refine Finset.sum_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => ?_
    simp [k.isLt]
  rw [hf, h3, h2, ← h1]
end LowerSemicontinuity
section AdjugateBorderRank
private lemma trace_adjugate_mul_sq_nonneg_of_isSumOfProducts {X : Type*} {n : ℕ}
    {G : (Fin 3 → X) → ℝ} (hG : IsSumOfProducts G n) (u₀ u₁ : X) (p q : Fin n → X) :
    0 ≤ (((Matrix.of fun a b => G ![u₀, p a, q b]).adjugate *
          Matrix.of fun a b => G ![u₁, p a, q b]) *
        ((Matrix.of fun a b => G ![u₀, p a, q b]).adjugate *
          Matrix.of fun a b => G ![u₁, p a, q b])).trace := by
  obtain ⟨f, hf⟩ := hG
  let V : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a k => f k 1 (p a)
  let W : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k b => f k 2 (q b)
  let d₀ : Fin n → ℝ := fun k => f k 0 u₀
  let d₁ : Fin n → ℝ := fun k => f k 0 u₁
  let D₀ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d₀
  let D₁ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d₁
  have hS₀ : (Matrix.of fun a b => G ![u₀, p a, q b]) = V * D₀ * W := by
    ext a b
    dsimp only [D₀, Matrix.of_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, V, W, d₀, Matrix.of_apply, hf, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hS₁ : (Matrix.of fun a b => G ![u₁, p a, q b]) = V * D₁ * W := by
    ext a b
    dsimp only [D₁, Matrix.of_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, V, W, d₁, Matrix.of_apply, hf, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hS₀, hS₁]
  let c : Fin n → ℝ := fun k => (∏ j ∈ Finset.univ.erase k, d₀ j) * d₁ k
  have hD_adj : D₀.adjugate * D₁ = Matrix.diagonal c := by
    rw [Matrix.adjugate_diagonal, Matrix.diagonal_mul_diagonal]
  have hprod : (V * D₀ * W).adjugate * (V * D₁ * W) =
      V.det • (W.adjugate * Matrix.diagonal c * W) := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
    have hassoc : W.adjugate * (D₀.adjugate * V.adjugate) * (V * D₁ * W) =
        W.adjugate * D₀.adjugate * (V.adjugate * V) * D₁ * W := by
      simp [Matrix.mul_assoc]
    rw [hassoc, Matrix.adjugate_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      Algebra.smul_mul_assoc, mul_one, Matrix.mul_assoc W.adjugate D₀.adjugate D₁, hD_adj]
  rw [hprod, smul_mul_smul_comm]
  have hsq : (W.adjugate * Matrix.diagonal c * W) * (W.adjugate * Matrix.diagonal c * W) =
      W.det • (W.adjugate * Matrix.diagonal (fun k => c k * c k) * W) := by
    have hassoc : (W.adjugate * Matrix.diagonal c * W) * (W.adjugate * Matrix.diagonal c * W) =
        W.adjugate * Matrix.diagonal c * (W * W.adjugate) * Matrix.diagonal c * W := by
      simp [Matrix.mul_assoc]
    rw [hassoc, Matrix.mul_adjugate, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      Algebra.smul_mul_assoc, mul_one, Matrix.mul_assoc W.adjugate, Matrix.diagonal_mul_diagonal]
  rw [hsq, smul_smul, Matrix.trace_smul]
  have htr : (W.adjugate * Matrix.diagonal (fun k => c k * c k) * W).trace =
      W.det * ∑ k : Fin n, c k * c k := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_adjugate, Algebra.smul_mul_assoc,
      one_mul, Matrix.trace_smul, Matrix.trace_diagonal, smul_eq_mul]
  rw [htr, smul_eq_mul]
  have h1 : (V.det * V.det * W.det) * (W.det * ∑ k : Fin n, c k * c k) =
      (V.det * W.det) ^ 2 * ∑ k : Fin n, c k ^ 2 := by
    have hsum : (∑ k : Fin n, c k * c k) = ∑ k : Fin n, c k ^ 2 :=
      Finset.sum_congr rfl fun k _ => (sq (c k)).symm
    rw [hsum]
    ring
  rw [h1]
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)
private lemma not_exists_rank_le_tendsto_of_trace_adjugate_neg {X ι : Type*} {n : ℕ}
    {l : Filter ι} [l.NeBot] {F : ι → (Fin 3 → X) → ℝ} {K : (Fin 3 → X) → ℝ}
    (u₀ u₁ : X) (p q : Fin n → X)
    (hneg : (((Matrix.of fun a b => K ![u₀, p a, q b]).adjugate *
          Matrix.of fun a b => K ![u₁, p a, q b]) *
        ((Matrix.of fun a b => K ![u₀, p a, q b]).adjugate *
          Matrix.of fun a b => K ![u₁, p a, q b])).trace < 0)
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (n : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (K x))) : False := by
  let S₀ (G : (Fin 3 → X) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun a b => G ![u₀, p a, q b]
  let S₁ (G : (Fin 3 → X) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun a b => G ![u₁, p a, q b]
  let Φ (G : (Fin 3 → X) → ℝ) : ℝ := ((S₀ G).adjugate * S₁ G * ((S₀ G).adjugate * S₁ G)).trace
  have hΦ_tend : Filter.Tendsto (fun i => Φ (F i)) l (𝓝 (Φ K)) := by
    have hS₀_t : Filter.Tendsto (fun i => S₀ (F i)) l (𝓝 (S₀ K)) :=
      tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => htend ![u₀, p a, q b]
    have hS₁_t : Filter.Tendsto (fun i => S₁ (F i)) l (𝓝 (S₁ K)) :=
      tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => htend ![u₁, p a, q b]
    have hadj_cont : Continuous
        (Matrix.adjugate : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [Matrix.adjugate_apply]
      refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
      by_cases h : i = b
      · subst h; simp only [Matrix.updateRow_self]; fun_prop
      · simp only [Matrix.updateRow_ne h]
        exact (continuous_apply j).comp (continuous_apply i)
    have hM_t : Filter.Tendsto (fun i => (S₀ (F i)).adjugate * S₁ (F i)) l
        (𝓝 ((S₀ K).adjugate * S₁ K)) :=
      (hadj_cont.continuousAt.tendsto.comp hS₀_t).mul hS₁_t
    have hsq_t := hM_t.mul hM_t
    have htr_cont : Continuous (Matrix.trace : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
      unfold Matrix.trace Matrix.diag
      fun_prop
    exact htr_cont.continuousAt.tendsto.comp hsq_t
  have hΦ_nonneg : ∀ᶠ i in l, 0 ≤ Φ (F i) := by
    filter_upwards [hrank] with i hi
    have hex : ∃ N ≤ n, IsSumOfProducts (F i) N := by
      by_contra hno
      push Not at hno
      have hgt : ((n : ℕ) : ℕ∞) < separableRank (F i) := by
        have hle : ((n + 1 : ℕ) : ℕ∞) ≤ separableRank (F i) :=
          le_iInf₂ fun N hN => by
            have : n < N := lt_of_not_ge fun hNn => hno N hNn hN
            exact_mod_cast Nat.succ_le_of_lt this
        exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hle
      exact not_lt_of_ge hi hgt
    obtain ⟨N, hNn, hprodN⟩ := hex
    exact trace_adjugate_mul_sq_nonneg_of_isSumOfProducts (isSumOfProducts_mono hNn hprodN)
      u₀ u₁ p q
  exact not_lt_of_ge (ge_of_tendsto hΦ_tend hΦ_nonneg) hneg
end AdjugateBorderRank
section UniversalApproximation
end UniversalApproximation
end KernelRank
end

set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → (Fin 3 → ℝ) → ℝ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (2 : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (Real.cos (∑ j, x j ^ 2)))) : False := by
  let r : ℝ := Real.sqrt (Real.pi / 2)
  have hr_sq : r ^ 2 = Real.pi / 2 := Real.sq_sqrt (by positivity)
  let p : Fin 2 → ℝ := ![0, r]
  refine not_exists_rank_le_tendsto_of_trace_adjugate_neg 0 r p p ?_ hrank htend
  have hS₀ : (Matrix.of fun a b : Fin 2 => Real.cos (∑ j : Fin 3, (![0, p a, p b] j) ^ 2)) =
      !![(1 : ℝ), 0; 0, -1] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [p, Fin.sum_univ_three, hr_sq, add_halves, Real.cos_pi_div_two, Real.cos_pi]
  have hc3pi : Real.cos (Real.pi + Real.pi / 2) = 0 := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hS₁ : (Matrix.of fun a b : Fin 2 => Real.cos (∑ j : Fin 3, (![r, p a, p b] j) ^ 2)) =
      !![(0 : ℝ), -1; -1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [p, Fin.sum_univ_three, hr_sq, add_halves, Real.cos_pi_div_two, Real.cos_pi, hc3pi]
  rw [hS₀, hS₁, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num
end KernelRank
