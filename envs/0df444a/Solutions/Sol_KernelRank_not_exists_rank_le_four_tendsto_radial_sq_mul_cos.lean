-- Prove2me | solution 1 for KernelRank.not_exists_rank_le_four_tendsto_radial_sq_mul_cos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:48:58.471084+00:00
-- url     : https://prove2.me/submissions/b3336ab3-2138-460f-a66d-98e911615570

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
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (4 : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l
      (𝓝 ((∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2)))) : False := by
  obtain ⟨h, hh_eq⟩ : ∃ h : ℝ, h = Real.pi / 2 := ⟨Real.pi / 2, rfl⟩
  have hh_pos : 0 < h := by rw [hh_eq]; positivity
  let p : Fin 4 → ℝ := ![0, Real.sqrt h, Real.sqrt (2 * h), Real.sqrt (3 * h)]
  refine not_exists_rank_le_tendsto_of_trace_adjugate_neg 0 (Real.sqrt h) p p ?_ hrank htend
  have hs1 : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh_pos.le
  have hs2 : Real.sqrt (2 * h) ^ 2 = 2 * h := Real.sq_sqrt (by positivity)
  have hs3 : Real.sqrt (3 * h) ^ 2 = 3 * h := Real.sq_sqrt (by positivity)
  have hc1 : Real.cos h = 0 := by rw [hh_eq]; exact Real.cos_pi_div_two
  have hc2 : Real.cos (2 * h) = -1 := by
    have : 2 * h = Real.pi := by rw [hh_eq]; ring
    rw [this, Real.cos_pi]
  have hc3 : Real.cos (3 * h) = 0 := by
    have : 3 * h = Real.pi + Real.pi / 2 := by rw [hh_eq]; ring
    rw [this, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hc4 : Real.cos (4 * h) = 1 := by
    have : 4 * h = 2 * Real.pi := by rw [hh_eq]; ring
    rw [this, Real.cos_two_pi]
  have hc5 : Real.cos (5 * h) = 0 := by
    have : 5 * h = h + 2 * Real.pi := by rw [hh_eq]; ring
    rw [this, Real.cos_add_two_pi, hc1]
  have hc6 : Real.cos (6 * h) = -1 := by
    have : 6 * h = 2 * h + 2 * Real.pi := by rw [hh_eq]; ring
    rw [this, Real.cos_add_two_pi, hc2]
  have hc7 : Real.cos (7 * h) = 0 := by
    have : 7 * h = 3 * h + 2 * Real.pi := by rw [hh_eq]; ring
    rw [this, Real.cos_add_two_pi, hc3]
  have hc2' : Real.cos (h * 2) = -1 := by rw [mul_comm, hc2]
  have hc3' : Real.cos (h * 3) = 0 := by rw [mul_comm, hc3]
  have hc4' : Real.cos (h * 4) = 1 := by rw [mul_comm, hc4]
  have hc5' : Real.cos (h * 5) = 0 := by rw [mul_comm, hc5]
  have hc6' : Real.cos (h * 6) = -1 := by rw [mul_comm, hc6]
  have hc7' : Real.cos (h * 7) = 0 := by rw [mul_comm, hc7]
  let A₀R : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0, 0, -2, 0;
       0, -2, 0, 4;
       -2, 0, 4, 0;
       0, 4, 0, -6]
  let A₁R : Matrix (Fin 4) (Fin 4) ℝ :=
    !![0, -2, 0, 4;
       -2, 0, 4, 0;
       0, 4, 0, -6;
       4, 0, -6, 0]
  let B₀R : Matrix (Fin 4) (Fin 4) ℝ :=
    !![-16, 0, -8, 0;
       0, 24, 0, 16;
       -8, 0, 0, 0;
       0, 16, 0, 8]
  have heval (u : ℝ) (a b : Fin 4) :
      (∑ j : Fin 3, (![u, p a, p b] j) ^ 2) *
        Real.cos (∑ j : Fin 3, (![u, p a, p b] j) ^ 2) =
      (u ^ 2 + p a ^ 2 + p b ^ 2) * Real.cos (u ^ 2 + p a ^ 2 + p b ^ 2) := by
    simp [Fin.sum_univ_three, add_assoc]
  have hS₀ : (Matrix.of fun a b : Fin 4 =>
      (∑ j : Fin 3, (![0, p a, p b] j) ^ 2) *
        Real.cos (∑ j : Fin 3, (![0, p a, p b] j) ^ 2)) = h • A₀R := by
    ext a b
    rw [Matrix.of_apply, heval, show (0 : ℝ) ^ 2 = 0 by ring, zero_add]
    fin_cases a <;> fin_cases b <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk];
       dsimp only [p, A₀R];
       rw [Matrix.smul_apply, smul_eq_mul];
       simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
         Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons];
       (repeat rw [show (0 : ℝ) ^ 2 = 0 by ring]);
       (repeat rw [hs1]); (repeat rw [hs2]); (repeat rw [hs3]);
       (try ring_nf);
       (try rw [hc1]); (try rw [hc2']); (try rw [hc3']);
       (try rw [hc4']); (try rw [hc5']); (try rw [hc6']);
       (try ring))
  have hS₁ : (Matrix.of fun a b : Fin 4 =>
      (∑ j : Fin 3, (![Real.sqrt h, p a, p b] j) ^ 2) *
        Real.cos (∑ j : Fin 3, (![Real.sqrt h, p a, p b] j) ^ 2)) = h • A₁R := by
    ext a b
    rw [Matrix.of_apply, heval, Real.sq_sqrt hh_pos.le]
    fin_cases a <;> fin_cases b <;>
      (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk];
       dsimp only [p, A₁R];
       rw [Matrix.smul_apply, smul_eq_mul];
       simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
         Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons];
       (repeat rw [show (0 : ℝ) ^ 2 = 0 by ring]);
       (repeat rw [hs1]); (repeat rw [hs2]); (repeat rw [hs3]);
       (try ring_nf);
       (try rw [hc1]); (try rw [hc2']); (try rw [hc3']); (try rw [hc4']);
       (try rw [hc5']); (try rw [hc6']); (try rw [hc7']);
       (try ring))
  have hBA : B₀R * A₀R = (16 : ℝ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B₀R, A₀R, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  have hdetA : A₀R.det = 16 := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
    simp [A₀R, Matrix.submatrix_apply, Fin.succAbove, Matrix.det_fin_three]
    norm_num
  have hadjA : A₀R.adjugate = B₀R := by
    have h1 : (16 : ℝ) • A₀R.adjugate = (16 : ℝ) • B₀R := by
      calc
        (16 : ℝ) • A₀R.adjugate = ((16 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) * A₀R.adjugate := by
          rw [Algebra.smul_mul_assoc, one_mul]
        _ = (B₀R * A₀R) * A₀R.adjugate := by rw [← hBA]
        _ = B₀R * (A₀R * A₀R.adjugate) := Matrix.mul_assoc _ _ _
        _ = B₀R * (A₀R.det • 1) := by rw [Matrix.mul_adjugate]
        _ = (16 : ℝ) • B₀R := by rw [hdetA, Algebra.mul_smul_comm, mul_one]
    exact smul_right_injective _ (by norm_num : (16 : ℝ) ≠ 0) h1
  have hmap : ((A₀R.adjugate * A₁R) * (A₀R.adjugate * A₁R)).trace = (-1024 : ℝ) := by
    rw [hadjA]
    simp only [B₀R, A₁R, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
    norm_num
  rw [hS₀, hS₁, Matrix.adjugate_smul]
  simp only [Fintype.card_fin]
  have hsmul_prod :
      (h ^ (4 - 1) • A₀R.adjugate * h • A₁R) = (h ^ 3 * h) • (A₀R.adjugate * A₁R) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [hsmul_prod, smul_mul_smul_comm, Matrix.trace_smul, hmap, smul_eq_mul]
  have hpow : 0 < (h ^ 3 * h) * (h ^ 3 * h) := by positivity
  nlinarith
end KernelRank
