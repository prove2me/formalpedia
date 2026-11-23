-- Prove2me | solution 1 for GraphSimOT.Gaps.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:38:59.989795+00:00
-- url     : https://prove2.me/submissions/fdaead0f-1390-4683-8fbc-5f1be6a436f4

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances
import Definitions.Def_GraphSimOT_Gaps_Spectral
import Theorems.Thm_GraphSimOT_Gaps_lemma_51

open Matrix GraphSimOT.Gaps

namespace Theorem14Aux

lemma lpNorm_two_eq_sqrt {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    lpNorm 2 x = Real.sqrt (∑ i : ι, x i ^ 2) := by
  unfold lpNorm
  rw [Real.sqrt_eq_rpow]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [Real.rpow_two, sq_abs]

lemma opNorm_two_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) :
    0 ≤ opNorm 2 2 M := by
  apply Real.sSup_nonneg
  rintro _ ⟨x, -, rfl⟩
  dsimp only
  rw [lpNorm_two_eq_sqrt]
  exact Real.sqrt_nonneg _

lemma opNorm_two_le_of_quad {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : κ → ℝ, ∑ j : κ, x j ^ 2 = 1 → ∑ i : ι, (M *ᵥ x) i ^ 2 ≤ C ^ 2) :
    opNorm 2 2 M ≤ C := by
  apply Real.sSup_le _ hC
  rintro _ ⟨x, hx, rfl⟩
  change lpNorm 2 x = 1 at hx
  dsimp only
  rw [lpNorm_two_eq_sqrt] at hx ⊢
  have hx_nn : 0 ≤ ∑ j : κ, x j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hx1 : ∑ j : κ, x j ^ 2 = 1 := by
    have := congrArg (· ^ 2) hx
    simpa [Real.sq_sqrt hx_nn] using this
  calc
    Real.sqrt (∑ i : ι, (M *ᵥ x) i ^ 2) ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt (h x hx1)
    _ = C := Real.sqrt_sq hC

lemma quad_le_frob {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (x : κ → ℝ) :
    ∑ i : ι, (M *ᵥ x) i ^ 2 ≤ (∑ i : ι, ∑ j : κ, M i j ^ 2) * (∑ j : κ, x j ^ 2) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro i _
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) x

lemma opNorm_two_le_frob {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) :
    opNorm 2 2 M ≤ Real.sqrt (∑ i : ι, ∑ j : κ, M i j ^ 2) := by
  have hf_nn : 0 ≤ ∑ i : ι, ∑ j : κ, M i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply opNorm_two_le_of_quad M (Real.sqrt_nonneg _)
  intro x hx
  rw [Real.sq_sqrt hf_nn]
  simpa [hx] using quad_le_frob M x

lemma opNorm_two_bddAbove {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) :
    BddAbove ((fun x : κ → ℝ => lpNorm 2 (M *ᵥ x)) '' {x | lpNorm 2 x = 1}) := by
  refine ⟨Real.sqrt (∑ i : ι, ∑ j : κ, M i j ^ 2), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  change lpNorm 2 x = 1 at hx
  dsimp only
  rw [lpNorm_two_eq_sqrt] at hx ⊢
  have hx_nn : 0 ≤ ∑ j : κ, x j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hx1 : ∑ j : κ, x j ^ 2 = 1 := by
    have := congrArg (· ^ 2) hx
    simpa [Real.sq_sqrt hx_nn] using this
  exact Real.sqrt_le_sqrt (by simpa [hx1] using quad_le_frob M x)

lemma mulVec_sq_le_opNorm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (x : κ → ℝ) :
    ∑ i : ι, (M *ᵥ x) i ^ 2 ≤ opNorm 2 2 M ^ 2 * ∑ j : κ, x j ^ 2 := by
  set X2 : ℝ := ∑ j : κ, x j ^ 2
  have hX2_nn : 0 ≤ X2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases hX2_nn.eq_or_lt with h0 | hpos
  · have hx0 : ∀ j : κ, x j = 0 := by
      intro j
      have hle : x j ^ 2 ≤ 0 := by
        rw [h0]
        exact Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ j)
      exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
    have hx_eq : x = 0 := funext hx0
    simp [hx_eq, X2]
  · set s : ℝ := Real.sqrt X2
    have hs_pos : 0 < s := Real.sqrt_pos.mpr hpos
    have hs_sq : s ^ 2 = X2 := Real.sq_sqrt hpos.le
    let u : κ → ℝ := (1 / s) • x
    have hu_norm : lpNorm 2 u = 1 := by
      rw [lpNorm_two_eq_sqrt]
      have hsum : ∑ j : κ, u j ^ 2 = (1 / s ^ 2) * X2 := by
        simp only [u, Pi.smul_apply, smul_eq_mul, mul_pow, _root_.one_div_pow, ← Finset.mul_sum, X2]
      rw [hsum, hs_sq, one_div_mul_cancel hpos.ne', Real.sqrt_one]
    have hMu : lpNorm 2 (M *ᵥ u) ≤ opNorm 2 2 M :=
      le_csSup (opNorm_two_bddAbove M) ⟨u, hu_norm, rfl⟩
    rw [lpNorm_two_eq_sqrt] at hMu
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hMu 2
    have hMu_nn : 0 ≤ ∑ i : ι, (M *ᵥ u) i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [Real.sq_sqrt hMu_nn] at hsq
    have hscale : ∑ i : ι, (M *ᵥ u) i ^ 2 = (1 / X2) * ∑ i : ι, (M *ᵥ x) i ^ 2 := by
      have hlin : M *ᵥ u = (1 / s) • (M *ᵥ x) := Matrix.mulVec_smul M (1 / s) x
      rw [hlin]
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, _root_.one_div_pow, ← Finset.mul_sum, hs_sq]
    rw [hscale, one_div_mul_eq_div, div_le_iff₀ hpos] at hsq
    exact hsq

lemma opNorm_two_add_le {n : ℕ} (M1 M2 : Matrix (Fin n) (Fin n) ℝ) :
    opNorm 2 2 (M1 + M2) ≤ opNorm 2 2 M1 + opNorm 2 2 M2 := by
  have h1_nn := opNorm_two_nonneg M1
  have h2_nn := opNorm_two_nonneg M2
  apply Real.sSup_le _ (add_nonneg h1_nn h2_nn)
  rintro _ ⟨x, hx, rfl⟩
  have hM1 : lpNorm 2 (M1 *ᵥ x) ≤ opNorm 2 2 M1 :=
    le_csSup (opNorm_two_bddAbove M1) ⟨x, hx, rfl⟩
  have hM2 : lpNorm 2 (M2 *ᵥ x) ≤ opNorm 2 2 M2 :=
    le_csSup (opNorm_two_bddAbove M2) ⟨x, hx, rfl⟩
  dsimp only
  rw [Matrix.add_mulVec, lpNorm_two_eq_sqrt]
  rw [lpNorm_two_eq_sqrt] at hM1 hM2
  let v1 : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 (Fin n → ℝ)).symm (M1 *ᵥ x)
  let v2 : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 (Fin n → ℝ)).symm (M2 *ᵥ x)
  have hv1 : ‖v1‖ = Real.sqrt (∑ i : Fin n, (M1 *ᵥ x) i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1; apply Finset.sum_congr rfl; intro i _; simp [v1]
  have hv2 : ‖v2‖ = Real.sqrt (∑ i : Fin n, (M2 *ᵥ x) i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1; apply Finset.sum_congr rfl; intro i _; simp [v2]
  have hv12 : ‖v1 + v2‖ = Real.sqrt (∑ i : Fin n, (M1 *ᵥ x + M2 *ᵥ x) i ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1; apply Finset.sum_congr rfl; intro i _; simp [v1, v2]
  have htri : ‖v1 + v2‖ ≤ ‖v1‖ + ‖v2‖ := norm_add_le v1 v2
  linarith

lemma opNorm_two_sub_le {n : ℕ} (M1 M2 : Matrix (Fin n) (Fin n) ℝ) :
    opNorm 2 2 (M1 - M2) ≤ opNorm 2 2 M1 + opNorm 2 2 M2 := by
  have hneg : opNorm 2 2 (-M2) = opNorm 2 2 M2 := by
    unfold opNorm
    congr 1; ext r; constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [lpNorm_two_eq_sqrt, Matrix.neg_mulVec]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [lpNorm_two_eq_sqrt, Matrix.neg_mulVec]
  rw [sub_eq_add_neg, ← hneg]
  exact opNorm_two_add_le M1 (-M2)

lemma opNorm_two_mul_le {n : ℕ} (M1 M2 : Matrix (Fin n) (Fin n) ℝ) :
    opNorm 2 2 (M1 * M2) ≤ opNorm 2 2 M1 * opNorm 2 2 M2 := by
  apply opNorm_two_le_of_quad (M1 * M2)
    (mul_nonneg (opNorm_two_nonneg M1) (opNorm_two_nonneg M2))
  intro x hx
  simp_rw [← Matrix.mulVec_mulVec]
  calc
    ∑ i : Fin n, (M1 *ᵥ (M2 *ᵥ x)) i ^ 2
        ≤ opNorm 2 2 M1 ^ 2 * ∑ k : Fin n, (M2 *ᵥ x) k ^ 2 := mulVec_sq_le_opNorm M1 (M2 *ᵥ x)
    _ ≤ opNorm 2 2 M1 ^ 2 * (opNorm 2 2 M2 ^ 2 * ∑ j : Fin n, x j ^ 2) :=
          mul_le_mul_of_nonneg_left (mulVec_sq_le_opNorm M2 x) (sq_nonneg _)
    _ = (opNorm 2 2 M1 * opNorm 2 2 M2) ^ 2 := by rw [hx]; ring

lemma opNorm_two_transpose_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    opNorm 2 2 Mᵀ ≤ opNorm 2 2 M := by
  apply opNorm_two_le_of_quad Mᵀ (opNorm_two_nonneg M)
  intro x hx
  set y : Fin n → ℝ := Mᵀ *ᵥ x
  set Y2 : ℝ := ∑ j : Fin n, y j ^ 2
  have hY2_nn : 0 ≤ Y2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases hY2_nn.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  have hdot : Y2 = ∑ i : Fin n, x i * (M *ᵥ y) i := by
    calc
      Y2 = ∑ j : Fin n, y j * y j := by
          apply Finset.sum_congr rfl; intro j _; ring
      _ = ∑ j : Fin n, y j * (∑ i : Fin n, M i j * x i) := rfl
      _ = ∑ i : Fin n, x i * (M *ᵥ y) i := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
  have hcs : Y2 ^ 2 ≤ (∑ i : Fin n, x i ^ 2) * (∑ i : Fin n, (M *ᵥ y) i ^ 2) := by
    rw [hdot]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (M *ᵥ y)
  have hMy := mulVec_sq_le_opNorm M y
  rw [hx, one_mul] at hcs
  have htot : Y2 * Y2 ≤ (opNorm 2 2 M ^ 2) * Y2 := by
    have : Y2 ^ 2 ≤ opNorm 2 2 M ^ 2 * Y2 := hcs.trans hMy
    linarith [sq Y2]
  exact le_of_mul_le_mul_right htot hpos

lemma opNorm_two_ds_le_one {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R ∈ doublyStochastic ℝ (Fin n)) : opNorm 2 2 R ≤ 1 := by
  rw [mem_doublyStochastic_iff_sum] at hR
  rcases hR with ⟨hRnn, hRrow, hRcol⟩
  apply opNorm_two_le_of_quad R zero_le_one
  intro x hx
  have hrow_cs : ∀ i : Fin n, (R *ᵥ x) i ^ 2 ≤ ∑ j : Fin n, R i j * x j ^ 2 := by
    intro i
    have hrew : (R *ᵥ x) i = ∑ j : Fin n, Real.sqrt (R i j) * (Real.sqrt (R i j) * x j) := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl; intro j _
      rw [← mul_assoc, Real.mul_self_sqrt (hRnn i j)]
    rw [hrew]
    calc
      (∑ j : Fin n, Real.sqrt (R i j) * (Real.sqrt (R i j) * x j)) ^ 2
          ≤ (∑ j : Fin n, Real.sqrt (R i j) ^ 2) *
            (∑ j : Fin n, (Real.sqrt (R i j) * x j) ^ 2) :=
            Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = (∑ j : Fin n, R i j) * (∑ j : Fin n, R i j * x j ^ 2) := by
            congr 1
            · apply Finset.sum_congr rfl; intro j _; exact Real.sq_sqrt (hRnn i j)
            · apply Finset.sum_congr rfl; intro j _
              rw [mul_pow, Real.sq_sqrt (hRnn i j)]
      _ = ∑ j : Fin n, R i j * x j ^ 2 := by rw [hRrow i, one_mul]
  calc
    ∑ i : Fin n, (R *ᵥ x) i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, R i j * x j ^ 2 :=
      Finset.sum_le_sum fun i _ => hrow_cs i
    _ = ∑ j : Fin n, (∑ i : Fin n, R i j) * x j ^ 2 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]
    _ = 1 ^ 2 := by
          have : ∑ j : Fin n, (∑ i : Fin n, R i j) * x j ^ 2 = ∑ j : Fin n, x j ^ 2 := by
            apply Finset.sum_congr rfl; intro j _
            rw [hRcol j, one_mul]
          rw [this, hx]; norm_num

lemma perm_ds {n : ℕ} (π : Equiv.Perm (Fin n)) :
    π.permMatrix ℝ ∈ doublyStochastic ℝ (Fin n) := by
  change π.permMatrix ℝ ∈ (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ))
  rw [doublyStochastic_eq_convexHull_permMatrix]
  exact subset_convexHull ℝ _ ⟨π, rfl⟩

lemma transpose_ds {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n)) :
    Qᵀ ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum] at hQ ⊢
  rcases hQ with ⟨hQnn, hQrow, hQcol⟩
  exact ⟨fun i j => hQnn j i, fun i => hQcol i, fun j => hQrow j⟩

lemma gammaQ_nonneg {n : ℕ} (Q A' B' : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ gammaQ Q A' B' := by
  apply Real.sSup_nonneg
  rintro _ ⟨f, g, -, -, rfl⟩
  exact abs_nonneg _

lemma gammaQ_bddAbove {n : ℕ} (hn : n ≠ 0) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n)) (A' B' : Matrix (Fin n) (Fin n) ℝ) :
    BddAbove {r : ℝ | ∃ f g : Fin n → Fin n → ℝ, normQ Q f = 1 ∧ normQ Q g = 1 ∧
      r = |(1 / (n : ℝ) ^ 2) *
        ∑ i, ∑ j, ∑ k, ∑ l, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l|} := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  rw [mem_doublyStochastic_iff_sum] at hQ
  rcases hQ with ⟨hQnn, hQrow, -⟩
  let i0 : Fin n := ⟨0, hn0⟩
  have huniv_ne : (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n))).Nonempty :=
    ⟨((i0, i0), (i0, i0)), Finset.mem_univ _⟩
  let M0 : ℝ := Finset.univ.sup' huniv_ne (fun p => |A' p.1.1 p.2.1 - B' p.1.2 p.2.2|)
  have hM0_nn : 0 ≤ M0 :=
    (abs_nonneg _).trans (Finset.le_sup' (fun p : (Fin n × Fin n) × (Fin n × Fin n) =>
      |A' p.1.1 p.2.1 - B' p.1.2 p.2.2|) (Finset.mem_univ ((i0, i0), (i0, i0))))
  have hentry : ∀ i j k l : Fin n, |A' i k - B' j l| ≤ M0 := fun i j k l =>
    Finset.le_sup' (fun p : (Fin n × Fin n) × (Fin n × Fin n) =>
      |A' p.1.1 p.2.1 - B' p.1.2 p.2.2|) (Finset.mem_univ ((i, j), (k, l)))
  refine ⟨M0, ?_⟩
  rintro r ⟨f, g, hf, hg, rfl⟩
  have hbound_l1 : ∀ h : Fin n → Fin n → ℝ, normQ Q h = 1 →
      ∑ i : Fin n, ∑ j : Fin n, Q i j * |h i j| ≤ n := by
    intro h hh
    have hinner : innerQ Q h h = 1 := by
      have hnn : 0 ≤ innerQ Q h h := by
        unfold innerQ
        apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg; intro i _
        apply Finset.sum_nonneg; intro j _
        have : Q i j * h i j * h i j = Q i j * (h i j ^ 2) := by ring
        rw [this]
        exact mul_nonneg (hQnn i j) (sq_nonneg _)
      have hsq : Real.sqrt (innerQ Q h h) ^ 2 = 1 ^ 2 := by rw [← normQ, hh]
      rw [Real.sq_sqrt hnn] at hsq
      linarith
    have hsum_sq : ∑ i : Fin n, ∑ j : Fin n, Q i j * h i j ^ 2 = n := by
      unfold innerQ at hinner
      have : ∑ i : Fin n, ∑ j : Fin n, Q i j * h i j * h i j =
          ∑ i : Fin n, ∑ j : Fin n, Q i j * h i j ^ 2 := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _; ring
      rw [this, one_div_mul_eq_div, div_eq_iff hnR.ne'] at hinner
      linarith
    have hsum_Q : ∑ i : Fin n, ∑ j : Fin n, Q i j = n := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, Q i j = ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_congr rfl fun i _ => hQrow i
        _ = n := by simp
    have hpt : ∀ i j : Fin n, 2 * (Q i j * |h i j|) ≤ Q i j + Q i j * h i j ^ 2 := by
      intro i j
      have hsq : 0 ≤ (|h i j| - 1) ^ 2 := sq_nonneg _
      have h1 : 2 * |h i j| ≤ 1 + h i j ^ 2 := by nlinarith [sq_abs (h i j)]
      have h2 := mul_le_mul_of_nonneg_left h1 (hQnn i j)
      linarith
    have hsum2 : 2 * ∑ i : Fin n, ∑ j : Fin n, Q i j * |h i j| ≤ 2 * (n : ℝ) := by
      calc
        2 * ∑ i : Fin n, ∑ j : Fin n, Q i j * |h i j|
            = ∑ i : Fin n, ∑ j : Fin n, 2 * (Q i j * |h i j|) := by simp_rw [Finset.mul_sum]
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, (Q i j + Q i j * h i j ^ 2) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
        _ = (∑ i : Fin n, ∑ j : Fin n, Q i j) +
            (∑ i : Fin n, ∑ j : Fin n, Q i j * h i j ^ 2) := by simp_rw [Finset.sum_add_distrib]
        _ = 2 * (n : ℝ) := by linarith
    linarith
  have hf1 := hbound_l1 f hf
  have hg1 := hbound_l1 g hg
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hn2)]
  have hterm_le : ∀ i j k l : Fin n,
      |f i j * Q i j * Q k l * (A' i k - B' j l) * g k l| ≤
        (Q i j * |f i j|) * (Q k l * |g k l|) * M0 := by
    intro i j k l
    have hrew : |f i j * Q i j * Q k l * (A' i k - B' j l) * g k l| =
        (Q i j * |f i j|) * (Q k l * |g k l|) * |A' i k - B' j l| := by
      calc
        |f i j * Q i j * Q k l * (A' i k - B' j l) * g k l|
            = |Q i j| * |Q k l| * |f i j| * |g k l| * |A' i k - B' j l| := by
                rw [abs_mul, abs_mul, abs_mul, abs_mul]; ring
        _ = (Q i j * |f i j|) * (Q k l * |g k l|) * |A' i k - B' j l| := by
                rw [abs_of_nonneg (hQnn i j), abs_of_nonneg (hQnn k l)]; ring
    rw [hrew]
    exact mul_le_mul_of_nonneg_left (hentry i j k l)
      (mul_nonneg (mul_nonneg (hQnn i j) (abs_nonneg _)) (mul_nonneg (hQnn k l) (abs_nonneg _)))
  calc
    (1 / (n : ℝ) ^ 2) * |∑ i, ∑ j, ∑ k, ∑ l, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l|
        ≤ (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, ∑ k, ∑ l,
            |f i j * Q i j * Q k l * (A' i k - B' j l) * g k l| := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, ∑ k, ∑ l,
          (Q i j * |f i j|) * (Q k l * |g k l|) * M0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          apply Finset.sum_le_sum; intro k _
          apply Finset.sum_le_sum; intro l _; exact hterm_le i j k l
    _ = (1 / (n : ℝ) ^ 2) * ((∑ i, ∑ j, Q i j * |f i j|) * (∑ k, ∑ l, Q k l * |g k l|) * M0) := by
          congr 1
          calc
            (∑ i, ∑ j, ∑ k, ∑ l, (Q i j * |f i j|) * (Q k l * |g k l|) * M0)
                = ∑ i, ∑ j, (Q i j * |f i j|) * (∑ k, ∑ l, (Q k l * |g k l|) * M0) := by
                    apply Finset.sum_congr rfl; intro i _
                    apply Finset.sum_congr rfl; intro j _
                    simp only [Finset.mul_sum, mul_assoc]
            _ = (∑ i, ∑ j, Q i j * |f i j|) * (∑ k, ∑ l, Q k l * |g k l|) * M0 := by
                  have hinner : (∑ k, ∑ l, (Q k l * |g k l|) * M0) =
                      (∑ k, ∑ l, Q k l * |g k l|) * M0 := by simp only [Finset.sum_mul]
                  simp_rw [hinner]; simp only [Finset.sum_mul, mul_assoc]
    _ ≤ (1 / (n : ℝ) ^ 2) * ((n : ℝ) * (n : ℝ) * M0) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hM0_nn
          exact mul_le_mul hf1 hg1 (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
            mul_nonneg (hQnn k l) (abs_nonneg _)) hnR.le
    _ = M0 := by
          have hn2' : (n : ℝ) ^ 2 ≠ 0 := hn2.ne'
          calc
            (1 / (n : ℝ) ^ 2) * ((n : ℝ) * (n : ℝ) * M0)
                = ((1 / (n : ℝ) ^ 2) * (n : ℝ) ^ 2) * M0 := by ring
            _ = M0 := by rw [one_div_mul_cancel hn2', one_mul]

/-- Lemma 50: `n⁻¹ ‖Qᵀ A' Q − B'‖_{2→2} ≤ γ_Q(A', B')`. -/
lemma lemma_50 {n : ℕ} (hn : n ≠ 0) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n)) (A' B' : Matrix (Fin n) (Fin n) ℝ) :
    opNorm 2 2 (Qᵀ * A' * Q - B') ≤ (n : ℝ) * gammaQ Q A' B' := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hQ' := hQ
  rw [mem_doublyStochastic_iff_sum] at hQ'
  rcases hQ' with ⟨hQnn, -, hQcol⟩
  set K : Matrix (Fin n) (Fin n) ℝ := Qᵀ * A' * Q - B'
  apply opNorm_two_le_of_quad K (mul_nonneg hnR.le (gammaQ_nonneg Q A' B'))
  intro x hx
  set z : Fin n → ℝ := K *ᵥ x
  set Z2 : ℝ := ∑ j : Fin n, z j ^ 2
  have hZ2_nn : 0 ≤ Z2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases hZ2_nn.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  set Z : ℝ := Real.sqrt Z2
  have hZ_pos : 0 < Z := Real.sqrt_pos.mpr hpos
  let u : Fin n → ℝ := fun j => z j / Z
  have hu_sq : ∑ j : Fin n, u j ^ 2 = 1 := by
    simp only [u, div_pow, ← Finset.sum_div, Z]
    rw [Real.sq_sqrt hpos.le, div_self hpos.ne']
  let f : Fin n → Fin n → ℝ := fun _i j => Real.sqrt n * u j
  let g : Fin n → Fin n → ℝ := fun _k l => Real.sqrt n * x l
  have hf_norm : normQ Q f = 1 := by
    unfold normQ innerQ
    have hsum : ∑ i : Fin n, ∑ j : Fin n, Q i j * f i j * f i j = n := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, Q i j * f i j * f i j
            = ∑ j : Fin n, ((Real.sqrt n) ^ 2 * u j ^ 2) * (∑ i : Fin n, Q i j) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro j _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro i _; simp only [f]; ring
        _ = (n : ℝ) * ∑ j : Fin n, u j ^ 2 := by
                rw [Real.sq_sqrt hnR.le, Finset.mul_sum]
                apply Finset.sum_congr rfl; intro j _
                rw [hQcol j, mul_one]
        _ = n := by rw [hu_sq, mul_one]
    rw [hsum, one_div_mul_cancel hnR.ne', Real.sqrt_one]
  have hg_norm : normQ Q g = 1 := by
    unfold normQ innerQ
    have hsum : ∑ k : Fin n, ∑ l : Fin n, Q k l * g k l * g k l = n := by
      calc
        ∑ k : Fin n, ∑ l : Fin n, Q k l * g k l * g k l
            = ∑ l : Fin n, ((Real.sqrt n) ^ 2 * x l ^ 2) * (∑ k : Fin n, Q k l) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro l _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro k _; simp only [g]; ring
        _ = (n : ℝ) * ∑ l : Fin n, x l ^ 2 := by
                rw [Real.sq_sqrt hnR.le, Finset.mul_sum]
                apply Finset.sum_congr rfl; intro l _
                rw [hQcol l, mul_one]
        _ = n := by rw [hx, mul_one]
    rw [hsum, one_div_mul_cancel hnR.ne', Real.sqrt_one]
  have hK_entry : ∀ j l : Fin n, K j l = ∑ i : Fin n, ∑ k : Fin n, Q i j * Q k l * (A' i k - B' j l) := by
    intro j l
    have h1 : (Qᵀ * A' * Q) j l = ∑ i : Fin n, ∑ k : Fin n, Q i j * Q k l * A' i k := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _; ring
    have h2 : B' j l = ∑ i : Fin n, ∑ k : Fin n, Q i j * Q k l * B' j l := by
      symm
      calc
        ∑ i : Fin n, ∑ k : Fin n, Q i j * Q k l * B' j l
            = ∑ i : Fin n, (B' j l * Q i j) * (∑ k : Fin n, Q k l) := by
                apply Finset.sum_congr rfl; intro i _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro k _; ring
        _ = B' j l * (∑ i : Fin n, Q i j) * (∑ k : Fin n, Q k l) := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ = B' j l := by rw [hQcol j, hQcol l, mul_one, mul_one]
    change (Qᵀ * A' * Q) j l - B' j l = _
    rw [h1]
    conv_lhs => rhs; rw [h2]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have hbilin : (1 / (n : ℝ) ^ 2) *
      ∑ i, ∑ j, ∑ k, ∑ l, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l = Z / n := by
    have hsum : ∑ i, ∑ j, ∑ k, ∑ l, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l =
        (n : ℝ) * ∑ j : Fin n, u j * z j := by
      calc
        _ = ∑ j : Fin n, ∑ l : Fin n, ((Real.sqrt n * Real.sqrt n) * u j * x l) *
              (∑ i : Fin n, ∑ k : Fin n, Q i j * Q k l * (A' i k - B' j l)) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro j _
              calc
                (∑ i, ∑ k, ∑ l, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l)
                    = ∑ i, ∑ l, ∑ k, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l := by
                        apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
                _ = ∑ l, ∑ i, ∑ k, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l := Finset.sum_comm
                _ = _ := by
                      apply Finset.sum_congr rfl; intro l _
                      simp only [Finset.mul_sum, f, g]
                      apply Finset.sum_congr rfl; intro i _
                      apply Finset.sum_congr rfl; intro k _; ring
        _ = (n : ℝ) * ∑ j : Fin n, u j * z j := by
              rw [Real.mul_self_sqrt hnR.le, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j _
              simp_rw [← hK_entry j]
              simp only [z, Matrix.mulVec, dotProduct, Finset.mul_sum]
              apply Finset.sum_congr rfl; intro l _; ring
    have huz : ∑ j : Fin n, u j * z j = Z := by
      calc
        ∑ j : Fin n, u j * z j = (∑ j : Fin n, z j ^ 2) / Z := by
            simp only [u, div_mul_eq_mul_div, ← Finset.sum_div]
            congr 1; apply Finset.sum_congr rfl; intro j _; ring
        _ = Z := by change Z2 / Z = Z; rw [div_eq_iff hZ_pos.ne']; exact (Real.mul_self_sqrt hpos.le).symm
    rw [hsum, huz]
    field_simp
  have hle_gamma : Z / n ≤ gammaQ Q A' B' := by
    unfold gammaQ
    apply le_csSup (gammaQ_bddAbove hn Q hQ A' B')
    refine ⟨f, g, hf_norm, hg_norm, ?_⟩
    rw [hbilin, abs_of_nonneg (by positivity)]
  have hZ_le : Z ≤ (n : ℝ) * gammaQ Q A' B' := by
    rwa [div_le_iff₀ hnR, mul_comm] at hle_gamma
  have hsq := pow_le_pow_left₀ hZ_pos.le hZ_le 2
  rwa [Real.sq_sqrt hpos.le] at hsq

lemma gammaQ_le_costOp {n : ℕ} (hn : n ≠ 0) (G H : SimpleGraph (Fin n))
    (Qstar : Matrix (Fin n) (Fin n) ℝ) (hQstar : Qstar ∈ DSstar n) :
    gammaQ ((n : ℝ) • Qstar) (adj G) (adj H) ≤ costOp 2 2 G H Qstar := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  set Q : Matrix (Fin n) (Fin n) ℝ := (n : ℝ) • Qstar
  apply Real.sSup_le _ (opNorm_two_nonneg _)
  rintro _ ⟨f, g, hf, hg, rfl⟩
  let u : Fin n × Fin n → ℝ := fun a => Real.sqrt (Qstar a.1 a.2) * f a.1 a.2
  let v : Fin n × Fin n → ℝ := fun b => Real.sqrt (Qstar b.1 b.2) * g b.1 b.2
  have hnorm_unit : ∀ (h : Fin n → Fin n → ℝ), normQ Q h = 1 →
      ∑ a : Fin n × Fin n, (Real.sqrt (Qstar a.1 a.2) * h a.1 a.2) ^ 2 = 1 := by
    intro h hh
    have hnn : 0 ≤ innerQ Q h h := by
      unfold innerQ
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg; intro i _
      apply Finset.sum_nonneg; intro j _
      have hQij : 0 ≤ Q i j := mul_nonneg hnR.le (hQstar.1 i j)
      have : Q i j * h i j * h i j = Q i j * h i j ^ 2 := by ring
      rw [this]; exact mul_nonneg hQij (sq_nonneg _)
    have h1 : innerQ Q h h = 1 := by
      have := congrArg (· ^ 2) hh
      simpa [normQ, Real.sq_sqrt hnn] using this
    rw [Fintype.sum_prod_type]
    calc
      ∑ i : Fin n, ∑ j : Fin n, (Real.sqrt (Qstar i j) * h i j) ^ 2
          = (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, Q i j * h i j * h i j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j _
              rw [mul_pow, Real.sq_sqrt (hQstar.1 i j)]
              simp only [Q, Matrix.smul_apply, smul_eq_mul]
              have hn_ne : (n : ℝ) ≠ 0 := hnR.ne'
              field_simp
      _ = 1 := h1
  have hu1 : ∑ a : Fin n × Fin n, u a ^ 2 = 1 := hnorm_unit f hf
  have hv1 : ∑ b : Fin n × Fin n, v b ^ 2 = 1 := hnorm_unit g hg
  have hpow00 : ∀ x : ℝ, 0 ≤ x → pow00 x (1 / (2 : ℝ)) = Real.sqrt x := by
    intro x hx
    unfold pow00
    rcases hx.eq_or_lt with rfl | hpos
    · simp
    · rw [if_neg hpos.ne', Real.sqrt_eq_rpow]
  have hBpq : ∀ a b : Fin n × Fin n,
      Bpq 2 2 G H Qstar a b =
        Real.sqrt (Qstar a.1 a.2) * (adj G a.1 b.1 - adj H a.2 b.2) * Real.sqrt (Qstar b.1 b.2) := by
    intro a b
    unfold Bpq disc
    have hexp : 1 - 1 / (2 : ℝ) = 1 / (2 : ℝ) := by ring
    rw [hexp, hpow00 _ (hQstar.1 a.1 a.2), hpow00 _ (hQstar.1 b.1 b.2)]
  have hbilin : (1 / (n : ℝ) ^ 2) *
      ∑ i, ∑ j, ∑ k, ∑ l, f i j * Q i j * Q k l * (adj G i k - adj H j l) * g k l =
      ∑ a : Fin n × Fin n, u a * (Bpq 2 2 G H Qstar *ᵥ v) a := by
    symm
    rw [Fintype.sum_prod_type]
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [Fintype.sum_prod_type, hBpq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    simp only [Finset.mul_sum, u, v, Q, Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    have hsq1 : Real.sqrt (Qstar i j) ^ 2 = Qstar i j := Real.sq_sqrt (hQstar.1 i j)
    have hsq2 : Real.sqrt (Qstar k l) ^ 2 = Qstar k l := Real.sq_sqrt (hQstar.1 k l)
    have hn_ne : (n : ℝ) ≠ 0 := hnR.ne'
    field_simp
    rw [hsq1, hsq2]; ring
  rw [hbilin]
  have hcs_sq : (∑ a : Fin n × Fin n, u a * (Bpq 2 2 G H Qstar *ᵥ v) a) ^ 2 ≤
      ∑ a : Fin n × Fin n, (Bpq 2 2 G H Qstar *ᵥ v) a ^ 2 := by
    calc
      (∑ a : Fin n × Fin n, u a * (Bpq 2 2 G H Qstar *ᵥ v) a) ^ 2
          ≤ (∑ a : Fin n × Fin n, u a ^ 2) *
            (∑ a : Fin n × Fin n, (Bpq 2 2 G H Qstar *ᵥ v) a ^ 2) :=
            Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u _
      _ = ∑ a : Fin n × Fin n, (Bpq 2 2 G H Qstar *ᵥ v) a ^ 2 := by rw [hu1, one_mul]
  have hv_lp : lpNorm 2 v = 1 := by rw [lpNorm_two_eq_sqrt, hv1, Real.sqrt_one]
  have hBv : Real.sqrt (∑ a : Fin n × Fin n, (Bpq 2 2 G H Qstar *ᵥ v) a ^ 2) ≤
      costOp 2 2 G H Qstar := by
    rw [← lpNorm_two_eq_sqrt]
    exact le_csSup (opNorm_two_bddAbove _) ⟨v, hv_lp, rfl⟩
  calc
    |∑ a : Fin n × Fin n, u a * (Bpq 2 2 G H Qstar *ᵥ v) a|
        = Real.sqrt ((∑ a : Fin n × Fin n, u a * (Bpq 2 2 G H Qstar *ᵥ v) a) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ a : Fin n × Fin n, (Bpq 2 2 G H Qstar *ᵥ v) a ^ 2) :=
          Real.sqrt_le_sqrt hcs_sq
    _ ≤ costOp 2 2 G H Qstar := hBv

lemma frob_eq_sum_onb {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ∑ i : Fin n, ∑ k : Fin n, M i k ^ 2 =
      ∑ r : Fin n, ∑ i : Fin n, (M *ᵥ (b r).ofLp) i ^ 2 := by
  have hrow : ∀ i : Fin n,
      ∑ k : Fin n, M i k ^ 2 = ∑ r : Fin n, (M *ᵥ (b r).ofLp) i ^ 2 := by
    intro i
    let m_i : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 (Fin n → ℝ)).symm (fun k => M i k)
    have hnorm : ‖b.repr m_i‖ ^ 2 = ‖m_i‖ ^ 2 := by rw [b.repr.norm_map]
    have h1 : ‖m_i‖ ^ 2 = ∑ k : Fin n, M i k ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      apply Finset.sum_congr rfl; intro k _; simp [m_i]
    have h2 : ‖b.repr m_i‖ ^ 2 = ∑ r : Fin n, (M *ᵥ (b r).ofLp) i ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      apply Finset.sum_congr rfl; intro r _
      have hrepr : (b.repr m_i).ofLp r = (M *ᵥ (b r).ofLp) i := by
        rw [b.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct]
        simp only [star_trivial, dotProduct, Matrix.mulVec, m_i]
        apply Finset.sum_congr rfl; intro k _
        simp
      rw [Real.norm_eq_abs, sq_abs, hrepr]
    linarith
  simp_rw [hrow]
  exact Finset.sum_comm

lemma perm_conj_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n))
    (i k : Fin n) :
    (π.permMatrix ℝ * M * (π.permMatrix ℝ)ᵀ) i k = M (π i) (π k) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  rw [Finset.sum_eq_single (π k)]
  · simp only [↓reduceIte, mul_one]
    rw [Finset.sum_eq_single (π i)]
    · simp
    · intro j _ hj; simp [hj.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro l _ hl; simp [hl.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma costOpPerm_le_conj {n : ℕ} (G H : SimpleGraph (Fin n)) (π : Equiv.Perm (Fin n)) :
    costOpPerm 2 2 G H π ≤
      opNorm 2 2 (adj G - π.permMatrix ℝ * adj H * (π.permMatrix ℝ)ᵀ) := by
  set P := π.permMatrix ℝ
  have hrel : permAdj G π - adj H = Pᵀ * (adj G - P * adj H * Pᵀ) * P := by
    ext w w'
    have hPtP : ∀ u v : Fin n, (Pᵀ * P) u v = if u = v then 1 else 0 := by
      intro u v
      simp only [P, Matrix.mul_apply, Matrix.transpose_apply, Equiv.Perm.permMatrix,
        PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
        ite_mul, one_mul, zero_mul]
      rw [Finset.sum_eq_single (π.symm u)]
      · simp [Equiv.apply_symm_apply]
      · intro x _ hx
        have : π x ≠ u := fun h => hx (π.eq_symm_apply.mpr h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h1 : (Pᵀ * adj G * P) w w' = permAdj G π w w' := by
      simp only [P, permAdj, Matrix.mul_apply, Matrix.transpose_apply, Equiv.Perm.permMatrix,
        PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
      rw [Finset.sum_eq_single (π.symm w')]
      · simp only [Equiv.apply_symm_apply, ↓reduceIte, mul_one]
        rw [Finset.sum_eq_single (π.symm w)]
        · simp
        · intro i _ hi
          have : π i ≠ w := fun h => hi (π.eq_symm_apply.mpr h)
          simp [this]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro k _ hk
        have : π k ≠ w' := fun h => hk (π.eq_symm_apply.mpr h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 : (Pᵀ * (P * adj H * Pᵀ) * P) w w' = adj H w w' := by
      have hassoc : Pᵀ * (P * adj H * Pᵀ) * P = (Pᵀ * P) * adj H * (Pᵀ * P) := by
        simp only [Matrix.mul_assoc]
      have hId : Pᵀ * P = 1 := by ext u v; rw [hPtP, Matrix.one_apply]
      rw [hassoc, hId, Matrix.one_mul, Matrix.mul_one]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply, h1, h2]
  unfold costOpPerm
  rw [hrel]
  have hP1 : opNorm 2 2 P ≤ 1 := opNorm_two_ds_le_one P (perm_ds π)
  have hPt1 : opNorm 2 2 Pᵀ ≤ 1 := (opNorm_two_transpose_le P).trans hP1
  calc
    opNorm 2 2 (Pᵀ * (adj G - P * adj H * Pᵀ) * P)
        ≤ opNorm 2 2 (Pᵀ * (adj G - P * adj H * Pᵀ)) * opNorm 2 2 P :=
          opNorm_two_mul_le _ _
    _ ≤ (opNorm 2 2 Pᵀ * opNorm 2 2 (adj G - P * adj H * Pᵀ)) * opNorm 2 2 P :=
          mul_le_mul_of_nonneg_right (opNorm_two_mul_le _ _) (opNorm_two_nonneg P)
    _ ≤ (1 * opNorm 2 2 (adj G - P * adj H * Pᵀ)) * 1 := by
          apply mul_le_mul _ hP1 (opNorm_two_nonneg _)
            (mul_nonneg zero_le_one (opNorm_two_nonneg _))
          exact mul_le_mul_of_nonneg_right hPt1 (opNorm_two_nonneg _)
    _ = opNorm 2 2 (adj G - P * adj H * Pᵀ) := by ring

lemma delta2_le_of_ds_pos_t {n : ℕ} (hn : n ≠ 0) (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (t : ℝ) (ht : 0 < t) :
    delta2 G H ≤ gammaQ Q (adj G) (adj H) + 2 * t + gammaQ Q (adj G) (adj H) / t := by
  classical
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  set pG : ℝ := (∑ i : Fin n, ∑ k : Fin n, adj G i k) / (n : ℝ) ^ 2
  have hpG_prod_le : pG * (1 - pG) ≤ 1 / 4 := by
    have : 0 ≤ (pG - 1 / 2) ^ 2 := sq_nonneg _
    linarith
  let J : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun _ _ => pG)
  set A' : Matrix (Fin n) (Fin n) ℝ := adj G - J
  set B' : Matrix (Fin n) (Fin n) ℝ := adj H - J
  have hA'_apply : ∀ i k : Fin n, A' i k = adj G i k - pG := fun _ _ => rfl
  have hB'_apply : ∀ j l : Fin n, B' j l = adj H j l - pG := fun _ _ => rfl
  have hgamma_eq : gammaQ Q A' B' = gammaQ Q (adj G) (adj H) := by
    unfold gammaQ
    congr 1; ext r; constructor <;>
    · rintro ⟨f, g, hf, hg, rfl⟩
      refine ⟨f, g, hf, hg, ?_⟩
      congr 2
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro l _
      rw [hA'_apply, hB'_apply]; ring
  have hA'_symm : A'.IsHermitian := by
    ext i k
    simp only [Matrix.conjTranspose_apply, star_trivial, hA'_apply, adj]
    by_cases h : G.Adj k i
    · simp [h, h.symm]
    · have h' : ¬ G.Adj i k := fun hik => h hik.symm
      simp [h, h']
  have hA'_frob : ∑ i : Fin n, ∑ k : Fin n, A' i k ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by
    have hadj_sq : ∀ i k : Fin n, adj G i k ^ 2 = adj G i k := by
      intro i k; unfold adj; split_ifs <;> norm_num
    have hsum_adj : ∑ i : Fin n, ∑ k : Fin n, adj G i k = (n : ℝ) ^ 2 * pG := by
      simp only [pG]; field_simp
    have hcalc : ∑ i : Fin n, ∑ k : Fin n, A' i k ^ 2 = (n : ℝ) ^ 2 * (pG * (1 - pG)) := by
      calc
        ∑ i : Fin n, ∑ k : Fin n, A' i k ^ 2
            = ∑ i : Fin n, ∑ k : Fin n, (adj G i k - 2 * pG * adj G i k + pG ^ 2) := by
                apply Finset.sum_congr rfl; intro i _
                apply Finset.sum_congr rfl; intro k _
                rw [hA'_apply, sub_sq, hadj_sq i k]; ring
        _ = (∑ i : Fin n, ∑ k : Fin n, adj G i k) -
            2 * pG * (∑ i : Fin n, ∑ k : Fin n, adj G i k) +
            (n : ℝ) ^ 2 * pG ^ 2 := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
              congr 1
              simp [sq]; ring
        _ = (n : ℝ) ^ 2 * (pG * (1 - pG)) := by rw [hsum_adj]; ring
    rw [hcalc]
    nlinarith
  let b := hA'_symm.eigenvectorBasis
  let lam := hA'_symm.eigenvalues
  have hA'_basis : ∀ s : Fin n, A' *ᵥ (b s).ofLp = lam s • (b s).ofLp :=
    fun s => hA'_symm.mulVec_eigenvectorBasis s
  let It : Finset (Fin n) := Finset.univ.filter (fun r => (n : ℝ) * t < |lam r|)
  let At : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun i k => ∑ r ∈ It, lam r * (b r).ofLp i * (b r).ofLp k)
  have hAt_basis : ∀ s : Fin n,
      At *ᵥ (b s).ofLp = if s ∈ It then lam s • (b s).ofLp else 0 := by
    intro s
    ext i
    simp only [At, Matrix.of_apply, Matrix.mulVec, dotProduct]
    have hswap : (∑ k : Fin n, (∑ r ∈ It, lam r * (b r).ofLp i * (b r).ofLp k) * (b s).ofLp k) =
        ∑ r ∈ It, lam r * (b r).ofLp i * inner ℝ (b r) (b s) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro r _
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hswap]
    have hortho : ∀ r : Fin n, inner ℝ (b r) (b s) = if r = s then 1 else 0 :=
      fun r => orthonormal_iff_ite.mp b.orthonormal r s
    simp_rw [hortho, mul_ite, mul_one, mul_zero]
    by_cases hs : s ∈ It
    · rw [Finset.sum_eq_single s]
      · simp [hs]
      · intro r _ hrs; simp [hrs]
      · intro h; exact absurd hs h
    · rw [if_neg hs, Pi.zero_apply, Finset.sum_eq_zero]
      intro r hr
      have hrs : r ≠ s := fun heq => hs (heq ▸ hr)
      simp [hrs]
  have hDiff_norm : opNorm 2 2 (A' - At) ≤ (n : ℝ) * t := by
    apply opNorm_two_le_of_quad (A' - At) (by positivity)
    intro x hx
    let xE : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 (Fin n → ℝ)).symm x
    have hx_decomp : x = ∑ s : Fin n, (b.repr xE).ofLp s • (b s).ofLp := by
      have h1 := b.sum_repr xE
      ext k
      have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v.ofLp k) h1
      simpa [xE] using h2.symm
    let coeff : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 (Fin n → ℝ)).symm
      (fun s => if s ∈ It then 0 else (b.repr xE).ofLp s * lam s)
    have hDiff_vec : (A' - At) *ᵥ x = (b.repr.symm coeff).ofLp := by
      have hlhs : (A' - At) *ᵥ x =
          ∑ s : Fin n, (if s ∈ It then (0 : ℝ) else (b.repr xE).ofLp s * lam s) • (b s).ofLp := by
        conv_lhs => rw [hx_decomp]
        rw [Matrix.mulVec_sum]
        apply Finset.sum_congr rfl; intro s _
        rw [Matrix.mulVec_smul, Matrix.sub_mulVec, hA'_basis s, hAt_basis s]
        by_cases hs : s ∈ It
        · simp [hs]
        · simp [hs, smul_smul]
      have hrhs := b.sum_repr_symm coeff
      rw [hlhs]
      ext k
      have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v.ofLp k) hrhs
      rw [← h2]
      simp only [WithLp.ofLp_sum, Finset.sum_apply, coeff]
      apply Finset.sum_congr rfl; intro c _
      by_cases hc : c ∈ It <;> simp [hc]
    have hnorm_eq : ∑ i : Fin n, ((A' - At) *ᵥ x) i ^ 2 =
        ∑ s : Fin n, (if s ∈ It then 0 else (b.repr xE).ofLp s * lam s) ^ 2 := by
      have hiso : ‖b.repr.symm coeff‖ ^ 2 = ‖coeff‖ ^ 2 := by rw [b.repr.symm.norm_map]
      have h1 : ‖b.repr.symm coeff‖ ^ 2 = ∑ i : Fin n, ((A' - At) *ᵥ x) i ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        apply Finset.sum_congr rfl; intro i _
        rw [Real.norm_eq_abs, sq_abs]
        change ((b.repr.symm coeff).ofLp i) ^ 2 = _
        rw [← hDiff_vec]
      have h2 : ‖coeff‖ ^ 2 =
          ∑ s : Fin n, (if s ∈ It then 0 else (b.repr xE).ofLp s * lam s) ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        apply Finset.sum_congr rfl; intro s _; simp [coeff]
      linarith
    have hparseval : ∑ s : Fin n, ((b.repr xE).ofLp s) ^ 2 = 1 := by
      have hiso : ‖b.repr xE‖ ^ 2 = ‖xE‖ ^ 2 := by rw [b.repr.norm_map]
      have h1 : ‖b.repr xE‖ ^ 2 = ∑ s : Fin n, ((b.repr xE).ofLp s) ^ 2 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        apply Finset.sum_congr rfl; intro s _; simp
      have h2 : ‖xE‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        simpa [xE] using hx
      linarith
    rw [hnorm_eq]
    calc
      ∑ s : Fin n, (if s ∈ It then 0 else (b.repr xE).ofLp s * lam s) ^ 2
          ≤ ∑ s : Fin n, ((n : ℝ) * t) ^ 2 * ((b.repr xE).ofLp s) ^ 2 := by
            apply Finset.sum_le_sum; intro s _
            by_cases hs : s ∈ It
            · simp only [hs, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
              positivity
            · simp only [hs, ↓reduceIte, mul_pow]
              have hle : |lam s| ≤ (n : ℝ) * t := not_lt.mp (by simpa [It] using hs)
              have hsq : lam s ^ 2 ≤ ((n : ℝ) * t) ^ 2 := by
                rw [← sq_abs (lam s)]
                exact pow_le_pow_left₀ (abs_nonneg _) hle 2
              nlinarith [sq_nonneg ((b.repr xE).ofLp s)]
      _ = ((n : ℝ) * t) ^ 2 := by rw [← Finset.mul_sum, hparseval, mul_one]
  have hIt_card : (It.card : ℝ) ≤ 1 / (4 * t ^ 2) := by
    have hb_norm1 : ∀ r : Fin n, ∑ i : Fin n, ((b r).ofLp i) ^ 2 = 1 := by
      intro r
      have h1 : ‖b r‖ = 1 := b.orthonormal.1 r
      have h2 : ‖b r‖ ^ 2 = 1 := by rw [h1]; norm_num
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
      simpa using h2
    have hlam_sum : ∑ r : Fin n, lam r ^ 2 = ∑ i : Fin n, ∑ k : Fin n, A' i k ^ 2 := by
      rw [frob_eq_sum_onb A' b]
      apply Finset.sum_congr rfl; intro r _
      rw [hA'_basis r]
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      rw [hb_norm1 r, mul_one]
    have hsub : ((n : ℝ) * t) ^ 2 * (It.card : ℝ) ≤ ∑ r : Fin n, lam r ^ 2 := by
      calc
        ((n : ℝ) * t) ^ 2 * (It.card : ℝ)
            = ∑ _r ∈ It, ((n : ℝ) * t) ^ 2 := by simp [mul_comm]
        _ ≤ ∑ r ∈ It, lam r ^ 2 := by
              apply Finset.sum_le_sum; intro r hr
              have hgt : (n : ℝ) * t < |lam r| := (Finset.mem_filter.mp hr).2
              rw [← sq_abs (lam r)]
              exact pow_le_pow_left₀ (by positivity) hgt.le 2
        _ ≤ ∑ r : Fin n, lam r ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    have htot : ((n : ℝ) * t) ^ 2 * (It.card : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by linarith
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * t ^ 2)]
    have hrew : (It.card : ℝ) * (4 * t ^ 2) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right (by simpa [one_mul] using hrew) hn2
  have hconv : Q ∈ convexHull ℝ
      {x : Matrix (Fin n) (Fin n) ℝ | ∃ σ : Equiv.Perm (Fin n), σ.permMatrix ℝ = x} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]; exact hQ
  rw [mem_convexHull_iff_exists_fintype] at hconv
  rcases hconv with ⟨ι, instFintype, w, z, hw0, hw1, hz, hQeq⟩
  choose πf hπf using hz
  have hQeq' : Q = ∑ s : ι, w s • (πf s).permMatrix ℝ := by
    rw [← hQeq]
    apply Finset.sum_congr rfl; intro s _; rw [hπf s]
  have hlem52 : ∀ x : Fin n → ℝ,
      ∑ s : ι, w s * (∑ i : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) *ᵥ x) i) ^ 2) =
        ∑ i : Fin n, ∑ j : Fin n, Q i j * (x i - (Qᵀ *ᵥ x) j) ^ 2 := by
    intro x
    have hterm : ∀ s : ι, ∀ i : Fin n,
        (((1 - (πf s).permMatrix ℝ * Qᵀ) *ᵥ x) i) ^ 2 =
          ∑ j : Fin n, ((πf s).permMatrix ℝ) i j * (x i - (Qᵀ *ᵥ x) j) ^ 2 := by
      intro s i
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← Matrix.mulVec_mulVec]
      have hPvec : ((πf s).permMatrix ℝ *ᵥ (Qᵀ *ᵥ x)) i = (Qᵀ *ᵥ x) (πf s i) := by
        simp only [Matrix.mulVec, dotProduct, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
          Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_eq_single (πf s i)]
        · simp
        · intro j _ hj; simp [hj.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hPvec]
      symm
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_eq_single (πf s i)]
      · simp
      · intro j _ hj; simp [hj.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hterm, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    have hQij : Q i j = ∑ s : ι, w s * ((πf s).permMatrix ℝ) i j := by
      rw [hQeq']; simp [Matrix.sum_apply]
    rw [hQij, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro s _; ring
  set γ : ℝ := gammaQ Q (adj G) (adj H)
  have hγ_nn : 0 ≤ γ := gammaQ_nonneg Q (adj G) (adj H)
  have hexp_frob : ∑ s : ι, w s *
      (∑ u : Fin n, ∑ k : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) * At) u k) ^ 2) ≤
      ((n : ℝ) * γ / (2 * t)) ^ 2 := by
    have hfrob_s : ∀ s : ι,
        ∑ u : Fin n, ∑ k : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) * At) u k) ^ 2 =
          ∑ r ∈ It, ∑ u : Fin n,
            (((1 - (πf s).permMatrix ℝ * Qᵀ) *ᵥ (A' *ᵥ (b r).ofLp)) u) ^ 2 := by
      intro s
      rw [frob_eq_sum_onb _ b]
      rw [← Finset.sum_subset (Finset.subset_univ It)]
      · apply Finset.sum_congr rfl; intro r hr
        have hmul : ((1 - (πf s).permMatrix ℝ * Qᵀ) * At) *ᵥ (b r).ofLp =
            (1 - (πf s).permMatrix ℝ * Qᵀ) *ᵥ (A' *ᵥ (b r).ofLp) := by
          rw [← Matrix.mulVec_mulVec, hAt_basis r, if_pos hr, hA'_basis r]
        rw [hmul]
      · intro r _ hr
        have hmul : ((1 - (πf s).permMatrix ℝ * Qᵀ) * At) *ᵥ (b r).ofLp = 0 := by
          rw [← Matrix.mulVec_mulVec, hAt_basis r, if_neg hr, Matrix.mulVec_zero]
        rw [hmul]; simp
    have hlhs_swap : ∑ s : ι, w s *
        (∑ u : Fin n, ∑ k : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) * At) u k) ^ 2) =
        ∑ r ∈ It, ∑ s : ι, w s *
          (∑ u : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) *ᵥ (A' *ᵥ (b r).ofLp)) u) ^ 2) := by
      calc
        _ = ∑ s : ι, ∑ r ∈ It, w s *
              (∑ u : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) *ᵥ (A' *ᵥ (b r).ofLp)) u) ^ 2) := by
              apply Finset.sum_congr rfl; intro s _
              rw [hfrob_s s, Finset.mul_sum]
        _ = _ := Finset.sum_comm
    rw [hlhs_swap]
    have heach_r : ∀ r ∈ It,
        ∑ s : ι, w s *
          (∑ u : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) *ᵥ (A' *ᵥ (b r).ofLp)) u) ^ 2) ≤
          (n : ℝ) ^ 2 * γ ^ 2 := by
      intro r _
      rw [hlem52 (A' *ᵥ (b r).ofLp)]
      have h51 := lemma_51 Q hQ A' B' (b r).ofLp
      rw [hgamma_eq] at h51
      have hbr1 : ∑ k : Fin n, ((b r).ofLp k) ^ 2 = 1 := by
        have h1 : ‖b r‖ ^ 2 = 1 := by rw [b.orthonormal.1 r]; norm_num
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h1
        simpa using h1
      rw [hbr1, mul_one] at h51
      have hmul := mul_le_mul_of_nonneg_left h51 hn2.le
      have hcancel : (n : ℝ) ^ 2 * ((1 / (n : ℝ) ^ 2) *
          ∑ i : Fin n, ∑ j : Fin n,
            Q i j * ((A' *ᵥ (b r).ofLp) i - (Qᵀ *ᵥ (A' *ᵥ (b r).ofLp)) j) ^ 2) =
          ∑ i : Fin n, ∑ j : Fin n,
            Q i j * ((A' *ᵥ (b r).ofLp) i - (Qᵀ *ᵥ (A' *ᵥ (b r).ofLp)) j) ^ 2 := by
        have hn2' : (n : ℝ) ^ 2 ≠ 0 := hn2.ne'
        field_simp
      linarith
    calc
      ∑ r ∈ It, ∑ s : ι, w s *
          (∑ u : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) *ᵥ (A' *ᵥ (b r).ofLp)) u) ^ 2)
          ≤ ∑ _r ∈ It, (n : ℝ) ^ 2 * γ ^ 2 := Finset.sum_le_sum heach_r
      _ = (It.card : ℝ) * ((n : ℝ) ^ 2 * γ ^ 2) := by simp
      _ ≤ (1 / (4 * t ^ 2)) * ((n : ℝ) ^ 2 * γ ^ 2) :=
            mul_le_mul_of_nonneg_right hIt_card (by positivity)
      _ = ((n : ℝ) * γ / (2 * t)) ^ 2 := by ring
  have hexists_s : ∃ s : ι,
      ∑ u : Fin n, ∑ k : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) * At) u k) ^ 2 ≤
        ((n : ℝ) * γ / (2 * t)) ^ 2 := by
    by_contra hnot
    have hgt : ∀ s : ι,
        ((n : ℝ) * γ / (2 * t)) ^ 2 <
          ∑ u : Fin n, ∑ k : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) * At) u k) ^ 2 :=
      fun s => lt_of_not_ge (fun h => hnot ⟨s, h⟩)
    have hex_pos : ∃ s : ι, 0 < w s := by
      by_contra hall0
      have h0 : ∀ s : ι, w s = 0 := fun s =>
        le_antisymm (not_lt.mp fun hp => hall0 ⟨s, hp⟩) (hw0 s)
      have : (∑ s : ι, w s) = 0 := by simp [h0]
      linarith
    rcases hex_pos with ⟨s_pos, hs_pos⟩
    have hstrict : ((n : ℝ) * γ / (2 * t)) ^ 2 <
        ∑ s : ι, w s *
          (∑ u : Fin n, ∑ k : Fin n, (((1 - (πf s).permMatrix ℝ * Qᵀ) * At) u k) ^ 2) := by
      calc
        ((n : ℝ) * γ / (2 * t)) ^ 2
            = ∑ s : ι, w s * ((n : ℝ) * γ / (2 * t)) ^ 2 := by
                rw [← Finset.sum_mul, hw1, one_mul]
        _ < _ := by
              apply Finset.sum_lt_sum
              · intro s _
                exact mul_le_mul_of_nonneg_left (hgt s).le (hw0 s)
              · exact ⟨s_pos, Finset.mem_univ _, mul_lt_mul_of_pos_left (hgt s_pos) hs_pos⟩
    linarith
  rcases hexists_s with ⟨s0, hs0⟩
  set π := πf s0
  set P := π.permMatrix ℝ
  set R := P * Qᵀ
  set E := (1 : Matrix (Fin n) (Fin n) ℝ) - R
  have hR_ds : R ∈ doublyStochastic ℝ (Fin n) :=
    Submonoid.mul_mem _ (perm_ds π) (transpose_ds Q hQ)
  have hR_norm : opNorm 2 2 R ≤ 1 := opNorm_two_ds_le_one R hR_ds
  have hRt_norm : opNorm 2 2 Rᵀ ≤ 1 := (opNorm_two_transpose_le R).trans hR_norm
  have hP_norm : opNorm 2 2 P ≤ 1 := opNorm_two_ds_le_one P (perm_ds π)
  have hPt_norm : opNorm 2 2 Pᵀ ≤ 1 := (opNorm_two_transpose_le P).trans hP_norm
  have hEAt_norm : opNorm 2 2 (E * At) ≤ (n : ℝ) * γ / (2 * t) := by
    calc
      opNorm 2 2 (E * At) ≤ Real.sqrt (∑ u : Fin n, ∑ k : Fin n, (E * At) u k ^ 2) :=
        opNorm_two_le_frob (E * At)
      _ ≤ Real.sqrt (((n : ℝ) * γ / (2 * t)) ^ 2) := Real.sqrt_le_sqrt hs0
      _ = (n : ℝ) * γ / (2 * t) := Real.sqrt_sq (by positivity)
  have hAt_symm : Atᵀ = At := by
    ext i k
    simp only [At, Matrix.transpose_apply, Matrix.of_apply]
    apply Finset.sum_congr rfl; intro r _; ring
  have hAt_split : At - R * At * Rᵀ = E * At + R * (E * At)ᵀ := by
    simp only [E, Matrix.sub_mul, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_sub,
      hAt_symm, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have hAt_part : opNorm 2 2 (At - R * At * Rᵀ) ≤ (n : ℝ) * γ / t := by
    rw [hAt_split]
    have h1 := opNorm_two_add_le (E * At) (R * (E * At)ᵀ)
    have h2 : opNorm 2 2 (R * (E * At)ᵀ) ≤ opNorm 2 2 (E * At) := by
      calc
        opNorm 2 2 (R * (E * At)ᵀ) ≤ opNorm 2 2 R * opNorm 2 2 (E * At)ᵀ := opNorm_two_mul_le _ _
        _ ≤ 1 * opNorm 2 2 (E * At) :=
              mul_le_mul hR_norm (opNorm_two_transpose_le _) (opNorm_two_nonneg _) zero_le_one
        _ = opNorm 2 2 (E * At) := one_mul _
    have hdouble : (n : ℝ) * γ / (2 * t) + (n : ℝ) * γ / (2 * t) = (n : ℝ) * γ / t := by ring
    linarith
  have hDiff_part : opNorm 2 2 ((A' - At) - R * (A' - At) * Rᵀ) ≤ 2 * (n : ℝ) * t := by
    have h1 := opNorm_two_sub_le (A' - At) (R * (A' - At) * Rᵀ)
    have h2 : opNorm 2 2 (R * (A' - At) * Rᵀ) ≤ opNorm 2 2 (A' - At) := by
      calc
        opNorm 2 2 (R * (A' - At) * Rᵀ)
            ≤ opNorm 2 2 (R * (A' - At)) * opNorm 2 2 Rᵀ := opNorm_two_mul_le _ _
        _ ≤ (opNorm 2 2 R * opNorm 2 2 (A' - At)) * opNorm 2 2 Rᵀ :=
              mul_le_mul_of_nonneg_right (opNorm_two_mul_le _ _) (opNorm_two_nonneg _)
        _ ≤ (1 * opNorm 2 2 (A' - At)) * 1 := by
              apply mul_le_mul _ hRt_norm (opNorm_two_nonneg _)
                (mul_nonneg zero_le_one (opNorm_two_nonneg _))
              exact mul_le_mul_of_nonneg_right hR_norm (opNorm_two_nonneg _)
        _ = opNorm 2 2 (A' - At) := by ring
    linarith
  have hA'RAR : opNorm 2 2 (A' - R * A' * Rᵀ) ≤ 2 * (n : ℝ) * t + (n : ℝ) * γ / t := by
    have hsplit : A' - R * A' * Rᵀ =
        ((A' - At) - R * (A' - At) * Rᵀ) + (At - R * At * Rᵀ) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [hsplit]
    exact (opNorm_two_add_le _ _).trans (add_le_add hDiff_part hAt_part)
  have hPQAQ : opNorm 2 2 (P * (Qᵀ * A' * Q - B') * Pᵀ) ≤ (n : ℝ) * γ := by
    have h50 := lemma_50 hn Q hQ A' B'
    rw [hgamma_eq] at h50
    calc
      opNorm 2 2 (P * (Qᵀ * A' * Q - B') * Pᵀ)
          ≤ opNorm 2 2 (P * (Qᵀ * A' * Q - B')) * opNorm 2 2 Pᵀ := opNorm_two_mul_le _ _
      _ ≤ (opNorm 2 2 P * opNorm 2 2 (Qᵀ * A' * Q - B')) * opNorm 2 2 Pᵀ :=
            mul_le_mul_of_nonneg_right (opNorm_two_mul_le _ _) (opNorm_two_nonneg _)
      _ ≤ (1 * ((n : ℝ) * γ)) * 1 := by
            apply mul_le_mul _ hPt_norm (opNorm_two_nonneg _)
              (mul_nonneg zero_le_one (mul_nonneg hnR.le hγ_nn))
            exact mul_le_mul hP_norm h50 (opNorm_two_nonneg _) zero_le_one
      _ = (n : ℝ) * γ := by ring
  have hcenter_eq : adj G - P * adj H * Pᵀ = A' - P * B' * Pᵀ := by
    have hPJP : P * J * Pᵀ = J := by
      ext i k
      dsimp only [P]
      rw [perm_conj_apply]
      simp [J]
    simp only [A', B', Matrix.mul_sub, Matrix.sub_mul, hPJP]
    abel
  have hmain_split : A' - P * B' * Pᵀ =
      (A' - R * A' * Rᵀ) + P * (Qᵀ * A' * Q - B') * Pᵀ := by
    have hRAR : R * A' * Rᵀ = P * (Qᵀ * A' * Q) * Pᵀ := by
      simp only [R, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hRAR]
    simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  have hdOp : dOp 2 2 G H ≤ (n : ℝ) * (γ + 2 * t + γ / t) := by
    calc
      dOp 2 2 G H ≤ costOpPerm 2 2 G H π := Finset.inf'_le _ (Finset.mem_univ π)
      _ ≤ opNorm 2 2 (adj G - P * adj H * Pᵀ) := costOpPerm_le_conj G H π
      _ = opNorm 2 2 ((A' - R * A' * Rᵀ) + P * (Qᵀ * A' * Q - B') * Pᵀ) := by
            rw [hcenter_eq, hmain_split]
      _ ≤ opNorm 2 2 (A' - R * A' * Rᵀ) + opNorm 2 2 (P * (Qᵀ * A' * Q - B') * Pᵀ) :=
            opNorm_two_add_le _ _
      _ ≤ (2 * (n : ℝ) * t + (n : ℝ) * γ / t) + (n : ℝ) * γ := add_le_add hA'RAR hPQAQ
      _ = (n : ℝ) * (γ + 2 * t + γ / t) := by ring
  unfold delta2 deltaOp
  have hexp : (1 : ℝ) / 2 + 1 - 1 / 2 = 1 := by ring
  rw [hexp, Real.rpow_one, div_le_iff₀ hnR]
  linarith

lemma delta2_le_of_Qstar {n : ℕ} (hn : n ≠ 0) (G H : SimpleGraph (Fin n))
    (Qstar : Matrix (Fin n) (Fin n) ℝ) (hQstar : Qstar ∈ DSstar n) :
    delta2 G H ≤ costOp 2 2 G H Qstar + 2 * Real.sqrt (2 * costOp 2 2 G H Qstar) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  let Q : Matrix (Fin n) (Fin n) ℝ := (n : ℝ) • Qstar
  have hQ : Q ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => mul_nonneg hnR.le (hQstar.1 i j), ?_, ?_⟩
    · intro i
      simp only [Q, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hQstar.2.1 i]
      exact mul_one_div_cancel hnR.ne'
    · intro j
      simp only [Q, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hQstar.2.2 j]
      exact mul_one_div_cancel hnR.ne'
  set γ : ℝ := gammaQ Q (adj G) (adj H)
  have hγ_nn : 0 ≤ γ := gammaQ_nonneg Q (adj G) (adj H)
  have hγ_le : γ ≤ costOp 2 2 G H Qstar := gammaQ_le_costOp hn G H Qstar hQstar
  have hbound_γ : delta2 G H ≤ γ + 2 * Real.sqrt (2 * γ) := by
    rcases hγ_nn.eq_or_lt with h0 | hpos
    · rw [← h0]; simp only [mul_zero, Real.sqrt_zero, add_zero]
      by_contra hgt
      have hd_pos : 0 < delta2 G H := lt_of_not_ge hgt
      let t : ℝ := delta2 G H / 4
      have ht_pos : 0 < t := by positivity
      have hle : delta2 G H ≤ γ + 2 * t + γ / t :=
        delta2_le_of_ds_pos_t hn G H Q hQ t ht_pos
      rw [← h0, zero_div, zero_add, add_zero] at hle
      linarith [show 2 * t = delta2 G H / 2 by simp [t]; ring]
    · let t : ℝ := Real.sqrt (γ / 2)
      have ht_pos : 0 < t := Real.sqrt_pos.mpr (by positivity)
      have hle : delta2 G H ≤ γ + 2 * t + γ / t :=
        delta2_le_of_ds_pos_t hn G H Q hQ t ht_pos
      have hcalc : 2 * t + γ / t = 2 * Real.sqrt (2 * γ) := by
        have ht_sq : t * t = γ / 2 := Real.mul_self_sqrt (by positivity)
        have hdiv : γ / t = 2 * t := by
          rw [div_eq_iff ht_pos.ne']
          linarith
        have h2γ : Real.sqrt (2 * γ) = 2 * t := by
          have h1 : (2 * t) ^ 2 = 2 * γ := by nlinarith
          rw [← h1, Real.sqrt_sq (by positivity)]
        linarith
      linarith
  have hsqrt_le : Real.sqrt (2 * γ) ≤ Real.sqrt (2 * costOp 2 2 G H Qstar) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

end Theorem14Aux

theorem solution {n : ℕ} (G H : SimpleGraph (Fin n)) :
    delta2 G H ≤ deltaOT2 G H + 2 * Real.sqrt (2 * deltaOT2 G H) := by
  by_cases hn : n = 0
  · subst hn
    have h0 : delta2 G H = 0 := by simp [delta2, deltaOp]
    have hOT_nn : 0 ≤ deltaOT2 G H := by
      apply Real.sInf_nonneg
      rintro _ ⟨_, -, rfl⟩
      exact Theorem14Aux.opNorm_two_nonneg _
    rw [h0]
    positivity
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  set δ : ℝ := deltaOT2 G H
  have hDS_ne : (DSstar n).Nonempty := by
    refine ⟨(1 / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ), ?_, ?_, ?_⟩
    · intro i j; simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> positivity
    · intro i; simp [Matrix.one_apply]
    · intro j; simp [Matrix.one_apply]
  have hδ_nn : 0 ≤ δ := by
    apply Real.sInf_nonneg
    rintro _ ⟨_, -, rfl⟩
    exact Theorem14Aux.opNorm_two_nonneg _
  by_contra hgt
  set d : ℝ := delta2 G H - (δ + 2 * Real.sqrt (2 * δ))
  have hd_pos : 0 < d := sub_pos.mpr (lt_of_not_ge hgt)
  let ε : ℝ := min (d / 4) (d ^ 2 / 32)
  have hε_pos : 0 < ε := lt_min (by positivity) (by positivity)
  rcases exists_lt_of_csInf_lt (hDS_ne.image (costOp 2 2 G H))
      (lt_add_of_pos_right δ hε_pos) with ⟨c, ⟨Qstar, hQstar, rfl⟩, hc_lt⟩
  have hQ_bound := Theorem14Aux.delta2_le_of_Qstar hn G H Qstar hQstar
  have hc_nn : 0 ≤ costOp 2 2 G H Qstar := Theorem14Aux.opNorm_two_nonneg _
  have hsqrt_sub : Real.sqrt (2 * (δ + ε)) ≤ Real.sqrt (2 * δ) + Real.sqrt (2 * ε) := by
    have ha : 0 ≤ 2 * δ := by positivity
    have hb : 0 ≤ 2 * ε := by positivity
    rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    apply Real.sqrt_le_sqrt
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    have : 0 ≤ 2 * Real.sqrt (2 * δ) * Real.sqrt (2 * ε) := by positivity
    linarith
  have hsqrt_le : Real.sqrt (2 * costOp 2 2 G H Qstar) ≤
      Real.sqrt (2 * δ) + Real.sqrt (2 * ε) :=
    (Real.sqrt_le_sqrt (by linarith)).trans hsqrt_sub
  have hε1 : ε ≤ d / 4 := min_le_left _ _
  have hε2 : 2 * Real.sqrt (2 * ε) ≤ d / 2 := by
    have hle32 : 2 * ε ≤ (d / 4) ^ 2 := by
      have : ε ≤ d ^ 2 / 32 := min_le_right _ _
      linarith
    have hsq1 : Real.sqrt (2 * ε) ≤ d / 4 :=
      (Real.sqrt_le_sqrt hle32).trans_eq (Real.sqrt_sq (by positivity))
    linarith
  linarith
