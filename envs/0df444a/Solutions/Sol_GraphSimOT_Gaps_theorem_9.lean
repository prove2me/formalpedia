-- Prove2me | solution 1 for GraphSimOT.Gaps.theorem_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:41:53.323843+00:00
-- url     : https://prove2.me/submissions/f69bad85-f48d-4f7e-b29e-0aa704465fa1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances
import Definitions.Def_GraphSimOT_Gaps_LocalEdit
import Theorems.Thm_GraphSimOT_Gaps_lemma_29
import Theorems.Thm_GraphSimOT_Gaps_proposition_32

open Matrix Filter Topology GraphSimOT.Gaps

namespace Theorem9Aux

lemma lpNorm_one_eq_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    lpNorm 1 x = ∑ i : ι, |x i| := by
  unfold lpNorm
  simp

lemma opNorm_one_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) :
    0 ≤ opNorm 1 1 M := by
  apply Real.sSup_nonneg
  rintro _ ⟨x, -, rfl⟩
  dsimp only
  rw [lpNorm_one_eq_sum]
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma opNorm_one_le_of_col {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j : κ, ∑ i : ι, |M i j| ≤ C) : opNorm 1 1 M ≤ C := by
  apply Real.sSup_le _ hC
  rintro _ ⟨x, hx, rfl⟩
  change lpNorm 1 x = 1 at hx
  dsimp only
  rw [lpNorm_one_eq_sum] at hx ⊢
  calc
    ∑ i : ι, |(M *ᵥ x) i|
        ≤ ∑ i : ι, ∑ j : κ, |M i j| * |x j| := by
          apply Finset.sum_le_sum; intro i _
          simp only [Matrix.mulVec, dotProduct]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
    _ = ∑ j : κ, (∑ i : ι, |M i j|) * |x j| := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]
    _ ≤ ∑ j : κ, C * |x j| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h j) (abs_nonneg _)
    _ = C := by rw [← Finset.mul_sum, hx, mul_one]

lemma opNorm_one_bddAbove {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℝ) :
    BddAbove ((fun x : κ → ℝ => lpNorm 1 (M *ᵥ x)) '' {x | lpNorm 1 x = 1}) := by
  refine ⟨∑ i : ι, ∑ j : κ, |M i j|, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  change lpNorm 1 x = 1 at hx
  dsimp only
  rw [lpNorm_one_eq_sum] at hx ⊢
  calc
    ∑ i : ι, |(M *ᵥ x) i|
        ≤ ∑ i : ι, ∑ j : κ, |M i j| * |x j| := by
          apply Finset.sum_le_sum; intro i _
          simp only [Matrix.mulVec, dotProduct]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
    _ = ∑ j : κ, (∑ i : ι, |M i j|) * |x j| := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]
    _ ≤ ∑ j : κ, (∑ i : ι, ∑ k : κ, |M i k|) * |x j| := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          apply Finset.sum_le_sum; intro i _
          exact Finset.single_le_sum (fun k _ => abs_nonneg (M i k)) (Finset.mem_univ j)
    _ = ∑ i : ι, ∑ k : κ, |M i k| := by rw [← Finset.mul_sum, hx, mul_one]

lemma adj_symm {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    adj G u v = adj G v u := by
  unfold adj
  by_cases h : G.Adj u v
  · simp [h, h.symm]
  · have h' : ¬ G.Adj v u := fun hvu => h hvu.symm
    simp [h, h']

lemma localCost_le_costOp_of_pos {n : ℕ} (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (v w : Fin n) (hpos : 0 < Q v w) :
    localCost G H Q v w ≤ costOp 1 1 G H Q := by
  classical
  rw [mem_doublyStochastic_iff_sum] at hQ
  rcases hQ with ⟨hQnn, -, -⟩
  let b0 : Fin n × Fin n := (v, w)
  let e : Fin n × Fin n → ℝ := fun b => if b = b0 then 1 else 0
  have he_norm : lpNorm 1 e = 1 := by
    rw [lpNorm_one_eq_sum, Finset.sum_eq_single b0]
    · simp [e]
    · intro b _ hb; simp [e, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hBe : lpNorm 1 (Bpq 1 1 G H Q *ᵥ e) = localCost G H Q v w := by
    rw [lpNorm_one_eq_sum, Fintype.sum_prod_type]
    unfold localCost
    apply Finset.sum_congr rfl; intro v' _
    apply Finset.sum_congr rfl; intro w' _
    have hmul : (Bpq 1 1 G H Q *ᵥ e) (v', w') = Bpq 1 1 G H Q (v', w') (v, w) := by
      simp only [Matrix.mulVec, dotProduct, e, b0, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single (v, w)]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hmul]
    have hval : Bpq 1 1 G H Q (v', w') (v, w) = Q v' w' * (adj G v' v - adj H w' w) := by
      unfold Bpq disc pow00
      dsimp only
      have hexp1 : (1 : ℝ) / 1 = 1 := by ring
      have hexp0 : (1 : ℝ) - 1 = 0 := by ring
      rw [hexp1, hexp0, if_neg hpos.ne', Real.rpow_zero, mul_one]
      congr 1
      split_ifs with h0
      · exact h0.symm
      · exact Real.rpow_one _
    rw [hval, abs_mul, abs_of_nonneg (hQnn v' w'), adj_symm G v' v, adj_symm H w' w, mul_comm]
  rw [← hBe]
  exact le_csSup (opNorm_one_bddAbove _) ⟨e, he_norm, rfl⟩

lemma exists_optimal_Q {n : ℕ} (G H : SimpleGraph (Fin n)) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ, Q ∈ doublyStochastic ℝ (Fin n) ∧
      (∀ v w, 0 < Q v w → localCost G H Q v w ≤ dOT1 G H) ∧
      ∃ σ : Equiv.Perm (Fin n), ∀ v, 0 < Q v (σ v) := by
  classical
  let K : Set (Fin n → Fin n → ℝ) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1
  have hcomp : IsCompact K :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hDS_ne : (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)).Nonempty :=
    ⟨1, Submonoid.one_mem _⟩
  have hseq : ∀ k : ℕ, ∃ Qk ∈ doublyStochastic ℝ (Fin n),
      costOp 1 1 G H Qk < dOT1 G H + 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    rcases exists_lt_of_csInf_lt (hDS_ne.image (costOp 1 1 G H))
        (lt_add_of_pos_right (dOT1 G H) hpos) with ⟨_, ⟨Qk, hQk, rfl⟩, hlt⟩
    exact ⟨Qk, hQk, hlt⟩
  choose Qseq hQseq_mem hQseq_lt using hseq
  let fseq : ℕ → (Fin n → Fin n → ℝ) := fun k i j => Qseq k i j
  have hfseq_K : ∀ k : ℕ, fseq k ∈ K := by
    intro k i _ j _
    have hk := (mem_doublyStochastic_iff_sum).mp (hQseq_mem k)
    refine ⟨hk.1 i j, ?_⟩
    calc
      Qseq k i j ≤ ∑ j' : Fin n, Qseq k i j' :=
        Finset.single_le_sum (fun j' _ => hk.1 i j') (Finset.mem_univ j)
      _ = 1 := hk.2.1 i
  rcases hcomp.tendsto_subseq hfseq_K with ⟨Qfun, hQfun_K, φ, hφ_mono, hφ_tend⟩
  let Q : Matrix (Fin n) (Fin n) ℝ := Matrix.of Qfun
  have hentry_tend : ∀ u x : Fin n,
      Tendsto (fun m => Qseq (φ m) u x) atTop (𝓝 (Q u x)) := by
    intro u x
    exact ((continuous_apply x).comp (continuous_apply u)).tendsto Qfun |>.comp hφ_tend
  have hQ : Q ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => (hQfun_K i trivial j trivial).1, ?_, ?_⟩
    · intro i
      have ht1 : Tendsto (fun m => ∑ j : Fin n, Qseq (φ m) i j) atTop (𝓝 (∑ j : Fin n, Q i j)) :=
        tendsto_finsetSum _ fun j _ => hentry_tend i j
      have heq1 : (fun m => ∑ j : Fin n, Qseq (φ m) i j) = fun _ => (1 : ℝ) := by
        ext m; exact ((mem_doublyStochastic_iff_sum).mp (hQseq_mem (φ m))).2.1 i
      rw [heq1] at ht1
      exact tendsto_nhds_unique ht1 tendsto_const_nhds
    · intro j
      have ht1 : Tendsto (fun m => ∑ i : Fin n, Qseq (φ m) i j) atTop (𝓝 (∑ i : Fin n, Q i j)) :=
        tendsto_finsetSum _ fun i _ => hentry_tend i j
      have heq1 : (fun m => ∑ i : Fin n, Qseq (φ m) i j) = fun _ => (1 : ℝ) := by
        ext m; exact ((mem_doublyStochastic_iff_sum).mp (hQseq_mem (φ m))).2.2 j
      rw [heq1] at ht1
      exact tendsto_nhds_unique ht1 tendsto_const_nhds
  have hQopt : ∀ v w : Fin n, 0 < Q v w → localCost G H Q v w ≤ dOT1 G H := by
    intro v w hpos
    have hev_pos : ∀ᶠ m in atTop, 0 < Qseq (φ m) v w :=
      (hentry_tend v w).eventually (lt_mem_nhds hpos)
    have hev_le : ∀ᶠ m in atTop,
        localCost G H (Qseq (φ m)) v w ≤ dOT1 G H + 1 / ((φ m : ℝ) + 1) := by
      filter_upwards [hev_pos] with m hm
      exact (localCost_le_costOp_of_pos G H (Qseq (φ m)) (hQseq_mem (φ m)) v w hm).trans
        (hQseq_lt (φ m)).le
    have hloc_tend : Tendsto (fun m => localCost G H (Qseq (φ m)) v w) atTop
        (𝓝 (localCost G H Q v w)) := by
      unfold localCost
      apply tendsto_finsetSum; intro v' _
      apply tendsto_finsetSum; intro w' _
      exact tendsto_const_nhds.mul (hentry_tend v' w')
    have hzero : Tendsto (fun m => 1 / ((φ m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ_mono.tendsto_atTop
    have hrhs_tend : Tendsto (fun m => dOT1 G H + 1 / ((φ m : ℝ) + 1)) atTop (𝓝 (dOT1 G H)) := by
      simpa using (tendsto_const_nhds (x := dOT1 G H)).add hzero
    exact le_of_tendsto_of_tendsto hloc_tend hrhs_tend hev_le
  have hconv : Q ∈ convexHull ℝ
      {x : Matrix (Fin n) (Fin n) ℝ | ∃ σ : Equiv.Perm (Fin n), σ.permMatrix ℝ = x} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]; exact hQ
  rw [mem_convexHull_iff_exists_fintype] at hconv
  rcases hconv with ⟨ι, instFintype, w, z, hw0, hw1, hz, hQeq⟩
  choose πf hπf using hz
  have hex_pos : ∃ i0 : ι, 0 < w i0 := by
    by_contra hall0
    have h0 : ∀ i : ι, w i = 0 := fun i =>
      le_antisymm (not_lt.mp fun hp => hall0 ⟨i, hp⟩) (hw0 i)
    have : (∑ i : ι, w i) = 0 := by simp [h0]
    linarith
  rcases hex_pos with ⟨i0, hi0⟩
  refine ⟨Q, hQ, hQopt, πf i0, ?_⟩
  intro v
  have hQval : Q v (πf i0 v) = ∑ i : ι, w i * ((πf i).permMatrix ℝ) v (πf i0 v) := by
    rw [← hQeq]
    have h1 : (∑ i : ι, w i • z i) v (πf i0 v) = ∑ i : ι, w i * z i v (πf i0 v) := by
      simp [Matrix.sum_apply]
    rw [h1]
    apply Finset.sum_congr rfl; intro i _; rw [hπf i]
  rw [hQval]
  have hterm_nn : ∀ i : ι, 0 ≤ w i * ((πf i).permMatrix ℝ) v (πf i0 v) := by
    intro i
    apply mul_nonneg (hw0 i)
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq]
    split_ifs <;> norm_num
  have hterm_i0 : w i0 * ((πf i0).permMatrix ℝ) v (πf i0 v) = w i0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have hle_sum := Finset.single_le_sum (fun i _ => hterm_nn i) (Finset.mem_univ i0)
  linarith

lemma dOT1_eq_mul_deltaOT1 {n : ℕ} (hn : n ≠ 0) (G H : SimpleGraph (Fin n)) :
    dOT1 G H = (n : ℝ) * deltaOT1 G H := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hBpq_scale : ∀ (c : ℝ), 0 < c → ∀ M : Matrix (Fin n) (Fin n) ℝ,
      Bpq 1 1 G H (c • M) = c • Bpq 1 1 G H M := by
    intro c hc M
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    unfold Bpq pow00
    simp only [Matrix.smul_apply, smul_eq_mul]
    have hexp1 : (1 : ℝ) / 1 = 1 := by ring
    have hexp0 : (1 : ℝ) - 1 = 0 := by ring
    rw [hexp1, hexp0]
    have hc0 : ∀ x : ℝ, (c * x = 0) ↔ (x = 0) := fun x => mul_eq_zero_iff_left hc.ne'
    simp only [hc0]
    by_cases ha : M a.1 a.2 = 0
    · simp [ha]
    · by_cases hb : M b.1 b.2 = 0
      · simp [ha, hb]
      · simp only [ha, hb, ↓reduceIte, Real.rpow_one, Real.rpow_zero]
        ring
  have hcost_le : ∀ (c : ℝ), 0 < c → ∀ M : Matrix (Fin n) (Fin n) ℝ,
      costOp 1 1 G H (c • M) ≤ c * costOp 1 1 G H M := by
    intro c hc M
    unfold costOp
    rw [hBpq_scale c hc M]
    apply Real.sSup_le _ (mul_nonneg hc.le (opNorm_one_nonneg _))
    rintro _ ⟨x, hx, rfl⟩
    dsimp only
    have hmul : lpNorm 1 ((c • Bpq 1 1 G H M) *ᵥ x) = c * lpNorm 1 (Bpq 1 1 G H M *ᵥ x) := by
      rw [Matrix.smul_mulVec, lpNorm_one_eq_sum, lpNorm_one_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc]
    rw [hmul]
    exact mul_le_mul_of_nonneg_left (le_csSup (opNorm_one_bddAbove _) ⟨x, hx, rfl⟩) hc.le
  have hDS_ne : (DSstar n).Nonempty := by
    refine ⟨(1 / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ), ?_, ?_, ?_⟩
    · intro i j; simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> positivity
    · intro i; simp [Matrix.one_apply]
    · intro j; simp [Matrix.one_apply]
  have hds_ne : (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)).Nonempty :=
    ⟨1, Submonoid.one_mem _⟩
  apply le_antisymm
  · rw [← div_le_iff₀' hnR]
    apply le_csInf (hDS_ne.image _)
    rintro _ ⟨Qstar, hQstar, rfl⟩
    rw [div_le_iff₀' hnR]
    let Q := (n : ℝ) • Qstar
    have hQ : Q ∈ doublyStochastic ℝ (Fin n) := by
      rw [mem_doublyStochastic_iff_sum]
      refine ⟨fun i j => mul_nonneg hnR.le (hQstar.1 i j), ?_, ?_⟩
      · intro i; simp only [Q, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hQstar.2.1 i]
        exact mul_one_div_cancel hnR.ne'
      · intro j; simp only [Q, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hQstar.2.2 j]
        exact mul_one_div_cancel hnR.ne'
    have hbdd : BddBelow (costOp 1 1 G H '' (doublyStochastic ℝ (Fin n) : Set _)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨_, -, rfl⟩
      exact opNorm_one_nonneg _
    exact (csInf_le hbdd ⟨Q, hQ, rfl⟩).trans (hcost_le n hnR Qstar)
  · apply le_csInf (hds_ne.image _)
    rintro _ ⟨Q, hQ, rfl⟩
    change Q ∈ doublyStochastic ℝ (Fin n) at hQ
    rw [mem_doublyStochastic_iff_sum] at hQ
    rcases hQ with ⟨hQnn, hQrow, hQcol⟩
    let Qstar : Matrix (Fin n) (Fin n) ℝ := (1 / (n : ℝ)) • Q
    have hQstar : Qstar ∈ DSstar n := by
      refine ⟨fun i j => mul_nonneg (by positivity) (hQnn i j), ?_, ?_⟩
      · intro i; simp [Qstar, ← Finset.mul_sum, hQrow i]
      · intro j; simp [Qstar, ← Finset.mul_sum, hQcol j]
    have hbdd : BddBelow (costOp 1 1 G H '' DSstar n) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨_, -, rfl⟩
      exact opNorm_one_nonneg _
    have hle := (csInf_le hbdd ⟨Qstar, hQstar, rfl⟩).trans (hcost_le (1 / (n : ℝ)) (by positivity) Q)
    have := mul_le_mul_of_nonneg_left hle hnR.le
    have hcancel : (n : ℝ) * (1 / (n : ℝ) * costOp 1 1 G H Q) = costOp 1 1 G H Q := by
      field_simp
    unfold deltaOT1 deltaOTOp
    linarith

lemma d1_le_zero_of_iso {n : ℕ} (G H : SimpleGraph (Fin n)) (φ : G ≃g H) :
    d1 G H ≤ 0 := by
  unfold d1 dOp
  refine (Finset.inf'_le _ (Finset.mem_univ φ.toEquiv)).trans ?_
  unfold costOpPerm
  apply opNorm_one_le_of_col _ le_rfl
  intro w'
  apply Finset.sum_nonpos; intro w _
  have h0 : (permAdj G φ.toEquiv - adj H) w w' = 0 := by
    simp only [Matrix.sub_apply, permAdj, adj]
    have hiff : G.Adj (φ.toEquiv.symm w) (φ.toEquiv.symm w') ↔ H.Adj w w' := by
      have := φ.map_rel_iff' (a := φ.toEquiv.symm w) (b := φ.toEquiv.symm w')
      simpa using this.symm
    by_cases hw : H.Adj w w'
    · simp [hw, hiff.mpr hw]
    · have hnw : ¬ G.Adj (φ.toEquiv.symm w) (φ.toEquiv.symm w') := fun hg => hw (hiff.mp hg)
      simp [hw, hnw]
  rw [h0, abs_zero]

lemma d1_le_n {n : ℕ} (G H : SimpleGraph (Fin n)) : d1 G H ≤ n := by
  unfold d1 dOp
  refine (Finset.inf'_le _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))).trans ?_
  apply opNorm_one_le_of_col _ (Nat.cast_nonneg n)
  intro j
  calc
    ∑ i : Fin n, |(permAdj G 1 - adj H) i j| ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum; intro i _
      simp only [Matrix.sub_apply, permAdj, adj]
      split_ifs <;> norm_num
    _ = n := by simp

lemma dOT1_le_n {n : ℕ} (G H : SimpleGraph (Fin n)) : dOT1 G H ≤ n := by
  have hbdd : BddBelow (costOp 1 1 G H '' (doublyStochastic ℝ (Fin n) : Set _)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨_, -, rfl⟩
    exact opNorm_one_nonneg _
  refine (csInf_le hbdd ⟨1, Submonoid.one_mem _, rfl⟩).trans ?_
  apply opNorm_one_le_of_col _ (Nat.cast_nonneg n)
  intro b
  rw [Fintype.sum_prod_type]
  by_cases hdiag : b.1 = b.2
  · calc
      ∑ v : Fin n, ∑ w : Fin n, |Bpq 1 1 G H 1 (v, w) b|
          ≤ ∑ v : Fin n, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro v _
            rw [Finset.sum_eq_single v]
            · unfold Bpq disc pow00 adj
              simp only [Matrix.one_apply, ↓reduceIte, one_ne_zero, hdiag]
              norm_num
              split_ifs <;> norm_num
            · intro w _ hw
              unfold Bpq pow00
              simp [Matrix.one_apply, hw.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
      _ = n := by simp
  · calc
      ∑ v : Fin n, ∑ w : Fin n, |Bpq 1 1 G H 1 (v, w) b| ≤ 0 := by
        apply Finset.sum_nonpos; intro v _
        apply Finset.sum_nonpos; intro w _
        unfold Bpq pow00
        simp [Matrix.one_apply, hdiag]
      _ ≤ n := Nat.cast_nonneg n

lemma log_four_div_antitone {y x : ℝ} (hy1 : 1 ≤ y) (hyx : y ≤ x) :
    Real.log (4 * x) / x ≤ Real.log (4 * y) / y := by
  have hy_pos : 0 < y := by linarith
  have hx_pos : 0 < x := by linarith
  rw [div_le_div_iff₀ hx_pos hy_pos]
  set u : ℝ := x / y
  have hu1 : 1 ≤ u := (one_le_div hy_pos).mpr hyx
  have hu_pos : 0 < u := by linarith
  have hx_eq : x = u * y := by simp only [u]; field_simp
  have hlog_prod : Real.log (4 * x) = Real.log (4 * y) + Real.log u := by
    rw [hx_eq, show 4 * (u * y) = (4 * y) * u by ring]
    exact Real.log_mul (by positivity) hu_pos.ne'
  have hlog4_ge1 : 1 ≤ Real.log (4 * y) := by
    have hexp : Real.exp 1 ≤ 4 * y := by
      have he1 := Real.exp_one_lt_d9
      linarith
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (4 * y) := Real.log_le_log (Real.exp_pos 1) hexp
  have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu_pos
  have hmul_log : Real.log u ≤ (u - 1) * Real.log (4 * y) := by
    calc
      Real.log u ≤ (u - 1) * 1 := by linarith
      _ ≤ (u - 1) * Real.log (4 * y) := mul_le_mul_of_nonneg_left hlog4_ge1 (by linarith)
  rw [hlog_prod, hx_eq]
  nlinarith

lemma const_bound_15 :
    (4 + 2 * Real.sqrt 2) / Real.sqrt (Real.log 4) + 4 * Real.sqrt 5 ≤ 15 := by
  have hlog4 : (4 : ℝ) / 3 < Real.log 4 := by
    have hexp : Real.exp (4 / 3) < 4 := by
      have he_nn : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
      have he_lt : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
      have hpow : Real.exp (4 / 3) ^ 3 = Real.exp 1 ^ 4 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1; norm_num
      have hlt_pow : Real.exp 1 ^ 4 < (2.72 : ℝ) ^ 4 :=
        pow_lt_pow_left₀ he_lt he_nn (by norm_num)
      have hlt64 : Real.exp 1 ^ 4 < (4 : ℝ) ^ 3 := by
        linarith [show (2.72 : ℝ) ^ 4 < (4 : ℝ) ^ 3 by norm_num]
      by_contra hge
      have hge' : 4 ≤ Real.exp (4 / 3) := le_of_not_gt hge
      have : (4 : ℝ) ^ 3 ≤ Real.exp (4 / 3) ^ 3 := pow_le_pow_left₀ (by norm_num) hge' 3
      linarith
    have := Real.log_lt_log (Real.exp_pos _) hexp
    rwa [Real.log_exp] at this
  have hsqrt_log4 : (23 : ℝ) / 20 ≤ Real.sqrt (Real.log 4) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 23 / 20)]
    apply Real.sqrt_le_sqrt
    linarith [show ((23 : ℝ) / 20) ^ 2 < 4 / 3 by norm_num]
  have hsqrt2 : Real.sqrt 2 ≤ (71 : ℝ) / 50 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 71 / 50)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt5 : Real.sqrt 5 ≤ (56 : ℝ) / 25 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 56 / 25)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpos_slog : 0 < Real.sqrt (Real.log 4) := by linarith
  rw [← sub_nonneg]
  have hdiv : (4 + 2 * Real.sqrt 2) / Real.sqrt (Real.log 4) ≤
      (4 + 2 * ((71 : ℝ) / 50)) / ((23 : ℝ) / 20) := by
    calc
      (4 + 2 * Real.sqrt 2) / Real.sqrt (Real.log 4)
          ≤ (4 + 2 * ((71 : ℝ) / 50)) / Real.sqrt (Real.log 4) :=
            div_le_div_of_nonneg_right (by linarith) hpos_slog.le
      _ ≤ (4 + 2 * ((71 : ℝ) / 50)) / ((23 : ℝ) / 20) :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsqrt_log4
  linarith

end Theorem9Aux

theorem solution {n : ℕ} (G H : SimpleGraph (Fin n)) :
    delta1 G H ≤ 15 * Real.sqrt (deltaOT1 G H * Real.log (4 / deltaOT1 G H)) := by
  classical
  have hrhs_nn : 0 ≤ 15 * Real.sqrt (deltaOT1 G H * Real.log (4 / deltaOT1 G H)) := by positivity
  by_cases hn : n = 0
  · subst hn
    have h0 : delta1 G H = 0 := by simp [delta1, deltaOp]
    linarith
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hdel1_eq : delta1 G H = d1 G H / n := by
    unfold delta1 deltaOp
    have hexp : (1 : ℝ) / 1 + 1 - 1 / 1 = 1 := by ring
    rw [hexp, Real.rpow_one]; rfl
  by_cases hiso : Nonempty (G ≃g H)
  · rcases hiso with ⟨φ⟩
    have hd0 : d1 G H ≤ 0 := Theorem9Aux.d1_le_zero_of_iso G H φ
    have : delta1 G H ≤ 0 := by
      rw [hdel1_eq]; exact div_nonpos_of_nonpos_of_nonneg hd0 hnR.le
    linarith
  have hemp : IsEmpty (G ≃g H) := not_nonempty_iff.mp hiso
  rcases Theorem9Aux.exists_optimal_Q G H with ⟨Q, hQ, hQopt, σ, hσ⟩
  have hL_ge1 : 1 ≤ dOT1 G H := (lemma_29 G H Q hQ hQopt σ hσ).2.2 hemp
  set L : ℝ := dOT1 G H
  set f : ℝ := deltaOT1 G H
  have hL_pos : 0 < L := by linarith
  have hLf : L = (n : ℝ) * f := Theorem9Aux.dOT1_eq_mul_deltaOT1 hn G H
  have hf_eq : f = L / n := by rw [hLf]; field_simp
  have hf_pos : 0 < f := by rw [hf_eq]; positivity
  have hf_le1 : f ≤ 1 := by
    rw [hf_eq, div_le_one hnR]
    exact Theorem9Aux.dOT1_le_n G H
  have heq20 : d1 G H ≤ 4 * L + 2 * Real.sqrt (2 * n * L) +
      4 * Real.sqrt (5 * n * Real.log (4 * n)) := by
    let ℓ : ℕ := ⌈Real.sqrt ((n : ℝ) / (2 * L))⌉₊
    have hs_pos : 0 < Real.sqrt ((n : ℝ) / (2 * L)) := Real.sqrt_pos.mpr (by positivity)
    have hℓ_pos : 0 < ℓ := Nat.ceil_pos.mpr (by positivity)
    have hℓR_pos : (0 : ℝ) < ℓ := Nat.cast_pos.mpr hℓ_pos
    have hℓ_ge : Real.sqrt ((n : ℝ) / (2 * L)) ≤ ℓ := Nat.le_ceil _
    have hℓ_le : (ℓ : ℝ) ≤ Real.sqrt ((n : ℝ) / (2 * L)) + 1 :=
      (Nat.ceil_lt_add_one hs_pos.le).le
    have hbal_ℓ : (n : ℝ) / ℓ + 2 * ℓ * L ≤ 2 * Real.sqrt (2 * n * L) + 2 * L := by
      have h1 : (n : ℝ) / ℓ ≤ (n : ℝ) / Real.sqrt ((n : ℝ) / (2 * L)) :=
        div_le_div_of_nonneg_left hnR.le hs_pos hℓ_ge
      have h2 : 2 * (ℓ : ℝ) * L ≤ 2 * (Real.sqrt ((n : ℝ) / (2 * L)) + 1) * L := by
        nlinarith
      have hprod : Real.sqrt ((n : ℝ) / (2 * L)) * Real.sqrt (2 * n * L) = n := by
        rw [← Real.sqrt_mul (by positivity)]
        have : (n : ℝ) / (2 * L) * (2 * n * L) = (n : ℝ) ^ 2 := by field_simp
        rw [this, Real.sqrt_sq hnR.le]
      have hdiv_eq : (n : ℝ) / Real.sqrt ((n : ℝ) / (2 * L)) = Real.sqrt (2 * n * L) := by
        rw [div_eq_iff hs_pos.ne']; linarith
      have hmul_eq : 2 * Real.sqrt ((n : ℝ) / (2 * L)) * L = Real.sqrt (2 * n * L) := by
        have hsq : (2 * Real.sqrt ((n : ℝ) / (2 * L)) * L) ^ 2 = 2 * n * L := by
          calc
            (2 * Real.sqrt ((n : ℝ) / (2 * L)) * L) ^ 2
                = 4 * L ^ 2 * (Real.sqrt ((n : ℝ) / (2 * L)) ^ 2) := by ring
            _ = 4 * L ^ 2 * ((n : ℝ) / (2 * L)) := by rw [Real.sq_sqrt (by positivity)]
            _ = 2 * n * L := by field_simp; ring
        rw [← hsq, Real.sqrt_sq (by positivity)]
      linarith
    have hlog4n_pos : 0 < Real.log (4 * n) := Real.log_pos (by linarith)
    let γstar : ℝ := Real.sqrt (5 * Real.log (4 * n) / n)
    have hγ_pos : 0 < γstar := Real.sqrt_pos.mpr (by positivity)
    have hγ_prod : γstar * Real.sqrt (5 * n * Real.log (4 * n)) = 5 * Real.log (4 * n) := by
      dsimp only [γstar]
      rw [← Real.sqrt_mul (by positivity)]
      have : 5 * Real.log (4 * n) / n * (5 * n * Real.log (4 * n)) =
          (5 * Real.log (4 * n)) ^ 2 := by field_simp
      rw [this, Real.sqrt_sq (by positivity)]
    have hγ_mul_n : γstar * n = Real.sqrt (5 * n * Real.log (4 * n)) := by
      have hsq : (γstar * n) ^ 2 = 5 * n * Real.log (4 * n) := by
        dsimp only [γstar]
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        field_simp
      rw [← hsq, Real.sqrt_sq (by positivity)]
    by_cases hγ_half : γstar ≤ 1 / 2
    · have hp32 := proposition_32 G H Q hQ hQopt hL_pos γstar hγ_pos hγ_half ℓ hℓ_pos
      have hbal_γ : 10 * Real.log (4 * n) / γstar + 2 * γstar * n =
          4 * Real.sqrt (5 * n * Real.log (4 * n)) := by
        have hdiv : 10 * Real.log (4 * n) / γstar =
            2 * Real.sqrt (5 * n * Real.log (4 * n)) := by
          rw [div_eq_iff hγ_pos.ne']
          linarith
        linarith
      linarith
    · have hγ_gt : 1 / 2 < γstar := lt_of_not_ge hγ_half
      have hd_le_n : d1 G H ≤ n := Theorem9Aux.d1_le_n G H
      have h2n : 2 * (n : ℝ) < 4 * Real.sqrt (5 * n * Real.log (4 * n)) := by
        have : (n : ℝ) / 2 < γstar * n := by
          have := mul_lt_mul_of_pos_right hγ_gt hnR
          linarith
        linarith
      have : 0 ≤ Real.sqrt (2 * n * L) := Real.sqrt_nonneg _
      linarith
  have h1_div_f_ge1 : 1 ≤ 1 / f := (one_le_div hf_pos).mpr hf_le1
  have h1_div_f_le_n : 1 / f ≤ n := by
    rw [div_le_iff₀ hf_pos, ← hLf]
    linarith
  have hlog_le : Real.log (4 * n) / n ≤ f * Real.log (4 / f) := by
    have hanti := Theorem9Aux.log_four_div_antitone h1_div_f_ge1 h1_div_f_le_n
    have hrew : Real.log (4 * (1 / f)) / (1 / f) = f * Real.log (4 / f) := by
      have h4 : 4 * (1 / f) = 4 / f := by ring
      rw [h4]
      have hf_ne : f ≠ 0 := hf_pos.ne'
      field_simp
    linarith
  have hdel_step : delta1 G H ≤ 4 * f + 2 * Real.sqrt (2 * f) +
      4 * Real.sqrt 5 * Real.sqrt (f * Real.log (4 / f)) := by
    rw [hdel1_eq, div_le_iff₀ hnR]
    have ht1 : 4 * L = (4 * f) * n := by rw [hLf]; ring
    have ht2 : 2 * Real.sqrt (2 * n * L) = 2 * Real.sqrt (2 * f) * n := by
      rw [hLf, show 2 * (n : ℝ) * ((n : ℝ) * f) = (n : ℝ) ^ 2 * (2 * f) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hnR.le]
      ring
    have ht3 : 4 * Real.sqrt (5 * n * Real.log (4 * n)) ≤
        4 * Real.sqrt 5 * Real.sqrt (f * Real.log (4 / f)) * n := by
      have hlog_n2 : 5 * (n : ℝ) * Real.log (4 * n) ≤
          5 * (n : ℝ) ^ 2 * (f * Real.log (4 / f)) := by
        have hmul := mul_le_mul_of_nonneg_left hlog_le (by positivity : (0 : ℝ) ≤ 5 * (n : ℝ) ^ 2)
        have hlhs_eq : 5 * (n : ℝ) ^ 2 * (Real.log (4 * n) / n) =
            5 * (n : ℝ) * Real.log (4 * n) := by field_simp
        linarith
      have hsq_le := Real.sqrt_le_sqrt hlog_n2
      have hrhs_eq : Real.sqrt (5 * (n : ℝ) ^ 2 * (f * Real.log (4 / f))) =
          Real.sqrt 5 * Real.sqrt (f * Real.log (4 / f)) * n := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hnR.le]
        ring
      linarith
    linarith
  set h : ℝ := Real.log (4 / f)
  have hh_ge : Real.log 4 ≤ h := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hf_pos]
    linarith
  have hh_pos : 0 < h := lt_of_lt_of_le (Real.log_pos (by norm_num)) hh_ge
  have hfh_pos : 0 < Real.sqrt (f * h) := Real.sqrt_pos.mpr (by positivity)
  have hf_le_fh : f ≤ Real.sqrt (f * h) / Real.sqrt (Real.log 4) := by
    have h1 : f ≤ Real.sqrt f := by
      have hs1 : Real.sqrt f ≤ 1 := by simpa using Real.sqrt_le_sqrt hf_le1
      calc
        f = Real.sqrt f * Real.sqrt f := (Real.mul_self_sqrt hf_pos.le).symm
        _ ≤ 1 * Real.sqrt f := mul_le_mul_of_nonneg_right hs1 (Real.sqrt_nonneg _)
        _ = Real.sqrt f := one_mul _
    have h2 : Real.sqrt (Real.log 4) ≤ Real.sqrt h := Real.sqrt_le_sqrt hh_ge
    have hs4_pos : 0 < Real.sqrt (Real.log 4) :=
      Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
    rw [le_div_iff₀ hs4_pos, Real.sqrt_mul hf_pos.le]
    exact mul_le_mul h1 h2 hs4_pos.le (Real.sqrt_nonneg _)
  have h2f_le : Real.sqrt (2 * f) ≤
      Real.sqrt 2 * Real.sqrt (f * h) / Real.sqrt (Real.log 4) := by
    have hs4_pos : 0 < Real.sqrt (Real.log 4) :=
      Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
    have h2 : Real.sqrt (Real.log 4) ≤ Real.sqrt h := Real.sqrt_le_sqrt hh_ge
    rw [le_div_iff₀ hs4_pos, Real.sqrt_mul (by norm_num), Real.sqrt_mul hf_pos.le, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2)
    exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg f)
  have hc15 := Theorem9Aux.const_bound_15
  have hmul15 := mul_le_mul_of_nonneg_right hc15 hfh_pos.le
  calc
    delta1 G H ≤ 4 * (Real.sqrt (f * h) / Real.sqrt (Real.log 4)) +
        2 * (Real.sqrt 2 * Real.sqrt (f * h) / Real.sqrt (Real.log 4)) +
        4 * Real.sqrt 5 * Real.sqrt (f * h) := by linarith
    _ = ((4 + 2 * Real.sqrt 2) / Real.sqrt (Real.log 4) + 4 * Real.sqrt 5) *
          Real.sqrt (f * h) := by ring
    _ ≤ 15 * Real.sqrt (f * h) := hmul15
