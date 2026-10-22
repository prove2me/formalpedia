-- Prove2me | solution 1 for MatrixAnalytic.FiniteQBD.linear_level_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T04:27:30.663994+00:00
-- url     : https://prove2.me/submissions/6da8f18f-2d48-4915-8eec-3933047858f8

import Mathlib
import Definitions.Def_MatrixAnalytic_FiniteQBD_Chain
import Definitions.Def_MatrixAnalytic_FiniteQBD_QBD


open MatrixAnalytic.FiniteQBD
open Matrix

section g77aGen
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem g77a_stoch_sum {P : V → V → ℝ} (hP : IsStochasticC P) (x : V) : ∑ y, P x y = 1 :=
  ((hP.2 x).unique (hasSum_fintype _)).symm

theorem g77a_reach {P : V → V → ℝ} (hP0 : ∀ x y, 0 ≤ P x y) (Sx : V → Prop)
    (hcl : ∀ x y, Sx x → 0 < P x y → Sx y) : ∀ t x y, Sx x → 0 < stepPow P t x y → Sx y := by
  intro t
  induction t with
  | zero =>
    intro x y hx h
    simp only [stepPow] at h
    split_ifs at h with hyx
    · subst hyx; exact hx
    · exact absurd h (lt_irrefl _)
  | succ t ih =>
    intro x y hx h
    simp only [stepPow, tsum_fintype] at h
    obtain ⟨z, -, hz⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0:ℝ))
      (by simpa using h)
    have hPzy : 0 < P z y := lt_of_le_of_ne (hP0 z y) (fun h0 => by
      rw [← h0, mul_zero] at hz; exact lt_irrefl _ hz)
    have hs : 0 < stepPow P t x z := (pos_iff_pos_of_mul_pos hz).2 hPzy
    exact hcl z y (ih x z hx hs) hPzy

/-- maximum principle: a function vanishing off `S` (with `S ≠ univ`) and harmonic on `S` is `≤ 0`. -/
theorem g77a_maxp {P : V → V → ℝ} (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (S : Set V) (z0 : V) (hz0 : z0 ∉ S) (u : V → ℝ) (hu0 : ∀ x, x ∉ S → u x = 0)
    (hh : ∀ x ∈ S, ∑ y, P x y * u y = u x) : ∀ x, u x ≤ 0 := by
  have : Nonempty V := ⟨z0⟩
  obtain ⟨x0, hx0⟩ := Finite.exists_max u
  by_contra hcon
  push Not at hcon
  obtain ⟨x1, hx1⟩ := hcon
  have hm : 0 < u x0 := lt_of_lt_of_le hx1 (hx0 x1)
  have hcl : ∀ x y, u x = u x0 → 0 < P x y → u y = u x0 := by
    intro x y hx hpxy
    have hxS : x ∈ S := by
      by_contra h; rw [hu0 x h] at hx; linarith
    have h1 : ∑ y, P x y * (u y - u x) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hh x hxS,
        g77a_stoch_sum hP x, one_mul, sub_self]
    have hnp : ∀ y ∈ Finset.univ, P x y * (u y - u x) ≤ 0 := fun y _ =>
      mul_nonpos_of_nonneg_of_nonpos (hP.1 x y) (by rw [hx]; linarith [hx0 y])
    have := (Finset.sum_eq_zero_iff_of_nonpos hnp).1 h1 y (Finset.mem_univ y)
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  obtain ⟨t, ht⟩ := hirr x0 z0
  have := g77a_reach hP.1 (fun x => u x = u x0) hcl t x0 z0 rfl ht
  rw [hu0 z0 hz0] at this; linarith

theorem g77a_maxp0 {P : V → V → ℝ} (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (S : Set V) (z0 : V) (hz0 : z0 ∉ S) (u : V → ℝ) (hu0 : ∀ x, x ∉ S → u x = 0)
    (hh : ∀ x ∈ S, ∑ y, P x y * u y = u x) : u = 0 := by
  funext x
  have h1 := g77a_maxp hP hirr S z0 hz0 u hu0 hh x
  have h2 := g77a_maxp hP hirr S z0 hz0 (-u) (fun x hx => by simp [hu0 x hx])
    (fun x hx => by simp [Finset.sum_neg_distrib, hh x hx]) x
  simp at h2
  simp; linarith

/-- harmonic everywhere implies constant. -/
theorem g77a_const {P : V → V → ℝ} (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (u : V → ℝ) (hh : ∀ x, ∑ y, P x y * u y = u x) (x0 : V) : ∀ x, u x = u x0 := by
  have : Nonempty V := ⟨x0⟩
  obtain ⟨m0, hm0⟩ := Finite.exists_max u
  have hcl : ∀ x y, u x = u m0 → 0 < P x y → u y = u m0 := by
    intro x y hx hpxy
    have h1 : ∑ y, P x y * (u y - u x) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hh x,
        g77a_stoch_sum hP x, one_mul, sub_self]
    have hnp : ∀ y ∈ Finset.univ, P x y * (u y - u x) ≤ 0 := fun y _ =>
      mul_nonpos_of_nonneg_of_nonpos (hP.1 x y) (by rw [hx]; linarith [hm0 y])
    have := (Finset.sum_eq_zero_iff_of_nonpos hnp).1 h1 y (Finset.mem_univ y)
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hall : ∀ x, u x = u m0 := fun x => by
    obtain ⟨t, ht⟩ := hirr m0 x
    exact g77a_reach hP.1 (fun x => u x = u m0) hcl t m0 x rfl ht
  intro x; rw [hall x, hall x0]

theorem g77a_left_ker {P : Matrix V V ℝ} (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (p π : V → ℝ) (hp : p ᵥ* P = p) (hπ : π ᵥ* P = π) (hπ1 : ∑ x, π x = 1) :
    p = (∑ x, p x) • π := by
  have hne : Nonempty V := by
    by_contra h; rw [not_nonempty_iff] at h; simp at hπ1
  obtain ⟨x0⟩ := hne
  have hker : LinearMap.ker (1 - P).mulVecLin = ℝ ∙ (fun _ => (1:ℝ)) := by
    ext v
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
    constructor
    · intro hv
      have hh : ∀ x, ∑ y, P x y * v y = v x := by
        intro x
        rw [sub_mulVec, one_mulVec] at hv
        have := congrFun hv x
        simp only [Pi.sub_apply, Pi.zero_apply, mulVec, dotProduct] at this
        linarith
      refine ⟨v x0, ?_⟩
      funext x; simp [g77a_const hP hirr v hh x0 x]
    · rintro ⟨c, rfl⟩
      rw [sub_mulVec, one_mulVec]
      funext x
      have : ∑ y, P x y * (c • fun _ => (1:ℝ)) y = c := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_one]
        rw [← Finset.sum_mul, g77a_stoch_sum hP x, one_mul]
      simp only [Pi.sub_apply, Pi.zero_apply, mulVec, dotProduct, this]
      simp
  have hrk : Module.finrank ℝ (LinearMap.ker (1 - P).mulVecLin) = 1 := by
    rw [hker, finrank_span_singleton]
    intro h; have := congrFun h x0; simp at this
  have hrkT : Module.finrank ℝ (LinearMap.ker (1 - P)ᵀ.mulVecLin) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (1 - P).mulVecLin
    have h2 := LinearMap.finrank_range_add_finrank_ker (1 - P)ᵀ.mulVecLin
    have h3 : (1 - P)ᵀ.rank = (1 - P).rank := Matrix.rank_transpose _
    simp only [Matrix.rank] at h3
    omega
  have hmem : ∀ w : V → ℝ, w ᵥ* P = w → w ∈ LinearMap.ker (1 - P)ᵀ.mulVecLin := by
    intro w hw
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, vecMul_sub,
      vecMul_one, hw, sub_self]
  have hπ0 : (⟨π, hmem π hπ⟩ : LinearMap.ker (1 - P)ᵀ.mulVecLin) ≠ 0 := by
    intro h
    have : π = 0 := congrArg Subtype.val h
    rw [this] at hπ1; simp at hπ1
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hπ0).1 hrkT ⟨p, hmem p hp⟩
  have hc' : c • π = p := congrArg Subtype.val hc
  have hs : ∑ x, p x = c := by
    rw [← hc']; simp [Pi.smul_apply, ← Finset.mul_sum, hπ1]
  rw [hs, hc']

end g77aGen

section g77aQBD
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def g77a_Dg (M : ℕ) (P00 A1 PMM : Matrix ι ι ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  if n = 0 then P00 else if n = M then PMM else A1

theorem g77a_sum_level {M : ℕ} (p : Fin (M + 1) × ι → ℝ) (B : Matrix ι ι ℝ) (k0 : ℕ) (j : ι) :
    ∑ x : Fin (M + 1) × ι, (if (x.1 : ℕ) = k0 then p x * B x.2 j else 0) =
      (block p k0 ᵥ* B) j := by
  rw [Fintype.sum_prod_type]
  by_cases hk : k0 < M + 1
  · have : ∀ k : Fin (M + 1), (∑ i : ι, (if ((k, i) : Fin (M + 1) × ι).1.val = k0
        then p (k, i) * B i j else 0)) =
        if k = ⟨k0, hk⟩ then ∑ i, p (k, i) * B i j else 0 := by
      intro k
      by_cases h : k = ⟨k0, hk⟩
      · subst h; simp
      · have : (k : ℕ) ≠ k0 := fun h' => h (Fin.ext h')
        simp [h, this]
    rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_ite_eq']
    simp [block, hk, vecMul, dotProduct]
  · have h1 : ∀ k : Fin (M + 1), (k : ℕ) ≠ k0 := fun k h => hk (h ▸ k.2)
    have h2 : block p k0 = 0 := by funext i; simp [block, hk]
    simp [h1, h2]

theorem g77a_sum_level' {M : ℕ} (u : Fin (M + 1) × ι → ℝ) (B : Matrix ι ι ℝ) (k0 : ℕ) (i : ι) :
    ∑ y : Fin (M + 1) × ι, (if (y.1 : ℕ) = k0 then B i y.2 * u y else 0) =
      (B *ᵥ block u k0) i := by
  rw [Fintype.sum_prod_type]
  by_cases hk : k0 < M + 1
  · have : ∀ k : Fin (M + 1), (∑ j : ι, (if ((k, j) : Fin (M + 1) × ι).1.val = k0
        then B i j * u (k, j) else 0)) =
        if k = ⟨k0, hk⟩ then ∑ j, B i j * u (k, j) else 0 := by
      intro k
      by_cases h : k = ⟨k0, hk⟩
      · subst h; simp
      · have : (k : ℕ) ≠ k0 := fun h' => h (Fin.ext h')
        simp [h, this]
    rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_ite_eq']
    simp [block, hk, mulVec, dotProduct]
  · have h1 : ∀ k : Fin (M + 1), (k : ℕ) ≠ k0 := fun k h => hk (h ▸ k.2)
    have h2 : block u k0 = 0 := by funext i; simp [block, hk]
    simp [h1, h2]

theorem g77a_vecMul_qbd (M : ℕ) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (p : Fin (M + 1) × ι → ℝ)
    (n : Fin (M + 1)) (j : ι) :
    (p ᵥ* qbdMatrix M P00 A0 A1 A2 PMM) (n, j) =
      (if (n : ℕ) = 0 then 0 else (block p ((n : ℕ) - 1) ᵥ* A0) j)
      + (block p n ᵥ* g77a_Dg M P00 A1 PMM n) j + (block p ((n : ℕ) + 1) ᵥ* A2) j := by
  have hpt : ∀ x : Fin (M + 1) × ι, p x * qbdMatrix M P00 A0 A1 A2 PMM x (n, j) =
      (if (n : ℕ) = 0 then 0 else
        (if (x.1 : ℕ) = (n : ℕ) - 1 then p x * A0 x.2 j else 0))
      + (if (x.1 : ℕ) = (n : ℕ) then p x * g77a_Dg M P00 A1 PMM n x.2 j else 0)
      + (if (x.1 : ℕ) = (n : ℕ) + 1 then p x * A2 x.2 j else 0) := by
    intro x
    obtain ⟨k, i⟩ := x
    simp only [qbdMatrix, g77a_Dg]
    have := k.2; have := n.2
    split_ifs <;> first | (exfalso; omega) | simp | ring
  simp only [vecMul, dotProduct]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · by_cases h2 : (n : ℕ) = 0
      · simp [h2]
      · simp only [h2, if_false]
        exact g77a_sum_level p A0 _ j
    · exact g77a_sum_level p _ _ j
  · exact g77a_sum_level p A2 _ j

theorem g77a_mulVec_qbd (M : ℕ) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (u : Fin (M + 1) × ι → ℝ)
    (n : Fin (M + 1)) (i : ι) :
    ∑ y, qbdMatrix M P00 A0 A1 A2 PMM (n, i) y * u y =
      (if (n : ℕ) = 0 then 0 else (A2 *ᵥ block u ((n : ℕ) - 1)) i)
      + (g77a_Dg M P00 A1 PMM n *ᵥ block u n) i + (A0 *ᵥ block u ((n : ℕ) + 1)) i := by
  have hpt : ∀ y : Fin (M + 1) × ι, qbdMatrix M P00 A0 A1 A2 PMM (n, i) y * u y =
      (if (n : ℕ) = 0 then 0 else
        (if (y.1 : ℕ) = (n : ℕ) - 1 then A2 i y.2 * u y else 0))
      + (if (y.1 : ℕ) = (n : ℕ) then g77a_Dg M P00 A1 PMM n i y.2 * u y else 0)
      + (if (y.1 : ℕ) = (n : ℕ) + 1 then A0 i y.2 * u y else 0) := by
    intro y
    obtain ⟨k, j⟩ := y
    simp only [qbdMatrix, g77a_Dg]
    have := k.2; have := n.2
    split_ifs <;> first | (exfalso; omega) | simp | ring
  rw [Finset.sum_congr rfl (fun y _ => hpt y), Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · by_cases h2 : (n : ℕ) = 0
      · simp [h2]
      · simp only [h2, if_false]
        exact g77a_sum_level' u A2 _ i
    · exact g77a_sum_level' u _ _ i
  · exact g77a_sum_level' u A0 _ i

end g77aQBD

section g77aQBD2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem g77a_col {M : ℕ} (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (p : Fin (M + 1) × ι → ℝ)
    (n : ℕ) (hn : n ≤ M) :
    block (p ᵥ* qbdMatrix M P00 A0 A1 A2 PMM) n =
      (if n = 0 then 0 else block p (n - 1) ᵥ* A0) + block p n ᵥ* g77a_Dg M P00 A1 PMM n
        + block p (n + 1) ᵥ* A2 := by
  funext j
  have h := g77a_vecMul_qbd M P00 A0 A1 A2 PMM p ⟨n, by omega⟩ j
  simp only at h
  simp only [block, show n < M + 1 by omega, dif_pos] at h ⊢
  rw [h]
  by_cases h0 : n = 0 <;> simp [h0]

theorem g77a_fix_iff {M : ℕ} (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (p : Fin (M + 1) × ι → ℝ) :
    p ᵥ* qbdMatrix M P00 A0 A1 A2 PMM = p ↔
      ∀ n, n ≤ M → (if n = 0 then 0 else block p (n - 1) ᵥ* A0) +
        block p n ᵥ* g77a_Dg M P00 A1 PMM n + block p (n + 1) ᵥ* A2 = block p n := by
  constructor
  · intro h n hn
    rw [← g77a_col P00 A0 A1 A2 PMM p n hn, h]
  · intro h
    funext x
    obtain ⟨k, j⟩ := x
    have := congrFun (h k (by omega)) j
    rw [← g77a_col P00 A0 A1 A2 PMM p k (by omega)] at this
    have hk := k.2
    simpa [block, hk] using this

theorem g77a_C_succ (M : ℕ) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Cmat M P00 A0 A1 A2 PMM n = g77a_Dg M P00 A1 PMM n +
      A2 * (1 - Cmat M P00 A0 A1 A2 PMM (n - 1))⁻¹ * A0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [Cmat, g77a_Dg]

noncomputable def g77a_W (C : ℕ → Matrix ι ι ℝ) (A0 : Matrix ι ι ℝ) (i : ℕ) (v : ι → ℝ) : ℕ → ι → ℝ
  | 0 => v
  | d + 1 => (1 - C (i - (d + 1)))⁻¹ *ᵥ (A0 *ᵥ g77a_W C A0 i v d)

theorem g77a_C_unit {M : ℕ} (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) [Nonempty ι]
    (hP : IsStochasticC (qbdMatrix M P00 A0 A1 A2 PMM))
    (hirr : IrreducibleC (qbdMatrix M P00 A0 A1 A2 PMM)) :
    ∀ i, i < M → IsUnit (1 - Cmat M P00 A0 A1 A2 PMM i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  set C := Cmat M P00 A0 A1 A2 PMM with hC
  rw [← Matrix.mulVec_injective_iff_isUnit]
  suffices hz : ∀ v, (1 - C i) *ᵥ v = 0 → v = 0 by
    intro v w hvw
    have := hz (v - w) (by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hvw)
    exact sub_eq_zero.1 this
  intro v hv
  let W : ℕ → ι → ℝ := fun k => if k ≤ i then g77a_W C A0 i v (i - k) else 0
  have hWi : W i = v := by simp [W, g77a_W]
  have hWk : ∀ k, k < i → W k = (1 - C k)⁻¹ *ᵥ (A0 *ᵥ W (k + 1)) := by
    intro k hk
    have e : i - k = (i - (k + 1)) + 1 := by omega
    have e2 : i - (i - (k + 1) + 1) = k := by omega
    simp only [W, if_pos hk.le, if_pos (show k + 1 ≤ i by omega), e, g77a_W, e2]
  have hWgt : ∀ k, i < k → W k = 0 := fun k hk => by simp [W, show ¬ k ≤ i by omega]
  have key : ∀ k, k ≤ i → (1 - C k) *ᵥ W k = A0 *ᵥ W (k + 1) := by
    intro k hk
    rcases lt_or_eq_of_le hk with hk | rfl
    · rw [hWk k hk, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).1 (ih k hk (by omega))), Matrix.one_mulVec]
    · rw [hWi, hv, hWgt (k + 1) (by omega), Matrix.mulVec_zero]
  let u : Fin (M + 1) × ι → ℝ := fun x => W x.1 x.2
  have hblk : ∀ k, block u k = W k := by
    intro k; funext j; by_cases hk : k < M + 1
    · simp [block, hk, u]
    · simp [block, hk, hWgt k (by omega)]
  obtain ⟨j0⟩ := ‹Nonempty ι›
  have hu := g77a_maxp0 hP hirr {x | (x.1 : ℕ) ≤ i} (⟨M, by omega⟩, j0) (by simp; omega) u
    (fun x hx => by simp at hx; simp [u, hWgt _ (by omega)]) ?_
  · funext j
    have := congrFun hu (⟨i, by omega⟩, j)
    simpa [u, hWi] using this
  · rintro ⟨n, j⟩ hn
    simp only [Set.mem_setOf_eq] at hn
    rw [g77a_mulVec_qbd]
    simp only [hblk]
    show _ = W n j
    have hk := key n hn
    have hvec : (if (n : ℕ) = 0 then 0 else A2 *ᵥ W ((n : ℕ) - 1)) +
        g77a_Dg M P00 A1 PMM n *ᵥ W n + A0 *ᵥ W ((n : ℕ) + 1) = W n := by
      rw [← hk, sub_mulVec, one_mulVec]
      by_cases h0 : (n : ℕ) = 0
      · have hD : g77a_Dg M P00 A1 PMM n = C n := by simp [g77a_Dg, h0, hC, Cmat]
        rw [if_pos h0, hD]; abel
      · rw [if_neg h0, hWk ((n : ℕ) - 1) (by omega)]
        try simp only [show (n : ℕ) - 1 + 1 = (n : ℕ) by omega]
        rw [hC, g77a_C_succ M P00 A0 A1 A2 PMM n (by omega)]
        simp only [add_mulVec, ← mulVec_mulVec]
        abel
    have := congrFun hvec j
    by_cases h0 : (n : ℕ) = 0
    · simp only [h0, if_true] at this ⊢; simpa using this
    · simp only [h0, if_false] at this ⊢; simpa using this

theorem g77a_vecMul_inv (C : Matrix ι ι ℝ) (hC : IsUnit C) (x y : ι → ℝ) :
    x ᵥ* C = y ↔ x = y ᵥ* C⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hC
  constructor
  · rintro rfl; rw [vecMul_vecMul, mul_nonsing_inv _ hd, vecMul_one]
  · rintro rfl; rw [vecMul_vecMul, nonsing_inv_mul _ hd, vecMul_one]

theorem g77a_fwd {M : ℕ} (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (hU : ∀ i, i < M → IsUnit (1 - Cmat M P00 A0 A1 A2 PMM i))
    (p : Fin (M + 1) × ι → ℝ) (hp : p ᵥ* qbdMatrix M P00 A0 A1 A2 PMM = p) :
    ∀ n, n ≤ M → block p n ᵥ* (1 - Cmat M P00 A0 A1 A2 PMM n) = block p (n + 1) ᵥ* A2 := by
  rw [g77a_fix_iff] at hp
  intro n
  induction n with
  | zero =>
    intro _
    have h := hp 0 (by omega)
    have hD : g77a_Dg M P00 A1 PMM 0 = Cmat M P00 A0 A1 A2 PMM 0 := by simp [g77a_Dg, Cmat]
    rw [if_pos rfl, hD] at h
    rw [vecMul_sub, vecMul_one]
    nth_rewrite 1 [← h]; abel
  | succ n ih =>
    intro hn
    have h := hp (n + 1) hn
    have e := ih (by omega)
    rw [g77a_vecMul_inv _ (hU n (by omega))] at e
    rw [if_neg (by omega), Nat.add_sub_cancel, e] at h
    rw [g77a_C_succ M P00 A0 A1 A2 PMM (n + 1) (by omega), Nat.add_sub_cancel]
    rw [vecMul_sub, vecMul_one, vecMul_add]
    simp only [vecMul_vecMul] at h ⊢
    nth_rewrite 1 [← h]
    abel

theorem g77a_bwd {M : ℕ} (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (hU : ∀ i, i < M → IsUnit (1 - Cmat M P00 A0 A1 A2 PMM i))
    (p : Fin (M + 1) × ι → ℝ)
    (hS : ∀ n, n ≤ M → block p n ᵥ* (1 - Cmat M P00 A0 A1 A2 PMM n) = block p (n + 1) ᵥ* A2) :
    p ᵥ* qbdMatrix M P00 A0 A1 A2 PMM = p := by
  rw [g77a_fix_iff]
  intro n hn
  have hn' := hS n hn
  rw [vecMul_sub, vecMul_one] at hn'
  rw [← hn']
  by_cases h0 : n = 0
  · subst h0
    have hD : g77a_Dg M P00 A1 PMM 0 = Cmat M P00 A0 A1 A2 PMM 0 := by simp [g77a_Dg, Cmat]
    rw [if_pos rfl, hD]; abel
  · have e := hS (n - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega), g77a_vecMul_inv _ (hU (n - 1) (by omega))] at e
    rw [if_neg h0, e, g77a_C_succ M P00 A0 A1 A2 PMM n (by omega), vecMul_add]
    simp only [vecMul_vecMul, Matrix.mul_assoc]
    abel

theorem g77a_fix_of_stat {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ)
    (hπ : IsStationaryC P π) : π ᵥ* P = π := by
  funext y
  simp only [vecMul, dotProduct]
  exact ((hπ.2.2 y).unique (hasSum_fintype _)).symm

theorem g77a_sum_blocks {M : ℕ} (p : Fin (M + 1) × ι → ℝ) :
    ∑ i ∈ Finset.range (M + 1), ∑ j : ι, block p i j = ∑ x, p x := by
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (fun i => ∑ j : ι, block p i j)]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  have hk := k.2
  simp [block, hk]

end g77aQBD2

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : ℕ) (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (P : Matrix (Fin (M + 1) × ι) (Fin (M + 1) × ι) ℝ)
    (hPdef : P = qbdMatrix M P00 A0 A1 A2 PMM)
    (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (π : Fin (M + 1) × ι → ℝ) (hπ : IsStationaryC P π) :
    (∀ i : ℕ, i < M → IsUnit (1 - Cmat M P00 A0 A1 A2 PMM i)) ∧
    -- `π` satisfies (10.4)–(10.6)
    (block π M = block π M ᵥ* Cmat M P00 A0 A1 A2 PMM M) ∧
    (∀ i : ℕ, i < M →
      block π i = block π (i + 1) ᵥ* (A2 * (1 - Cmat M P00 A0 A1 A2 PMM i)⁻¹)) ∧
    (∑ i ∈ Finset.range (M + 1), ∑ j : ι, block π i j = 1) ∧
    -- and (10.4)–(10.6) determine `π`
    (∀ p : Fin (M + 1) × ι → ℝ,
      block p M = block p M ᵥ* Cmat M P00 A0 A1 A2 PMM M →
      (∀ i : ℕ, i < M →
        block p i = block p (i + 1) ᵥ* (A2 * (1 - Cmat M P00 A0 A1 A2 PMM i)⁻¹)) →
      ∑ i ∈ Finset.range (M + 1), ∑ j : ι, block p i j = 1 →
      p = π) := by
  subst hPdef
  have hU := g77a_C_unit hM P00 A0 A1 A2 PMM hP hirr
  have hfix := g77a_fix_of_stat _ π hπ
  have hS := g77a_fwd hM P00 A0 A1 A2 PMM hU π hfix
  have hMp1 : block π (M + 1) = 0 := by funext j; simp [block]
  have hsum : ∑ x, π x = 1 := (hasSum_fintype π).unique hπ.2.1
  refine ⟨hU, ?_, ?_, ?_, ?_⟩
  · have h := hS M le_rfl
    rw [hMp1, zero_vecMul, vecMul_sub, vecMul_one, sub_eq_zero] at h
    exact h
  · intro i hi
    have h := hS i hi.le
    rw [g77a_vecMul_inv _ (hU i hi), vecMul_vecMul] at h
    exact h
  · rw [g77a_sum_blocks, hsum]
  · intro p h4 h5 h6
    have hS' : ∀ n, n ≤ M → block p n ᵥ* (1 - Cmat M P00 A0 A1 A2 PMM n) =
        block p (n + 1) ᵥ* A2 := by
      intro n hn
      rcases lt_or_eq_of_le hn with hn | rfl
      · rw [g77a_vecMul_inv _ (hU n hn), vecMul_vecMul]
        exact h5 n hn
      · have hMp1' : block p (n + 1) = 0 := by funext j; simp [block]
        rw [hMp1', zero_vecMul, vecMul_sub, vecMul_one, sub_eq_zero]
        exact h4
    have hpfix := g77a_bwd P00 A0 A1 A2 PMM hU p hS'
    have := g77a_left_ker hP hirr p π hpfix hfix hsum
    rw [g77a_sum_blocks] at h6
    rw [this, h6, one_smul]
