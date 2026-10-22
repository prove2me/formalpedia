-- Prove2me | solution 1 for MatrixAnalytic.FiniteQBD.rank_one_subdiagonal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T04:42:27.890226+00:00
-- url     : https://prove2.me/submissions/e83e2c12-a285-4b43-a583-d2e24e5267f2

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

section g77aR1
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem g77a_vmv_mulVec (u v w : ι → ℝ) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem g77a_vecMul_vmv (u v w : ι → ℝ) : w ᵥ* vecMulVec u v = (w ⬝ᵥ u) • v := by
  ext i
  simp only [vecMul, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem g77a_unit_of_inj (B : Matrix ι ι ℝ) (h : ∀ v, B *ᵥ v = 0 → v = 0) : IsUnit B := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have := h (v - w) (by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hvw)
  exact sub_eq_zero.1 this

theorem g77a_harmW {M : ℕ} (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) [Nonempty ι]
    (hP : IsStochasticC (qbdMatrix M P00 A0 A1 A2 PMM))
    (hirr : IrreducibleC (qbdMatrix M P00 A0 A1 A2 PMM))
    (W : ℕ → ι → ℝ) (Sl : ℕ → Prop) (L : ℕ) (hL : L ≤ M) (hLS : ¬ Sl L)
    (hout : ∀ n, ¬ Sl n → W n = 0) (hgt : ∀ n, M < n → W n = 0)
    (hh : ∀ n, n ≤ M → Sl n → (if n = 0 then 0 else A2 *ᵥ W (n - 1)) +
        g77a_Dg M P00 A1 PMM n *ᵥ W n + A0 *ᵥ W (n + 1) = W n) :
    ∀ n, W n = 0 := by
  let u : Fin (M + 1) × ι → ℝ := fun x => W x.1 x.2
  have hblk : ∀ k, block u k = W k := by
    intro k; funext j; by_cases hk : k < M + 1
    · simp [block, hk, u]
    · simp [block, hk, hgt k (by omega)]
  obtain ⟨j0⟩ := ‹Nonempty ι›
  have hu := g77a_maxp0 hP hirr {x | Sl (x.1 : ℕ)} (⟨L, by omega⟩, j0) (by simpa using hLS) u
    (fun x hx => by
      have hx' : ¬ Sl (x.1 : ℕ) := hx
      simp [u, hout _ hx']) ?_
  · intro n
    by_cases hn : n ≤ M
    · funext j
      have := congrFun hu (⟨n, by omega⟩, j)
      simpa [u] using this
    · exact hgt n (by omega)
  · rintro ⟨n, j⟩ hn
    have hn' : Sl (n : ℕ) := hn
    rw [g77a_mulVec_qbd]
    simp only [hblk]
    show _ = W n j
    have := congrFun (hh n (by omega) hn') j
    by_cases h0 : (n : ℕ) = 0
    · simp only [h0, if_true] at this ⊢; simpa using this
    · simp only [h0, if_false] at this ⊢; simpa using this

theorem g77a_rows {M : ℕ} (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (hP : IsStochasticC (qbdMatrix M P00 A0 A1 A2 PMM)) :
    P00 *ᵥ (fun _ => (1:ℝ)) + A0 *ᵥ (fun _ => (1:ℝ)) = (fun _ => (1:ℝ)) ∧
    (∀ n, 1 ≤ n → n + 1 ≤ M → A2 *ᵥ (fun _ => (1:ℝ)) + A1 *ᵥ (fun _ => (1:ℝ)) +
      A0 *ᵥ (fun _ => (1:ℝ)) = (fun _ => (1:ℝ))) ∧
    A2 *ᵥ (fun _ => (1:ℝ)) + PMM *ᵥ (fun _ => (1:ℝ)) = (fun _ => (1:ℝ)) := by
  let o : Fin (M + 1) × ι → ℝ := fun _ => 1
  have hb : ∀ k, k ≤ M → block o k = fun _ => (1:ℝ) := by
    intro k hk; funext j; simp [block, o, show k < M + 1 by omega]
  have hb' : block o (M + 1) = 0 := by funext j; simp [block]
  have h : ∀ n : Fin (M + 1), ∀ i,
      ((if (n : ℕ) = 0 then 0 else (A2 *ᵥ block o ((n : ℕ) - 1)) i)
      + (g77a_Dg M P00 A1 PMM n *ᵥ block o n) i + (A0 *ᵥ block o ((n : ℕ) + 1)) i) = 1 := by
    intro n i
    rw [← g77a_mulVec_qbd]
    simpa [o] using g77a_stoch_sum hP (n, i)
  refine ⟨?_, ?_, ?_⟩
  · funext i
    have := h ⟨0, by omega⟩ i
    simp only [if_true, hb 0 (by omega), hb 1 hM, g77a_Dg, zero_add] at this
    simpa using this
  · intro n h1 h2
    funext i
    have := h ⟨n, by omega⟩ i
    simp only [show (n : ℕ) ≠ 0 by omega, if_false, hb (n - 1) (by omega), hb n (by omega),
      hb (n + 1) (by omega), g77a_Dg, show n ≠ M by omega] at this
    simpa using this
  · funext i
    have := h ⟨M, by omega⟩ i
    simp only [show M ≠ 0 by omega, if_false, hb (M - 1) (by omega), hb M le_rfl, hb',
      g77a_Dg, if_true, mulVec_zero] at this
    simpa using this

theorem g77a_flux {M : ℕ} (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (hP : IsStochasticC (qbdMatrix M P00 A0 A1 A2 PMM))
    (p : Fin (M + 1) × ι → ℝ) (hp : p ᵥ* qbdMatrix M P00 A0 A1 A2 PMM = p) :
    ∀ i, i < M → block p (i + 1) ⬝ᵥ (A2 *ᵥ fun _ => (1:ℝ)) =
      block p i ⬝ᵥ (A0 *ᵥ fun _ => (1:ℝ)) := by
  obtain ⟨rs0, rsI, -⟩ := g77a_rows hM P00 A0 A1 A2 PMM hP
  rw [g77a_fix_iff] at hp
  intro i
  induction i with
  | zero =>
    intro _
    have h := congrArg (· ⬝ᵥ (fun _ => (1:ℝ))) (hp 0 (by omega))
    simp only [if_true, zero_add, add_dotProduct, ← dotProduct_mulVec, g77a_Dg] at h
    have e : P00 *ᵥ (fun _ => (1:ℝ)) = (fun _ => (1:ℝ)) - A0 *ᵥ (fun _ => (1:ℝ)) := by
      ext k; have := congrFun rs0 k; simp only [Pi.add_apply, Pi.sub_apply] at this ⊢; linarith
    rw [e, dotProduct_sub] at h
    linarith
  | succ i ih =>
    intro hi
    have h := congrArg (· ⬝ᵥ (fun _ => (1:ℝ))) (hp (i + 1) (by omega))
    simp only [show i + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel, add_dotProduct,
      ← dotProduct_mulVec, g77a_Dg, show i + 1 ≠ M by omega] at h
    have e : A1 *ᵥ (fun _ => (1:ℝ)) = (fun _ => (1:ℝ)) - A0 *ᵥ (fun _ => (1:ℝ)) -
        A2 *ᵥ (fun _ => (1:ℝ)) := by
      ext k; have := congrFun (rsI (i + 1) (by omega) (by omega)) k
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢; linarith
    rw [e, dotProduct_sub, dotProduct_sub] at h
    have := ih (by omega)
    linarith

end g77aR1

theorem g77a_r1 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : ℕ) (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (hP : IsStochasticC (qbdMatrix M P00 A0 A1 A2 PMM))
    (hirr : IrreducibleC (qbdMatrix M P00 A0 A1 A2 PMM))
    (π : Fin (M + 1) × ι → ℝ) (hπ : IsStationaryC (qbdMatrix M P00 A0 A1 A2 PMM) π) :
    ∀ c r : ι → ℝ, A2 = vecMulVec c r → A2.rank = 1 → r ⬝ᵥ (fun _ => (1 : ℝ)) = 1 →
      IsUnit (1 - PMM) ∧
      (2 ≤ M → IsUnit (1 - A1 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r)) ∧
      ∀ p : Fin (M + 1) × ι → ℝ,
        ((∀ i : ℕ, 1 ≤ i → i ≤ M - 1 →
            block p i =
              block p 0 ᵥ* (A0 * (1 - A1 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r)⁻¹) ^ i) ∧
          block p M =
            block p 0 ᵥ* ((A0 * (1 - A1 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r)⁻¹) ^ (M - 1) *
              (A0 * (1 - PMM)⁻¹)) ∧
          ∑ x, p x = 1 ∧
          block p 0 ᵥ* (1 - P00 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r) = 0) ↔ p = π := by
  intro c r hA2 _ hr1
  obtain ⟨rs0, rsI, rsM⟩ := g77a_rows hM P00 A0 A1 A2 PMM hP
  have hfl0 := g77a_flux hM P00 A0 A1 A2 PMM hP
  obtain ⟨a, ha⟩ : ∃ a, a = A0 *ᵥ fun _ => (1 : ℝ) := ⟨_, rfl⟩
  rw [← ha]
  rw [← ha] at rs0 rsI hfl0
  obtain ⟨K, hK⟩ : ∃ K, K = 1 - A1 - vecMulVec a r := ⟨_, rfl⟩
  rw [← hK]
  have hc : A2 *ᵥ (fun _ => (1 : ℝ)) = c := by rw [hA2, g77a_vmv_mulVec, hr1, one_smul]
  rw [hc] at rsI rsM hfl0
  have hpA2 : ∀ x : ι → ℝ, x ᵥ* A2 = (x ⬝ᵥ c) • r := fun x => by rw [hA2, g77a_vecMul_vmv]
  -- `I - P_MM` is invertible
  have hUM : IsUnit (1 - PMM) := by
    apply g77a_unit_of_inj
    intro v hv
    have hv' : PMM *ᵥ v = v := by
      rw [sub_mulVec, one_mulVec, sub_eq_zero] at hv; exact hv.symm
    let W : ℕ → ι → ℝ := fun n => if n = M then v else 0
    have := g77a_harmW P00 A0 A1 A2 PMM hP hirr W (fun n => n = M) 0 (by omega) (by omega)
      (fun n hn => by simp [W, hn]) (fun n hn => by simp [W, show n ≠ M by omega]) ?_ M
    · simpa [W] using this
    · intro n hn hnM
      rw [hnM]
      simp [W, g77a_Dg, show M ≠ 0 by omega, show M - 1 ≠ M by omega, hv']
  have hUMd := (Matrix.isUnit_iff_isUnit_det _).1 hUM
  -- `K` is invertible when `M ≥ 2`
  have hUK : 2 ≤ M → IsUnit K := by
    intro hM2
    apply g77a_unit_of_inj
    intro v hv
    have hKv : A1 *ᵥ v + (r ⬝ᵥ v) • a = v := by
      rw [hK, sub_mulVec, sub_mulVec, one_mulVec, g77a_vmv_mulVec] at hv
      ext k; have := congrFun hv k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at this ⊢; linarith
    let W : ℕ → ι → ℝ := fun n =>
      if n = 1 then v else if 2 ≤ n ∧ n ≤ M then (r ⬝ᵥ v) • (fun _ => (1 : ℝ)) else 0
    have hW1 : W 1 = v := by simp [W]
    have hW0 : W 0 = 0 := by simp [W]
    have hWm : ∀ n, 2 ≤ n → n ≤ M → W n = (r ⬝ᵥ v) • (fun _ => (1 : ℝ)) := by
      intro n h1 h2; simp [W, show n ≠ 1 by omega, h1, h2]
    have hA2W : ∀ n, 2 ≤ n → n ≤ M → A2 *ᵥ W (n - 1) = (r ⬝ᵥ v) • c := by
      intro n h1 h2
      rcases eq_or_lt_of_le h1 with rfl | h1'
      · rw [show 2 - 1 = 1 by rfl, hW1, hA2, g77a_vmv_mulVec]
      · rw [hWm (n - 1) (by omega) (by omega), mulVec_smul, hc]
    have := g77a_harmW P00 A0 A1 A2 PMM hP hirr W (fun n => 1 ≤ n) 0 (by omega) (by omega)
      (fun n hn => by simp [W, show n ≠ 1 by omega, show ¬ 2 ≤ n by omega])
      (fun n hn => by simp [W, show n ≠ 1 by omega, show ¬ n ≤ M by omega]) ?_ 1
    · simpa [hW1] using this
    · intro n hn h1
      rcases eq_or_lt_of_le h1 with rfl | h1'
      · simp only [show (1 : ℕ) ≠ 0 by omega, if_false, Nat.sub_self, hW0, mulVec_zero,
          zero_add, g77a_Dg, show (1 : ℕ) ≠ M by omega, hW1, hWm 2 le_rfl hM2, mulVec_smul]
        rw [← ha]; exact hKv
      · rw [if_neg (by omega), hA2W n (by omega) hn, hWm n (by omega) hn]
        rcases lt_or_eq_of_le hn with hn' | rfl
        · rw [hWm (n + 1) (by omega) (by omega)]
          simp only [g77a_Dg, if_neg (show n ≠ 0 by omega), if_neg (show n ≠ M by omega),
            mulVec_smul, ← ha]
          have := rsI n (by omega) (by omega)
          ext k; have := congrFun this k
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
          rw [← mul_add, ← mul_add, this]
        · have hWn1 : W (n + 1) = 0 := by simp [W, show n ≠ 0 by omega]
          rw [hWn1, mulVec_zero, add_zero]
          simp only [g77a_Dg, if_neg (show n ≠ 0 by omega), if_true, mulVec_smul]
          ext k; have := congrFun rsM k
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
          rw [← mul_add, this]
  have hfixπ := g77a_fix_of_stat _ π hπ
  have hsumπ : ∑ x, π x = 1 := (hasSum_fintype π).unique hπ.2.1
  -- equations (E) from stationarity
  have hE : ∀ p : Fin (M + 1) × ι → ℝ, p ᵥ* qbdMatrix M P00 A0 A1 A2 PMM = p →
      (∀ n, 1 ≤ n → n + 1 ≤ M → block p n ᵥ* K = block p (n - 1) ᵥ* A0) ∧
      block p M ᵥ* (1 - PMM) = block p (M - 1) ᵥ* A0 ∧
      block p 0 ᵥ* (1 - P00 - vecMulVec a r) = 0 := by
    intro p hp
    have hfl := hfl0 p hp
    rw [g77a_fix_iff] at hp
    refine ⟨?_, ?_, ?_⟩
    · intro n h1 h2
      have h := hp n (by omega)
      rw [if_neg (by omega), hpA2, hfl n (by omega)] at h
      simp only [g77a_Dg, if_neg (show n ≠ 0 by omega), if_neg (show n ≠ M by omega)] at h
      rw [hK, vecMul_sub, vecMul_sub, vecMul_one, g77a_vecMul_vmv]
      ext k; have := congrFun h k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢; linarith
    · have h := hp M le_rfl
      have hb : block p (M + 1) = 0 := by funext j; simp [block]
      rw [if_neg (by omega), hb, zero_vecMul, add_zero] at h
      simp only [g77a_Dg, if_neg (show M ≠ 0 by omega), if_true] at h
      rw [vecMul_sub, vecMul_one]
      ext k; have := congrFun h k
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢; linarith
    · have h := hp 0 (by omega)
      rw [if_pos rfl, hpA2, hfl 0 (by omega)] at h
      simp only [g77a_Dg, if_true] at h
      rw [vecMul_sub, vecMul_sub, vecMul_one, g77a_vecMul_vmv]
      ext k; have := congrFun h k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        zero_add] at this ⊢; linarith
  -- stationarity from (E)
  have hF : ∀ p : Fin (M + 1) × ι → ℝ,
      (∀ n, 1 ≤ n → n + 1 ≤ M → block p n ᵥ* K = block p (n - 1) ᵥ* A0) →
      block p M ᵥ* (1 - PMM) = block p (M - 1) ᵥ* A0 →
      block p 0 ᵥ* (1 - P00 - vecMulVec a r) = 0 →
      p ᵥ* qbdMatrix M P00 A0 A1 A2 PMM = p := by
    intro p e1 e2 e3
    have hfl : ∀ n, 1 ≤ n → n ≤ M → block p n ⬝ᵥ c = block p (n - 1) ⬝ᵥ a := by
      intro n h1 h2
      rcases lt_or_eq_of_le h2 with h2 | rfl
      · have h := congrArg (· ⬝ᵥ (fun _ => (1 : ℝ))) (e1 n h1 (by omega))
        simp only [← dotProduct_mulVec] at h
        have hK1 : K *ᵥ (fun _ => (1 : ℝ)) = c := by
          rw [hK, sub_mulVec, sub_mulVec, one_mulVec, g77a_vmv_mulVec, hr1, one_smul]
          have := rsI n h1 (by omega)
          ext k; have := congrFun this k
          simp only [Pi.add_apply, Pi.sub_apply] at this ⊢; linarith
        rw [hK1, ← ha] at h; exact h
      · have h := congrArg (· ⬝ᵥ (fun _ => (1 : ℝ))) e2
        simp only [← dotProduct_mulVec] at h
        have hM1 : (1 - PMM) *ᵥ (fun _ => (1 : ℝ)) = c := by
          rw [sub_mulVec, one_mulVec]
          ext k; have := congrFun rsM k
          simp only [Pi.add_apply, Pi.sub_apply] at this ⊢; linarith
        rw [hM1, ← ha] at h; exact h
    rw [g77a_fix_iff]
    intro n hn
    by_cases h0 : n = 0
    · subst h0
      rw [if_pos rfl, hpA2, hfl 1 le_rfl hM]
      simp only [g77a_Dg, if_true]
      rw [vecMul_sub, vecMul_sub, vecMul_one, g77a_vecMul_vmv] at e3
      ext k; have := congrFun e3 k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        zero_add, Nat.sub_self] at this ⊢; linarith
    · rw [if_neg h0]
      rcases lt_or_eq_of_le hn with hn' | rfl
      · have h := e1 n (by omega) (by omega)
        rw [hpA2, hfl (n + 1) (by omega) (by omega), Nat.add_sub_cancel]
        simp only [g77a_Dg, if_neg h0, if_neg (show n ≠ M by omega)]
        rw [hK, vecMul_sub, vecMul_sub, vecMul_one, g77a_vecMul_vmv] at h
        ext k; have := congrFun h k
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢; linarith
      · have hb : block p (n + 1) = 0 := by funext j; simp [block]
        rw [hb, zero_vecMul, add_zero]
        simp only [g77a_Dg, if_neg h0, if_true]
        rw [vecMul_sub, vecMul_one] at e2
        ext k; have := congrFun e2 k
        simp only [Pi.add_apply, Pi.sub_apply] at this ⊢; linarith
  refine ⟨hUM, hUK, fun p => ⟨?_, ?_⟩⟩
  · rintro ⟨c1, c2, c3, c4⟩
    have e1 : ∀ n, 1 ≤ n → n + 1 ≤ M → block p n ᵥ* K = block p (n - 1) ᵥ* A0 := by
      intro n h1 h2
      have hKd := (Matrix.isUnit_iff_isUnit_det _).1 (hUK (by omega))
      have hpn : block p n = block p (n - 1) ᵥ* (A0 * K⁻¹) := by
        rcases eq_or_lt_of_le h1 with rfl | h1'
        · rw [c1 1 le_rfl (by omega), pow_one]
        · rw [c1 n h1 (by omega), c1 (n - 1) (by omega) (by omega), vecMul_vecMul, ← pow_succ,
            Nat.sub_add_cancel (by omega)]
      rw [hpn, vecMul_vecMul, Matrix.mul_assoc, nonsing_inv_mul _ hKd, Matrix.mul_one]
    have e2 : block p M ᵥ* (1 - PMM) = block p (M - 1) ᵥ* A0 := by
      have hpM : block p M = block p (M - 1) ᵥ* (A0 * (1 - PMM)⁻¹) := by
        by_cases hM1 : M = 1
        · rw [c2, show M - 1 = 0 by omega, pow_zero, Matrix.one_mul]
        · rw [c2, c1 (M - 1) (by omega) (by omega), vecMul_vecMul]
      rw [hpM, vecMul_vecMul, Matrix.mul_assoc, nonsing_inv_mul _ hUMd, Matrix.mul_one]
    have hfix := hF p e1 e2 c4
    have := g77a_left_ker hP hirr p π hfix hfixπ hsumπ
    rw [this, c3, one_smul]
  · intro hpπ
    rw [hpπ]
    obtain ⟨e1, e2, e3⟩ := hE π hfixπ
    have hrec : ∀ n, 1 ≤ n → n + 1 ≤ M → block π n = block π (n - 1) ᵥ* (A0 * K⁻¹) := by
      intro n h1 h2
      have hKd := (Matrix.isUnit_iff_isUnit_det _).1 (hUK (by omega))
      rw [← vecMul_vecMul, ← e1 n h1 h2, vecMul_vecMul, mul_nonsing_inv _ hKd, vecMul_one]
    have c1 : ∀ i, 1 ≤ i → i ≤ M - 1 → block π i = block π 0 ᵥ* (A0 * K⁻¹) ^ i := by
      intro i h1 h2
      induction i with
      | zero => omega
      | succ i ih =>
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · rw [hrec 1 le_rfl (by omega), pow_one]
        · rw [hrec (i + 1) (by omega) (by omega), Nat.add_sub_cancel, ih hi (by omega),
            vecMul_vecMul, ← pow_succ]
    refine ⟨c1, ?_, hsumπ, e3⟩
    have hpM : block π M = block π (M - 1) ᵥ* (A0 * (1 - PMM)⁻¹) := by
      rw [← vecMul_vecMul, ← e2, vecMul_vecMul, mul_nonsing_inv _ hUMd, vecMul_one]
    by_cases hM1 : M = 1
    · rw [hpM, show M - 1 = 0 by omega, pow_zero, Matrix.one_mul]
    · rw [hpM, c1 (M - 1) (by omega) (by omega), vecMul_vecMul]

section g77aRev
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def g77a_sig (M : ℕ) (ι : Type*) : (Fin (M + 1) × ι) ≃ (Fin (M + 1) × ι) :=
  Equiv.prodCongr Fin.revPerm (Equiv.refl ι)

theorem g77a_sig_apply (M : ℕ) (x : Fin (M + 1) × ι) : g77a_sig M ι x = (Fin.rev x.1, x.2) := rfl

theorem g77a_sig_sig (M : ℕ) (x : Fin (M + 1) × ι) : g77a_sig M ι (g77a_sig M ι x) = x := by
  simp [g77a_sig_apply]

theorem g77a_qbd_rev' (M : ℕ) (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (k l : Fin (M + 1))
    (i j : ι) :
    qbdMatrix M PMM A2 A1 A0 P00 (k, i) (l, j) =
      qbdMatrix M P00 A0 A1 A2 PMM (Fin.rev k, i) (Fin.rev l, j) := by
  simp only [qbdMatrix, Fin.val_rev]
  have := k.2; have := l.2; have := hM
  split_ifs <;> first | rfl | (exfalso; omega)

theorem g77a_qbd_rev (M : ℕ) (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (x y : Fin (M + 1) × ι) :
    qbdMatrix M PMM A2 A1 A0 P00 x y =
      qbdMatrix M P00 A0 A1 A2 PMM (g77a_sig M ι x) (g77a_sig M ι y) := by
  obtain ⟨k, i⟩ := x
  obtain ⟨l, j⟩ := y
  exact g77a_qbd_rev' M hM P00 A0 A1 A2 PMM k l i j

theorem g77a_stoch_rev {M : ℕ} (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (hP : IsStochasticC (qbdMatrix M P00 A0 A1 A2 PMM)) :
    IsStochasticC (qbdMatrix M PMM A2 A1 A0 P00) := by
  refine ⟨fun x y => by rw [g77a_qbd_rev M hM]; exact hP.1 _ _, fun x => ?_⟩
  have h := hP.2 (g77a_sig M ι x)
  rw [← (g77a_sig M ι).hasSum_iff] at h
  convert h using 1
  funext y; exact g77a_qbd_rev M hM P00 A0 A1 A2 PMM x y

theorem g77a_step_rev {M : ℕ} (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (t : ℕ) (x y : Fin (M + 1) × ι) :
    stepPow (qbdMatrix M PMM A2 A1 A0 P00) t x y =
      stepPow (qbdMatrix M P00 A0 A1 A2 PMM) t (g77a_sig M ι x) (g77a_sig M ι y) := by
  induction t generalizing y with
  | zero =>
    simp only [stepPow]
    by_cases h : y = x
    · subst h; simp
    · have : g77a_sig M ι y ≠ g77a_sig M ι x := fun h' => h ((g77a_sig M ι).injective h')
      simp [h, this]
  | succ t ih =>
    simp only [stepPow, tsum_fintype]
    rw [← (g77a_sig M ι).sum_comp]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ih, g77a_qbd_rev M hM, g77a_sig_sig]

theorem g77a_irr_rev {M : ℕ} (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (hirr : IrreducibleC (qbdMatrix M P00 A0 A1 A2 PMM)) :
    IrreducibleC (qbdMatrix M PMM A2 A1 A0 P00) := by
  intro x y
  obtain ⟨t, ht⟩ := hirr (g77a_sig M ι x) (g77a_sig M ι y)
  exact ⟨t, by rw [g77a_step_rev hM]; exact ht⟩

theorem g77a_stat_rev {M : ℕ} (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ) (π : Fin (M + 1) × ι → ℝ)
    (hπ : IsStationaryC (qbdMatrix M P00 A0 A1 A2 PMM) π) :
    IsStationaryC (qbdMatrix M PMM A2 A1 A0 P00) (π ∘ g77a_sig M ι) := by
  refine ⟨fun x => hπ.1 _, ?_, fun y => ?_⟩
  · exact ((g77a_sig M ι).hasSum_iff).2 hπ.2.1
  · have h := hπ.2.2 (g77a_sig M ι y)
    rw [← (g77a_sig M ι).hasSum_iff] at h
    convert h using 1
    funext x; simp only [Function.comp_apply]; rw [g77a_qbd_rev M hM]
    rfl

theorem g77a_block_rev {M : ℕ} (p : Fin (M + 1) × ι → ℝ) (i : ℕ) (hi : i ≤ M) :
    block (p ∘ g77a_sig M ι) i = block p (M - i) := by
  funext j
  simp only [block, show i < M + 1 by omega, show M - i < M + 1 by omega, dif_pos,
    Function.comp_apply, g77a_sig_apply]
  congr 2
  ext; simp [Fin.val_rev]

theorem g77a_sum_rev {M : ℕ} (p : Fin (M + 1) × ι → ℝ) :
    ∑ x, (p ∘ g77a_sig M ι) x = ∑ x, p x :=
  (g77a_sig M ι).sum_comp p

end g77aRev
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : ℕ) (hM : 1 ≤ M) (P00 A0 A1 A2 PMM : Matrix ι ι ℝ)
    (P : Matrix (Fin (M + 1) × ι) (Fin (M + 1) × ι) ℝ)
    (hPdef : P = qbdMatrix M P00 A0 A1 A2 PMM)
    (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (π : Fin (M + 1) × ι → ℝ) (hπ : IsStationaryC P π) :
    -- first statement: `A₂ = c·r` of rank 1, `r1 = 1`
    (∀ c r : ι → ℝ, A2 = vecMulVec c r → A2.rank = 1 → r ⬝ᵥ (fun _ => (1 : ℝ)) = 1 →
      IsUnit (1 - PMM) ∧
      (2 ≤ M → IsUnit (1 - A1 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r)) ∧
      ∀ p : Fin (M + 1) × ι → ℝ,
        ((∀ i : ℕ, 1 ≤ i → i ≤ M - 1 →
            block p i =
              block p 0 ᵥ* (A0 * (1 - A1 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r)⁻¹) ^ i) ∧
          block p M =
            block p 0 ᵥ* ((A0 * (1 - A1 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r)⁻¹) ^ (M - 1) *
              (A0 * (1 - PMM)⁻¹)) ∧
          ∑ x, p x = 1 ∧
          block p 0 ᵥ* (1 - P00 - vecMulVec (A0 *ᵥ fun _ => (1 : ℝ)) r) = 0) ↔ p = π) ∧
    -- second statement: `A₀ = c·r` of rank 1, `r1 = 1`
    (∀ c r : ι → ℝ, A0 = vecMulVec c r → A0.rank = 1 → r ⬝ᵥ (fun _ => (1 : ℝ)) = 1 →
      IsUnit (1 - P00) ∧
      (2 ≤ M → IsUnit (1 - A1 - vecMulVec (A2 *ᵥ fun _ => (1 : ℝ)) r)) ∧
      ∀ p : Fin (M + 1) × ι → ℝ,
        ((∀ i : ℕ, 1 ≤ i → i ≤ M - 1 →
            block p (M - i) =
              block p M ᵥ* (A2 * (1 - A1 - vecMulVec (A2 *ᵥ fun _ => (1 : ℝ)) r)⁻¹) ^ i) ∧
          block p 0 =
            block p M ᵥ* ((A2 * (1 - A1 - vecMulVec (A2 *ᵥ fun _ => (1 : ℝ)) r)⁻¹) ^ (M - 1) *
              (A2 * (1 - P00)⁻¹)) ∧
          ∑ x, p x = 1 ∧
          block p M ᵥ* (1 - PMM - vecMulVec (A2 *ᵥ fun _ => (1 : ℝ)) r) = 0) ↔ p = π) := by
  subst hPdef
  refine ⟨g77a_r1 M hM P00 A0 A1 A2 PMM hP hirr π hπ, ?_⟩
  intro c r h1 h2 h3
  obtain ⟨u1, u2, u3⟩ := g77a_r1 M hM PMM A2 A1 A0 P00 (g77a_stoch_rev hM _ _ _ _ _ hP)
    (g77a_irr_rev hM _ _ _ _ _ hirr) (π ∘ g77a_sig M ι) (g77a_stat_rev hM _ _ _ _ _ π hπ) c r h1 h2 h3
  refine ⟨u1, u2, fun p => ?_⟩
  have hb := g77a_block_rev p
  have key := u3 (p ∘ g77a_sig M ι)
  rw [g77a_sum_rev, hb 0 (by omega), hb M le_rfl, Nat.sub_zero, Nat.sub_self] at key
  have hiff : p ∘ g77a_sig M ι = π ∘ g77a_sig M ι ↔ p = π := by
    constructor
    · intro h; funext x; have := congrFun h (g77a_sig M ι x); simpa [g77a_sig_sig] using this
    · rintro rfl; rfl
  rw [hiff] at key
  rw [← key]
  constructor
  · rintro ⟨a1, a2, a3, a4⟩
    refine ⟨fun i hi1 hi2 => ?_, a2, a3, a4⟩
    rw [hb i (by omega)]; exact a1 i hi1 hi2
  · rintro ⟨a1, a2, a3, a4⟩
    refine ⟨fun i hi1 hi2 => ?_, a2, a3, a4⟩
    have := a1 i hi1 hi2; rwa [hb i (by omega)] at this
