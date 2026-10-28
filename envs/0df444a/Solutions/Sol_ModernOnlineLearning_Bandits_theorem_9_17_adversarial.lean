-- Prove2me | solution 1 for ModernOnlineLearning.Bandits.theorem_9_17_adversarial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T19:17:35.690291+00:00
-- url     : https://prove2.me/submissions/e18fa9f7-7ce5-4ce7-90b9-e52bc4b8570e

import Mathlib
import Definitions.Def_ModernOnlineLearning_Bandits_Tsallis
set_option autoImplicit false
noncomputable section

open Finset

namespace P482

open ModernOnlineLearning.Bandits

/-! ### Elementary inequalities -/

lemma sum_sqrt_le {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∑ i, Real.sqrt (p i) ≤ Real.sqrt d := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1:ℝ))
    (fun i => Real.sqrt (p i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  have h2 : ∑ i, Real.sqrt (p i) ^ 2 = 1 := by
    rw [← hs]; exact Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hp i))
  rw [h2, mul_one] at h
  have hnn : 0 ≤ ∑ i, Real.sqrt (p i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  calc ∑ i, Real.sqrt (p i) = Real.sqrt ((∑ i, Real.sqrt (p i)) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt d := Real.sqrt_le_sqrt h

lemma coord_bound (ℓ a s c : ℝ) (hℓ : 0 ≤ ℓ) (ha : 0 < a) (hc : 0 < c) :
    ℓ * (a ^ 2 - s ^ 2) - c * (s - a) ^ 2 / (2 * a) ≤ 2 * a ^ 2 * a * ℓ ^ 2 / c := by
  have h1 : ℓ * (a ^ 2 - s ^ 2) ≤ 2 * a * ℓ * (a - s) := by
    nlinarith [mul_nonneg hℓ (sq_nonneg (a - s))]
  have h2 : 2 * a * ℓ * (a - s) ≤ c * (s - a) ^ 2 / (2 * a) + 2 * a ^ 2 * a * ℓ ^ 2 / c := by
    rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (c * (a - s) - 2 * a ^ 2 * ℓ)]
  linarith

lemma term_id (G ℓ c a s : ℝ) (ha : 0 < a) :
    (G + ℓ) * a ^ 2 - c * a - ((G + ℓ) * s ^ 2 - c * s) + (G - c / (2 * a)) * (s ^ 2 - a ^ 2)
      = ℓ * (a ^ 2 - s ^ 2) - c * (s - a) ^ 2 / (2 * a) := by
  field_simp
  ring

lemma sum_inv_sqrt_le (T : ℕ) :
    ∑ t ∈ Icc 1 T, 1 / Real.sqrt (t : ℝ) ≤ 2 * Real.sqrt (T : ℝ) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have hsq1 := Real.sq_sqrt (show (0:ℝ) ≤ (n : ℝ) + 1 by linarith)
    have hsq0 := Real.sq_sqrt hn
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    push_cast
    have key : 1 / Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt ((n : ℝ) + 1) - 2 * Real.sqrt n := by
      rw [div_le_iff₀ hs1]
      nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n)]
    linarith

/-! ### First-order condition and stability for the Tsallis objective -/

lemma simplex_le_one {d : ℕ} {p : Fin d → ℝ} (hp : IsSimplex p) (i : Fin d) : p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)

lemma foc {d : ℕ} (G : Fin d → ℝ) (c : ℝ) (X y : Fin d → ℝ)
    (hX : IsSimplex X) (hXpos : ∀ i, 0 < X i) (hy : IsSimplex y)
    (hmin : ∀ p, IsSimplex p →
      (∑ i, G i * X i) - c * ∑ i, Real.sqrt (X i) ≤ (∑ i, G i * p i) - c * ∑ i, Real.sqrt (p i)) :
    ∑ i, (G i - c / (2 * Real.sqrt (X i))) * (y i - X i) = 0 := by
  set φ : ℝ → ℝ := fun s => (∑ i, G i * (X i + s * (y i - X i))) -
      c * ∑ i, Real.sqrt (X i + s * (y i - X i)) with hφ
  have hder : HasDerivAt φ ((∑ i, G i * (y i - X i)) -
      c * ∑ i, (y i - X i) / (2 * Real.sqrt (X i))) 0 := by
    have hlin : ∀ i, HasDerivAt (fun s : ℝ => X i + s * (y i - X i)) (y i - X i) 0 := by
      intro i
      have := ((hasDerivAt_id (0:ℝ)).mul_const (y i - X i)).const_add (X i)
      simpa using this
    have h1 : HasDerivAt (fun s : ℝ => ∑ i, G i * (X i + s * (y i - X i)))
        (∑ i, G i * (y i - X i)) 0 := by
      have := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hlin i).const_mul (G i))
      rwa [Finset.sum_fn] at this
    have h2 : HasDerivAt (fun s : ℝ => ∑ i, Real.sqrt (X i + s * (y i - X i)))
        (∑ i, (y i - X i) / (2 * Real.sqrt (X i))) 0 := by
      have := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hlin i).sqrt
        (by simp; exact (hXpos i).ne'))
      rw [Finset.sum_fn] at this
      simpa using this
    exact h1.sub (h2.const_mul c)
  have hmin0 : IsLocalMin φ 0 := by
    obtain ⟨m, hm, hmle⟩ : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ X i := by
      by_cases hne : Nonempty (Fin d)
      · obtain ⟨i0, hi0⟩ := Finite.exists_min X
        exact ⟨X i0, hXpos i0, hi0⟩
      · exact ⟨1, one_pos, fun i => (hne ⟨i⟩).elim⟩
    set m' := min m 1 with hm'
    have hm'pos : 0 < m' := lt_min hm one_pos
    have hm'le : m' ≤ m := min_le_left _ _
    have hm'1 : m' ≤ 1 := min_le_right _ _
    filter_upwards [Ioo_mem_nhds (show -m' < 0 by linarith) hm'pos] with s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hp : IsSimplex (fun i => X i + s * (y i - X i)) := by
      refine ⟨fun i => ?_, ?_⟩
      · have hy1 := simplex_le_one hy i
        have hX1 := simplex_le_one hX i
        have hy0 := hy.1 i
        have hX0 := hX.1 i
        have hmi := hmle i
        nlinarith [mul_nonneg (show 0 ≤ m' + s by linarith) (show 0 ≤ 1 + (y i - X i) by linarith),
          mul_nonneg (show 0 ≤ m' - s by linarith) (show 0 ≤ 1 - (y i - X i) by linarith)]
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hX.2, hy.2]
        ring
    have := hmin _ hp
    simp only [hφ]
    simpa using this
  have h0 := hmin0.hasDerivAt_eq_zero hder
  rw [← h0]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

lemma stab {d : ℕ} (G ℓ : Fin d → ℝ) (c : ℝ) (hc : 0 < c) (X y : Fin d → ℝ)
    (hX : IsSimplex X) (hXpos : ∀ i, 0 < X i) (hy : IsSimplex y) (hℓ : ∀ i, 0 ≤ ℓ i)
    (hmin : ∀ p, IsSimplex p →
      (∑ i, G i * X i) - c * ∑ i, Real.sqrt (X i) ≤ (∑ i, G i * p i) - c * ∑ i, Real.sqrt (p i)) :
    ((∑ i, (G i + ℓ i) * X i) - c * ∑ i, Real.sqrt (X i)) -
      ((∑ i, (G i + ℓ i) * y i) - c * ∑ i, Real.sqrt (y i))
      ≤ ∑ i, 2 * X i * Real.sqrt (X i) * ℓ i ^ 2 / c := by
  have h0 := foc G c X y hX hXpos hy hmin
  have hterm : ∀ i, (G i + ℓ i) * X i - c * Real.sqrt (X i) -
      ((G i + ℓ i) * y i - c * Real.sqrt (y i)) +
      (G i - c / (2 * Real.sqrt (X i))) * (y i - X i)
      ≤ 2 * X i * Real.sqrt (X i) * ℓ i ^ 2 / c := by
    intro i
    have ha : 0 < Real.sqrt (X i) := Real.sqrt_pos.mpr (hXpos i)
    have e := term_id (G i) (ℓ i) c (Real.sqrt (X i)) (Real.sqrt (y i)) ha
    have b := coord_bound (ℓ i) (Real.sqrt (X i)) (Real.sqrt (y i)) c (hℓ i) ha hc
    rw [Real.sq_sqrt (hX.1 i), Real.sq_sqrt (hy.1 i)] at e b
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  rw [Finset.sum_add_distrib, h0, add_zero] at hsum
  calc _ = ∑ i, ((G i + ℓ i) * X i - c * Real.sqrt (X i) -
      ((G i + ℓ i) * y i - c * Real.sqrt (y i))) := by
        simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ _ := hsum

/-! ### Deterministic FTRL bound along one path -/

lemma ftrl {d : ℕ} (L : ℝ) (hL : 0 < L) (N : ℕ) (X ℓ : ℕ → Fin d → ℝ)
    (hX : ∀ t ∈ Icc 1 N, IsSimplex (X t)) (hXpos : ∀ t ∈ Icc 1 N, ∀ i, 0 < X t i)
    (hℓ : ∀ t ∈ Icc 1 N, ∀ i, 0 ≤ ℓ t i)
    (hmin : ∀ t ∈ Icc 1 N, ∀ p, IsSimplex p →
      (∑ i, (∑ s ∈ Ico 1 t, ℓ s i) * X t i) - 4 * L * Real.sqrt (t : ℝ) * ∑ i, Real.sqrt (X t i)
        ≤ (∑ i, (∑ s ∈ Ico 1 t, ℓ s i) * p i) - 4 * L * Real.sqrt (t : ℝ) * ∑ i, Real.sqrt (p i))
    (k : Fin d) :
    ∑ t ∈ Icc 1 N, ∑ i, ℓ t i * X t i ≤
      ∑ t ∈ Icc 1 N, ℓ t k + (Real.sqrt d - 1) * (4 * L * Real.sqrt (N : ℝ)) +
      ∑ t ∈ Icc 1 N, ∑ i, 2 * X t i * Real.sqrt (X t i) * ℓ t i ^ 2 /
        (4 * L * Real.sqrt (t : ℝ)) := by
  -- H n p : the objective after round n, with the round-n regularizer
  set c : ℕ → ℝ := fun n => 4 * L * Real.sqrt (n : ℝ) with hc
  set H : ℕ → (Fin d → ℝ) → ℝ := fun n p =>
    (∑ i, (∑ s ∈ Ico 1 (n + 1), ℓ s i) * p i) - c n * ∑ i, Real.sqrt (p i) with hH
  set stb : ℕ → ℝ := fun t => ∑ i, 2 * X t i * Real.sqrt (X t i) * ℓ t i ^ 2 /
        (4 * L * Real.sqrt (t : ℝ)) with hstb
  have claim : ∀ n ≤ N, ∀ y, IsSimplex y →
      ∑ t ∈ Icc 1 n, ∑ i, ℓ t i * X t i ≤ H n y + Real.sqrt d * c n + ∑ t ∈ Icc 1 n, stb t := by
    intro n
    induction n with
    | zero =>
      intro _ y _
      simp [hH, hc]
    | succ n ih =>
      intro hn y hy
      have hmem : n + 1 ∈ Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hn⟩
      have ih' := ih (by omega) (X (n + 1)) (hX _ hmem)
      have hcpos : 0 < c (n + 1) := by
        simp only [hc]; have : (0:ℝ) < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
          Real.sqrt_pos.mpr (by positivity)
        positivity
      have hst := stab (fun i => ∑ s ∈ Ico 1 (n + 1), ℓ s i) (ℓ (n + 1)) (c (n + 1)) hcpos
        (X (n + 1)) y (hX _ hmem) (hXpos _ hmem) hy (hℓ _ hmem) (hmin _ hmem)
      have hG : ∀ i, (∑ s ∈ Ico 1 (n + 1 + 1), ℓ s i) = (∑ s ∈ Ico 1 (n + 1), ℓ s i) + ℓ (n + 1) i :=
        fun i => Finset.sum_Ico_succ_top (by omega) _
      have hS := sum_sqrt_le (X (n + 1)) (hX _ hmem).1 (hX _ hmem).2
      have hmono : c n ≤ c (n + 1) := by
        simp only [hc]
        have : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by push_cast; linarith)
        nlinarith
      have hHn : H n (X (n + 1)) + ∑ i, ℓ (n + 1) i * X (n + 1) i =
          H (n + 1) (X (n + 1)) + (c (n + 1) - c n) * ∑ i, Real.sqrt (X (n + 1) i) := by
        simp only [hH, hG, add_mul, Finset.sum_add_distrib]
        ring
      have hHy : H (n + 1) y = ((∑ i, ((∑ s ∈ Ico 1 (n + 1), ℓ s i) + ℓ (n + 1) i) * y i) -
          c (n + 1) * ∑ i, Real.sqrt (y i)) := by
        simp only [hH, hG]
      have hHX : H (n + 1) (X (n + 1)) =
          ((∑ i, ((∑ s ∈ Ico 1 (n + 1), ℓ s i) + ℓ (n + 1) i) * X (n + 1) i) -
          c (n + 1) * ∑ i, Real.sqrt (X (n + 1) i)) := by
        simp only [hH, hG]
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have hstb : stb (n + 1) = ∑ i, 2 * X (n + 1) i * Real.sqrt (X (n + 1) i) * ℓ (n + 1) i ^ 2 /
          c (n + 1) := by simp only [hstb, hc]
      have h3 : (c (n + 1) - c n) * ∑ i, Real.sqrt (X (n + 1) i) ≤
          (c (n + 1) - c n) * Real.sqrt d :=
        mul_le_mul_of_nonneg_left hS (by linarith)
      rw [← hHy, ← hHX, ← hstb] at hst
      nlinarith
  have hmemk : IsSimplex (fun i : Fin d => if i = k then (1:ℝ) else 0) := by
    refine ⟨fun i => by dsimp only; split_ifs <;> norm_num, by simp⟩
  have hfin := claim N le_rfl _ hmemk
  have hHk : H N (fun i : Fin d => if i = k then (1:ℝ) else 0) =
      (∑ t ∈ Icc 1 N, ℓ t k) - c N := by
    simp only [hH]
    have e1 : (Ico 1 (N + 1)) = Icc 1 N := by ext t; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    have e2 : ∑ x : Fin d, Real.sqrt (if x = k then (1:ℝ) else 0) = 1 := by
      simp [apply_ite Real.sqrt]
    simp [e1, e2]
  rw [hHk] at hfin
  simp only [hstb, hc] at hfin ⊢
  linarith

/-! ### The finite path law -/

section Prob

variable {T d : ℕ}

def wt (anchor : Fin d) (x : ArmPath T d → ℕ → Fin d → ℝ) (m : ℕ) (A : ArmPath T d) : ℝ :=
  if A 0 = anchor then ∏ t ∈ Icc 1 m, x A t (armAt A t) else 0

def Dep (m : ℕ) (f : ArmPath T d → ℝ) : Prop :=
  ∀ A B : ArmPath T d, A 0 = B 0 → (∀ s ∈ Icc 1 m, armAt A s = armAt B s) → f A = f B

lemma fiber (c : Fin (T + 1)) (G : ArmPath T d → ℝ) :
    (d : ℝ) * ∑ A, G A = ∑ A, ∑ a, G (Function.update A c a) := by
  classical
  let e := Equiv.piSplitAt c (fun _ : Fin (T + 1) => Fin d)
  have hupd : ∀ (a a' : Fin d) (r : {j // j ≠ c} → Fin d),
      Function.update (e.symm (a, r)) c a' = e.symm (a', r) := by
    intro a a' r
    funext j
    by_cases h : j = c
    · subst h; simp [e, Equiv.piSplitAt_symm_apply]
    · simp [e, Equiv.piSplitAt_symm_apply, Function.update, h]
  rw [← e.symm.sum_comp G, ← e.symm.sum_comp (fun A => ∑ a, G (Function.update A c a))]
  simp only [Fintype.sum_prod_type, hupd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  congr 1
  exact Finset.sum_comm

lemma armAt_update_ne (A : ArmPath T d) (j : Fin (T + 1)) (a : Fin d) (s : ℕ)
    (h : min s T ≠ j.val) : armAt (Function.update A j a) s = armAt A s := by
  unfold armAt
  rw [Function.update_of_ne]
  intro h'
  exact h (congrArg Fin.val h')

lemma armAt_update_self (A : ArmPath T d) (j : Fin (T + 1)) (a : Fin d) :
    armAt (Function.update A j a) j.val = a := by
  unfold armAt
  have : (⟨min j.val T, Nat.lt_succ_of_le (Nat.min_le_right _ T)⟩ : Fin (T + 1)) = j :=
    Fin.ext (by have := j.isLt; simp; omega)
  rw [this, Function.update_self]

lemma dep_update {m : ℕ} {f : ArmPath T d → ℝ} (hf : Dep m f) (A : ArmPath T d)
    (j : Fin (T + 1)) (hj : m < j.val) (a : Fin d) : f (Function.update A j a) = f A := by
  apply hf
  · rw [Function.update_of_ne]
    intro h; rw [← h] at hj; simp at hj
  · intro s hs
    have := Finset.mem_Icc.mp hs
    exact armAt_update_ne A j a s (by omega)

lemma dep_mono {m m' : ℕ} {f : ArmPath T d → ℝ} (hf : Dep m f) (h : m ≤ m') : Dep m' f :=
  fun A B h0 hs => hf A B h0 (fun s hs' => hs s (by
    have := Finset.mem_Icc.mp hs'; exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩))

variable {L : ℝ} {g : ℕ → Fin d → ℝ} {x : ArmPath T d → ℕ → Fin d → ℝ}

lemma dep_x (hRun : IsTsallisRun L g x) {t m : ℕ} (ht : t ∈ Icc 1 T) (htm : t ≤ m + 1)
    (F : (Fin d → ℝ) → ℝ) : Dep m (fun A => F (x A t)) := by
  intro A B _ hs
  have : x A t = x B t := hRun.2 A B t ht (fun s hs' => by
    have := Finset.mem_Ico.mp hs'; exact hs s (Finset.mem_Icc.mpr ⟨this.1, by omega⟩))
  simp only [this]

lemma dep_ind {t m : ℕ} (ht : 1 ≤ t) (htm : t ≤ m) (i : Fin d) :
    Dep (T := T) m (fun A => if armAt A t = i then (1:ℝ) else 0) := by
  intro A B _ hs
  simp only [hs t (Finset.mem_Icc.mpr ⟨ht, htm⟩)]

lemma dep_wt (hRun : IsTsallisRun L g x) (anchor : Fin d) {m : ℕ} (hm : m ≤ T) :
    Dep m (wt anchor x m) := by
  intro A B h0 hs
  unfold wt
  rw [h0]
  congr 1
  refine Finset.prod_congr rfl (fun t ht => ?_)
  have ht' := Finset.mem_Icc.mp ht
  have hx : x A t = x B t := hRun.2 A B t (Finset.mem_Icc.mpr ⟨ht'.1, by omega⟩)
    (fun s hs' => by
      have := Finset.mem_Ico.mp hs'; exact hs s (Finset.mem_Icc.mpr ⟨this.1, by omega⟩))
  rw [hx, hs t ht]

lemma wt_succ (anchor : Fin d) (m : ℕ) (A : ArmPath T d) :
    wt anchor x (m + 1) A = wt anchor x m A * x A (m + 1) (armAt A (m + 1)) := by
  unfold wt
  split_ifs
  · rw [Finset.prod_Icc_succ_top (by omega)]
  · simp

lemma step (hRun : IsTsallisRun L g x) (anchor : Fin d) {m : ℕ} (hm : m + 1 ≤ T)
    (H : ArmPath T d → ℝ) :
    (d : ℝ) * ∑ A, wt anchor x (m + 1) A * H A =
      ∑ A, wt anchor x m A * ∑ a, x A (m + 1) a *
        H (Function.update A ⟨m + 1, by omega⟩ a) := by
  rw [fiber ⟨m + 1, by omega⟩]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [wt_succ]
  have h1 : wt anchor x m (Function.update A ⟨m + 1, by omega⟩ a) = wt anchor x m A :=
    dep_update (dep_wt hRun anchor (by omega)) A _ (by simp) a
  have h2 : x (Function.update A ⟨m + 1, by omega⟩ a) (m + 1) = x A (m + 1) :=
    hRun.2 _ A (m + 1) (Finset.mem_Icc.mpr ⟨by omega, hm⟩) (fun s hs => by
      have := Finset.mem_Ico.mp hs
      exact armAt_update_ne A _ a s (by simp; omega))
  have h3 : armAt (Function.update A ⟨m + 1, by omega⟩ a) (m + 1) = a :=
    armAt_update_self A ⟨m + 1, by omega⟩ a
  rw [h1, h2, h3]
  ring

lemma marg (hRun : IsTsallisRun L g x) (anchor : Fin d) {m : ℕ} (hm : m + 1 ≤ T)
    (H : ArmPath T d → ℝ) (hH : Dep m H) :
    (d : ℝ) * ∑ A, wt anchor x (m + 1) A * H A = ∑ A, wt anchor x m A * H A := by
  rw [step hRun anchor hm H]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  congr 1
  have hs := (hRun.1 A (m + 1) (Finset.mem_Icc.mpr ⟨by omega, hm⟩)).1.2
  simp only [dep_update hH A ⟨m + 1, by omega⟩ (by simp) _]
  rw [← Finset.sum_mul, hs, one_mul]

lemma iter (hRun : IsTsallisRun L g x) (anchor : Fin d) (H : ArmPath T d → ℝ) :
    ∀ n m, m + n = T → Dep m H →
      (d : ℝ) ^ n * ∑ A, wt anchor x T A * H A = ∑ A, wt anchor x m A * H A := by
  intro n
  induction n with
  | zero => intro m hm _; subst hm; simp
  | succ n ih =>
    intro m hm hH
    rw [pow_succ, mul_comm ((d:ℝ) ^ n), mul_assoc, ih (m + 1) (by omega) (dep_mono hH (by omega))]
    exact marg hRun anchor (by omega) H hH

lemma tower (hRun : IsTsallisRun L g x) (anchor : Fin d) (hd : 0 < d) {t : ℕ} (ht : t ∈ Icc 1 T)
    (i : Fin d) (F : (Fin d → ℝ) → ℝ) :
    ∑ A, pathWeight anchor x A * (F (x A t) * if armAt A t = i then (1:ℝ) else 0) =
      ∑ A, pathWeight anchor x A * (F (x A t) * x A t i) := by
  have ht' := Finset.mem_Icc.mp ht
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hdep1 : Dep (m + 1) (fun A => F (x A (m + 1)) * if armAt A (m + 1) = i then (1:ℝ) else 0) := by
    intro A B h0 hs
    dsimp only
    have hx : x A (m + 1) = x B (m + 1) := hRun.2 A B (m + 1) ht (fun s hs' => by
      have := Finset.mem_Ico.mp hs'; exact hs s (Finset.mem_Icc.mpr ⟨this.1, by omega⟩))
    rw [hx, hs (m + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)]
  have hdep2 : Dep (m + 1) (fun A => F (x A (m + 1)) * x A (m + 1) i) := by
    intro A B h0 hs
    dsimp only
    have hx : x A (m + 1) = x B (m + 1) := hRun.2 A B (m + 1) ht (fun s hs' => by
      have := Finset.mem_Ico.mp hs'; exact hs s (Finset.mem_Icc.mpr ⟨this.1, by omega⟩))
    rw [hx]
  have e1 := iter hRun anchor _ (T - (m + 1)) (m + 1) (by omega) hdep1
  have e2 := iter hRun anchor _ (T - (m + 1)) (m + 1) (by omega) hdep2
  have s1 := step hRun anchor (m := m) ht'.2
    (fun A => F (x A (m + 1)) * if armAt A (m + 1) = i then (1:ℝ) else 0)
  have s2 := step hRun anchor (m := m) ht'.2 (fun A => F (x A (m + 1)) * x A (m + 1) i)
  have heq : ∑ A, wt anchor x (m + 1) A *
      (F (x A (m + 1)) * if armAt A (m + 1) = i then (1:ℝ) else 0) =
      ∑ A, wt anchor x (m + 1) A * (F (x A (m + 1)) * x A (m + 1) i) := by
    have hdpos : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    apply mul_left_cancel₀ hdpos
    rw [s1, s2]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    congr 1
    have hxA : ∀ a, x (Function.update A ⟨m + 1, by omega⟩ a) (m + 1) = x A (m + 1) := fun a =>
      hRun.2 _ A (m + 1) ht (fun s hs => by
        have := Finset.mem_Ico.mp hs
        exact armAt_update_ne A _ a s (by simp; omega))
    simp only [hxA, armAt_update_self A ⟨m + 1, by omega⟩]
    have hs := (hRun.1 A (m + 1) ht).1.2
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_mul, hs]
    ring
  have hpow : (d : ℝ) ^ (T - (m + 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd.ne')
  apply mul_left_cancel₀ hpow
  have r1 : ∀ A, pathWeight anchor x A = wt anchor x T A := fun A => rfl
  simp only [r1]
  rw [e1, e2, heq]

lemma sum_weight (hRun : IsTsallisRun L g x) (anchor : Fin d) (hd : 0 < d) :
    ∑ A, pathWeight anchor x A = 1 := by
  have e := iter hRun anchor (fun _ => (1:ℝ)) T 0 (by omega) (fun _ _ _ _ => rfl)
  simp only [mul_one] at e
  have h0 : (d : ℝ) * ∑ A : ArmPath T d, wt anchor x 0 A = (d : ℝ) ^ (T + 1) := by
    rw [fiber 0]
    have : ∀ A : ArmPath T d, ∑ a, wt anchor x 0 (Function.update A 0 a) = 1 := by
      intro A
      simp [wt, Function.update_self]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    push_cast; rfl
  have hdpos : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (d : ℝ) ^ (T + 1) * ∑ A, pathWeight anchor x A = (d : ℝ) ^ (T + 1) := by
    rw [pow_succ, mul_comm ((d:ℝ) ^ T), mul_assoc]
    change (d:ℝ) * ((d:ℝ) ^ T * ∑ A, wt anchor x T A) = _
    rw [e, h0]; ring
  have hp : (d : ℝ) ^ (T + 1) ≠ 0 := pow_ne_zero _ hdpos
  calc ∑ A, pathWeight anchor x A = ((d : ℝ) ^ (T + 1))⁻¹ * ((d : ℝ) ^ (T + 1) *
      ∑ A, pathWeight anchor x A) := by field_simp
    _ = 1 := by rw [this]; field_simp

lemma weight_nonneg (hRun : IsTsallisRun L g x) (anchor : Fin d) (A : ArmPath T d) :
    0 ≤ pathWeight anchor x A := by
  unfold pathWeight
  split_ifs
  · exact Finset.prod_nonneg (fun t ht => (hRun.1 A t ht).2.1 _ |>.le)
  · exact le_rfl

end Prob

end P482

namespace P482

open ModernOnlineLearning.Bandits

def ind {T d : ℕ} (A : ArmPath T d) (t : ℕ) (i : Fin d) : ℝ := if armAt A t = i then 1 else 0

def psi {T d : ℕ} (L : ℝ) (g : ℕ → Fin d → ℝ) (x : ArmPath T d → ℕ → Fin d → ℝ)
    (A : ArmPath T d) (t : ℕ) (i : Fin d) : ℝ :=
  2 * g t i ^ 2 * Real.sqrt (x A t i) / x A t i / (4 * L * Real.sqrt (t : ℝ))

def phi {T d : ℕ} (g : ℕ → Fin d → ℝ) (x : ArmPath T d → ℕ → Fin d → ℝ) (k : Fin d)
    (A : ArmPath T d) (t : ℕ) : ℝ :=
  g t k / x A t k

lemma lin1 {T d : ℕ} (w : ArmPath T d → ℝ) (f : ArmPath T d → ℕ → Fin d → ℝ) (S : Finset ℕ) :
    ∑ A, w A * ∑ t ∈ S, ∑ i, f A t i = ∑ t ∈ S, ∑ i, ∑ A, w A * f A t i := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun t _ => Finset.sum_comm)

lemma lin2 {T d : ℕ} (w : ArmPath T d → ℝ) (f : ArmPath T d → ℕ → ℝ) (S : Finset ℕ) :
    ∑ A, w A * ∑ t ∈ S, f A t = ∑ t ∈ S, ∑ A, w A * f A t := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

lemma final_arith (d T : ℕ) (hd2 : 2 ≤ d) (L : ℝ) (hL : 0 < L) :
    (Real.sqrt d - 1) * (4 * L * Real.sqrt (T : ℝ)) + L * Real.sqrt d * Real.sqrt (T : ℝ) ≤
      32 * L * Real.sqrt (((d : ℝ) - 1) * (T : ℝ)) := by
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    linarith
  rw [Real.sqrt_mul hd1]
  have h4 : Real.sqrt d ≤ 2 * Real.sqrt ((d : ℝ) - 1) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    have e : Real.sqrt (4 * ((d : ℝ) - 1)) = 2 * Real.sqrt ((d : ℝ) - 1) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← e]
    exact Real.sqrt_le_sqrt (by linarith)
  have hu : 0 ≤ L * Real.sqrt (T : ℝ) := mul_nonneg hL.le (Real.sqrt_nonneg _)
  have hs1 : 0 ≤ Real.sqrt ((d : ℝ) - 1) := Real.sqrt_nonneg _
  have hsd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h4 hu, mul_nonneg hu hs1, mul_nonneg hu hsd]

end P482

open ModernOnlineLearning.Bandits Finset in
theorem solution {T d : ℕ} (hd : 0 < d)
    (L : ℝ) (hL : 0 < L) (anchor : Fin d)
    (g : ℕ → Fin d → ℝ)
    (x : ArmPath T d → ℕ → Fin d → ℝ)
    (hBound : ∀ t ∈ Finset.Icc 1 T, ∀ i, 0 ≤ g t i ∧ g t i ≤ L)
    (hRun : IsTsallisRun L g x) (k : Fin d) :
    expectedRegret anchor g x k ≤
      32 * L * Real.sqrt (((d : ℝ) - 1) * (T : ℝ)) := by
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · obtain rfl : d = 1 := by omega
    have h0 : expectedRegret anchor g x k = 0 := by
      unfold expectedRegret
      refine Finset.sum_eq_zero (fun A _ => ?_)
      have : ∀ t, g t (armAt A t) - g t k = 0 := fun t => by
        rw [Subsingleton.elim (armAt A t) k]; ring
      simp [this]
    rw [h0]; positivity
  · have hw0 : ∀ A, 0 ≤ pathWeight anchor x A := fun A => P482.weight_nonneg hRun anchor A
    have hw1 : ∑ A, pathWeight anchor x A = 1 := P482.sum_weight hRun anchor hd
    have hsT : ∀ t ∈ Icc 1 T, 0 < Real.sqrt (t : ℝ) := fun t ht =>
      Real.sqrt_pos.mpr (by have := (Finset.mem_Icc.mp ht).1; exact_mod_cast this)
    set K : ℝ := (Real.sqrt d - 1) * (4 * L * Real.sqrt (T : ℝ)) with hK
    have hpath : ∀ A, ∑ t ∈ Icc 1 T, (g t (armAt A t) - g t k) ≤
        K + ∑ t ∈ Icc 1 T, ∑ i, P482.psi L g x A t i * P482.ind A t i +
        ∑ t ∈ Icc 1 T, (P482.phi g x k A t * P482.ind A t k - g t k) := by
      intro A
      have hf := P482.ftrl L hL T (x A) (lossEstimate g x A)
        (fun t ht => (hRun.1 A t ht).1) (fun t ht => (hRun.1 A t ht).2.1)
        (fun t ht i => by
          unfold lossEstimate; split_ifs
          · exact div_nonneg (hBound t ht i).1 ((hRun.1 A t ht).2.1 i).le
          · exact le_rfl)
        (fun t ht p hp => (hRun.1 A t ht).2.2 p hp) k
      have e1 : ∑ t ∈ Icc 1 T, ∑ i, lossEstimate g x A t i * x A t i =
          ∑ t ∈ Icc 1 T, g t (armAt A t) := by
        refine Finset.sum_congr rfl (fun t ht => ?_)
        have hpos := (hRun.1 A t ht).2.1 (armAt A t)
        simp only [lossEstimate, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        field_simp
      have e2 : ∑ t ∈ Icc 1 T, lossEstimate g x A t k =
          ∑ t ∈ Icc 1 T, P482.phi g x k A t * P482.ind A t k := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        simp only [lossEstimate, P482.ind, P482.phi]; split_ifs <;> ring
      have e3 : ∑ t ∈ Icc 1 T, ∑ i, 2 * x A t i * Real.sqrt (x A t i) * lossEstimate g x A t i ^ 2 /
          (4 * L * Real.sqrt (t : ℝ)) =
          ∑ t ∈ Icc 1 T, ∑ i, P482.psi L g x A t i * P482.ind A t i := by
        refine Finset.sum_congr rfl (fun t ht => Finset.sum_congr rfl (fun i _ => ?_))
        have hpos := (hRun.1 A t ht).2.1 i
        have hst := hsT t ht
        simp only [lossEstimate, P482.ind, P482.psi]
        split_ifs
        · field_simp
        · simp
      rw [e1, e2, e3] at hf
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      linarith
    have hE : expectedRegret anchor g x k ≤ ∑ A, pathWeight anchor x A *
        (K + ∑ t ∈ Icc 1 T, ∑ i, P482.psi L g x A t i * P482.ind A t i +
        ∑ t ∈ Icc 1 T, (P482.phi g x k A t * P482.ind A t k - g t k)) := by
      unfold expectedRegret
      exact Finset.sum_le_sum (fun A _ => mul_le_mul_of_nonneg_left (hpath A) (hw0 A))
    simp only [mul_add, Finset.sum_add_distrib] at hE
    rw [← Finset.sum_mul, hw1, one_mul,
      P482.lin1 (fun A => pathWeight anchor x A) (fun A t i => P482.psi L g x A t i * P482.ind A t i),
      P482.lin2 (fun A => pathWeight anchor x A) (fun A t => P482.phi g x k A t * P482.ind A t k - g t k)]
      at hE
    have hphi : ∀ t ∈ Icc 1 T,
        ∑ A, pathWeight anchor x A * (P482.phi g x k A t * P482.ind A t k - g t k) = 0 := by
      intro t ht
      simp only [mul_sub, Finset.sum_sub_distrib]
      have tw : ∑ A, pathWeight anchor x A * (P482.phi g x k A t * P482.ind A t k) =
          ∑ A, pathWeight anchor x A * (P482.phi g x k A t * x A t k) :=
        P482.tower hRun anchor hd ht k (fun p => g t k / p k)
      rw [tw]
      have : ∀ A, P482.phi g x k A t * x A t k = g t k := fun A => by
        have hpos := (hRun.1 A t ht).2.1 k
        unfold P482.phi; field_simp
      simp only [this, ← Finset.sum_mul, hw1, one_mul, sub_self]
    have hpsi : ∀ t ∈ Icc 1 T,
        ∑ i, ∑ A, pathWeight anchor x A * (P482.psi L g x A t i * P482.ind A t i) ≤
          2 * L ^ 2 / (4 * L * Real.sqrt (t : ℝ)) * Real.sqrt d := by
      intro t ht
      have hst := hsT t ht
      have hC : 0 ≤ 2 * L ^ 2 / (4 * L * Real.sqrt (t : ℝ)) := by positivity
      calc ∑ i, ∑ A, pathWeight anchor x A * (P482.psi L g x A t i * P482.ind A t i)
          = ∑ i, ∑ A, pathWeight anchor x A * (P482.psi L g x A t i * x A t i) :=
            Finset.sum_congr rfl (fun i _ => P482.tower hRun anchor hd ht i
              (fun p => 2 * g t i ^ 2 * Real.sqrt (p i) / p i / (4 * L * Real.sqrt (t : ℝ))))
        _ ≤ ∑ i, ∑ A, pathWeight anchor x A *
              (2 * L ^ 2 / (4 * L * Real.sqrt (t : ℝ)) * Real.sqrt (x A t i)) := by
            refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun A _ => ?_))
            refine mul_le_mul_of_nonneg_left ?_ (hw0 A)
            have hpos := (hRun.1 A t ht).2.1 i
            have hg := hBound t ht i
            have e : P482.psi L g x A t i * x A t i =
                2 * g t i ^ 2 / (4 * L * Real.sqrt (t : ℝ)) * Real.sqrt (x A t i) := by
              unfold P482.psi; field_simp
            rw [e]
            refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            nlinarith
        _ = ∑ A, pathWeight anchor x A *
              (2 * L ^ 2 / (4 * L * Real.sqrt (t : ℝ)) * ∑ i, Real.sqrt (x A t i)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun A _ => ?_)
            rw [Finset.mul_sum, Finset.mul_sum]
        _ ≤ ∑ A, pathWeight anchor x A * (2 * L ^ 2 / (4 * L * Real.sqrt (t : ℝ)) * Real.sqrt d) := by
            refine Finset.sum_le_sum (fun A _ => mul_le_mul_of_nonneg_left ?_ (hw0 A))
            exact mul_le_mul_of_nonneg_left
              (P482.sum_sqrt_le _ (hRun.1 A t ht).1.1 (hRun.1 A t ht).1.2) hC
        _ = 2 * L ^ 2 / (4 * L * Real.sqrt (t : ℝ)) * Real.sqrt d := by
            rw [← Finset.sum_mul, hw1, one_mul]
    rw [Finset.sum_congr rfl hphi, Finset.sum_const_zero, add_zero] at hE
    have hS := Finset.sum_le_sum hpsi
    have hS2 : ∑ t ∈ Icc 1 T, 2 * L ^ 2 / (4 * L * Real.sqrt (t : ℝ)) * Real.sqrt d =
        L * Real.sqrt d / 2 * ∑ t ∈ Icc 1 T, 1 / Real.sqrt (t : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have hst := hsT t ht
      field_simp
      ring
    have hinv := P482.sum_inv_sqrt_le T
    have hLd : 0 ≤ L * Real.sqrt d / 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left hinv hLd
    have hfin := P482.final_arith d T hd2 L hL
    linarith
