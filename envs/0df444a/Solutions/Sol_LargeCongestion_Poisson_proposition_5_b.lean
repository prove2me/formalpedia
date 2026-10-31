-- Prove2me | solution 1 for LargeCongestion.Poisson.proposition_5_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:32:35.656055+00:00
-- url     : https://prove2.me/submissions/1af9f34d-9699-4af1-b536-cad749b9d910

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

open MeasureTheory ProbabilityTheory LargeCongestion.Poisson

namespace LCPProp5bAux

lemma pmf_nonneg (x : ℝ) (k : ℕ) : 0 ≤ poissonPmf x k := measureReal_nonneg

lemma pmf_succ {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    ((k : ℝ) + 1) * poissonPmf x (k + 1) = x * poissonPmf x k := by
  rw [poissonPmf_eq hx, poissonPmf_eq hx, Nat.factorial_succ, pow_succ]
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  push_cast
  field_simp

lemma pmf_zero_param (k : ℕ) (hk : k ≠ 0) : poissonPmf 0 k = 0 := by
  rw [poissonPmf_eq le_rfl, zero_pow hk]; simp

lemma summable_at_zero (f : ℕ → ℝ) : Summable (fun k => f k * poissonPmf 0 k) := by
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  simp only [Finset.mem_singleton] at hk
  rw [pmf_zero_param k hk, mul_zero]

/-- `Ssh x f i`: `E[|f(X + i)|] < ∞` for `X ∼ Poisson(x)`. -/
def Ssh (x : ℝ) (f : ℕ → ℝ) (i : ℕ) : Prop :=
  Summable (fun k : ℕ => |f (k + i)| * poissonPmf x k)

/-- `Mom x f i`: `E[X^i |f(X)|] < ∞` for `X ∼ Poisson(x)`. -/
def Mom (x : ℝ) (f : ℕ → ℝ) (i : ℕ) : Prop :=
  Summable (fun k : ℕ => (k : ℝ) ^ i * |f k| * poissonPmf x k)

/-- For a nonnegative sequence, `∑ k f k < ∞` implies `∑ f k < ∞`. -/
lemma summable_of_mul_k (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (h : Summable (fun k : ℕ => (k : ℝ) * f k)) : Summable f := by
  rw [← summable_nat_add_iff 1]
  have h' := (summable_nat_add_iff 1).2 h
  refine Summable.of_nonneg_of_le (fun k => hf _) (fun k => ?_) h'
  have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith [k.cast_nonneg (α := ℝ)]
  calc f (k + 1) = 1 * f (k + 1) := (one_mul _).symm
    _ ≤ ((k + 1 : ℕ) : ℝ) * f (k + 1) := mul_le_mul_of_nonneg_right this (hf _)

lemma mul_k_iff (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) (j : ℕ) :
    Summable (fun k : ℕ => (k : ℝ) * f k) ↔ Summable (fun k : ℕ => ((k : ℝ) + j) * f k) := by
  constructor
  · intro h
    have h0 := summable_of_mul_k f hf h
    have := h.add (h0.mul_left (j : ℝ))
    refine this.congr (fun k => ?_)
    ring
  · intro h
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg k.cast_nonneg (hf k)) (fun k => ?_) h
    exact mul_le_mul_of_nonneg_right (by linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]) (hf k)

lemma P1 {x : ℝ} (hx : 0 < x) (g : ℕ → ℝ) : Ssh x g 1 ↔ Mom x g 1 := by
  unfold Ssh Mom
  rw [← summable_nat_add_iff 1 (f := fun k : ℕ => (k : ℝ) ^ 1 * |g k| * poissonPmf x k)]
  have heq : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 1 * |g (k + 1)| * poissonPmf x (k + 1)) =
      fun k => x * (|g (k + 1)| * poissonPmf x k) := by
    funext k
    have := pmf_succ hx.le k
    push_cast
    linear_combination |g (k + 1)| * this
  rw [heq, summable_mul_left_iff hx.ne']

lemma Pj {x : ℝ} (hx : 0 < x) : ∀ (j : ℕ) (g : ℕ → ℝ), Ssh x g j ↔ Mom x g j := by
  intro j
  induction j with
  | zero =>
    intro g
    unfold Ssh Mom
    simp
  | succ j ih =>
    intro g
    -- left side
    have hL : Ssh x g (j + 1) ↔ Summable (fun k : ℕ => (k : ℝ) * (|g (k + j)| * poissonPmf x k)) := by
      have := P1 hx (fun k => g (k + j))
      unfold Ssh Mom at this
      unfold Ssh
      have e1 : (fun k : ℕ => |g (k + (j + 1))| * poissonPmf x k) =
          fun k => |g (k + 1 + j)| * poissonPmf x k := by
        funext k; congr 3; omega
      rw [e1, this]
      apply summable_congr
      intro k; ring
    have hR : Mom x g (j + 1) ↔
        Summable (fun k : ℕ => ((k : ℝ) + j) * (|g (k + j)| * poissonPmf x k)) := by
      have h1 : Mom x g (j + 1) ↔ Mom x (fun k => (k : ℝ) * g k) j := by
        unfold Mom
        apply summable_congr
        intro k
        rw [abs_mul, Nat.abs_cast, pow_succ]
        ring
      rw [h1, ← ih]
      unfold Ssh
      apply summable_congr
      intro k
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      push_cast
      ring
    rw [hL, hR]
    exact mul_k_iff _ (fun k => mul_nonneg (abs_nonneg _) (pmf_nonneg _ _)) j

lemma mom_mono (x : ℝ) (g : ℕ → ℝ) (i : ℕ) (h : Mom x g (i + 1)) : Mom x g i := by
  unfold Mom at *
  rw [← summable_nat_add_iff 1] at h ⊢
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (mul_nonneg (by positivity)
    (abs_nonneg _)) (pmf_nonneg _ _)) (fun k => ?_) h
  have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith [k.cast_nonneg (α := ℝ)]
  have h2 : ((k + 1 : ℕ) : ℝ) ^ i ≤ ((k + 1 : ℕ) : ℝ) ^ (i + 1) :=
    pow_le_pow_right₀ h1 (Nat.le_succ i)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
    (pmf_nonneg _ _)

lemma ssh_mono {x : ℝ} (hx : 0 < x) (g : ℕ → ℝ) (i : ℕ) (h : Ssh x g (i + 1)) : Ssh x g i :=
  (Pj hx i g).2 (mom_mono x g i ((Pj hx (i + 1) g).1 h))

lemma claim1 {x : ℝ} (hx : 0 < x) :
    ∀ (j : ℕ) (h : ℕ → ℝ), Ssh x h j → Ssh x (deltaPow j h) 0 := by
  intro j
  induction j with
  | zero => intro h hh; simpa [deltaPow] using hh
  | succ j ih =>
    intro h hh
    have hd : Ssh x (delta h) j := by
      have h0 := ssh_mono hx h j hh
      unfold Ssh at *
      refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (pmf_nonneg _ _))
        (fun k => ?_) (hh.add h0)
      unfold delta
      have : k + j + 1 = k + (j + 1) := by omega
      rw [this, ← add_mul]
      exact mul_le_mul_of_nonneg_right (abs_sub _ _) (pmf_nonneg _ _)
    have := ih (delta h) hd
    have e : deltaPow (j + 1) h = deltaPow j (delta h) := by
      simp only [deltaPow, Function.iterate_succ_apply]
    rw [e]; exact this

lemma base {x : ℝ} (hx : 0 < x) (g : ℕ → ℝ) (hg : Ssh x (delta g) 0) : Ssh x g 1 := by
  unfold Ssh at *
  set a : ℕ → ℝ := fun k => |g (k + 1)| * poissonPmf x k with ha
  set b : ℕ → ℝ := fun k => |delta g (k + 0)| * poissonPmf x k with hb
  have ha0 : ∀ k, 0 ≤ a k := fun k => mul_nonneg (abs_nonneg _) (pmf_nonneg _ _)
  have hb0 : ∀ k, 0 ≤ b k := fun k => mul_nonneg (abs_nonneg _) (pmf_nonneg _ _)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 * x ≤ K := ⟨⌈2 * x⌉₊, Nat.le_ceil _⟩
  have hrec : ∀ k, K ≤ k → a (k + 1) ≤ b (k + 1) + a k / 2 := by
    intro k hk
    have hkR : (K : ℝ) ≤ k := by exact_mod_cast hk
    have hp := pmf_succ hx.le k
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hp' : poissonPmf x (k + 1) ≤ poissonPmf x k / 2 := by
      have : ((k : ℝ) + 1) * poissonPmf x (k + 1) ≤ ((k : ℝ) + 1) * (poissonPmf x k / 2) := by
        rw [hp]; nlinarith [pmf_nonneg x k]
      exact le_of_mul_le_mul_left this hpos
    have htri : |g (k + 1 + 1)| ≤ |delta g (k + 1 + 0)| + |g (k + 1)| := by
      unfold delta
      simp only [add_zero]
      calc |g (k + 1 + 1)| = |(g (k + 1 + 1) - g (k + 1)) + g (k + 1)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    simp only [ha, hb]
    calc |g (k + 1 + 1)| * poissonPmf x (k + 1)
        ≤ (|delta g (k + 1 + 0)| + |g (k + 1)|) * poissonPmf x (k + 1) :=
          mul_le_mul_of_nonneg_right htri (pmf_nonneg _ _)
      _ = |delta g (k + 1 + 0)| * poissonPmf x (k + 1) + |g (k + 1)| * poissonPmf x (k + 1) := by
          ring
      _ ≤ |delta g (k + 1 + 0)| * poissonPmf x (k + 1) + |g (k + 1)| * (poissonPmf x k / 2) := by
          gcongr
      _ = _ := by ring
  have hbs : Summable (fun m => b (K + 1 + m)) := by
    have := (summable_nat_add_iff (K + 1)).2 hg
    refine this.congr (fun m => ?_)
    simp only [hb, add_zero]
    rw [show m + (K + 1) = K + 1 + m by omega]
  -- `V(n)`: `∑_{m<n} a(K+1+m) + a(K+n) ≤ 2 ∑_{m<n} b(K+1+m) + 2 a K`
  have hV : ∀ n, ∑ m ∈ Finset.range n, a (K + 1 + m) + a (K + n) ≤
      2 * ∑ m ∈ Finset.range n, b (K + 1 + m) + 2 * a K := by
    intro n
    induction n with
    | zero => simp; linarith [ha0 K]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have := hrec (K + n) (by omega)
      rw [show K + n + 1 = K + 1 + n by omega] at this
      rw [show K + (n + 1) = K + 1 + n by omega]
      linarith
  have htail : Summable (fun m => a (K + 1 + m)) := by
    apply summable_of_sum_range_le (c := 2 * ∑' m, b (K + 1 + m) + 2 * a K)
    · intro m; exact ha0 _
    · intro n
      have h1 := hV n
      have h2 : ∑ m ∈ Finset.range n, b (K + 1 + m) ≤ ∑' m, b (K + 1 + m) :=
        hbs.sum_le_tsum _ (fun m _ => hb0 _)
      linarith [ha0 (K + n)]
  have : Summable (fun m => a (m + (K + 1))) := htail.congr (fun m => by congr 1; omega)
  exact (summable_nat_add_iff (K + 1)).1 this

lemma claim2 {x : ℝ} (hx : 0 < x) :
    ∀ (j : ℕ) (h : ℕ → ℝ), Ssh x (deltaPow j h) 0 → Ssh x h j := by
  intro j
  induction j with
  | zero => intro h hh; simpa [deltaPow] using hh
  | succ j ih =>
    intro h hh
    have e : deltaPow (j + 1) h = deltaPow j (delta h) := by
      simp only [deltaPow, Function.iterate_succ_apply]
    rw [e] at hh
    have h1 : Ssh x (delta h) j := ih (delta h) hh
    have h2 : Ssh x (delta (fun k => h (k + j))) 0 := by
      unfold Ssh at *
      refine h1.congr (fun k => ?_)
      simp only [delta, add_zero]
      rw [show k + 1 + j = k + j + 1 by omega]
    have h3 := base hx _ h2
    unfold Ssh at *
    refine h3.congr (fun k => ?_)
    simp only []
    rw [show k + 1 + j = k + (j + 1) by omega]

end LCPProp5bAux

open LCPProp5bAux in
theorem solution (h : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) (j : ℕ) (hj : 1 ≤ j) :
    (Summable (fun k : ℕ => |deltaPow j h k| * poissonPmf x k) ↔
        Summable (fun k : ℕ => |h (k + j)| * poissonPmf x k)) ∧
      (Summable (fun k : ℕ => |h (k + j)| * poissonPmf x k) ↔
        Summable (fun k : ℕ => (k : ℝ) ^ j * |h k| * poissonPmf x k)) := by
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨⟨fun _ => summable_at_zero _, fun _ => summable_at_zero _⟩,
      ⟨fun _ => ?_, fun _ => summable_at_zero _⟩⟩
    refine (summable_at_zero (fun k => (k : ℝ) ^ j * |h k|)).congr (fun k => ?_)
    ring
  · have e0 : ∀ f : ℕ → ℝ, Ssh x f 0 ↔ Summable (fun k : ℕ => |f k| * poissonPmf x k) := by
      intro f; unfold Ssh; simp
    refine ⟨?_, Pj hpos j h⟩
    rw [← e0]
    exact ⟨claim2 hpos j h, claim1 hpos j h⟩
