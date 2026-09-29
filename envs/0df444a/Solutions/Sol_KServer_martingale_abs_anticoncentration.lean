-- Prove2me | solution 1 for KServer.martingale_abs_anticoncentration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T09:35:11.33521+00:00
-- url     : https://prove2.me/submissions/6a57ee20-6f96-4d1c-bb01-fda4f6e607f0

import Mathlib
import Definitions.Def_KServer_discrete_martingale

open Finset KServer

/-! Elementary anti-concentration for finite discrete martingales, replacing
Ibragimov's martingale Berry–Esseen in the BCR lower bound. -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Conditioning: if `f` and `h` are constant on the fibers of `key` and on every
fiber the `P`-weighted sum of `g` equals `h` times the fiber mass, then `f·g` and
`f·h` have the same expectation. -/
private theorem cond_eq (P : Ω → ℝ) (key : Ω → ℕ) (f g h : Ω → ℝ)
    (hf : ∀ ω ω', key ω = key ω' → f ω = f ω')
    (hcl : ∀ ω₀ : Ω, ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω * g ω
      = h ω₀ * ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω)
    (hh : ∀ ω ω', key ω = key ω' → h ω = h ω') :
    ∑ ω, P ω * (f ω * g ω) = ∑ ω, P ω * (f ω * h ω) := by
  classical
  have hfib : ∀ F : Ω → ℝ, ∑ ω, F ω
      = ∑ b ∈ univ.image key, ∑ ω ∈ univ.filter (fun ω => key ω = b), F ω := by
    intro F
    exact (Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image_of_mem key
      (Finset.mem_univ x)) F).symm
  rw [hfib fun ω => P ω * (f ω * g ω), hfib fun ω => P ω * (f ω * h ω)]
  refine Finset.sum_congr rfl ?_
  intro b hb
  obtain ⟨ω₀, -, hω₀⟩ := Finset.mem_image.mp hb
  have hset : (univ.filter fun ω => key ω = b) = univ.filter fun ω => key ω = key ω₀ := by
    rw [hω₀]
  rw [hset]
  have hleft : ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω * (f ω * g ω)
      = f ω₀ * ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω * g ω := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro ω hω
    have hk : key ω = key ω₀ := (Finset.mem_filter.mp hω).2
    rw [hf ω ω₀ hk]
    ring
  have hright : ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω * (f ω * h ω)
      = f ω₀ * (h ω₀ * ∑ ω ∈ univ.filter (fun ω => key ω = key ω₀), P ω) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro ω hω
    have hk : key ω = key ω₀ := (Finset.mem_filter.mp hω).2
    rw [hf ω ω₀ hk, hh ω ω₀ hk]
    ring
  rw [hleft, hright, hcl ω₀]

section Martingale

variable (P : Ω → ℝ) (N : ℕ) (hist : ℕ → Ω → ℕ) (X v : ℕ → Ω → ℝ)

variable {P N hist X v}

private theorem S_succ (j : ℕ) (ω : Ω) : mgSum X (j + 1) ω = mgSum X j ω + X j ω := by
  unfold mgSum
  rw [Finset.sum_range_succ]

variable (H : IsDiscreteMartingale P N hist X v)

/-- Partial sums are `hist j`-measurable. -/
private theorem S_meas (H : IsDiscreteMartingale P N hist X v) (j : ℕ) (hj : j ≤ N)
    (ω ω' : Ω) (h : hist j ω = hist j ω') : mgSum X j ω = mgSum X j ω' := by
  unfold mgSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hiN : i < N := lt_of_lt_of_le (Finset.mem_range.mp hi) hj
  exact H.hadapt i hiN ω ω' (H.href (i + 1) j (Finset.mem_range.mp hi) ω ω' h)

/-- Conditional-mean-zero against any `hist j`-measurable weight. -/
private theorem mart_mul (H : IsDiscreteMartingale P N hist X v) (j : ℕ) (hj : j < N)
    (f : Ω → ℝ) (hf : ∀ ω ω', hist j ω = hist j ω' → f ω = f ω') :
    ∑ ω, P ω * (f ω * X j ω) = 0 := by
  have h := cond_eq P (hist j) f (X j) (fun _ => 0) hf
    (fun ω₀ => by rw [zero_mul]; exact H.hmart j hj ω₀) (fun _ _ _ => rfl)
  rw [h]
  simp

/-- Conditional second moment against any `hist j`-measurable weight. -/
private theorem var_mul (H : IsDiscreteMartingale P N hist X v) (j : ℕ) (hj : j < N)
    (f : Ω → ℝ) (hf : ∀ ω ω', hist j ω = hist j ω' → f ω = f ω') :
    ∑ ω, P ω * (f ω * (X j ω) ^ 2) = ∑ ω, P ω * (f ω * v j ω) :=
  cond_eq P (hist j) f (fun ω => (X j ω) ^ 2) (v j) hf
    (fun ω₀ => H.hvar j hj ω₀) (fun ω ω' h => H.hvmeas j hj ω ω' h)

/-- Orthogonality of increments: the second moment is the expected total variance. -/
private theorem second_moment (H : IsDiscreteMartingale P N hist X v) :
    ∑ ω, P ω * (mgSum X N ω) ^ 2 = ∑ ω, P ω * (∑ j ∈ range N, v j ω) := by
  have key : ∀ k, k ≤ N → ∑ ω, P ω * (mgSum X k ω) ^ 2
      = ∑ ω, P ω * (∑ j ∈ range k, v j ω) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [mgSum]
    | succ k ih =>
      intro hk
      have hkN : k < N := hk
      have hexp : ∀ ω, (mgSum X (k + 1) ω) ^ 2
          = (mgSum X k ω) ^ 2 + 2 * (mgSum X k ω * X k ω) + (X k ω) ^ 2 := by
        intro ω
        rw [S_succ]
        ring
      have h1 : ∑ ω, P ω * (mgSum X (k + 1) ω) ^ 2
          = (∑ ω, P ω * (mgSum X k ω) ^ 2) + 2 * (∑ ω, P ω * (mgSum X k ω * X k ω))
            + ∑ ω, P ω * (X k ω) ^ 2 := by
        have e : ∀ ω : Ω, P ω * (mgSum X (k + 1) ω) ^ 2
            = P ω * (mgSum X k ω) ^ 2 + 2 * (P ω * (mgSum X k ω * X k ω)) + P ω * (X k ω) ^ 2 := by
          intro ω
          rw [S_succ]
          ring
        rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum]
      have h2 : ∑ ω, P ω * (mgSum X k ω * X k ω) = 0 :=
        mart_mul H k hkN (mgSum X k) (S_meas H k (le_of_lt hkN))
      have h3 : ∑ ω, P ω * (X k ω) ^ 2 = ∑ ω, P ω * v k ω := by
        have := var_mul H k hkN (fun _ => 1) (fun _ _ _ => rfl)
        simpa using this
      have h4 : ∑ ω, P ω * (∑ j ∈ range (k + 1), v j ω)
          = (∑ ω, P ω * (∑ j ∈ range k, v j ω)) + ∑ ω, P ω * v k ω := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.sum_range_succ]
        ring
      rw [h1, h2, h3, ih (le_of_lt hkN), h4]
      ring
  exact key N (le_refl N)

/-- Weighted second moments are nondecreasing in time. -/
private theorem weighted_sq_mono (H : IsDiscreteMartingale P N hist X v) (j k : ℕ)
    (f : Ω → ℝ) (hf : ∀ ω ω', hist j ω = hist j ω' → f ω = f ω')
    (hf0 : ∀ ω, 0 ≤ f ω) (hjk : j ≤ k) (hkN : k ≤ N) :
    ∑ ω, P ω * (f ω * (mgSum X k ω) ^ 2) ≤ ∑ ω, P ω * (f ω * (mgSum X N ω) ^ 2) := by
  have main : ∀ k', k ≤ k' → k' ≤ N →
      ∑ ω, P ω * (f ω * (mgSum X k ω) ^ 2) ≤ ∑ ω, P ω * (f ω * (mgSum X k' ω) ^ 2) := by
    intro k'
    induction k' with
    | zero =>
      intro h1 _
      have hk0 : k = 0 := by omega
      rw [hk0]
    | succ k' ih =>
      intro h1 h2
      by_cases hk : k = k' + 1
      · rw [hk]
      · have h1' : k ≤ k' := by omega
        have h2' : k' ≤ N := by omega
        refine le_trans (ih h1' h2') ?_
        have hk'N : k' < N := by omega
        have hmid : ∑ ω, P ω * (f ω * mgSum X k' ω * X k' ω) = 0 :=
          mart_mul H k' hk'N (fun ω => f ω * mgSum X k' ω) (fun ω ω' h => by
            show f ω * mgSum X k' ω = f ω' * mgSum X k' ω'
            rw [hf ω ω' (H.href j k' (by omega) ω ω' h),
              S_meas H k' (le_of_lt hk'N) ω ω' h])
        have hexp : ∑ ω, P ω * (f ω * (mgSum X (k' + 1) ω) ^ 2)
            = (∑ ω, P ω * (f ω * (mgSum X k' ω) ^ 2))
              + 2 * (∑ ω, P ω * (f ω * mgSum X k' ω * X k' ω))
              + ∑ ω, P ω * (f ω * (X k' ω) ^ 2) := by
          have e : ∀ ω : Ω, P ω * (f ω * (mgSum X (k' + 1) ω) ^ 2)
              = P ω * (f ω * (mgSum X k' ω) ^ 2)
                + 2 * (P ω * (f ω * mgSum X k' ω * X k' ω))
                + P ω * (f ω * (X k' ω) ^ 2) := by
            intro ω
            rw [S_succ]
            ring
          rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_add_distrib,
            Finset.sum_add_distrib, ← Finset.mul_sum]
        have hpos : 0 ≤ ∑ ω, P ω * (f ω * (X k' ω) ^ 2) :=
          Finset.sum_nonneg fun ω _ => mul_nonneg (H.hP ω)
            (mul_nonneg (hf0 ω) (sq_nonneg _))
        rw [hexp, hmid]
        linarith
  exact main N hkN (le_refl N)

/-- The fourth-moment bound: `E[S⁴] ≤ 8·B·E[S²] + 3γ²B·(ΣP)` for a martingale with
increments bounded by `γ` and total conditional variance at most `B`. -/
private theorem fourth_moment (H : IsDiscreteMartingale P N hist X v) (γ B : ℝ) (hγ : 0 ≤ γ)
    (hX : ∀ j, j < N → ∀ ω, |X j ω| ≤ γ)
    (hv0 : ∀ j, j < N → ∀ ω, 0 ≤ v j ω)
    (hVB : ∀ ω, ∑ j ∈ range N, v j ω ≤ B) :
    ∑ ω, P ω * (mgSum X N ω) ^ 4
      ≤ 8 * B * (∑ ω, P ω * (mgSum X N ω) ^ 2) + 3 * γ ^ 2 * B * (∑ ω, P ω) := by
  have main : ∀ k, k ≤ N →
      ∑ ω, P ω * (mgSum X k ω) ^ 4
        ≤ 8 * (∑ ω, P ω * ((mgSum X N ω) ^ 2 * (∑ j ∈ range k, v j ω)))
          + 3 * γ ^ 2 * (∑ ω, P ω * (∑ j ∈ range k, v j ω)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have h1 : ∀ ω : Ω, P ω * (mgSum X 0 ω) ^ 4 = 0 := by
        intro ω
        have : mgSum X 0 ω = 0 := by
          unfold mgSum
          simp
        rw [this]
        ring
      have h2 : ∀ ω : Ω, P ω * ((mgSum X N ω) ^ 2 * (∑ j ∈ range 0, v j ω)) = 0 := by
        intro ω
        simp
      have h3 : ∀ ω : Ω, P ω * (∑ j ∈ range 0, v j ω) = 0 := by
        intro ω
        simp
      rw [Finset.sum_congr rfl fun ω _ => h1 ω, Finset.sum_congr rfl fun ω _ => h2 ω,
        Finset.sum_congr rfl fun ω _ => h3 ω]
      simp
    | succ k ih =>
      intro hk
      have hkN : k < N := hk
      have hSm := S_meas H k (le_of_lt hkN)
      -- vanishing odd term
      have hodd : ∑ ω, P ω * ((mgSum X k ω) ^ 3 * X k ω) = 0 :=
        mart_mul H k hkN (fun ω => (mgSum X k ω) ^ 3) (fun ω ω' h => by
          show (mgSum X k ω) ^ 3 = (mgSum X k ω') ^ 3
          rw [hSm ω ω' h])
      -- square term
      have hsq : ∑ ω, P ω * ((mgSum X k ω) ^ 2 * (X k ω) ^ 2)
          = ∑ ω, P ω * ((mgSum X k ω) ^ 2 * v k ω) :=
        var_mul H k hkN (fun ω => (mgSum X k ω) ^ 2) (fun ω ω' h => by
          show (mgSum X k ω) ^ 2 = (mgSum X k ω') ^ 2
          rw [hSm ω ω' h])
      -- cube term
      have hcube : ∑ ω, P ω * (mgSum X k ω * (X k ω) ^ 3)
          ≤ γ * ∑ ω, P ω * (|mgSum X k ω| * (X k ω) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun ω _ => ?_
        have h1 : mgSum X k ω * (X k ω) ^ 3 ≤ |mgSum X k ω| * (γ * (X k ω) ^ 2) := by
          calc mgSum X k ω * (X k ω) ^ 3 ≤ |mgSum X k ω * (X k ω) ^ 3| := le_abs_self _
            _ = |mgSum X k ω| * (|X k ω| * (X k ω) ^ 2) := by
                rw [abs_mul, pow_succ, abs_mul, abs_sq]
                ring
            _ ≤ |mgSum X k ω| * (γ * (X k ω) ^ 2) := by
                refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                exact mul_le_mul_of_nonneg_right (hX k hkN ω) (sq_nonneg _)
        calc P ω * (mgSum X k ω * (X k ω) ^ 3)
            ≤ P ω * (|mgSum X k ω| * (γ * (X k ω) ^ 2)) :=
              mul_le_mul_of_nonneg_left h1 (H.hP ω)
          _ = γ * (P ω * (|mgSum X k ω| * (X k ω) ^ 2)) := by ring
      have hcube3 : ∑ ω, P ω * (|mgSum X k ω| * (X k ω) ^ 2)
          = ∑ ω, P ω * (|mgSum X k ω| * v k ω) :=
        var_mul H k hkN (fun ω => |mgSum X k ω|) (fun ω ω' h => by
          show |mgSum X k ω| = |mgSum X k ω'|
          rw [hSm ω ω' h])
      -- quartic term
      have hquart2 : ∑ ω, P ω * (X k ω) ^ 2 = ∑ ω, P ω * v k ω := by
        have h := var_mul H k hkN (fun _ => 1) (fun _ _ _ => rfl)
        calc ∑ ω, P ω * (X k ω) ^ 2 = ∑ ω, P ω * (1 * (X k ω) ^ 2) := by
              refine Finset.sum_congr rfl fun ω _ => by ring
          _ = ∑ ω, P ω * (1 * v k ω) := h
          _ = ∑ ω, P ω * v k ω := by
              refine Finset.sum_congr rfl fun ω _ => by ring
      have hquart : ∑ ω, P ω * (X k ω) ^ 4 ≤ γ ^ 2 * ∑ ω, P ω * v k ω := by
        rw [← hquart2, Finset.mul_sum]
        refine Finset.sum_le_sum fun ω _ => ?_
        have h2 : (X k ω) ^ 2 ≤ γ ^ 2 := by
          have h3 := hX k hkN ω
          nlinarith [abs_nonneg (X k ω), sq_abs (X k ω)]
        calc P ω * (X k ω) ^ 4 ≤ P ω * (γ ^ 2 * (X k ω) ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ (H.hP ω)
              nlinarith [sq_nonneg (X k ω)]
          _ = γ ^ 2 * (P ω * (X k ω) ^ 2) := by ring
      -- 4γ·E[|S|v] ≤ 2·E[S²v] + 2γ²·E[v]
      have habs : 4 * (γ * ∑ ω, P ω * (|mgSum X k ω| * v k ω))
          ≤ 2 * (∑ ω, P ω * ((mgSum X k ω) ^ 2 * v k ω))
            + 2 * γ ^ 2 * (∑ ω, P ω * v k ω) := by
        have e : ∀ ω : Ω, 4 * (γ * (P ω * (|mgSum X k ω| * v k ω)))
            ≤ 2 * (P ω * ((mgSum X k ω) ^ 2 * v k ω)) + 2 * γ ^ 2 * (P ω * v k ω) := by
          intro ω
          have h1 : 0 ≤ P ω * v k ω := mul_nonneg (H.hP ω) (hv0 k hkN ω)
          have h2 : 2 * γ * |mgSum X k ω| ≤ (mgSum X k ω) ^ 2 + γ ^ 2 := by
            nlinarith [sq_nonneg (|mgSum X k ω| - γ), sq_abs (mgSum X k ω)]
          nlinarith [abs_nonneg (mgSum X k ω)]
        calc 4 * (γ * ∑ ω, P ω * (|mgSum X k ω| * v k ω))
            = ∑ ω, 4 * (γ * (P ω * (|mgSum X k ω| * v k ω))) := by
              rw [Finset.mul_sum, Finset.mul_sum]
          _ ≤ ∑ ω, (2 * (P ω * ((mgSum X k ω) ^ 2 * v k ω)) + 2 * γ ^ 2 * (P ω * v k ω)) :=
              Finset.sum_le_sum fun ω _ => e ω
          _ = _ := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      -- monotonicity to time N
      have hmono : ∑ ω, P ω * (v k ω * (mgSum X k ω) ^ 2)
          ≤ ∑ ω, P ω * (v k ω * (mgSum X N ω) ^ 2) :=
        weighted_sq_mono H k k (v k) (fun ω ω' h => H.hvmeas k hkN ω ω' h)
          (fun ω => hv0 k hkN ω) (le_refl k) (le_of_lt hkN)
      have hswap1 : ∑ ω, P ω * ((mgSum X k ω) ^ 2 * v k ω)
          = ∑ ω, P ω * (v k ω * (mgSum X k ω) ^ 2) :=
        Finset.sum_congr rfl fun ω _ => by ring
      -- expansion of the fourth power
      have hexp : ∑ ω, P ω * (mgSum X (k + 1) ω) ^ 4
          = (∑ ω, P ω * (mgSum X k ω) ^ 4)
            + 4 * (∑ ω, P ω * ((mgSum X k ω) ^ 3 * X k ω))
            + 6 * (∑ ω, P ω * ((mgSum X k ω) ^ 2 * (X k ω) ^ 2))
            + 4 * (∑ ω, P ω * (mgSum X k ω * (X k ω) ^ 3))
            + ∑ ω, P ω * (X k ω) ^ 4 := by
        have e : ∀ ω : Ω, P ω * (mgSum X (k + 1) ω) ^ 4
            = P ω * (mgSum X k ω) ^ 4 + 4 * (P ω * ((mgSum X k ω) ^ 3 * X k ω))
              + 6 * (P ω * ((mgSum X k ω) ^ 2 * (X k ω) ^ 2))
              + 4 * (P ω * (mgSum X k ω * (X k ω) ^ 3)) + P ω * (X k ω) ^ 4 := by
          intro ω
          rw [S_succ]
          ring
        rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      -- range-splitting of the accumulators
      have hV1 : ∑ ω, P ω * ((mgSum X N ω) ^ 2 * (∑ j ∈ range (k + 1), v j ω))
          = (∑ ω, P ω * ((mgSum X N ω) ^ 2 * (∑ j ∈ range k, v j ω)))
            + ∑ ω, P ω * (v k ω * (mgSum X N ω) ^ 2) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.sum_range_succ]
        ring
      have hV2 : ∑ ω, P ω * (∑ j ∈ range (k + 1), v j ω)
          = (∑ ω, P ω * (∑ j ∈ range k, v j ω)) + ∑ ω, P ω * v k ω := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.sum_range_succ]
        ring
      have hihk := ih (le_of_lt hkN)
      have hcube3' : γ * ∑ ω, P ω * (|mgSum X k ω| * (X k ω) ^ 2)
          = γ * ∑ ω, P ω * (|mgSum X k ω| * v k ω) := by rw [hcube3]
      rw [hexp, hodd, hsq, hV1, hV2]
      linarith [hcube, hcube3', hquart, habs, hmono, hihk, hswap1]
  have hmain := main N (le_refl N)
  have hub1 : ∑ ω, P ω * ((mgSum X N ω) ^ 2 * (∑ j ∈ range N, v j ω))
      ≤ B * ∑ ω, P ω * (mgSum X N ω) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    calc P ω * ((mgSum X N ω) ^ 2 * (∑ j ∈ range N, v j ω))
        ≤ P ω * ((mgSum X N ω) ^ 2 * B) := by
          refine mul_le_mul_of_nonneg_left ?_ (H.hP ω)
          exact mul_le_mul_of_nonneg_left (hVB ω) (sq_nonneg _)
      _ = B * (P ω * (mgSum X N ω) ^ 2) := by ring
  have hub2 : ∑ ω, P ω * (∑ j ∈ range N, v j ω) ≤ B * ∑ ω, P ω := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    calc P ω * (∑ j ∈ range N, v j ω) ≤ P ω * B :=
          mul_le_mul_of_nonneg_left (hVB ω) (H.hP ω)
      _ = B * P ω := by ring
  have hγ2 : (0 : ℝ) ≤ 3 * γ ^ 2 := by positivity
  nlinarith [hmain, hub1, hub2]

end Martingale

/-- Cauchy–Schwarz twice: `(E f²)³ ≤ (E |f|)² · (E f⁴)` over nonnegative weights. -/
private theorem sq_cubed_le_abs_sq_mul_quartic (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω) (f : Ω → ℝ) :
    (∑ ω, P ω * f ω ^ 2) ^ 3 ≤ (∑ ω, P ω * |f ω|) ^ 2 * (∑ ω, P ω * f ω ^ 4) := by
  classical
  have hcs1 : (∑ ω, P ω * f ω ^ 2) ^ 2
      ≤ (∑ ω, P ω * |f ω|) * (∑ ω, P ω * |f ω| ^ 3) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun ω _ => mul_nonneg (hP ω) (abs_nonneg _))
      (fun ω _ => mul_nonneg (hP ω) (by positivity)) ?_
    intro ω _
    have habs : |f ω| ^ 2 = f ω ^ 2 := sq_abs _
    have h : (P ω * f ω ^ 2) ^ 2 = (P ω * |f ω|) * (P ω * |f ω| ^ 3) := by
      calc (P ω * f ω ^ 2) ^ 2 = P ω ^ 2 * (|f ω| ^ 2) ^ 2 := by rw [habs]; ring
        _ = (P ω * |f ω|) * (P ω * |f ω| ^ 3) := by ring
    exact le_of_eq h
  have hcs2 : (∑ ω, P ω * |f ω| ^ 3) ^ 2
      ≤ (∑ ω, P ω * f ω ^ 2) * (∑ ω, P ω * f ω ^ 4) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun ω _ => mul_nonneg (hP ω) (sq_nonneg _))
      (fun ω _ => mul_nonneg (hP ω) (by positivity)) ?_
    intro ω _
    have h : (P ω * |f ω| ^ 3) ^ 2 = (P ω * f ω ^ 2) * (P ω * f ω ^ 4) := by
      have habs : |f ω| ^ 2 = f ω ^ 2 := sq_abs _
      calc (P ω * |f ω| ^ 3) ^ 2 = P ω ^ 2 * (|f ω| ^ 2) ^ 3 := by ring
        _ = P ω ^ 2 * (f ω ^ 2) ^ 3 := by rw [habs]
        _ = (P ω * f ω ^ 2) * (P ω * f ω ^ 4) := by ring
    exact le_of_eq h
  set A := ∑ ω, P ω * |f ω| with hA
  set B2 := ∑ ω, P ω * f ω ^ 2 with hB2
  set C := ∑ ω, P ω * |f ω| ^ 3 with hC
  set D := ∑ ω, P ω * f ω ^ 4 with hD
  have hB2nn : 0 ≤ B2 := Finset.sum_nonneg fun ω _ => mul_nonneg (hP ω) (sq_nonneg _)
  have hDnn : 0 ≤ D := Finset.sum_nonneg fun ω _ => mul_nonneg (hP ω) (by positivity)
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun ω _ => mul_nonneg (hP ω) (abs_nonneg _)
  have hCnn : 0 ≤ C := Finset.sum_nonneg fun ω _ => mul_nonneg (hP ω) (by positivity)
  rcases eq_or_lt_of_le hB2nn with hB0 | hB0
  · rw [← hB0]
    have hz : (0 : ℝ) ^ 3 = 0 := by norm_num
    rw [hz]
    exact mul_nonneg (sq_nonneg _) hDnn
  · -- B2⁴ ≤ A²C² ≤ A²·B2·D, divide by B2 > 0
    have h1 : B2 ^ 4 ≤ A ^ 2 * C ^ 2 := by nlinarith
    have h2 : A ^ 2 * C ^ 2 ≤ A ^ 2 * (B2 * D) := by nlinarith [sq_nonneg A]
    have h3 : B2 ^ 4 ≤ A ^ 2 * (B2 * D) := le_trans h1 h2
    have h4 : B2 ^ 4 = B2 * B2 ^ 3 := by ring
    have h5 : A ^ 2 * (B2 * D) = B2 * (A ^ 2 * D) := by ring
    rw [h4, h5] at h3
    exact le_of_mul_le_mul_left h3 hB0

/-- **Anti-concentration for a stopped martingale**: if the total conditional
variance lies in `[T₀, B]` pathwise and increments are bounded by `γ`, then
`T₀³ ≤ (E|S|)² · (8B² + 3γ²B)`. -/
theorem solution
    (P : Ω → ℝ) (N : ℕ) (hist : ℕ → Ω → ℕ) (X v : ℕ → Ω → ℝ)
    (H : IsDiscreteMartingale P N hist X v) (γ B T₀ : ℝ) (hγ : 0 ≤ γ)
    (hX : ∀ j, j < N → ∀ ω, |X j ω| ≤ γ)
    (hv0 : ∀ j, j < N → ∀ ω, 0 ≤ v j ω)
    (hVB : ∀ ω, ∑ j ∈ range N, v j ω ≤ B)
    (hVT : ∀ ω, T₀ ≤ ∑ j ∈ range N, v j ω)
    (hT₀ : 0 ≤ T₀) (hB : 0 ≤ B) (hPsum : ∑ ω, P ω = 1) :
    T₀ ^ 3 ≤ (∑ ω, P ω * |mgSum X N ω|) ^ 2 * (8 * B ^ 2 + 3 * γ ^ 2 * B) := by
  have h2 := second_moment H
  have h4 := fourth_moment H γ B hγ hX hv0 hVB
  rw [hPsum, mul_one] at h4
  have hE2lb : T₀ ≤ ∑ ω, P ω * (mgSum X N ω) ^ 2 := by
    rw [h2]
    calc T₀ = T₀ * ∑ ω, P ω := by rw [hPsum, mul_one]
      _ = ∑ ω, T₀ * P ω := by rw [Finset.mul_sum]
      _ ≤ ∑ ω, P ω * (∑ j ∈ range N, v j ω) := by
          refine Finset.sum_le_sum fun ω _ => ?_
          calc T₀ * P ω = P ω * T₀ := by ring
            _ ≤ P ω * (∑ j ∈ range N, v j ω) :=
              mul_le_mul_of_nonneg_left (hVT ω) (H.hP ω)
  have hE2ub : ∑ ω, P ω * (mgSum X N ω) ^ 2 ≤ B := by
    rw [h2]
    calc ∑ ω, P ω * (∑ j ∈ range N, v j ω) ≤ ∑ ω, P ω * B := by
          refine Finset.sum_le_sum fun ω _ => ?_
          exact mul_le_mul_of_nonneg_left (hVB ω) (H.hP ω)
      _ = B := by rw [← Finset.sum_mul, hPsum, one_mul]
  have hcs := sq_cubed_le_abs_sq_mul_quartic P H.hP (mgSum X N)
  have hE4 : ∑ ω, P ω * (mgSum X N ω) ^ 4 ≤ 8 * B ^ 2 + 3 * γ ^ 2 * B := by
    calc ∑ ω, P ω * (mgSum X N ω) ^ 4
        ≤ 8 * B * (∑ ω, P ω * (mgSum X N ω) ^ 2) + 3 * γ ^ 2 * B := h4
      _ ≤ 8 * B * B + 3 * γ ^ 2 * B := by
          nlinarith [hB, hE2ub]
      _ = 8 * B ^ 2 + 3 * γ ^ 2 * B := by ring
  have hcube_mono : T₀ ^ 3 ≤ (∑ ω, P ω * (mgSum X N ω) ^ 2) ^ 3 := by
    exact pow_le_pow_left₀ hT₀ hE2lb 3
  have habs_nn : 0 ≤ (∑ ω, P ω * |mgSum X N ω|) ^ 2 := sq_nonneg _
  calc T₀ ^ 3 ≤ (∑ ω, P ω * (mgSum X N ω) ^ 2) ^ 3 := hcube_mono
    _ ≤ (∑ ω, P ω * |mgSum X N ω|) ^ 2 * (∑ ω, P ω * (mgSum X N ω) ^ 4) := hcs
    _ ≤ (∑ ω, P ω * |mgSum X N ω|) ^ 2 * (8 * B ^ 2 + 3 * γ ^ 2 * B) :=
        mul_le_mul_of_nonneg_left hE4 habs_nn
