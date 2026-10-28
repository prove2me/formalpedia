-- Prove2me | solution 1 for ModernOnlineLearning.LowerBounds.theorem_A_14_p1
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T08:13:59.10699+00:00
-- url     : https://prove2.me/submissions/8820e68e-6177-4058-85e3-c22ad53fa195

import Mathlib

namespace Prove2SwarmSubmission

namespace BacklogCuratorKhintchine

abbrev Cube (N : ℕ) := Fin N → Bool

noncomputable def avg (N : ℕ) (f : Cube N → ℝ) : ℝ :=
  ((2 : ℝ) ^ N)⁻¹ * ∑ ω : Cube N, f ω

def negate {N : ℕ} (ω : Cube N) : Cube N := fun i => !(ω i)

def flip {N : ℕ} (i : Fin N) (ω : Cube N) : Cube N :=
  Function.update ω i (!(ω i))

def signedSum {N : ℕ} (x : Fin N → ℝ) (ω : Cube N) : ℝ :=
  ∑ i : Fin N, (if ω i then (1 : ℝ) else -1) * x i

noncomputable def energy {N : ℕ} (f : Cube N → ℝ) : ℝ :=
  ∑ i : Fin N, avg N (fun ω => ((f ω - f (flip i ω)) / 2) ^ 2)

end BacklogCuratorKhintchine

namespace BacklogCuratorKhintchine

theorem cube_two_pow_ne_zero (N : ℕ) : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero N two_ne_zero

theorem cube_two_pow_inv_nonneg (N : ℕ) : 0 ≤ ((2 : ℝ) ^ N)⁻¹ :=
  inv_nonneg.mpr (pow_nonneg zero_le_two N)

theorem sum_cube_const (N : ℕ) (c : ℝ) : ∑ _ω : Cube N, c = (2 : ℝ) ^ N * c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp

theorem avg_const (N : ℕ) (c : ℝ) : avg N (fun _ => c) = c := by
  unfold avg
  rw [sum_cube_const, ← mul_assoc, inv_mul_cancel₀ (cube_two_pow_ne_zero N), one_mul]

theorem avg_add {N : ℕ} (f g : Cube N → ℝ) :
    avg N (fun ω => f ω + g ω) = avg N f + avg N g := by
  unfold avg
  rw [Finset.sum_add_distrib, mul_add]

theorem avg_sub {N : ℕ} (f g : Cube N → ℝ) :
    avg N (fun ω => f ω - g ω) = avg N f - avg N g := by
  unfold avg
  rw [Finset.sum_sub_distrib, mul_sub]

theorem avg_neg {N : ℕ} (f : Cube N → ℝ) :
    avg N (fun ω => -f ω) = -avg N f := by
  unfold avg
  rw [Finset.sum_neg_distrib]
  ring

theorem avg_const_mul {N : ℕ} (c : ℝ) (f : Cube N → ℝ) :
    avg N (fun ω => c * f ω) = c * avg N f := by
  unfold avg
  rw [← Finset.mul_sum]
  ring

theorem avg_mul_const {N : ℕ} (f : Cube N → ℝ) (c : ℝ) :
    avg N (fun ω => f ω * c) = avg N f * c := by
  unfold avg
  rw [← Finset.sum_mul]
  ring

theorem avg_nonneg {N : ℕ} (f : Cube N → ℝ) (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ avg N f := by
  unfold avg
  exact mul_nonneg (cube_two_pow_inv_nonneg N) (Finset.sum_nonneg (fun ω _ => hf ω))

theorem avg_mono {N : ℕ} (f g : Cube N → ℝ) (h : ∀ ω, f ω ≤ g ω) : avg N f ≤ avg N g := by
  unfold avg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ω _ => h ω))
    (cube_two_pow_inv_nonneg N)

theorem negate_involutive {N : ℕ} : Function.Involutive (@negate N) := by
  intro ω
  funext i
  simp [negate]

theorem flip_involutive {N : ℕ} (i : Fin N) : Function.Involutive (flip i) := by
  intro ω
  simp [flip]

theorem sum_negate {N : ℕ} (g : Cube N → ℝ) : ∑ ω, g (negate ω) = ∑ ω, g ω :=
  Fintype.sum_bijective negate negate_involutive.bijective
    (fun ω => g (negate ω)) g (fun _ => rfl)

theorem sum_flip {N : ℕ} (i : Fin N) (g : Cube N → ℝ) : ∑ ω, g (flip i ω) = ∑ ω, g ω :=
  Fintype.sum_bijective (flip i) (flip_involutive i).bijective
    (fun ω => g (flip i ω)) g (fun _ => rfl)

theorem avg_negate {N : ℕ} (f : Cube N → ℝ) : avg N (fun ω => f (negate ω)) = avg N f := by
  unfold avg
  rw [sum_negate f]

theorem flip_apply_self {N : ℕ} (i : Fin N) (ω : Cube N) : flip i ω i = !ω i := by
  rw [flip, Function.update_apply, if_pos rfl]

theorem flip_apply_of_ne {N : ℕ} {i j : Fin N} (hji : j ≠ i) (ω : Cube N) :
    flip i ω j = ω j := by
  rw [flip, Function.update_apply, if_neg hji]

theorem sign_mul_self (b : Bool) :
    (if b then (1 : ℝ) else -1) * (if b then (1 : ℝ) else -1) = 1 := by
  cases b <;> norm_num

theorem sign_not (b : Bool) :
    (if !b then (1 : ℝ) else -1) = -(if b then (1 : ℝ) else -1) := by
  cases b <;> norm_num

theorem sum_sign_mul_sign {N : ℕ} (i j : Fin N) :
    ∑ ω : Cube N, (if ω i then (1 : ℝ) else -1) * (if ω j then (1 : ℝ) else -1) =
      if i = j then (2 : ℝ) ^ N else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    simp only [sign_mul_self]
    rw [sum_cube_const, mul_one]
  · rw [if_neg hij]
    have h := sum_flip i
      (fun ω => (if ω i then (1 : ℝ) else -1) * (if ω j then (1 : ℝ) else -1))
    have hterm : ∀ ω : Cube N,
        (if flip i ω i then (1 : ℝ) else -1) * (if flip i ω j then (1 : ℝ) else -1) =
          -((if ω i then (1 : ℝ) else -1) * (if ω j then (1 : ℝ) else -1)) := by
      intro ω
      rw [flip_apply_self, flip_apply_of_ne (Ne.symm hij), sign_not]
      ring
    simp only [hterm, Finset.sum_neg_distrib] at h
    linarith

theorem sum_signedSum_sq {N : ℕ} (x : Fin N → ℝ) :
    ∑ ω : Cube N, (signedSum x ω) ^ 2 = (2 : ℝ) ^ N * ∑ i : Fin N, (x i) ^ 2 := by
  unfold signedSum
  have hexp : ∀ ω : Cube N, (∑ i, (if ω i then (1 : ℝ) else -1) * x i) ^ 2 =
      ∑ i, ∑ j, x i * x j *
        ((if ω i then (1 : ℝ) else -1) * (if ω j then (1 : ℝ) else -1)) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  calc
    ∑ ω : Cube N, (∑ i, (if ω i then (1 : ℝ) else -1) * x i) ^ 2
        = ∑ ω : Cube N, ∑ i, ∑ j, x i * x j *
            ((if ω i then (1 : ℝ) else -1) * (if ω j then (1 : ℝ) else -1)) :=
          Finset.sum_congr rfl (fun ω _ => hexp ω)
    _ = ∑ i, ∑ j, ∑ ω : Cube N, x i * x j *
            ((if ω i then (1 : ℝ) else -1) * (if ω j then (1 : ℝ) else -1)) :=
          Finset.sum_comm.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
    _ = ∑ i, ∑ j, x i * x j * (if i = j then (2 : ℝ) ^ N else 0) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [← Finset.mul_sum, sum_sign_mul_sign]
    _ = ∑ i, x i * x i * (2 : ℝ) ^ N := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_eq_single i]
          · rw [if_pos rfl]
          · intro b _ hb
            rw [if_neg (Ne.symm hb), mul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
    _ = (2 : ℝ) ^ N * ∑ i : Fin N, (x i) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)

theorem avg_signedSum_sq {N : ℕ} (x : Fin N → ℝ) :
    avg N (fun omega => (signedSum x omega)^2) = ∑ i : Fin N, (x i)^2 := by
  unfold avg
  rw [sum_signedSum_sq, ← mul_assoc, inv_mul_cancel₀ (cube_two_pow_ne_zero N), one_mul]

/-! ### First-coordinate recursion -/

theorem sum_cube_succ {N : ℕ} (f : Cube (N + 1) → ℝ) :
    ∑ ω : Cube (N + 1), f ω =
      ∑ ω : Cube N, (f (Fin.cons false ω) + f (Fin.cons true ω)) := by
  have hbij : Function.Bijective
      (fun p : Bool × Cube N => (Fin.cons p.1 p.2 : Cube (N + 1))) := by
    constructor
    · rintro ⟨a, ω⟩ ⟨b, η⟩ hab
      simp only [Fin.cons_inj] at hab
      rw [hab.1, hab.2]
    · intro ω
      exact ⟨(ω 0, Fin.tail ω), Fin.cons_self_tail ω⟩
  calc
    ∑ ω : Cube (N + 1), f ω = ∑ p : Bool × Cube N, f (Fin.cons p.1 p.2) :=
      (Fintype.sum_bijective _ hbij (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm
    _ = ∑ b : Bool, ∑ ω : Cube N, f (Fin.cons b ω) := Fintype.sum_prod_type _
    _ = ∑ ω : Cube N, f (Fin.cons true ω) + ∑ ω : Cube N, f (Fin.cons false ω) :=
      Fintype.sum_bool _
    _ = ∑ ω : Cube N, (f (Fin.cons false ω) + f (Fin.cons true ω)) :=
      (add_comm _ _).trans Finset.sum_add_distrib.symm

theorem avg_succ {N : ℕ} (f : Cube (N + 1) → ℝ) :
    avg (N + 1) f =
      (avg N (fun ω => f (Fin.cons false ω)) + avg N (fun ω => f (Fin.cons true ω))) / 2 := by
  unfold avg
  rw [sum_cube_succ, Finset.sum_add_distrib]
  ring


end BacklogCuratorKhintchine

namespace BacklogCuratorKhintchine

def slice {N : ℕ} (f : Cube (N + 1) → ℝ) (b : Bool) : Cube N → ℝ :=
  fun ω => f (Fin.cons b ω)

noncomputable def evenPart {N : ℕ} (f : Cube (N + 1) → ℝ) : Cube N → ℝ :=
  fun ω => (slice f false ω + slice f true ω) / 2

noncomputable def oddPart {N : ℕ} (f : Cube (N + 1) → ℝ) : Cube N → ℝ :=
  fun ω => (slice f false ω - slice f true ω) / 2

end BacklogCuratorKhintchine

namespace BacklogCuratorKhintchine

/-- Global sign reversal commutes with head splitting. -/
theorem parity_negate_cons {N : ℕ} (b : Bool) (ω : Cube N) :
    negate (Fin.cons b ω) = Fin.cons (!b) (negate ω) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- For even functions, reversing the tail swaps the two head slices. -/
theorem slice_negate_of_even {N : ℕ} (f : Cube (N + 1) → ℝ)
    (heven : ∀ η, f (negate η) = f η) (b : Bool) (ω : Cube N) :
    slice f (!b) (negate ω) = slice f b ω := by
  change f (Fin.cons (!b) (negate ω)) = f (Fin.cons b ω)
  rw [← parity_negate_cons b ω]
  exact heven (Fin.cons b ω)

/-- The head-average part of an even function is even on the smaller cube. -/
theorem evenPart_even {N : ℕ} (f : Cube (N + 1) → ℝ)
    (heven : ∀ η, f (negate η) = f η) :
    ∀ ω, evenPart f (negate ω) = evenPart f ω := by
  intro ω
  have h0 := slice_negate_of_even f heven false ω
  have h1 := slice_negate_of_even f heven true ω
  change slice f true (negate ω) = slice f false ω at h0
  change slice f false (negate ω) = slice f true ω at h1
  change (slice f false (negate ω) + slice f true (negate ω)) / 2 =
    (slice f false ω + slice f true ω) / 2
  rw [h1, h0]
  ring

/-- The head-difference part of an even function is odd on the smaller cube. -/
theorem oddPart_odd {N : ℕ} (f : Cube (N + 1) → ℝ)
    (heven : ∀ η, f (negate η) = f η) :
    ∀ ω, oddPart f (negate ω) = -oddPart f ω := by
  intro ω
  have h0 := slice_negate_of_even f heven false ω
  have h1 := slice_negate_of_even f heven true ω
  change slice f true (negate ω) = slice f false ω at h0
  change slice f false (negate ω) = slice f true ω at h1
  change (slice f false (negate ω) - slice f true (negate ω)) / 2 =
    -((slice f false ω - slice f true ω) / 2)
  rw [h1, h0]
  ring

/-- A finite odd average vanishes, once negate-invariance of the average is supplied. -/
theorem parity_avg_eq_zero_of_odd {N : ℕ} (g : Cube N → ℝ)
    (hodd : ∀ ω, g (negate ω) = -g ω)
    (hinvariant : avg N (fun ω => g (negate ω)) = avg N g) :
    avg N g = 0 := by
  have hfun : (fun ω => g (negate ω)) = fun ω => -g ω := funext hodd
  have hneg : avg N (fun ω => -g ω) = -avg N g := by
    unfold avg
    rw [Finset.sum_neg_distrib]
    ring
  rw [hfun, hneg] at hinvariant
  linarith

/-- The odd part of an even function has zero mean. -/
theorem avg_oddPart_eq_zero {N : ℕ} (f : Cube (N + 1) → ℝ)
    (heven : ∀ η, f (negate η) = f η)
    (hnegate : ∀ g : Cube N → ℝ,
      avg N (fun ω => g (negate ω)) = avg N g) :
    avg N (oddPart f) = 0 :=
  parity_avg_eq_zero_of_odd (oddPart f) (oddPart_odd f heven) (hnegate (oddPart f))

/-- First moment under a head split. The exposed premise is the finite-cube recurrence. -/
theorem avg_succ_evenPart {N : ℕ} (f : Cube (N + 1) → ℝ)
    (hrec : ∀ g : Cube (N + 1) → ℝ,
      avg (N + 1) g = avg N
        (fun ω => (g (Fin.cons false ω) + g (Fin.cons true ω)) / 2)) :
    avg (N + 1) f = avg N (evenPart f) := by
  exact hrec f

/-- The exact algebraic identity at a paired cube point. -/
theorem slice_sq_average {N : ℕ} (f : Cube (N + 1) → ℝ) (ω : Cube N) :
    ((slice f false ω) ^ 2 + (slice f true ω) ^ 2) / 2 =
      (evenPart f ω) ^ 2 + (oddPart f ω) ^ 2 := by
  unfold evenPart oddPart
  ring

/-- Second moment splits into the two smaller-cube second moments.
Only elementary average recurrence and additivity are exposed to the caller. -/
theorem avg_succ_sq_parts {N : ℕ} (f : Cube (N + 1) → ℝ)
    (hrec : ∀ g : Cube (N + 1) → ℝ,
      avg (N + 1) g = avg N
        (fun ω => (g (Fin.cons false ω) + g (Fin.cons true ω)) / 2))
    (hadd : ∀ g h : Cube N → ℝ,
      avg N (fun ω => g ω + h ω) = avg N g + avg N h) :
    avg (N + 1) (fun η => (f η) ^ 2) =
      avg N (fun ω => (evenPart f ω) ^ 2) + avg N (fun ω => (oddPart f ω) ^ 2) := by
  have hpoint :
      (fun ω => ((f (Fin.cons false ω)) ^ 2 + (f (Fin.cons true ω)) ^ 2) / 2) =
        (fun ω => (evenPart f ω) ^ 2 + (oddPart f ω) ^ 2) := by
    funext ω
    exact slice_sq_average f ω
  calc
    avg (N + 1) (fun η => (f η) ^ 2) =
        avg N (fun ω => ((f (Fin.cons false ω)) ^ 2 +
          (f (Fin.cons true ω)) ^ 2) / 2) := hrec (fun η => (f η) ^ 2)
    _ = avg N (fun ω => (evenPart f ω) ^ 2 + (oddPart f ω) ^ 2) :=
      congrArg (avg N) hpoint
    _ = avg N (fun ω => (evenPart f ω) ^ 2) +
          avg N (fun ω => (oddPart f ω) ^ 2) := hadd _ _

/-- The variance decomposition used in the ordinary and even inductions. -/
theorem variance_succ_parts {N : ℕ} (f : Cube (N + 1) → ℝ)
    (hrec : ∀ g : Cube (N + 1) → ℝ,
      avg (N + 1) g = avg N
        (fun ω => (g (Fin.cons false ω) + g (Fin.cons true ω)) / 2))
    (hadd : ∀ g h : Cube N → ℝ,
      avg N (fun ω => g ω + h ω) = avg N g + avg N h) :
    avg (N + 1) (fun η => (f η) ^ 2) - (avg (N + 1) f) ^ 2 =
      (avg N (fun ω => (evenPart f ω) ^ 2) - (avg N (evenPart f)) ^ 2) +
        avg N (fun ω => (oddPart f ω) ^ 2) := by
  rw [avg_succ_sq_parts f hrec hadd, avg_succ_evenPart f hrec]
  ring

/-- Evaluation of the average on the singleton zero-dimensional cube. -/
theorem avg_zero_dim (f : Cube 0 → ℝ) :
    avg 0 f = f (fun i => Fin.elim0 i) := by
  have hconst : ∀ ω : Cube 0, f ω = f (fun i => Fin.elim0 i) := by
    intro ω
    apply congrArg f
    funext i
    exact Fin.elim0 i
  unfold avg
  simp only [pow_zero, inv_one, one_mul]
  calc
    (∑ ω : Cube 0, f ω) = ∑ _ω : Cube 0, f (fun i => Fin.elim0 i) :=
      Finset.sum_congr rfl (fun ω _hω => hconst ω)
    _ = f (fun i => Fin.elim0 i) := by simp

/-- The zero-dimensional variance is zero for every function. -/
theorem avg_zero_dim_variance (f : Cube 0 → ℝ) :
    avg 0 (fun ω => (f ω) ^ 2) - (avg 0 f) ^ 2 = 0 := by
  rw [avg_zero_dim, avg_zero_dim]
  ring

end BacklogCuratorKhintchine

namespace BacklogCuratorKhintchine

/-- Head flips only change the head bit. -/
theorem energy_flip_cons_zero {N : ℕ} (b : Bool) (ω : Cube N) :
    flip (0 : Fin (N + 1)) (Fin.cons b ω) = Fin.cons (!b) ω := by
  simp only [flip, Fin.cons_zero, Fin.update_cons_zero]

/-- A tail-coordinate flip commutes with adding the head bit. -/
theorem energy_flip_cons_succ {N : ℕ} (i : Fin N) (b : Bool) (ω : Cube N) :
    flip i.succ (Fin.cons b ω) = Fin.cons b (flip i ω) := by
  simp only [flip, Fin.cons_succ]
  exact (Fin.cons_update (α := fun _ : Fin (N + 1) => Bool)
    b ω i (!(ω i))).symm

/-- The two head derivatives have the same square. -/
theorem energy_head_derivative_sq {N : ℕ} (f : Cube (N + 1) → ℝ)
    (b : Bool) (ω : Cube N) :
    ((f (Fin.cons b ω) - f (flip (0 : Fin (N + 1)) (Fin.cons b ω))) / 2) ^ 2 =
      (oddPart f ω) ^ 2 := by
  rw [energy_flip_cons_zero]
  cases b with
  | false => rfl
  | true =>
      change ((f (Fin.cons true ω) - f (Fin.cons false ω)) / 2) ^ 2 =
        ((f (Fin.cons false ω) - f (Fin.cons true ω)) / 2) ^ 2
      ring

/-- Averaging the head-coordinate energy gives exactly the odd-part second moment.
The sole averaging premise is the head-coordinate splitting identity. -/
theorem energy_head_split {N : ℕ} (f : Cube (N + 1) → ℝ)
    (hsplit : ∀ φ : Cube (N + 1) → ℝ,
      avg (N + 1) φ = (avg N (slice φ false) + avg N (slice φ true)) / 2) :
    avg (N + 1) (fun ω => ((f ω - f (flip (0 : Fin (N + 1)) ω)) / 2) ^ 2) =
      avg N (fun ω => (oddPart f ω) ^ 2) := by
  let D : Cube (N + 1) → ℝ :=
    fun ω => ((f ω - f (flip (0 : Fin (N + 1)) ω)) / 2) ^ 2
  change avg (N + 1) D = _
  have hfalse : slice D false = fun ω => (oddPart f ω) ^ 2 := by
    funext ω
    exact energy_head_derivative_sq f false ω
  have htrue : slice D true = fun ω => (oddPart f ω) ^ 2 := by
    funext ω
    exact energy_head_derivative_sq f true ω
  rw [hsplit D, hfalse, htrue]
  ring

/-- A tail-coordinate energy splits as the energies of the even and odd parts.
No averaging linearity theorem is assumed: the required identity follows directly
from the defining finite sums and the parallelogram identity. -/
theorem energy_tail_split {N : ℕ} (f : Cube (N + 1) → ℝ)
    (hsplit : ∀ φ : Cube (N + 1) → ℝ,
      avg (N + 1) φ = (avg N (slice φ false) + avg N (slice φ true)) / 2)
    (i : Fin N) :
    avg (N + 1) (fun ω => ((f ω - f (flip i.succ ω)) / 2) ^ 2) =
      avg N (fun ω => ((evenPart f ω - evenPart f (flip i ω)) / 2) ^ 2) +
      avg N (fun ω => ((oddPart f ω - oddPart f (flip i ω)) / 2) ^ 2) := by
  let D : Cube (N + 1) → ℝ := fun ω => ((f ω - f (flip i.succ ω)) / 2) ^ 2
  let A : Bool → Cube N → ℝ :=
    fun b ω => ((slice f b ω - slice f b (flip i ω)) / 2) ^ 2
  let G : Cube N → ℝ :=
    fun ω => ((evenPart f ω - evenPart f (flip i ω)) / 2) ^ 2
  let H : Cube N → ℝ :=
    fun ω => ((oddPart f ω - oddPart f (flip i ω)) / 2) ^ 2
  have hfalse : slice D false = A false := by
    funext ω
    dsimp only [D, A, slice]
    rw [energy_flip_cons_succ]
  have htrue : slice D true = A true := by
    funext ω
    dsimp only [D, A, slice]
    rw [energy_flip_cons_succ]
  have hpoint : ∀ ω : Cube N, A false ω + A true ω = 2 * (G ω + H ω) := by
    intro ω
    dsimp only [A, G, H, evenPart, oddPart, slice]
    ring
  have hsum :
      (∑ ω : Cube N, A false ω) + (∑ ω : Cube N, A true ω) =
        2 * ((∑ ω : Cube N, G ω) + (∑ ω : Cube N, H ω)) := by
    calc
      _ = ∑ ω : Cube N, (A false ω + A true ω) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ ω : Cube N, 2 * (G ω + H ω) := by
        apply Finset.sum_congr rfl
        intro ω _
        exact hpoint ω
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
  change avg (N + 1) D = avg N G + avg N H
  rw [hsplit D, hfalse, htrue]
  change
    ((((2 : ℝ) ^ N)⁻¹ * ∑ ω : Cube N, A false ω) +
      (((2 : ℝ) ^ N)⁻¹ * ∑ ω : Cube N, A true ω)) / 2 =
        ((2 : ℝ) ^ N)⁻¹ * (∑ ω : Cube N, G ω) +
        ((2 : ℝ) ^ N)⁻¹ * (∑ ω : Cube N, H ω)
  calc
    _ = (((2 : ℝ) ^ N)⁻¹ / 2) *
        ((∑ ω : Cube N, A false ω) + (∑ ω : Cube N, A true ω)) := by ring
    _ = (((2 : ℝ) ^ N)⁻¹ / 2) *
        (2 * ((∑ ω : Cube N, G ω) + (∑ ω : Cube N, H ω))) := by rw [hsum]
    _ = _ := by ring

/-- Exact head-coordinate energy decomposition, conditional only on `avg_succ`.
All dimensions, including a zero-dimensional tail, are allowed. -/
theorem energy_split_of_avg_succ {N : ℕ} (f : Cube (N + 1) → ℝ)
    (hsplit : ∀ φ : Cube (N + 1) → ℝ,
      avg (N + 1) φ = (avg N (slice φ false) + avg N (slice φ true)) / 2) :
    energy f = energy (evenPart f) + energy (oddPart f) +
      avg N (fun ω => (oddPart f ω) ^ 2) := by
  unfold energy
  rw [Fin.sum_univ_succ]
  rw [energy_head_split f hsplit]
  simp_rw [energy_tail_split f hsplit]
  rw [Finset.sum_add_distrib]
  ring

end BacklogCuratorKhintchine


namespace BacklogCuratorKhintchine

theorem reviewer_energy_nonneg {N : ℕ} (f : Cube N → ℝ) : 0 ≤ energy f := by
  unfold energy
  apply Finset.sum_nonneg
  intro i _hi
  unfold avg
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) N))
    (Finset.sum_nonneg fun ω _hω => sq_nonneg _)

/-- Ordinary cube Poincare follows from the finite coordinate identities.
The supplied facts are equalities of finite averages and energies. -/
theorem ordinary_poincare_from_splits
    (hzero : ∀ f : Cube 0 → ℝ,
      avg 0 (fun ω => (f ω) ^ 2) = (avg 0 f) ^ 2)
    (hmean : ∀ {N : ℕ} (f : Cube (N + 1) → ℝ),
      avg (N + 1) f = avg N (evenPart f))
    (hsecond : ∀ {N : ℕ} (f : Cube (N + 1) → ℝ),
      avg (N + 1) (fun ω => (f ω) ^ 2) =
        avg N (fun ω => (evenPart f ω) ^ 2) +
          avg N (fun ω => (oddPart f ω) ^ 2))
    (henergy : ∀ {N : ℕ} (f : Cube (N + 1) → ℝ),
      energy f = energy (evenPart f) + energy (oddPart f) +
        avg N (fun ω => (oddPart f ω) ^ 2)) :
    ∀ (N : ℕ) (f : Cube N → ℝ),
      avg N (fun ω => (f ω) ^ 2) - (avg N f) ^ 2 ≤ energy f := by
  intro N
  induction N with
  | zero =>
      intro f
      rw [hzero f]
      simpa only [sub_self] using reviewer_energy_nonneg f
  | succ N ih =>
      intro f
      have hg := ih (evenPart f)
      have hh := reviewer_energy_nonneg (oddPart f)
      rw [hsecond f, hmean f, henergy f]
      linarith

/-- The sharp even cube inequality. The full finite-cube theorem is obtained
by supplying the coordinate identities and parity facts, without an analytic
inequality premise. -/
theorem even_poincare_from_splits
    (hzero : ∀ f : Cube 0 → ℝ,
      avg 0 (fun ω => (f ω) ^ 2) = (avg 0 f) ^ 2)
    (hmean : ∀ {N : ℕ} (f : Cube (N + 1) → ℝ),
      avg (N + 1) f = avg N (evenPart f))
    (hsecond : ∀ {N : ℕ} (f : Cube (N + 1) → ℝ),
      avg (N + 1) (fun ω => (f ω) ^ 2) =
        avg N (fun ω => (evenPart f ω) ^ 2) +
          avg N (fun ω => (oddPart f ω) ^ 2))
    (henergy : ∀ {N : ℕ} (f : Cube (N + 1) → ℝ),
      energy f = energy (evenPart f) + energy (oddPart f) +
        avg N (fun ω => (oddPart f ω) ^ 2))
    (hevenPart : ∀ {N : ℕ} (f : Cube (N + 1) → ℝ),
      (∀ ω, f (negate ω) = f ω) →
        ∀ ω, evenPart f (negate ω) = evenPart f ω)
    (hoddMean : ∀ {N : ℕ} (f : Cube (N + 1) → ℝ),
      (∀ ω, f (negate ω) = f ω) → avg N (oddPart f) = 0) :
    ∀ (N : ℕ) (f : Cube N → ℝ),
      (∀ ω, f (negate ω) = f ω) →
        avg N (fun ω => (f ω) ^ 2) - (avg N f) ^ 2 ≤ energy f / 2 := by
  intro N
  induction N with
  | zero =>
      intro f _heven
      rw [hzero f]
      have hnonneg := reviewer_energy_nonneg f
      linarith
  | succ N ih =>
      intro f heven
      have hg := ih (evenPart f) (hevenPart f heven)
      have hh := ordinary_poincare_from_splits hzero hmean hsecond henergy N (oddPart f)
      rw [hoddMean f heven] at hh
      norm_num at hh
      rw [hsecond f, hmean f, henergy f]
      linarith

end BacklogCuratorKhintchine

namespace BacklogCuratorKhintchine

/-- The average of a paired function can be taken before the head average. -/
theorem reviewer_avg_succ_inside {N : ℕ} (f : Cube (N + 1) → ℝ) :
    avg (N + 1) f = avg N
      (fun ω => (f (Fin.cons false ω) + f (Fin.cons true ω)) / 2) := by
  calc
    avg (N + 1) f =
        (avg N (fun ω => f (Fin.cons false ω)) +
          avg N (fun ω => f (Fin.cons true ω))) / 2 := avg_succ f
    _ = avg N (fun ω => (f (Fin.cons false ω) + f (Fin.cons true ω)) / 2) := by
      simp_rw [div_eq_mul_inv]
      rw [← avg_add]
      exact (avg_mul_const
        (fun ω => f (Fin.cons false ω) + f (Fin.cons true ω)) ((2 : ℝ)⁻¹)).symm

/-- Improved cube Poincare for globally even real functions, with the exact
normalization and energy fixed by the owner interface. -/
theorem even_poincare {N : ℕ} (f : Cube N → ℝ)
    (heven : ∀ ω, f (negate ω) = f ω) :
    avg N (fun ω => (f ω) ^ 2) - (avg N f) ^ 2 ≤ energy f / 2 := by
  exact even_poincare_from_splits
    (fun g => by simp only [avg_zero_dim])
    (fun g => avg_succ_evenPart g reviewer_avg_succ_inside)
    (fun g => avg_succ_sq_parts g reviewer_avg_succ_inside avg_add)
    (fun g => energy_split_of_avg_succ g (fun φ => avg_succ φ))
    (fun g hg => evenPart_even g hg)
    (fun g hg => avg_oddPart_eq_zero g hg avg_negate)
    N f heven

end BacklogCuratorKhintchine

namespace BacklogCuratorKhintchine
/-- Positivity of the literal averaging factor in the frozen statement. -/
theorem avg_weight_pos (N : ℕ) : 0 < ((2 : ℝ) ^ N)⁻¹ := by
  positivity

/-- A finite nonnegative function has a nonnegative cube average. -/
theorem avg_nonneg_owner {N : ℕ} (f : Cube N → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ avg N f := by
  exact mul_nonneg (le_of_lt (avg_weight_pos N))
    (Finset.sum_nonneg fun ω _ => hf ω)

/-- The mean absolute Rademacher sum is nonnegative, including the empty cube. -/
theorem mean_abs_nonneg {N : ℕ} (x : Fin N → ℝ) :
    0 ≤ avg N (fun ω => |signedSum x ω|) := by
  exact avg_nonneg_owner _ (fun ω => abs_nonneg (signedSum x ω))

/-- The second moment of the absolute sum is unchanged. -/
theorem avg_abs_sq_eq {N : ℕ} (x : Fin N → ℝ) :
    avg N (fun ω => |signedSum x ω| ^ 2) =
      avg N (fun ω => signedSum x ω ^ 2) := by
  simp only [sq_abs]

/-- The coefficient square sum is nonnegative for every finite dimension. -/
theorem sum_sq_nonneg (N : ℕ) (x : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, x i ^ 2 := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

/-- Zero coefficients give the exact lower bound with equality. -/
theorem zero_coefficients (N : ℕ) :
    (1 / Real.sqrt 2) * Real.sqrt (∑ i : Fin N, ((0 : Fin N → ℝ) i) ^ 2) ≤
      ((2 : ℝ) ^ N)⁻¹ *
        ∑ ω : Fin N → Bool,
          |∑ i : Fin N, (if ω i then (1 : ℝ) else -1) * (0 : Fin N → ℝ) i| := by
  simp

/-- The empty-dimensional expression has the expected value zero. -/
theorem empty_dimension (x : Fin 0 → ℝ) :
    (1 / Real.sqrt 2) * Real.sqrt (∑ i : Fin 0, (x i) ^ 2) ≤
      ((2 : ℝ) ^ 0)⁻¹ *
        ∑ ω : Fin 0 → Bool,
          |∑ i : Fin 0, (if ω i then (1 : ℝ) else -1) * x i| := by
  simp


/-- The exact sharp constant, from the quadratic estimate delivered by even Poincare. -/
theorem sharp_sqrt_bound {q m : ℝ} (hq : 0 ≤ q) (hm : 0 ≤ m)
    (h : q ≤ 2 * m ^ 2) :
    (1 / Real.sqrt 2) * Real.sqrt q ≤ m := by
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hsqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_q_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  have hsqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt htwo
  have hproduct_nonneg : 0 ≤ m * Real.sqrt 2 :=
    mul_nonneg hm (Real.sqrt_nonneg 2)
  have hsquare : (Real.sqrt q) ^ 2 ≤ (m * Real.sqrt 2) ^ 2 := by
    calc
      (Real.sqrt q) ^ 2 = q := hsqrt_q_sq
      _ ≤ 2 * m ^ 2 := h
      _ = (m * Real.sqrt 2) ^ 2 := by
        rw [mul_pow, hsqrt_two_sq]
        ring
  have hroot : Real.sqrt q ≤ m * Real.sqrt 2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg q) hproduct_nonneg).mp hsquare
  calc
    (1 / Real.sqrt 2) * Real.sqrt q = Real.sqrt q / Real.sqrt 2 := by ring
    _ ≤ m := (div_le_iff₀ hsqrt_two_pos).mpr hroot

/-- Even Poincare and the gradient bound imply the exact needed quadratic estimate. -/
theorem quadratic_bound_of_variance_energy {q m e : ℝ}
    (hvariance : q - m ^ 2 ≤ e / 2) (henergy : e ≤ q) :
    q ≤ 2 * m ^ 2 := by
  linarith

/-- Direct assembly interface for a nonnegative second moment and nonnegative mean. -/
theorem sharp_sqrt_bound_of_variance_energy {q m e : ℝ}
    (hq : 0 ≤ q) (hm : 0 ≤ m)
    (hvariance : q - m ^ 2 ≤ e / 2) (henergy : e ≤ q) :
    (1 / Real.sqrt 2) * Real.sqrt q ≤ m :=
  sharp_sqrt_bound hq hm (quadratic_bound_of_variance_energy hvariance henergy)


theorem gradient_boolSign_not (b : Bool) :
    (if !b then (1 : ℝ) else -1) = -(if b then (1 : ℝ) else -1) := by
  cases b <;> norm_num

theorem gradient_boolSign_sq (b : Bool) :
    (if b then (1 : ℝ) else -1) ^ 2 = 1 := by
  cases b <;> norm_num

/-- Flipping one coordinate changes exactly its own signed summand. -/
theorem signedSum_sub_flip {N : ℕ} (x : Fin N → ℝ) (i : Fin N) (ω : Cube N) :
    signedSum x ω - signedSum x (flip i ω) =
      2 * (if ω i then (1 : ℝ) else -1) * x i := by
  have hsign : (if flip i ω i then (1 : ℝ) else -1) =
      -(if ω i then (1 : ℝ) else -1) := by
    simp only [flip, Function.update_self, gradient_boolSign_not]
  unfold signedSum
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ j : Fin N,
      ((if ω j then (1 : ℝ) else -1) * x j -
        (if flip i ω j then (1 : ℝ) else -1) * x j)) =
        (if ω i then (1 : ℝ) else -1) * x i -
          (if flip i ω i then (1 : ℝ) else -1) * x i := by
      apply Finset.sum_eq_single i
      · intro j _hj hji
        simp only [flip, Function.update_of_ne hji, sub_self]
      · simp
    _ = 2 * (if ω i then (1 : ℝ) else -1) * x i := by
      rw [hsign]
      ring

theorem gradient_signedSum_negate {N : ℕ} (x : Fin N → ℝ) (ω : Cube N) :
    signedSum x (negate ω) = -signedSum x ω := by
  unfold signedSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [negate]
  by_cases hi : ω i = true
  · simp [hi]
  · have hfalse : ω i = false := Bool.eq_false_iff.mpr hi
    simp [hfalse]

theorem abs_signedSum_negate {N : ℕ} (x : Fin N → ℝ) (ω : Cube N) :
    |signedSum x (negate ω)| = |signedSum x ω| := by
  rw [gradient_signedSum_negate, abs_neg]

/-- The squared reverse-triangle estimate, in the normalization of energy. -/
theorem gradient_abs_sub_sq_le (a b : ℝ) :
    ((|a| - |b|) / 2) ^ 2 ≤ ((a - b) / 2) ^ 2 := by
  have hprod : a * b ≤ |a| * |b| := by
    simpa only [abs_mul] using le_abs_self (a * b)
  nlinarith [sq_abs a, sq_abs b]

theorem signedSum_flip_gradient_sq {N : ℕ} (x : Fin N → ℝ)
    (i : Fin N) (ω : Cube N) :
    ((signedSum x ω - signedSum x (flip i ω)) / 2) ^ 2 = (x i) ^ 2 := by
  calc
    ((signedSum x ω - signedSum x (flip i ω)) / 2) ^ 2 =
        (if ω i then (1 : ℝ) else -1) ^ 2 * (x i) ^ 2 := by
      rw [signedSum_sub_flip]
      ring
    _ = (x i) ^ 2 := by rw [gradient_boolSign_sq, one_mul]

theorem abs_signedSum_flip_sq_le {N : ℕ} (x : Fin N → ℝ)
    (i : Fin N) (ω : Cube N) :
    ((|signedSum x ω| - |signedSum x (flip i ω)|) / 2) ^ 2 ≤ (x i) ^ 2 := by
  exact (gradient_abs_sub_sq_le (signedSum x ω) (signedSum x (flip i ω))).trans_eq
    (signedSum_flip_gradient_sq x i ω)

/-- Uniquely named local averaging helper, avoiding the shared avg API. -/
theorem gradient_avg_mono {N : ℕ} (f g : Cube N → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω) : avg N f ≤ avg N g := by
  unfold avg
  have hsum : (∑ ω : Cube N, f ω) ≤ ∑ ω : Cube N, g ω :=
    Finset.sum_le_sum (fun ω _hω => hfg ω)
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem gradient_avg_const (N : ℕ) (c : ℝ) : avg N (fun _ => c) = c := by
  unfold avg
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (Cube N) : ℝ) = (2 : ℝ) ^ N := by
    simp [Cube]
  have hpow : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
  rw [hcard, ← mul_assoc, inv_mul_cancel₀ hpow, one_mul]

/-- The absolute signed sum has energy at most the coefficient square sum. -/
theorem energy_abs_signedSum_le {N : ℕ} (x : Fin N → ℝ) :
    energy (fun ω => |signedSum x ω|) ≤ ∑ i : Fin N, (x i) ^ 2 := by
  unfold energy
  apply Finset.sum_le_sum
  intro i _hi
  exact (gradient_avg_mono
      (fun ω => ((|signedSum x ω| - |signedSum x (flip i ω)|) / 2) ^ 2)
      (fun _ => (x i) ^ 2) (abs_signedSum_flip_sq_le x i)).trans_eq
    (gradient_avg_const N ((x i) ^ 2))


/-- Exact sharp reduction, with each outstanding cube estimate an explicit premise. -/
theorem sharp_cube_bound_of_moment_poincare_energy {N : ℕ} (x : Fin N → ℝ)
    (hmoment : avg N (fun ω => (signedSum x ω) ^ 2) = ∑ i : Fin N, x i ^ 2)
    (hpoincare : avg N (fun ω => |signedSum x ω| ^ 2) -
      (avg N (fun ω => |signedSum x ω|)) ^ 2 ≤
        energy (fun ω => |signedSum x ω|) / 2)
    (henergy : energy (fun ω => |signedSum x ω|) ≤ ∑ i : Fin N, x i ^ 2) :
    (1 / Real.sqrt 2) * Real.sqrt (∑ i : Fin N, x i ^ 2) ≤
      ((2 : ℝ) ^ N)⁻¹ *
        ∑ ω : Fin N → Bool,
          |∑ i : Fin N, (if ω i then (1 : ℝ) else -1) * x i| := by
  have hvariance : (∑ i : Fin N, x i ^ 2) -
      (avg N (fun ω => |signedSum x ω|)) ^ 2 ≤
        energy (fun ω => |signedSum x ω|) / 2 := by
    simpa only [avg_abs_sq_eq, hmoment] using hpoincare
  exact sharp_sqrt_bound_of_variance_energy
    (sum_sq_nonneg N x) (mean_abs_nonneg x) hvariance henergy


/-- Once the general spectral gap and the signed-sum moment are proved, assembly is exact. -/
theorem sharp_bound_from_even_poincare {N : ℕ} (x : Fin N → ℝ)
    (hmoment : avg N (fun ω => (signedSum x ω) ^ 2) = ∑ i : Fin N, x i ^ 2)
    (hpoincare : ∀ (f : Cube N → ℝ), (∀ ω, f (negate ω) = f ω) →
      avg N (fun ω => f ω ^ 2) - (avg N f) ^ 2 ≤ energy f / 2) :
    (1 / Real.sqrt 2) * Real.sqrt (∑ i : Fin N, x i ^ 2) ≤
      ((2 : ℝ) ^ N)⁻¹ *
        ∑ ω : Fin N → Bool,
          |∑ i : Fin N, (if ω i then (1 : ℝ) else -1) * x i| := by
  exact sharp_cube_bound_of_moment_poincare_energy x hmoment
    (hpoincare (fun ω => |signedSum x ω|) (abs_signedSum_negate x))
    (energy_abs_signedSum_le x)

end BacklogCuratorKhintchine

namespace ModernOnlineLearning.LowerBounds

/-- The lower-bound, real-coefficient `p = 1` case of Theorem A.14,
printed p. 296. Uniform `Bool` vectors are independent Rademacher signs. -/
theorem theorem_A_14_p1 {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    (1 / Real.sqrt 2) * Real.sqrt (∑ i : Fin N, (x i) ^ 2) ≤
      ((2 : ℝ) ^ N)⁻¹ *
        ∑ ω : Fin N → Bool,
          |∑ i : Fin N, (if ω i then (1 : ℝ) else -1) * x i| := by
  cases N with
  | zero => omega
  | succ _ =>
      exact BacklogCuratorKhintchine.sharp_bound_from_even_poincare x
        (BacklogCuratorKhintchine.avg_signedSum_sq x)
        (fun f heven => BacklogCuratorKhintchine.even_poincare f heven)

end ModernOnlineLearning.LowerBounds

end Prove2SwarmSubmission

theorem solution {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    (1 / Real.sqrt 2) * Real.sqrt (∑ i : Fin N, (x i) ^ 2) ≤
      ((2 : ℝ) ^ N)⁻¹ *
        ∑ ω : Fin N → Bool,
          |∑ i : Fin N, (if ω i then (1 : ℝ) else -1) * x i| := by
  exact Prove2SwarmSubmission.ModernOnlineLearning.LowerBounds.theorem_A_14_p1 hN x
