-- Prove2me | solution 1 for Module.End.eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/34ab4dfc-257a-529f-b044-1925b3d82186

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul

set_option autoImplicit false

namespace P2mKcSerreRigidity

open Module Polynomial

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

def PCong (p : ℕ) (D : Module.End R M) (k : ℕ) : Prop :=
  ∀ x : M, ∃ y : M, D x = p ^ k • y

namespace PCong

variable {p : ℕ}

theorem zero_right (D : Module.End R M) : PCong p D 0 :=
  fun x => ⟨D x, by rw [pow_zero, one_smul]⟩

theorem zero_left (k : ℕ) : PCong p (0 : Module.End R M) k :=
  fun _ => ⟨0, by rw [LinearMap.zero_apply, smul_zero]⟩

theorem mono {D : Module.End R M} {k j : ℕ} (h : PCong p D k) (hjk : j ≤ k) : PCong p D j := by
  intro x
  obtain ⟨y, hy⟩ := h x
  refine ⟨p ^ (k - j) • y, ?_⟩
  rw [hy, ← mul_smul, ← pow_add, Nat.add_sub_cancel' hjk]

theorem add {D D' : Module.End R M} {k : ℕ} (h : PCong p D k) (h' : PCong p D' k) :
    PCong p (D + D') k := by
  intro x
  obtain ⟨y, hy⟩ := h x
  obtain ⟨y', hy'⟩ := h' x
  exact ⟨y + y', by rw [LinearMap.add_apply, hy, hy', smul_add]⟩

theorem neg {D : Module.End R M} {k : ℕ} (h : PCong p D k) : PCong p (-D) k := by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨-y, by rw [LinearMap.neg_apply, hy, smul_neg]⟩

theorem mul_left {D : Module.End R M} {k : ℕ} (h : PCong p D k) (D' : Module.End R M) :
    PCong p (D' * D) k := by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨D' y, by rw [Module.End.mul_apply, hy, map_nsmul]⟩

theorem mul_right {D : Module.End R M} {k : ℕ} (h : PCong p D k) (D' : Module.End R M) :
    PCong p (D * D') k := by
  intro x
  obtain ⟨y, hy⟩ := h (D' x)
  exact ⟨y, by rw [Module.End.mul_apply, hy]⟩

theorem natCast_mul (X : Module.End R M) (j : ℕ) :
    PCong p (((p ^ j : ℕ) : Module.End R M) * X) j :=
  fun x => ⟨X x, by rw [Module.End.mul_apply, Module.End.natCast_apply]⟩

end PCong

theorem smul_pow_cancel {p : ℕ} (htf : ∀ x : M, p • x = 0 → x = 0) :
    ∀ (j : ℕ) {x y : M}, p ^ j • x = p ^ j • y → x = y := by
  intro j
  induction j with
  | zero => intro x y h; simpa using h
  | succ j ih =>
      intro x y h
      apply ih
      have h' : p • (p ^ j • x - p ^ j • y) = 0 := by
        rw [smul_sub, ← mul_smul, ← mul_smul, ← pow_succ', h, sub_self]
      exact sub_eq_zero.mp (htf _ h')

theorem natCast_mul_cancel {p : ℕ} (htf : ∀ x : M, p • x = 0 → x = 0) (j : ℕ)
    {F G : Module.End R M}
    (h : ((p ^ j : ℕ) : Module.End R M) * F = ((p ^ j : ℕ) : Module.End R M) * G) : F = G := by
  ext x
  have := congrArg (fun T : Module.End R M => T x) h
  simp only [Module.End.mul_apply, Module.End.natCast_apply] at this
  exact smul_pow_cancel htf j this

theorem PCong.exists_eq_natCast_mul {p : ℕ} (htf : ∀ x : M, p • x = 0 → x = 0)
    {D : Module.End R M} {k : ℕ} (h : PCong p D k) :
    ∃ W : Module.End R M, D = ((p ^ k : ℕ) : Module.End R M) * W := by
  classical
  choose w hw using h
  refine ⟨{ toFun := w, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply smul_pow_cancel htf k
    rw [← hw, map_add, hw, hw, smul_add]
  · intro r x
    apply smul_pow_cancel htf k
    rw [← hw, map_smul, hw, RingHom.id_apply, smul_comm]
  · ext x
    rw [Module.End.mul_apply, Module.End.natCast_apply]
    exact hw x

theorem PCong.of_natCast_mul_succ {p : ℕ} (htf : ∀ x : M, p • x = 0 → x = 0)
    {W : Module.End R M} {b : ℕ}
    (h : PCong p (((p ^ b : ℕ) : Module.End R M) * W) (b + 1)) : PCong p W 1 := by
  intro x
  obtain ⟨y, hy⟩ := h x
  refine ⟨y, smul_pow_cancel htf b ?_⟩
  rw [Module.End.mul_apply, Module.End.natCast_apply] at hy
  rw [hy, ← mul_smul, ← pow_add]

theorem exists_one_add_X_pow (n : ℕ) :
    ∃ Q : ℤ[X], ((1 : ℤ[X]) + X) ^ n = 1 + (n : ℤ[X]) * X + (n.choose 2 : ℤ[X]) * X ^ 2 + X ^ 3 * Q := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨Q, hQ⟩ := ih
      refine ⟨(n.choose 2 : ℤ[X]) + Q + Q * X, ?_⟩
      have hc : ((n + 1).choose 2 : ℤ[X]) = (n : ℤ[X]) + (n.choose 2 : ℤ[X]) := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
      rw [pow_succ, hQ, hc]
      push_cast
      ring

theorem exists_one_add_pow {E : Type*} [Ring E] (D : E) (n : ℕ) :
    ∃ Q : E, (1 + D) ^ n = 1 + (n : E) * D + (n.choose 2 : E) * D ^ 2 + D ^ 3 * Q := by
  obtain ⟨Q, hQ⟩ := exists_one_add_X_pow n
  refine ⟨Polynomial.aeval D Q, ?_⟩
  have := congrArg (Polynomial.aeval D) hQ
  simpa only [map_pow, map_add, map_one, Polynomial.aeval_X, map_mul, map_natCast] using this

theorem eq_one_of_prime_pow_eq_one {p : ℕ} (hp : p.Prime)
    (htf : ∀ x : M, p • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ n : ℕ, ∃ y : M, x = p ^ n • y) → x = 0)
    {a : ℕ} (ha : 1 ≤ a) (ha2 : p = 2 → 2 ≤ a)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (w : Module.End R M) (hw : w ^ ℓ = 1)
    (hwa : PCong p (w - 1) a) : w = 1 := by
  classical
  by_contra hne
  set D : Module.End R M := w - 1 with hDdef
  have hD : D ≠ 0 := sub_ne_zero.mpr hne

  have hb : ∃ b, a ≤ b ∧ PCong p D b ∧ ¬ PCong p D (b + 1) := by
    by_contra hall
    push Not at hall
    have hall' : ∀ k, PCong p D (a + k) := by
      intro k
      induction k with
      | zero => simpa using hwa
      | succ k ih => exact hall (a + k) (Nat.le_add_right a k) ih
    apply hD
    ext x
    rw [LinearMap.zero_apply]
    apply hsep
    intro n
    obtain ⟨y, hy⟩ := (hall' n).mono (Nat.le_add_left n a) x
    exact ⟨y, hy⟩
  obtain ⟨b, hab, hb, hb1⟩ := hb
  have hb1' : 1 ≤ b := le_trans ha hab
  obtain ⟨W, hW⟩ := hb.exists_eq_natCast_mul htf
  have hW1 : ¬ PCong p W 1 := fun h => hb1 (by
    rw [hW]

    intro x
    obtain ⟨y, hy⟩ := h x
    refine ⟨y, ?_⟩
    rw [Module.End.mul_apply, Module.End.natCast_apply, hy, ← mul_smul, pow_one, ← pow_succ])

  obtain ⟨Q, hQ⟩ := exists_one_add_pow D ℓ
  have h1D : (1 : Module.End R M) + D = w := by rw [hDdef]; abel
  rw [h1D, hw] at hQ
  have hE1 : (ℓ : Module.End R M) * D + (ℓ.choose 2 : Module.End R M) * D ^ 2 + D ^ 3 * Q = 0 := by
    have : (1 : Module.End R M) + ((ℓ : Module.End R M) * D + (ℓ.choose 2 : Module.End R M) * D ^ 2
        + D ^ 3 * Q) = 1 + 0 := by
      rw [add_zero, ← add_assoc, ← add_assoc]; exact hQ.symm
    exact add_left_cancel this

  set q : Module.End R M := ((p ^ b : ℕ) : Module.End R M) with hqdef
  have hqc : ∀ T : Module.End R M, q * T = T * q := fun T => Nat.cast_comm _ _
  have hE1' : (ℓ : Module.End R M) * D + (ℓ.choose 2 : Module.End R M) * D ^ 2 + D ^ 3 * Q =
      q * ((ℓ : Module.End R M) * W + q * ((ℓ.choose 2 : Module.End R M) * (W * W))
        + q * q * (W * W * W * Q)) := by
    rw [hW]
    have e1 : (ℓ : Module.End R M) * (q * W) = q * ((ℓ : Module.End R M) * W) := by
      rw [← mul_assoc, ← hqc, mul_assoc]
    have e2 : (ℓ.choose 2 : Module.End R M) * (q * W) ^ 2 =
        q * (q * ((ℓ.choose 2 : Module.End R M) * (W * W))) := by
      rw [pow_two]

      calc (ℓ.choose 2 : Module.End R M) * (q * W * (q * W))
          = ((ℓ.choose 2 : Module.End R M) * q) * (W * q) * W := by noncomm_ring
        _ = (q * (ℓ.choose 2 : Module.End R M)) * (q * W) * W := by rw [hqc, ← hqc W]
        _ = q * (q * ((ℓ.choose 2 : Module.End R M) * (W * W))) := by
            rw [show (q * (ℓ.choose 2 : Module.End R M)) * (q * W) * W
                = q * (((ℓ.choose 2 : Module.End R M) * q) * (W * W)) by noncomm_ring, ← hqc]
            noncomm_ring
    have e3 : (q * W) ^ 3 * Q = q * (q * q * (W * W * W * Q)) := by
      calc (q * W) ^ 3 * Q = q * (W * q) * (W * q) * W * Q := by noncomm_ring
        _ = q * (q * W) * (q * W) * W * Q := by rw [← hqc W]
        _ = q * (q * (W * q) * W * W * Q) := by noncomm_ring
        _ = q * (q * (q * W) * W * W * Q) := by rw [← hqc W]
        _ = q * (q * q * (W * W * W * Q)) := by noncomm_ring
    rw [e1, e2, e3, ← mul_add, ← mul_add]
  have hE2 : (ℓ : Module.End R M) * W + q * ((ℓ.choose 2 : Module.End R M) * (W * W))
      + q * q * (W * W * W * Q) = 0 := by
    apply natCast_mul_cancel htf b
    rw [← hqdef, mul_zero, ← hE1', hE1]

  have hqq : q * q = ((p ^ (2 * b) : ℕ) : Module.End R M) := by
    rw [hqdef, ← Nat.cast_mul, ← pow_add, two_mul]
  rw [hqq] at hE2
  rcases eq_or_ne ℓ p with hℓp | hℓp
  ·
    subst hℓp

    have hZ : ∃ Z : Module.End R M,
        q * ((ℓ.choose 2 : Module.End R M) * (W * W))
          + ((ℓ ^ (2 * b) : ℕ) : Module.End R M) * (W * W * W * Q)
        = ((ℓ ^ 2 : ℕ) : Module.End R M) * Z := by
      rcases eq_or_ne ℓ 2 with hℓ2 | hℓ2
      ·
        have hb2 : 2 ≤ b := le_trans (ha2 hℓ2) hab
        refine ⟨((ℓ ^ (b - 2) : ℕ) : Module.End R M) * ((ℓ.choose 2 : Module.End R M) * (W * W))
          + ((ℓ ^ (2 * b - 2) : ℕ) : Module.End R M) * (W * W * W * Q), ?_⟩
        rw [mul_add]
        congr 1
        · conv_rhs => rw [← mul_assoc, ← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hb2]
        · conv_rhs => rw [← mul_assoc, ← Nat.cast_mul, ← pow_add,
            Nat.add_sub_cancel' (by omega : 2 ≤ 2 * b)]
      ·
        have hlt : 2 < ℓ := lt_of_le_of_ne hℓ.two_le hℓ2.symm
        obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self hℓ two_ne_zero hlt
        refine ⟨((ℓ ^ (b - 1) * c : ℕ) : Module.End R M) * (W * W)
          + ((ℓ ^ (2 * b - 2) : ℕ) : Module.End R M) * (W * W * W * Q), ?_⟩
        rw [mul_add]
        congr 1
        · conv_lhs => rw [hqdef, hc, ← mul_assoc, ← Nat.cast_mul]
          conv_rhs => rw [← mul_assoc, ← Nat.cast_mul]
          congr 2
          have eb : ℓ ^ b = ℓ ^ (b - 1) * ℓ := by rw [← pow_succ, Nat.sub_add_cancel hb1']
          rw [eb]
          ring
        · conv_rhs => rw [← mul_assoc, ← Nat.cast_mul, ← pow_add,
            Nat.add_sub_cancel' (by omega : 2 ≤ 2 * b)]
    obtain ⟨Z, hZ⟩ := hZ
    have h3 : ((ℓ ^ 1 : ℕ) : Module.End R M) * (W + (ℓ : Module.End R M) * Z) =
        ((ℓ ^ 1 : ℕ) : Module.End R M) * 0 := by
      rw [mul_zero, pow_one, mul_add, ← mul_assoc, ← Nat.cast_mul, ← pow_two, ← hZ, ← add_assoc]
      exact hE2
    have h4 : W + (ℓ : Module.End R M) * Z = 0 := natCast_mul_cancel htf 1 h3
    apply hW1
    intro x
    refine ⟨-(Z x), ?_⟩
    have : W = -((ℓ : Module.End R M) * Z) := eq_neg_of_add_eq_zero_left h4
    rw [this, LinearMap.neg_apply, Module.End.mul_apply, Module.End.natCast_apply, pow_one, smul_neg]
  ·
    have hcop : IsCoprime (ℓ : ℤ) (p : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hℓ hp).mpr hℓp)
    have hℓW : PCong p ((ℓ : Module.End R M) * W) 1 := by
      have : (ℓ : Module.End R M) * W =
          -(q * ((ℓ.choose 2 : Module.End R M) * (W * W))
            + ((p ^ (2 * b) : ℕ) : Module.End R M) * (W * W * W * Q)) := by
        apply eq_neg_of_add_eq_zero_left
        rw [← add_assoc]; exact hE2
      rw [this]
      refine PCong.neg (PCong.add ?_ ?_)
      · exact (PCong.natCast_mul _ b).mono hb1'
      · exact (PCong.natCast_mul _ (2 * b)).mono (by omega)
    apply hW1
    intro x
    obtain ⟨y, hy⟩ := hℓW x
    rw [Module.End.mul_apply, Module.End.natCast_apply, pow_one] at hy
    obtain ⟨s, t, hst⟩ := hcop
    refine ⟨s • y + t • W x, ?_⟩
    calc W x = (1 : ℤ) • W x := (one_smul ℤ _).symm
      _ = (s * ℓ + t * p : ℤ) • W x := by rw [hst]
      _ = s • ((ℓ : ℤ) • W x) + t • ((p : ℤ) • W x) := by rw [add_smul, mul_smul, mul_smul]
      _ = s • (ℓ • W x) + t • (p • W x) := by rw [natCast_zsmul, natCast_zsmul]
      _ = p ^ 1 • (s • y + t • W x) := by rw [hy, pow_one, smul_add, smul_comm p s, smul_comm p t]

theorem eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul
    {p : ℕ} (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) (ha2 : p = 2 → 2 ≤ a)
    (htf : ∀ x : M, p • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ n : ℕ, ∃ y : M, x = p ^ n • y) → x = 0)
    (u : M →ₗ[R] M) (m : ℕ) (hm : m ≠ 0) (hu : u ^ m = 1)
    (hcong : ∀ x : M, ∃ y : M, u x - x = p ^ a • y) :
    u = 1 := by
  classical
  have hua : PCong p (u - 1) a := fun x => by
    obtain ⟨y, hy⟩ := hcong x
    exact ⟨y, by rw [LinearMap.sub_apply, Module.End.one_apply, hy]⟩

  have hex : ∃ n, 0 < n ∧ u ^ n = 1 := ⟨m, Nat.pos_of_ne_zero hm, hu⟩
  set n₀ := Nat.find hex with hn₀def
  obtain ⟨hn₀pos, hn₀⟩ : 0 < n₀ ∧ u ^ n₀ = 1 := Nat.find_spec hex
  by_contra hne
  have hn1 : n₀ ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hn₀
    exact hne hn₀
  obtain ⟨ℓ, hℓ, c, hc⟩ := Nat.exists_prime_and_dvd hn1
  have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hc; omega)
  have hclt : c < n₀ := by
    rw [hc]
    exact lt_mul_left hcpos hℓ.one_lt

  have hvℓ : (u ^ c) ^ ℓ = 1 := by rw [← pow_mul, mul_comm, ← hc]; exact hn₀
  have hva : PCong p (u ^ c - 1) a := by
    rw [← geom_sum_mul u c]
    exact hua.mul_left _
  have hv : u ^ c = 1 := eq_one_of_prime_pow_eq_one hp htf hsep ha ha2 hℓ (u ^ c) hvℓ hva
  exact Nat.find_min hex hclt ⟨hcpos, hv⟩

end P2mKcSerreRigidity

theorem solution
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {p : ℕ} (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) (ha2 : p = 2 → 2 ≤ a)
    (htf : ∀ x : M, p • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ n : ℕ, ∃ y : M, x = p ^ n • y) → x = 0)
    (u : M →ₗ[R] M) (m : ℕ) (hm : m ≠ 0) (hu : u ^ m = 1)
    (hcong : ∀ x : M, ∃ y : M, u x - x = p ^ a • y) :
    u = 1 :=
  P2mKcSerreRigidity.eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul hp a ha ha2 htf hsep
    u m hm hu hcong

end S_Module_End_eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul
end P2MW
export P2MW.S_Module_End_eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul (solution)
