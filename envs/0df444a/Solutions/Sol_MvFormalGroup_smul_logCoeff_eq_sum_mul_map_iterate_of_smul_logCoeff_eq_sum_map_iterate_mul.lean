-- Prove2me | solution 1 for MvFormalGroup.smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5704886f-e0b5-5290-8c68-a66661503227

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul

set_option autoImplicit false

universe u

open Finset Finset.Nat

namespace B23U4

theorem sum_antidiagonal_assoc {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → ℕ → ℕ → M) :
    ∑ x ∈ antidiagonal n, ∑ y ∈ antidiagonal x.2, F x.1 y.1 y.2 =
      ∑ x ∈ antidiagonal n, ∑ y ∈ antidiagonal x.1, F y.1 y.2 x.2 := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun z => ⟨(z.1.1 + z.2.1, z.2.2), (z.1.1, z.2.1)⟩)
    (fun z => ⟨(z.2.1, z.2.2 + z.1.2), (z.2.2, z.1.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨m, r⟩, ⟨i, j⟩⟩ h
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨by omega, by simp⟩
  · rintro ⟨⟨s, j⟩, ⟨m, i⟩⟩ h
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨by omega, by simp⟩
  · rintro ⟨⟨m, r⟩, ⟨i, j⟩⟩ h
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h
    ext <;> simp <;> omega
  · rintro ⟨⟨s, j⟩, ⟨m, i⟩⟩ h
    simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h
    ext <;> simp <;> omega
  · rintro ⟨⟨m, r⟩, ⟨i, j⟩⟩ h
    rfl

theorem lastPeel {R : Type*} [CommRing R] {d : ℕ} (τ : R →+* R) (c : R)
    (hc : ∀ M N : Matrix (Fin d) (Fin d) R, c • M = c • N → M = N) (hτc : τ c = c)
    (Xm a : ℕ → Matrix (Fin d) (Fin d) R) (h1 : a 0 = 1)
    (h2 : ∀ k, c • a (k + 1) =
      ∑ x ∈ antidiagonal k, Xm x.1 * (a x.2).map ⇑(τ ^ (x.1 + 1))) :
    ∀ n, c • a (n + 1) = ∑ x ∈ antidiagonal n, a x.1 * (Xm x.2).map ⇑(τ ^ x.1) := by

  have hτkc : ∀ k, (τ ^ k) c = c := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, RingHom.coe_mul, Function.comp_apply, hτc, ih]
  have hms : ∀ (k : ℕ) (M : Matrix (Fin d) (Fin d) R),
      (c • M).map ⇑(τ ^ k) = c • M.map ⇑(τ ^ k) := by
    intro k M; ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      smul_eq_mul, map_mul, hτkc]
  have hmap_mul : ∀ (k : ℕ) (M N : Matrix (Fin d) (Fin d) R),
      (M * N).map ⇑(τ ^ k) = M.map ⇑(τ ^ k) * N.map ⇑(τ ^ k) := fun k M N => Matrix.map_mul
  have hmap_map : ∀ (k l : ℕ) (M : Matrix (Fin d) (Fin d) R),
      (M.map ⇑(τ ^ k)).map ⇑(τ ^ l) = M.map ⇑(τ ^ (l + k)) := by
    intro k l M; rw [Matrix.map_map, pow_add, RingHom.coe_mul]
  have hmap_sum : ∀ (k : ℕ) (s : Finset (ℕ × ℕ)) (G : ℕ × ℕ → Matrix (Fin d) (Fin d) R),
      (∑ y ∈ s, G y).map ⇑(τ ^ k) = ∑ y ∈ s, (G y).map ⇑(τ ^ k) := by
    intro k s G
    show (τ ^ k).mapMatrix (∑ y ∈ s, G y) = ∑ y ∈ s, (τ ^ k).mapMatrix (G y)
    exact map_sum _ _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [h2 0]
      simp [h1, Matrix.map_one]
    | succ n =>
      apply hc
      have eL : c • (c • a (n + 1 + 1)) = c • Xm (n + 1) +
          ∑ x ∈ antidiagonal n, ∑ y ∈ antidiagonal x.2,
            Xm x.1 * ((a y.1).map ⇑(τ ^ (x.1 + 1)) * (Xm y.2).map ⇑(τ ^ (x.1 + 1 + y.1))) := by
        rw [h2 (n + 1), Finset.smul_sum, sum_antidiagonal_succ']
        dsimp only
        congr 1
        · rw [h1, Matrix.map_one _ (map_zero _) (map_one _), mul_one]
        · refine Finset.sum_congr rfl fun x hx => ?_
          have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
          rw [← Matrix.mul_smul, ← hms, ih x.2 (by omega), hmap_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hmap_mul, hmap_map]
      have eR : c • ∑ x ∈ antidiagonal (n + 1), a x.1 * (Xm x.2).map ⇑(τ ^ x.1) =
          c • Xm (n + 1) +
          ∑ x ∈ antidiagonal n, ∑ y ∈ antidiagonal x.1,
            Xm y.1 * ((a y.2).map ⇑(τ ^ (y.1 + 1)) * (Xm x.2).map ⇑(τ ^ (y.1 + 1 + y.2))) := by
        rw [Finset.smul_sum, sum_antidiagonal_succ]
        dsimp only
        congr 1
        · rw [h1, one_mul, pow_zero, RingHom.coe_one, Matrix.map_id]
        · refine Finset.sum_congr rfl fun x _ => ?_
          rw [← smul_mul_assoc, h2 x.1, Finset.sum_mul]
          refine Finset.sum_congr rfl fun y hy => ?_
          have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
          rw [mul_assoc, show x.1 + 1 = y.1 + 1 + y.2 by omega]
      have key := sum_antidiagonal_assoc n
        (fun m i j => Xm m * ((a i).map ⇑(τ ^ (m + 1)) * (Xm j).map ⇑(τ ^ (m + 1 + i))))
      rw [eL, eR, key]

end B23U4

theorem solution
    (p : ℕ) [Fact p.Prime] (d : ℕ)
    (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (h1 : a 0 = 1)
    (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
    (n : ℕ) :
    (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (n + 1)
      = ∑ m ∈ Finset.range (n + 1),
          a (n - m) * (Matrix.of fun i j => (MvPolynomial.X (m, i, j) :
            MvPolynomial (ℕ × Fin d × Fin d) (Padic p))).map
              (⇑(MvPolynomial.aeval fun v =>
                (MvPolynomial.X v : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ p))^[n - m] := by
  have hp : p.Prime := Fact.out
  let σ : MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p]
      MvPolynomial (ℕ × Fin d × Fin d) (Padic p) :=
    MvPolynomial.aeval fun v => MvPolynomial.X v ^ p
  let τ : MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →+*
      MvPolynomial (ℕ × Fin d × Fin d) (Padic p) := σ.toRingHom
  have hτ : ∀ k, ((⇑(MvPolynomial.aeval fun v =>
      (MvPolynomial.X v : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ p))^[k] :
        MvPolynomial (ℕ × Fin d × Fin d) (Padic p) → MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
      = ⇑(τ ^ k) := fun k => by
    rw [RingHom.coe_pow]; rfl
  have hτc : τ (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = p := map_natCast τ p
  have hu : IsUnit (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) := by
    have h0 : IsUnit (p : Padic p) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
    have := h0.map (algebraMap (Padic p) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    rwa [map_natCast] at this
  have hc : ∀ M N : Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • M =
        (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • N → M = N :=
    fun M N h => (IsUnit.smul_left_cancel hu).mp h
  set Xm : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) :=
    fun m => Matrix.of fun i j => (MvPolynomial.X (m, i, j) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
    with hXm
  have h2' : ∀ k, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1) =
      ∑ x ∈ antidiagonal k, Xm x.1 * (a x.2).map ⇑(τ ^ (x.1 + 1)) := by
    intro k
    rw [h2 k, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun m r => Xm m * (a r).map ⇑(τ ^ (m + 1))) k]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hτ]
  have key := B23U4.lastPeel τ (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) hc hτc Xm a h1 h2' n
  rw [key, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun m r => a r * (Xm m).map ⇑(τ ^ r)) n]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← hτ, hXm]

end S_MvFormalGroup_smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul
end P2MW
export P2MW.S_MvFormalGroup_smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul (solution)
