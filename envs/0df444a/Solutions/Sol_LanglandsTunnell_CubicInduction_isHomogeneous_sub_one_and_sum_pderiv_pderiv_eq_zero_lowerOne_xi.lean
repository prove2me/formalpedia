-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e0075d56-1d2a-53f8-8207-4d497d24ce3c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi

set_option autoImplicit false

namespace WsC
namespace L1H

open MvPolynomial

noncomputable section

abbrev R3 := MvPolynomial (Fin 3) ℂ

theorem pderiv_comm (i j : Fin 3) (p : R3) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have h : ⁅(pderiv i : Derivation ℂ R3 R3), (pderiv j : Derivation ℂ R3 R3)⁆ = 0 := by
    refine MvPolynomial.derivation_ext (fun k => ?_)
    rw [Derivation.commutator_apply]
    classical
    simp only [pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℂ R3 R3 => D p) h
  simp only [Derivation.commutator_apply] at h2
  have h3 : pderiv i (pderiv j p) - pderiv j (pderiv i p) = 0 := by simpa using h2
  exact sub_eq_zero.mp h3

theorem sort10 (q : R3) : pderiv 0 (pderiv 1 q) = pderiv 1 (pderiv 0 q) := pderiv_comm 0 1 q
theorem sort20 (q : R3) : pderiv 0 (pderiv 2 q) = pderiv 2 (pderiv 0 q) := pderiv_comm 0 2 q
theorem sort21 (q : R3) : pderiv 1 (pderiv 2 q) = pderiv 2 (pderiv 1 q) := pderiv_comm 1 2 q

theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
theorem ne10 : (1 : Fin 3) ≠ 0 := by decide
theorem ne02 : (0 : Fin 3) ≠ 2 := by decide
theorem ne20 : (2 : Fin 3) ≠ 0 := by decide
theorem ne12 : (1 : Fin 3) ≠ 2 := by decide
theorem ne21 : (2 : Fin 3) ≠ 1 := by decide

def Lap (q : R3) : R3 := ∑ i : Fin 3, pderiv i (pderiv i q)

theorem Lap_eq (q : R3) :
    Lap q = pderiv 0 (pderiv 0 q) + pderiv 1 (pderiv 1 q) + pderiv 2 (pderiv 2 q) := by
  simp [Lap, Fin.sum_univ_three]

theorem Lap_add (q r : R3) : Lap (q + r) = Lap q + Lap r := by
  simp only [Lap_eq, map_add]; ring

theorem Lap_sub (q r : R3) : Lap (q - r) = Lap q - Lap r := by
  simp only [Lap_eq, map_sub]; ring

theorem Lap_neg (q : R3) : Lap (-q) = -Lap q := by
  simp only [Lap_eq, map_neg]; ring

theorem Lap_zero : Lap 0 = 0 := by
  simp [Lap_eq]

theorem Lap_C_mul (k : ℂ) (q : R3) : Lap (C k * q) = C k * Lap q := by
  simp only [Lap_eq, pderiv_mul, pderiv_C, zero_mul, zero_add]; ring

theorem Lap_sum {ι : Type} (s : Finset ι) (f : ι → R3) :
    Lap (∑ i ∈ s, f i) = ∑ i ∈ s, Lap (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Lap_add, ih]

theorem Lap_pderiv (j : Fin 3) (q : R3) : Lap (pderiv j q) = pderiv j (Lap q) := by
  simp only [Lap_eq, map_add]
  rw [pderiv_comm 0 j, pderiv_comm 0 j, pderiv_comm 1 j, pderiv_comm 1 j, pderiv_comm 2 j,
    pderiv_comm 2 j]

theorem Lap_X_mul (c : Fin 3) (q : R3) : Lap (X c * q) = X c * Lap q + C 2 * pderiv c q := by
  have hc : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
  rcases hc with rfl | rfl | rfl <;>
  · simp only [Lap_eq, pderiv_mul, pderiv_X_self, pderiv_X_of_ne ne01, pderiv_X_of_ne ne10,
      pderiv_X_of_ne ne02, pderiv_X_of_ne ne20, pderiv_X_of_ne ne12, pderiv_X_of_ne ne21,
      map_add, map_zero, Derivation.map_one_eq_zero, pderiv_one, zero_mul, one_mul, zero_add,
      add_zero, map_ofNat]
    ring

theorem Lap_rot (i j : Fin 3) (p : R3) (hp : Lap p = 0) :
    Lap (X i * pderiv j p - X j * pderiv i p) = 0 := by
  rw [Lap_sub, Lap_X_mul, Lap_X_mul, Lap_pderiv, Lap_pderiv, hp, map_zero, map_zero, mul_zero,
    mul_zero, zero_add, zero_add, pderiv_comm i j, sub_self]

def Xi (ν : Fin 3 → ℂ) (p : R3) : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
  Matrix.of fun c d =>
    if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
    else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
      MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)

def eps (a c d : Fin 3) : ℂ :=
  (((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
    (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2

theorem eps_swap (a c d : Fin 3) : eps a d c = -eps a c d := by
  unfold eps; ring

def lower1 (M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ)) : MvPolynomial (Fin 3) ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
      (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
      (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))

theorem lower1_eq (M : Matrix (Fin 3) (Fin 3) R3) :
    lower1 M = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      C (eps a c d) * (X c * pderiv b (pderiv d (M a b))) := rfl

theorem Xi_harm (ν : Fin 3 → ℂ) (p : R3) (hp : Lap p = 0) (c d : Fin 3) :
    Lap (Xi ν p c d) = 0 := by
  unfold Xi
  rw [Matrix.of_apply]
  split_ifs with h
  · rw [Lap_C_mul, hp, mul_zero]
  · rw [Lap_neg, Lap_rot _ _ _ hp, neg_zero]

theorem Lap_term (e : ℂ) (c b d : Fin 3) (m : R3) (hm : Lap m = 0) :
    Lap (C e * (X c * pderiv b (pderiv d m))) = C e * (C 2 * pderiv c (pderiv b (pderiv d m))) := by
  rw [Lap_C_mul, Lap_X_mul, Lap_pderiv, Lap_pderiv, hm, map_zero, map_zero, mul_zero, zero_add]

theorem T_symm (c b d : Fin 3) (m : R3) :
    pderiv c (pderiv b (pderiv d m)) = pderiv d (pderiv b (pderiv c m)) := by
  rw [pderiv_comm b d, pderiv_comm c d, pderiv_comm c b]

theorem lower1_harm (M : Matrix (Fin 3) (Fin 3) R3) (hM : ∀ a b, Lap (M a b) = 0) :
    Lap (lower1 M) = 0 := by
  rw [lower1_eq, Lap_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [Lap_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [Lap_sum]
  simp_rw [Lap_sum, Lap_term _ _ _ _ _ (hM a b)]

  set S := ∑ c : Fin 3, ∑ d : Fin 3, C (eps a c d) * (C 2 * pderiv c (pderiv b (pderiv d (M a b))))
    with hS
  have hneg : S = -S := by
    conv_lhs => rw [hS, Finset.sum_comm]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [eps_swap a d c, T_symm c b d, map_neg, neg_mul]
  have h2 : (2 : ℂ) • S = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hneg]
    exact add_neg_cancel S
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem X_mul_pderiv_pderiv_isHomogeneous {q : R3} {n : ℕ} (hq : q.IsHomogeneous n)
    (c b d : Fin 3) : (X c * pderiv b (pderiv d q)).IsHomogeneous (n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : (pderiv d q).IsHomogeneous 0 := by
      have := hq.pderiv (i := d)
      rwa [show n - 1 = 0 by omega] at this
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h1
    rw [h1, pderiv_C, mul_zero]
    apply isHomogeneous_zero
  · have := (isHomogeneous_X ℂ c).mul ((hq.pderiv (i := d)).pderiv (i := b))
    rwa [show 1 + (n - 1 - 1) = n - 1 by omega] at this

theorem X_mul_pderiv_isHomogeneous {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ) (a b : Fin 3) :
    (X a * pderiv b p).IsHomogeneous ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with h | h
  · subst h
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp
    rw [hp, pderiv_C, mul_zero]
    apply isHomogeneous_zero
  · have := (isHomogeneous_X ℂ a).mul (hp.pderiv (i := b))
    rwa [show 1 + (ℓ - 1) = ℓ by omega] at this

theorem Xi_isHomogeneous (ν : Fin 3 → ℂ) {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ) (c d : Fin 3) :
    (Xi ν p c d).IsHomogeneous ℓ := by
  unfold Xi
  rw [Matrix.of_apply]
  split_ifs with h
  · exact hp.C_mul _
  · exact ((X_mul_pderiv_isHomogeneous hp _ _).sub (X_mul_pderiv_isHomogeneous hp _ _)).neg

theorem main (ν : Fin 3 → ℂ) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    (lower1 (Xi ν p)).IsHomogeneous (ℓ - 1) ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i (lower1 (Xi ν p)))) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [lower1_eq]
    refine IsHomogeneous.sum _ _ _ (fun a _ => IsHomogeneous.sum _ _ _ (fun b _ =>
      IsHomogeneous.sum _ _ _ (fun c _ => IsHomogeneous.sum _ _ _ (fun d _ => ?_))))
    exact (X_mul_pderiv_pderiv_isHomogeneous (Xi_isHomogeneous ν hp a b) c b d).C_mul _
  · have hp0 : Lap p = 0 := hharm
    have := lower1_harm (Xi ν p) (Xi_harm ν p hp0)
    exact this

end

end WsC.L1H

open WsC.L1H in
theorem solution
    (ν : Fin 3 → ℂ) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    (lower₁ (Ξ ν p)).IsHomogeneous (ℓ - 1) ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i (lower₁ (Ξ ν p)))) = 0 := by
  exact WsC.L1H.main ν ℓ p hp hharm

end S_LanglandsTunnell_CubicInduction_isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi (solution)
