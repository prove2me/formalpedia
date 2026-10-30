-- Prove2me | solution 1 for MazurProof.N13MumfordCenteredDoublingJet.diskCoord_double_mod_sq_of_cross
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T05:02:07.827817+00:00
-- url     : https://prove2.me/submissions/274c463b-9a90-437d-a913-4d13e16ac12b

import Mathlib
import Definitions.Def_MazurN13_L1


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13MumfordCenteredDoublingJet
open Polynomial
attribute [local instance] MazurProof.N13MumfordCenteredDoublingJet.instFactPrimeOfNatNat_fLT

namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
theorem u_sub_base (P : DiskPair) :
    P.u - N13AbelChartBase.baseSmoothMumford.u =
      C (-(P.x₀ + (P.x₁ + 1))) * X +
        C (P.x₀ * P.x₁) := by
  simp [N13TwoAdicAbelChartData.DiskPair.u,
    N13FormalAbelLinearization.uBase]
  ring
end
end MazurProof.N13MumfordFormalTransitionJet

namespace MazurProof.N13MumfordCenteredDoublingJet
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13MumfordCenteredDoublingJet.instFactPrimeOfNatNat_fLT
/-- Cancellation by a unit preserves membership in an ideal. -/
private theorem mem_of_mul_mem_right_isUnit
    (J : Ideal R₂) {a b : R₂}
    (hb : IsUnit b) (hab : a * b ∈ J) : a ∈ J := by
  obtain ⟨u, rfl⟩ := hb
  have h := J.mul_mem_left (↑u⁻¹) hab
  simpa [mul_assoc, mul_left_comm, mul_comm] using h
end
end MazurProof.N13MumfordCenteredDoublingJet

namespace MazurProof.N13MumfordCenteredDoublingJet
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13MumfordCenteredDoublingJet.instFactPrimeOfNatNat_fLT
/-- Membership of only coefficients one and three in the cross-multiplied
centered product implies the two coefficient congruences for the monic
polynomial of a proposed double.

The calculation is stated for an arbitrary ideal containing the two
coordinates of `P`.  The constant coefficient has one additional product of
the two first-order coefficients of `u_P-u_B`; the linear coefficient is
exactly the negative of cross coefficient three. -/
theorem centeredUDeviation_double_mod_ideal_sq_of_cross
    (J : Ideal R₂) (P Q : DiskPair)
    (hr : P.x₀ ∈ J)
    (hs : P.x₁ + 1 ∈ J)
    (h₁ :
      (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 1 ∈
        J * J)
    (h₃ :
      (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 3 ∈
        J * J) :
    ((Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0) ∈
        J * J) ∧
      ((Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1) ∈
        J * J) := by
  let U := N13AbelChartBase.baseSmoothMumford.u
  let A := P.u - U
  let B := Q.u - U
  let E := P.u ^ 2 - U * Q.u
  let a₁ := -(P.x₀ + (P.x₁ + 1))
  let a₀ := P.x₀ * P.x₁
  let b₁ := -(Q.x₀ + (Q.x₁ + 1))
  let b₀ := Q.x₀ * Q.x₁
  let d₁ := a₁ + a₁ - b₁
  let d₀ := a₀ + a₀ - b₀
  have hU : U = X ^ 2 + X := by
    simp [U, N13FormalAbelLinearization.uBase]
  have hApoly : A = C a₁ * X + C a₀ := by
    simpa [A, U, a₁, a₀] using
      N13MumfordFormalTransitionJet.u_sub_base P
  have hBpoly : B = C b₁ * X + C b₀ := by
    simpa [B, U, b₁, b₀] using
      N13MumfordFormalTransitionJet.u_sub_base Q
  have hPu : P.u = U + (C a₁ * X + C a₀) := by
    calc
      P.u = U + A := by simp [A]
      _ = U + (C a₁ * X + C a₀) := by rw [hApoly]
  have hQu : Q.u = U + (C b₁ * X + C b₀) := by
    calc
      Q.u = U + B := by simp [B]
      _ = U + (C b₁ * X + C b₀) := by rw [hBpoly]
  have hEpoly :
      E =
        C d₁ * X ^ 3 +
          C (d₀ + d₁ + a₁ ^ 2) * X ^ 2 +
          C (d₀ + a₁ * a₀ + a₁ * a₀) * X +
          C (a₀ ^ 2) := by
    dsimp only [E]
    rw [hPu, hQu, hU]
    simp only [d₁, d₀, map_add, map_sub, map_mul, map_pow]
    ring
  have hA₀eq : A.coeff 0 = a₀ := by
    rw [hApoly]
    simp
  have hA₁eq : A.coeff 1 = a₁ := by
    rw [hApoly]
    simp
  have hB₀eq : B.coeff 0 = b₀ := by
    rw [hBpoly]
    simp
  have hB₁eq : B.coeff 1 = b₁ := by
    rw [hBpoly]
    simp
  have hE₁eq : E.coeff 1 = d₀ + a₁ * a₀ + a₁ * a₀ := by
    rw [hEpoly]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
    norm_num
  have hE₃eq : E.coeff 3 = d₁ := by
    rw [hEpoly]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
    norm_num
  have hA₀ : A.coeff 0 ∈ J := by
    rw [hA₀eq]
    dsimp only [a₀]
    exact J.mul_mem_right P.x₁ hr
  have hA₁ : A.coeff 1 ∈ J := by
    rw [hA₁eq]
    dsimp only [a₁]
    exact J.neg_mem (J.add_mem hr hs)
  have hzero :
      (Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0) =
        -(P.u ^ 2 -
            N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 1 +
          (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 *
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 +
          (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 *
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 := by
    change
      B.coeff 0 - (A.coeff 0 + A.coeff 0) =
        -(E.coeff 1) + A.coeff 1 * A.coeff 0 +
          A.coeff 1 * A.coeff 0
    rw [hA₀eq, hA₁eq, hB₀eq, hE₁eq]
    simp only [d₀]
    ring
  have hone :
      (Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1) =
        -(P.u ^ 2 -
            N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 3 := by
    change B.coeff 1 - (A.coeff 1 + A.coeff 1) = -(E.coeff 3)
    rw [hA₁eq, hB₁eq, hE₃eq]
    simp only [d₁]
    ring
  constructor
  · rw [hzero]
    exact
      (J * J).add_mem
        ((J * J).add_mem ((J * J).neg_mem h₁)
          (Ideal.mul_mem_mul hA₁ hA₀))
        (Ideal.mul_mem_mul hA₁ hA₀)
  · rw [hone]
    exact (J * J).neg_mem h₃
end
end MazurProof.N13MumfordCenteredDoublingJet

namespace MazurProof.N13MumfordCenteredDoublingJet
noncomputable section
open Algebra Module Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- Specializing the coefficient reducer to the moving coordinate ideal of
`P` gives the one-sided congruence used by the unary doubling chart. -/
theorem centeredUDeviation_double_mod_sq_of_cross
    (P Q : DiskPair)
    (h₁ :
      (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 1 ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P)
    (h₃ :
      (P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 3 ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P) :
    ((Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 0) ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P) ∧
      ((Q.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 -
          ((P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1 +
            (P.u - N13AbelChartBase.baseSmoothMumford.u).coeff 1) ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P) := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  apply centeredUDeviation_double_mod_ideal_sq_of_cross I P Q
  · apply Ideal.subset_span
    exact Set.mem_range_self (0 : Fin 2)
  · apply Ideal.subset_span
    exact Set.mem_range_self (1 : Fin 2)
  · exact h₁
  · exact h₃
end
end MazurProof.N13MumfordCenteredDoublingJet

attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
theorem solution (P Q : DiskPair) (h₁ : (P.u ^ 2 - N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 1 ∈ N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P * N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P) (h₃ : (P.u ^ 2 - N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff 3 ∈ N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P * N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P) (i : Fin 2) : N13TwoAdicAbelChartData.DiskPair.coord Q i - (N13TwoAdicAbelChartData.DiskPair.coord P i + N13TwoAdicAbelChartData.DiskPair.coord P i) ∈ N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P * N13TwoAdicKernelChart.coordIdeal N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  let A := P.u - N13AbelChartBase.baseSmoothMumford.u
  let B := Q.u - N13AbelChartBase.baseSmoothMumford.u
  have hcoeff := centeredUDeviation_double_mod_sq_of_cross P Q h₁ h₃
  have hA₀ : A.coeff 0 = P.x₀ * P.x₁ := by
    rw [show A = P.u - N13AbelChartBase.baseSmoothMumford.u from rfl,
      N13MumfordFormalTransitionJet.u_sub_base]
    simp
  have hA₁ : A.coeff 1 = -(P.x₀ + (P.x₁ + 1)) := by
    rw [show A = P.u - N13AbelChartBase.baseSmoothMumford.u from rfl,
      N13MumfordFormalTransitionJet.u_sub_base]
    simp
  have hB₀ : B.coeff 0 = Q.x₀ * Q.x₁ := by
    rw [show B = Q.u - N13AbelChartBase.baseSmoothMumford.u from rfl,
      N13MumfordFormalTransitionJet.u_sub_base]
    simp
  have hB₁ : B.coeff 1 = -(Q.x₀ + (Q.x₁ + 1)) := by
    rw [show B = Q.u - N13AbelChartBase.baseSmoothMumford.u from rfl,
      N13MumfordFormalTransitionJet.u_sub_base]
    simp
  have hcoeff₀ :
      B.coeff 0 - (A.coeff 0 + A.coeff 0) ∈ I * I := by
    simpa only [A, B, I] using hcoeff.1
  have hcoeff₁ :
      B.coeff 1 - (A.coeff 1 + A.coeff 1) ∈ I * I := by
    simpa only [A, B, I] using hcoeff.2
  have hp₀ : P.x₀ ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (0 : Fin 2)
  have hp₁ : P.x₁ + 1 ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (1 : Fin 2)
  have hA₀mem : A.coeff 0 ∈ I := by
    rw [hA₀]
    exact I.mul_mem_right P.x₁ hp₀
  have hA₁mem : A.coeff 1 ∈ I := by
    rw [hA₁]
    exact I.neg_mem (I.add_mem hp₀ hp₁)
  have hB₀mem : B.coeff 0 ∈ I := by
    have hdiff : B.coeff 0 - (A.coeff 0 + A.coeff 0) ∈ I :=
      Ideal.mul_le_left hcoeff₀
    have hsum := I.add_mem hdiff (I.add_mem hA₀mem hA₀mem)
    convert hsum using 1
    ring
  have hB₁mem : B.coeff 1 ∈ I := by
    have hdiff : B.coeff 1 - (A.coeff 1 + A.coeff 1) ∈ I :=
      Ideal.mul_le_left hcoeff₁
    have hsum := I.add_mem hdiff (I.add_mem hA₁mem hA₁mem)
    convert hsum using 1
    ring
  have hx₁unit : IsUnit Q.x₁ := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_neg_one
    simpa using Q.x₁_add_one_mem
  have hq₀ : Q.x₀ ∈ I := by
    rw [hB₀] at hB₀mem
    exact mem_of_mul_mem_right_isUnit I hx₁unit hB₀mem
  have hq₁ : Q.x₁ + 1 ∈ I := by
    rw [hB₁] at hB₁mem
    have hsumRaw := I.neg_mem hB₁mem
    have hsum : Q.x₀ + (Q.x₁ + 1) ∈ I := by
      convert hsumRaw using 1
      ring
    have hsub := I.sub_mem hsum hq₀
    convert hsub using 1
    ring
  have hpProd : P.x₀ * (P.x₁ + 1) ∈ I * I :=
    Ideal.mul_mem_mul hp₀ hp₁
  have hqProd : Q.x₀ * (Q.x₁ + 1) ∈ I * I :=
    Ideal.mul_mem_mul hq₀ hq₁
  have hcoord₀ :
      Q.x₀ - (P.x₀ + P.x₀) ∈ I * I := by
    have hprodDiff :
        Q.x₀ * (Q.x₁ + 1) -
            (P.x₀ * (P.x₁ + 1) +
              P.x₀ * (P.x₁ + 1)) ∈ I * I :=
      (I * I).sub_mem hqProd ((I * I).add_mem hpProd hpProd)
    have hsum := (I * I).add_mem ((I * I).neg_mem hcoeff₀) hprodDiff
    rw [hA₀, hB₀] at hsum
    convert hsum using 1
    ring
  have hcoord₁ :
      (Q.x₁ + 1) -
          ((P.x₁ + 1) + (P.x₁ + 1)) ∈ I * I := by
    have hsum := (I * I).sub_mem ((I * I).neg_mem hcoeff₁) hcoord₀
    rw [hA₁, hB₁] at hsum
    convert hsum using 1
    ring
  fin_cases i
  · change
      Q.x₀ - (P.x₀ + P.x₀) ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P
    simpa only [I] using hcoord₀
  · change
      (Q.x₁ + 1) - ((P.x₁ + 1) + (P.x₁ + 1)) ∈
        N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P *
          N13TwoAdicKernelChart.coordIdeal
            N13TwoAdicAbelChartData.DiskPair.coord P
    simpa only [I] using hcoord₁
