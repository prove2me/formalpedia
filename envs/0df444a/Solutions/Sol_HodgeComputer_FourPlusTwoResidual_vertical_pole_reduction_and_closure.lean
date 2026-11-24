-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.vertical_pole_reduction_and_closure
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T20:11:36.063835+00:00
-- url     : https://prove2.me/submissions/be0e27aa-b85c-46d4-b91a-1c115968e472

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

section VerticalPoleHelpers

open scoped BigOperators

private lemma p2m_fieldAction_apply {ι K : Type} [Fintype ι] [Field K] [CharZero K]
    (δ : ι → Derivation ℚ K K) (v : ι → K) (f : K) :
    HodgeComputer.FourPlusTwoResidual.fieldAction δ v f = ∑ i, v i * δ i f := by
  have hh := congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := ℚ) (A := K) (M := K))
    (fun i => v i • δ i) Finset.univ) f
  simpa only [HodgeComputer.FourPlusTwoResidual.fieldAction,
    Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply,
    Derivation.smul_apply, smul_eq_mul] using hh

private lemma p2m_chartCurrent_add {ι K : Type} [Fintype ι] [Field K] [CharZero K]
    (δ : ι → Derivation ℚ K K) (P : K) (v w : ι → K) :
    HodgeComputer.FourPlusTwoResidual.chartCurrent δ P (fun i => v i + w i) =
      HodgeComputer.FourPlusTwoResidual.chartCurrent δ P v +
        HodgeComputer.FourPlusTwoResidual.chartCurrent δ P w := by
  simp only [HodgeComputer.FourPlusTwoResidual.chartCurrent, p2m_fieldAction_apply,
    HodgeComputer.FourPlusTwoResidual.fieldDivergence, add_mul, map_add, Finset.sum_add_distrib]
  ring

private lemma p2m_chartCurrent_sub {ι K : Type} [Fintype ι] [Field K] [CharZero K]
    (δ : ι → Derivation ℚ K K) (P : K) (v w : ι → K) :
    HodgeComputer.FourPlusTwoResidual.chartCurrent δ P (fun i => v i - w i) =
      HodgeComputer.FourPlusTwoResidual.chartCurrent δ P v -
        HodgeComputer.FourPlusTwoResidual.chartCurrent δ P w := by
  simp only [HodgeComputer.FourPlusTwoResidual.chartCurrent, p2m_fieldAction_apply,
    HodgeComputer.FourPlusTwoResidual.fieldDivergence, sub_mul, map_sub, Finset.sum_sub_distrib]
  ring

private lemma p2m_chartCurrent_single_two {L : Type} [Field L] [CharZero L]
    (δ : Fin 3 → Derivation ℚ L L) (P v : L) :
    HodgeComputer.FourPlusTwoResidual.chartCurrent δ P (Pi.single 2 v) =
      (2 / 3 : L) * (v * δ 2 P) - P * δ 2 v := by
  simp only [HodgeComputer.FourPlusTwoResidual.chartCurrent, p2m_fieldAction_apply,
    HodgeComputer.FourPlusTwoResidual.fieldDivergence, Fin.sum_univ_three]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  rw [Pi.single_eq_of_ne h02, Pi.single_eq_of_ne h12, Pi.single_eq_same]
  simp

private lemma p2m_deriv_pow_mul_self {L : Type} [Field L] [CharZero L]
    (D : Derivation ℚ L L) (u : L) (m : ℕ) :
    u * D (u ^ m) = (m : L) * u ^ m * D u := by
  induction m with
  | zero =>
    have h1 : D 1 = 0 := by
      have h := D.leibniz 1 1
      simp only [mul_one, smul_eq_mul, one_mul] at h
      linear_combination -h
    simp [pow_zero, h1]
  | succ m ih =>
    rw [pow_succ, Derivation.leibniz]
    simp only [smul_eq_mul]
    calc
      u * (u ^ m * D u + u * D (u ^ m))
          = u ^ m * u * D u + u * (u * D (u ^ m)) := by ring
      _ = u ^ m * u * D u + u * ((m : L) * u ^ m * D u) := by rw [ih]
      _ = ((m + 1 : ℕ) : L) * (u ^ m * u) * D u := by push_cast; ring

private lemma p2m_deriv_pow {L : Type} [Field L] [CharZero L]
    (D : Derivation ℚ L L) (z : L) (n : ℕ) :
    D (z ^ (n + 1)) = ((n + 1 : ℕ) : L) * z ^ n * D z := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    rw [pow_succ z (k + 1), Derivation.leibniz]
    simp only [smul_eq_mul, ih]
    push_cast
    ring

private lemma p2m_deriv_aeval {F L : Type} [Field F] [Field L] [CharZero L] [Algebra F L]
    (D : Derivation ℚ L L) (hF : ∀ c : F, D (algebraMap F L c) = 0)
    (z : L) (p : Polynomial F) :
    D (Polynomial.aeval z p) = Polynomial.aeval z (Polynomial.derivative p) * D z := by
  induction p using Polynomial.induction_on with
  | C c =>
    simp [Polynomial.aeval_C, hF c]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul]
  | monomial n c _ =>
    have hpow := p2m_deriv_pow D z n
    simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
      Polynomial.derivative_C_mul_X_pow, Nat.add_sub_cancel]
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, hF c, mul_zero, add_zero, hpow, map_natCast]
    ring

private lemma p2m_single_Step {F L : Type} [Field F] [CharZero F] [Field L] [CharZero L]
    [Algebra F L] (δ : Fin 3 → Derivation ℚ L L) (t : L)
    (ht : δ 2 t = 1) (hF : ∀ c : F, δ 2 (algebraMap F L c) = 0)
    (P a : Polynomial F) (m : ℕ) (hP : Polynomial.aeval (t ^ 2) P ≠ 0) :
    HodgeComputer.FourPlusTwoResidual.chartCurrent δ (Polynomial.aeval (t ^ 2) P)
      (Pi.single 2 (t * (Polynomial.aeval (t ^ 2) a / (Polynomial.aeval (t ^ 2) P) ^ m))) =
      (((2 * (m : L) + 4 / 3) * t ^ 2 * Polynomial.aeval (t ^ 2) (Polynomial.derivative P) *
          Polynomial.aeval (t ^ 2) a) -
        Polynomial.aeval (t ^ 2) P * Polynomial.aeval (t ^ 2) a -
        2 * t ^ 2 * Polynomial.aeval (t ^ 2) P *
          Polynomial.aeval (t ^ 2) (Polynomial.derivative a)) /
        (Polynomial.aeval (t ^ 2) P) ^ m := by
  set P_L : L := Polynomial.aeval (t ^ 2) P
  set A_L : L := Polynomial.aeval (t ^ 2) a
  set dP_L : L := Polynomial.aeval (t ^ 2) (Polynomial.derivative P)
  set dA_L : L := Polynomial.aeval (t ^ 2) (Polynomial.derivative a)
  set v : L := t * (A_L / P_L ^ m)
  have hPm : P_L ^ m ≠ 0 := pow_ne_zero m hP
  have ht2 : δ 2 (t ^ 2) = 2 * t := by
    rw [sq, Derivation.leibniz]
    simp only [smul_eq_mul, ht]
    ring
  have hδP : δ 2 P_L = dP_L * (2 * t) := by
    dsimp only [P_L, dP_L]
    rw [p2m_deriv_aeval (δ 2) hF (t ^ 2) P, ht2]
  have hδA : δ 2 A_L = dA_L * (2 * t) := by
    dsimp only [A_L, dA_L]
    rw [p2m_deriv_aeval (δ 2) hF (t ^ 2) a, ht2]
  have hv_mul : v * P_L ^ m = t * A_L := by
    dsimp only [v]
    field_simp [hPm]
  have hdiff_v : P_L * δ 2 v * P_L ^ m =
      P_L * A_L + 2 * t ^ 2 * P_L * dA_L - 2 * (m : L) * t ^ 2 * dP_L * A_L := by
    have h1 := congrArg (δ 2) hv_mul
    rw [(δ 2).leibniz v (P_L ^ m), (δ 2).leibniz t A_L] at h1
    rw [ht, hδA] at h1
    simp only [smul_eq_mul] at h1
    have hpow := p2m_deriv_pow_mul_self (δ 2) P_L m
    rw [hδP] at hpow
    calc
      P_L * δ 2 v * P_L ^ m
          = P_L * (P_L ^ m * δ 2 v) := by ring
      _ = P_L * (t * (dA_L * (2 * t)) + A_L * 1 - v * δ 2 (P_L ^ m)) := by
            congr 1; linear_combination h1
      _ = P_L * (t * (dA_L * (2 * t)) + A_L * 1) - v * (P_L * δ 2 (P_L ^ m)) := by ring
      _ = P_L * (t * (dA_L * (2 * t)) + A_L * 1) -
            v * ((m : L) * P_L ^ m * (dP_L * (2 * t))) := by rw [hpow]
      _ = P_L * A_L + 2 * t ^ 2 * P_L * dA_L -
            (v * P_L ^ m) * (2 * (m : L) * t * dP_L) := by ring
      _ = P_L * A_L + 2 * t ^ 2 * P_L * dA_L -
            (t * A_L) * (2 * (m : L) * t * dP_L) := by rw [hv_mul]
      _ = P_L * A_L + 2 * t ^ 2 * P_L * dA_L - 2 * (m : L) * t ^ 2 * dP_L * A_L := by ring
  rw [p2m_chartCurrent_single_two, eq_div_iff hPm]
  calc
    ((2 / 3 : L) * (v * δ 2 P_L) - P_L * δ 2 v) * P_L ^ m
        = (2 / 3 : L) * (v * P_L ^ m) * δ 2 P_L - P_L * δ 2 v * P_L ^ m := by ring
    _ = (2 / 3 : L) * (t * A_L) * (dP_L * (2 * t)) -
          (P_L * A_L + 2 * t ^ 2 * P_L * dA_L - 2 * (m : L) * t ^ 2 * dP_L * A_L) := by
          rw [hv_mul, hδP, hdiff_v]
    _ = (2 * (m : L) + 4 / 3) * t ^ 2 * dP_L * A_L -
          P_L * A_L - 2 * t ^ 2 * P_L * dA_L := by ring

end VerticalPoleHelpers

theorem solution :
    (∀ {F L : Type} [Field F] [CharZero F] [Field L] [CharZero L] [Algebra F L]
      (δ : Fin 3 → Derivation ℚ L L) (t : L),
      δ 2 t = 1 →
      (∀ c : F, δ 2 (algebraMap F L c) = 0) →
      ∀ (P a : Polynomial F) (m : ℕ),
        Polynomial.aeval (t ^ 2) P ≠ 0 →
        HodgeComputer.FourPlusTwoResidual.chartCurrent δ (Polynomial.aeval (t ^ 2) P)
          (Pi.single 2 (t * (Polynomial.aeval (t ^ 2) a / (Polynomial.aeval (t ^ 2) P) ^ m))) =
          (((2 * (m : L) + 4 / 3) * t ^ 2 * Polynomial.aeval (t ^ 2) (Polynomial.derivative P) *
              Polynomial.aeval (t ^ 2) a) -
            Polynomial.aeval (t ^ 2) P * Polynomial.aeval (t ^ 2) a -
            2 * t ^ 2 * Polynomial.aeval (t ^ 2) P *
              Polynomial.aeval (t ^ 2) (Polynomial.derivative a)) /
            (Polynomial.aeval (t ^ 2) P) ^ m) ∧
    (∀ {F L : Type} [Field F] [CharZero F] [Field L] [CharZero L] [Algebra F L]
      (δ : Fin 3 → Derivation ℚ L L) (t : L),
      δ 2 t = 1 →
      (∀ c : F, δ 2 (algebraMap F L c) = 0) →
      ∀ (P : Polynomial F),
        Polynomial.aeval (t ^ 2) P ≠ 0 →
        IsCoprime (Polynomial.X * Polynomial.derivative P) P →
        ∀ (m : ℕ) (N : Polynomial F),
          ∃ (f_vert : L) (S_bar : Polynomial F),
            Polynomial.aeval (t ^ 2) N / (Polynomial.aeval (t ^ 2) P) ^ m =
              HodgeComputer.FourPlusTwoResidual.chartCurrent δ (Polynomial.aeval (t ^ 2) P)
                (Pi.single 2 (t * f_vert)) +
              Polynomial.aeval (t ^ 2) S_bar) ∧
    (∀ {L : Type} [Field L] [CharZero L]
      (δ : Fin 3 → Derivation ℚ L L)
      (P_el t c S_star S_bar : L)
      (q_star q_vert q_corr : Fin 3 → L),
      c ≠ 0 →
      (∀ i : Fin 3, δ i c = 0) →
      HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el q_star = S_star →
      S_star = HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el q_vert + S_bar →
      HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el q_corr = S_bar - c * t ^ 4 →
      HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el
        (fun i => (q_star i - q_vert i - q_corr i) / c) = t ^ 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F L _ _ _ _ _ δ t ht hF P a m hP
    exact p2m_single_Step δ t ht hF P a m hP
  · intro F L _ _ _ _ _ δ t ht hF P hP hcop m
    obtain ⟨u, v, huv⟩ := hcop
    induction m with
    | zero =>
      intro N
      refine ⟨0, N, ?_⟩
      rw [pow_zero, div_one, mul_zero, p2m_chartCurrent_single_two]
      simp
    | succ m ih =>
      intro N
      let κ : F := 2 * ((m + 1 : ℕ) : F) + 4 / 3
      have h3 : (3 : F) ≠ 0 := by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)
      have hκ : κ ≠ 0 := by
        intro h0
        have hmul : κ * 3 = ((6 * m + 10 : ℕ) : F) := by
          dsimp only [κ]
          push_cast
          field_simp [h3]
          ring
        rw [h0, zero_mul] at hmul
        have hnat : ((6 * m + 10 : ℕ) : F) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (6 * m + 9))
        exact hnat hmul.symm
      let a : Polynomial F := Polynomial.C κ⁻¹ * (N * u)
      let N' : Polynomial F := N * v + a + 2 * Polynomial.X * Polynomial.derivative a
      have hpoly : N =
          (Polynomial.C κ * Polynomial.X * Polynomial.derivative P * a -
            P * a - 2 * Polynomial.X * P * Polynomial.derivative a) + P * N' := by
        have hκ_inv : Polynomial.C κ * Polynomial.C κ⁻¹ = (1 : Polynomial F) := by
          rw [← map_mul, mul_inv_cancel₀ hκ, map_one]
        dsimp only [a, N']
        calc
          N = N * 1 := (mul_one N).symm
          _ = N * (u * (Polynomial.X * Polynomial.derivative P) + v * P) := by rw [huv]
          _ = 1 * (N * u) * (Polynomial.X * Polynomial.derivative P) + P * (N * v) := by ring
          _ = (Polynomial.C κ * Polynomial.C κ⁻¹) * (N * u) *
                (Polynomial.X * Polynomial.derivative P) + P * (N * v) := by rw [hκ_inv]
          _ = (Polynomial.C κ * Polynomial.X * Polynomial.derivative P *
                (Polynomial.C κ⁻¹ * (N * u)) -
                P * (Polynomial.C κ⁻¹ * (N * u)) -
                2 * Polynomial.X * P * Polynomial.derivative a) +
              P * (N * v + Polynomial.C κ⁻¹ * (N * u) +
                2 * Polynomial.X * Polynomial.derivative a) := by ring
      have haeval_κ : Polynomial.aeval (t ^ 2) (Polynomial.C κ) =
          (2 * ((m + 1 : ℕ) : L) + 4 / 3 : L) := by
        dsimp only [κ]
        simp [Polynomial.aeval_C, map_ofNat]
      have haeval_N := congrArg (Polynomial.aeval (t ^ 2)) hpoly
      simp only [map_add, map_sub, map_mul, map_ofNat, Polynomial.aeval_X, haeval_κ] at haeval_N
      set P_L : L := Polynomial.aeval (t ^ 2) P
      have hstep := p2m_single_Step δ t ht hF P a (m + 1) hP
      obtain ⟨f_rem, S_bar, hrem⟩ := ih N'
      refine ⟨Polynomial.aeval (t ^ 2) a / P_L ^ (m + 1) + f_rem, S_bar, ?_⟩
      have hsingle_add :
          (Pi.single (2 : Fin 3)
              (t * (Polynomial.aeval (t ^ 2) a / P_L ^ (m + 1) + f_rem)) : Fin 3 → L) =
            fun i =>
              Pi.single 2 (t * (Polynomial.aeval (t ^ 2) a / P_L ^ (m + 1))) i +
                Pi.single 2 (t * f_rem) i := by
        ext i
        fin_cases i <;> simp [mul_add]
      rw [haeval_N, add_div, ← hstep]
      have hcancel : P_L * Polynomial.aeval (t ^ 2) N' / P_L ^ (m + 1) =
          Polynomial.aeval (t ^ 2) N' / P_L ^ m := by
        rw [pow_succ' P_L m, mul_div_mul_left _ _ hP]
      rw [hcancel, hrem, hsingle_add, p2m_chartCurrent_add, add_assoc]
  · intro L _ _ δ P_el t c S_star S_bar q_star q_vert q_corr hc hδc h_star h_vert h_corr
    have hδ1 : ∀ i : Fin 3, δ i 1 = 0 := by
      intro i
      have h := (δ i).leibniz 1 1
      simp only [mul_one, smul_eq_mul, one_mul] at h
      linear_combination -h
    have hδcinv : ∀ i : Fin 3, δ i c⁻¹ = 0 := by
      intro i
      have h1 : δ i (c * c⁻¹) = δ i 1 := congrArg (δ i) (mul_inv_cancel₀ hc)
      rw [Derivation.leibniz, hδ1 i] at h1
      simp only [smul_eq_mul, hδc i, mul_zero, add_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left hc
    let q_num : Fin 3 → L := fun i => q_star i - q_vert i - q_corr i
    have hscale :
        HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el (fun i => q_num i / c) =
          c⁻¹ * HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el q_num := by
      have hdiv_i : ∀ i : Fin 3, δ i (q_num i / c) = c⁻¹ * δ i (q_num i) := by
        intro i
        rw [div_eq_mul_inv, Derivation.leibniz]
        simp only [smul_eq_mul, hδcinv i, mul_zero, zero_add]
      unfold HodgeComputer.FourPlusTwoResidual.chartCurrent
        HodgeComputer.FourPlusTwoResidual.fieldDivergence
      rw [p2m_fieldAction_apply, p2m_fieldAction_apply]
      have hsum1 : (∑ i : Fin 3, q_num i / c * δ i P_el) =
          c⁻¹ * ∑ i : Fin 3, q_num i * δ i P_el := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [div_eq_mul_inv]
        ring
      have hsum2 : (∑ i : Fin 3, δ i (q_num i / c)) =
          c⁻¹ * ∑ i : Fin 3, δ i (q_num i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact hdiv_i i
      rw [hsum1, hsum2]
      ring
    have hnum :
        HodgeComputer.FourPlusTwoResidual.chartCurrent δ P_el q_num = c * t ^ 4 := by
      dsimp only [q_num]
      rw [p2m_chartCurrent_sub, p2m_chartCurrent_sub, h_star, h_vert, h_corr]
      ring
    rw [hscale, hnum, inv_mul_cancel_left₀ hc]
