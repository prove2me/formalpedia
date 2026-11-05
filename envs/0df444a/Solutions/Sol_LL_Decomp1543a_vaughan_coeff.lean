-- Prove2me | solution 1 for LL_Decomp1543a.vaughan_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:23.419369+00:00
-- url     : https://prove2.me/submissions/399c2473-5bcf-47bf-8840-8997fa3c7e6b

import Mathlib
import Definitions.Def_LL_Decomp1543a_lam1
import Definitions.Def_LL_Decomp1543a_lam2
import Definitions.Def_LL_Decomp1543a_lam3
import Definitions.Def_LL_Decomp1543a_am
import Definitions.Def_LL_Decomp1543a_lam4

open Real Finset ArithmeticFunction

namespace VaAAux

theorem lam_mobius_log (n : ℕ) (hn : 1 ≤ n) :
    (vonMangoldt n : ℝ) = ∑ t ∈ n.divisors, (moebius t : ℝ) * Real.log ((n / t : ℕ) : ℝ) := by
  have h := (sum_eq_iff_sum_mul_moebius_eq (R := ℝ) (f := fun n => (vonMangoldt n : ℝ))
    (g := fun n => Real.log n)).1 (fun n hn => vonMangoldt_sum) n hn
  rw [← h, Nat.sum_divisorsAntidiagonal (fun a b => (moebius a : ℝ) * Real.log b)]

theorem sum_moebius_div (m : ℕ) : ∑ t ∈ m.divisors, (moebius t : ℝ) = if m = 1 then 1 else 0 := by
  have h := congrArg (fun f => f m) (moebius_mul_coe_zeta)
  simp only [coe_mul_zeta_apply, one_apply] at h
  have h' : ((∑ t ∈ m.divisors, moebius t : ℤ) : ℝ) = ((if m = 1 then 1 else 0 : ℤ) : ℝ) := by
    rw [h]
  simpa [apply_ite] using h'

theorem divisors_filter_mul (n d : ℕ) (hd : d ∣ n) :
    n.divisors.filter (fun t => d * t ∣ n) = (n / d).divisors := by
  ext t
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨(Nat.dvd_div_iff_mul_dvd hd).2 h3, fun h => h2 ?_⟩
    have := Nat.div_mul_cancel hd
    rw [h] at this
    simpa using this.symm
  · rintro ⟨h1, h2⟩
    have h3 : d * t ∣ n := (Nat.dvd_div_iff_mul_dvd hd).1 h1
    refine ⟨⟨(Dvd.intro_left _ rfl).trans h3, ?_⟩, h3⟩
    rintro rfl
    simp_all

open LL_Decomp1543a in
theorem log_split (U : ℝ) (m : ℕ) :
    Real.log m = ∑ d ∈ m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U), (vonMangoldt d : ℝ)
      + am U m := by
  rw [← vonMangoldt_sum, ← sum_filter_add_sum_filter_not _ (fun d : ℕ => (d : ℝ) ≤ U)]
  congr 1
  unfold am
  apply sum_congr _ (fun _ _ => rfl)
  apply filter_congr
  intro d _
  exact not_le

open LL_Decomp1543a in
theorem vaughan_aux (U V : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (vonMangoldt n : ℝ) = lam1 U n + lam2 V n + lam3 U V n + lam4 U V n := by
  have hn0 : n ≠ 0 := by omega
  have hW : ∀ t ∈ n.divisors,
      ∑ d ∈ (n / t).divisors.filter (fun d : ℕ => (d : ℝ) ≤ U), (vonMangoldt d : ℝ)
        = ∑ d ∈ n.divisors, if ((d : ℝ) ≤ U ∧ d * t ∣ n) then (vonMangoldt d : ℝ) else 0 := by
    intro t ht
    have htn : t ∣ n := Nat.dvd_of_mem_divisors ht
    rw [← divisors_filter_mul n t htn, filter_filter, sum_filter]
    apply sum_congr rfl
    intro d _
    simp only [mul_comm t d, and_comm]
  have hT1 : ∑ t ∈ n.divisors, (moebius t : ℝ) *
      ∑ d ∈ (n / t).divisors.filter (fun d : ℕ => (d : ℝ) ≤ U), (vonMangoldt d : ℝ)
      = lam1 U n := by
    rw [sum_congr rfl (fun t ht => by rw [hW t ht])]
    simp_rw [mul_sum]
    rw [sum_comm]
    have key : ∀ d ∈ n.divisors, ∑ t ∈ n.divisors, (moebius t : ℝ) *
        (if ((d : ℝ) ≤ U ∧ d * t ∣ n) then (vonMangoldt d : ℝ) else 0)
        = if (d = n ∧ (d : ℝ) ≤ U) then (vonMangoldt d : ℝ) else 0 := by
      intro d hd
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
      by_cases hdU : (d : ℝ) ≤ U
      · simp only [hdU, true_and, mul_ite, mul_zero]
        rw [← sum_filter, divisors_filter_mul n d hdn, ← sum_mul, sum_moebius_div]
        have : n / d = 1 ↔ d = n := by
          constructor
          · intro h
            have := Nat.div_mul_cancel hdn
            rw [h] at this
            simpa using this
          · rintro rfl
            exact Nat.div_self (Nat.pos_of_ne_zero hn0)
        by_cases hdn' : d = n
        · simp [hdn', Nat.div_self (Nat.pos_of_ne_zero hn0)]
        · simp [hdn', this]
      · simp [hdU]
    rw [sum_congr rfl key]
    rw [sum_eq_single n]
    · simp [lam1]
    · intro d _ hdn
      simp [hdn]
    · intro h
      exact absurd (Nat.mem_divisors.2 ⟨dvd_rfl, hn0⟩) h
  have hT2 : ∑ t ∈ n.divisors.filter (fun t : ℕ => (t : ℝ) ≤ V), (moebius t : ℝ) *
      ∑ d ∈ (n / t).divisors.filter (fun d : ℕ => (d : ℝ) ≤ U), (vonMangoldt d : ℝ)
      = ∑ r ∈ n.divisors, ∑ t ∈ n.divisors,
        if ((r : ℝ) ≤ U ∧ (t : ℝ) ≤ V ∧ r * t ∣ n) then (vonMangoldt r : ℝ) * (moebius t : ℝ)
          else 0 := by
    rw [sum_filter, sum_comm]
    have : ∀ t ∈ n.divisors, (if (t : ℝ) ≤ V then (moebius t : ℝ) *
        ∑ d ∈ (n / t).divisors.filter (fun d : ℕ => (d : ℝ) ≤ U), (vonMangoldt d : ℝ) else 0)
        = ∑ d ∈ n.divisors, if ((d : ℝ) ≤ U ∧ (t : ℝ) ≤ V ∧ d * t ∣ n) then
          (vonMangoldt d : ℝ) * (moebius t : ℝ) else 0 := by
      intro t ht
      rw [hW t ht]
      by_cases htV : (t : ℝ) ≤ V
      · simp only [htV, if_true, mul_sum, true_and]
        apply sum_congr rfl
        intro d _
        by_cases h : ((d : ℝ) ≤ U ∧ d * t ∣ n) <;> simp [h, mul_comm]
      · simp [htV]
    rw [sum_congr rfl this, sum_comm]
  have hlog : ∀ t ∈ n.divisors, (moebius t : ℝ) * Real.log ((n / t : ℕ) : ℝ) =
      (moebius t : ℝ) * ∑ d ∈ (n / t).divisors.filter (fun d : ℕ => (d : ℝ) ≤ U),
        (vonMangoldt d : ℝ) + (moebius t : ℝ) * am U (n / t) := by
    intro t _
    rw [← mul_add, ← log_split]
  rw [lam_mobius_log n hn,
    ← sum_filter_add_sum_filter_not n.divisors (fun t : ℕ => (t : ℝ) ≤ V)]
  have h2 : ∑ t ∈ n.divisors.filter (fun t : ℕ => ¬ (t : ℝ) ≤ V),
      (moebius t : ℝ) * Real.log ((n / t : ℕ) : ℝ) = lam1 U n + lam3 U V n + lam4 U V n := by
    rw [sum_congr rfl (fun t ht => hlog t (mem_filter.1 ht).1), sum_add_distrib]
    have e1 := sum_filter_add_sum_filter_not n.divisors (fun t : ℕ => (t : ℝ) ≤ V)
      (fun t => (moebius t : ℝ) *
        ∑ d ∈ (n / t).divisors.filter (fun d : ℕ => (d : ℝ) ≤ U), (vonMangoldt d : ℝ))
    rw [hT1, hT2] at e1
    have e3 : lam3 U V n = - ∑ r ∈ n.divisors, ∑ t ∈ n.divisors,
        if ((r : ℝ) ≤ U ∧ (t : ℝ) ≤ V ∧ r * t ∣ n) then (vonMangoldt r : ℝ) * (moebius t : ℝ)
          else 0 := rfl
    have e4 : lam4 U V n = ∑ t ∈ n.divisors.filter (fun t : ℕ => ¬ (t : ℝ) ≤ V),
        (moebius t : ℝ) * am U (n / t) := by
      unfold lam4
      apply sum_congr _ (fun _ _ => rfl)
      apply filter_congr
      intro d _
      exact not_le.symm
    rw [e4, e3]
    linarith
  rw [h2]
  unfold lam2
  ring

end VaAAux

open LL_Decomp1543a in
theorem solution (U V : ℝ) (hV : 1 ≤ V) (n : ℕ) (hn : 1 ≤ n) :
    (vonMangoldt n : ℝ) = lam1 U n + lam2 V n + lam3 U V n + lam4 U V n :=
  VaAAux.vaughan_aux U V n hn
