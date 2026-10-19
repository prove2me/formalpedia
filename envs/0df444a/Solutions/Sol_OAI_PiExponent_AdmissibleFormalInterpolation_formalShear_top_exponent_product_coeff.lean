-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_top_exponent_product_coeff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:16:46.684478+00:00
-- url     : https://prove2.me/submissions/a8845c01-183f-491e-949a-145794a47c45

import Mathlib
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem pie_coeff_lift {m : ℕ} (D : PowerSeries ℂ) (b : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff b (liftLogSeries m D) =
      if b.tail = 0 then PowerSeries.coeff (b 0) D else 0 := by
  conv_lhs => rw [← Finsupp.cons_tail b]
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv]
  simp only [liftLogSeries, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
    Function.comp_apply, RingEquiv.coe_toRingHom]
  rw [show (MvPowerSeries.finSuccEquiv ℂ m)
      ((MvPowerSeries.finSuccEquiv ℂ m).symm.toRingEquiv (PowerSeries.map MvPowerSeries.C D))
      = PowerSeries.map MvPowerSeries.C D from
    (MvPowerSeries.finSuccEquiv ℂ m).apply_symm_apply _]
  rw [PowerSeries.coeff_map, MvPowerSeries.coeff_C]

/-- weight of the non-zero coordinates -/
def pieW {m : ℕ} (e : Fin (m + 1) →₀ ℕ) : ℕ := ∑ j : Fin m, e j.succ

def pieP {m : ℕ} (N : ℕ) (p : MvPowerSeries (Fin (m + 1)) ℂ) : Prop :=
  ∀ e, MvPowerSeries.coeff e p ≠ 0 → pieW e ≤ N ∧ (pieW e = N → e 0 = 0)

theorem pieW_add {m : ℕ} (e f : Fin (m + 1) →₀ ℕ) : pieW (e + f) = pieW e + pieW f := by
  simp [pieW, Finset.sum_add_distrib]

theorem pieP_one {m : ℕ} : pieP (m := m) 0 1 := by
  intro e he
  rw [MvPowerSeries.coeff_one] at he
  split_ifs at he with h
  · subst h; simp [pieW]
  · exact absurd rfl he

theorem pieP_mul {m : ℕ} {N M : ℕ} {p q : MvPowerSeries (Fin (m + 1)) ℂ}
    (hp : pieP N p) (hq : pieP M q) : pieP (N + M) (p * q) := by
  intro e he
  rw [MvPowerSeries.coeff_mul] at he
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 := hp x.1 (left_ne_zero_of_mul hne)
  have h2 := hq x.2 (right_ne_zero_of_mul hne)
  subst hx
  rw [pieW_add]
  refine ⟨by omega, fun h => ?_⟩
  have a1 := h1.2 (by omega)
  have a2 := h2.2 (by omega)
  simp [a1, a2]

theorem pieP_pow {m : ℕ} {N : ℕ} {p : MvPowerSeries (Fin (m + 1)) ℂ}
    (hp : pieP N p) (k : ℕ) : pieP (N * k) (p ^ k) := by
  induction k with
  | zero => simpa using pieP_one
  | succ k ih => rw [pow_succ, Nat.mul_succ]; exact pieP_mul ih hp

theorem pieP_prod {m : ℕ} {ι : Type*} (s : Finset ι) (N : ι → ℕ)
    (p : ι → MvPowerSeries (Fin (m + 1)) ℂ) (hp : ∀ i ∈ s, pieP (N i) (p i)) :
    pieP (∑ i ∈ s, N i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pieP_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact pieP_mul (hp a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hp i (Finset.mem_insert_of_mem hi)))

theorem pieP_factor {m : ℕ} (i : Fin m) (f : PowerSeries ℂ) :
    pieP 1 (MvPowerSeries.X i.succ + liftLogSeries m f) := by
  intro e he
  rw [map_add, pie_coeff_lift, MvPowerSeries.coeff_X] at he
  by_cases h : e = Finsupp.single i.succ 1
  · subst h
    have : pieW (Finsupp.single i.succ 1 : Fin (m + 1) →₀ ℕ) = 1 := by
      simp only [pieW]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Finsupp.single_apply, Ne.symm hj]
      · simp
    refine ⟨this.le, fun _ => ?_⟩
    simp [Finsupp.single_apply, Fin.succ_ne_zero]
  · rw [if_neg h, zero_add] at he
    split_ifs at he with ht
    · have : pieW e = 0 := by
        simp only [pieW]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        have := DFunLike.congr_fun ht j
        simpa [Finsupp.tail, Fin.tail] using this
      omega
    · exact absurd rfl he

theorem solution
    {m : ℕ} (f : Fin m → PowerSeries ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ)
    (hpos : d 0 ≠ 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (f i)) ^ (a i.succ)) = 0 := by
  by_contra hne
  have hP := pieP_prod Finset.univ (fun i => 1 * a i.succ) _
    (fun i _ => pieP_pow (pieP_factor i (f i)) (a i.succ)) d hne
  apply hpos
  apply hP.2
  simp [pieW, htop]
