-- Prove2me | solution 1 for ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5a588856-0123-5947-90a8-799174e6b5bd

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun
import Theorems.Thm_ModularCurve_hasSum_qParam_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow

set_option autoImplicit false

noncomputable section

namespace SExpPi

open ModularCurve Complex Filter Finset
open scoped Topology

def IsIntPS (A : PowerSeries ℂ) : Prop := ∀ n : ℕ, IsIntegral ℤ (PowerSeries.coeff n A)

theorem IsIntPS.one : IsIntPS 1 := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_zero

theorem IsIntPS.mul {A B : PowerSeries ℂ} (hA : IsIntPS A) (hB : IsIntPS B) : IsIntPS (A * B) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact IsIntegral.sum _ fun p _ => (hA _).mul (hB _)

theorem IsIntPS.pow {A : PowerSeries ℂ} (hA : IsIntPS A) (k : ℕ) : IsIntPS (A ^ k) := by
  induction k with
  | zero => simpa using IsIntPS.one
  | succ k ih => rw [pow_succ]; exact ih.mul hA

theorem IsIntPS.prod {ι : Type*} (s : Finset ι) (A : ι → PowerSeries ℂ) (h : ∀ i ∈ s, IsIntPS (A i)) :
    IsIntPS (∏ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsIntPS.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

variable (h : ℝ) (hh : 0 < h)

def Expands (A : PowerSeries ℂ) (F : UpperHalfPlane → ℂ) : Prop :=
  ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m A * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)

variable {h}

theorem Expands.one : Expands h 1 (fun _ => 1) := by
  intro τ
  have : (fun m : ℕ => PowerSeries.coeff m (1 : PowerSeries ℂ) * Function.Periodic.qParam h (τ : ℂ) ^ m) =
      fun m => if m = 0 then 1 else 0 := by
    funext m; rw [PowerSeries.coeff_one]; split_ifs with hm <;> simp [hm]
  rw [this]
  simpa using hasSum_ite_eq 0 (1 : ℂ)

include hh in
theorem Expands.mul {A B : PowerSeries ℂ} {F G : UpperHalfPlane → ℂ} (hA : Expands h A F) (hB : Expands h B G) :
    Expands h (A * B) (fun τ => F τ * G τ) :=
  fun τ => ModularCurve.hasSum_qParam_mul h hh A B F G hA hB τ

include hh in
theorem Expands.pow {A : PowerSeries ℂ} {F : UpperHalfPlane → ℂ} (hA : Expands h A F) (k : ℕ) :
    Expands h (A ^ k) (fun τ => F τ ^ k) := by
  induction k with
  | zero => simpa using (Expands.one (h := h))
  | succ k ih =>
    have := Expands.mul hh ih hA
    simpa [pow_succ] using this

include hh in
theorem Expands.prod {ι : Type*} (s : Finset ι) {A : ι → PowerSeries ℂ} {F : ι → UpperHalfPlane → ℂ}
    (hAF : ∀ i ∈ s, Expands h (A i) (F i)) :
    Expands h (∏ i ∈ s, A i) (fun τ => ∏ i ∈ s, F i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Expands.one (h := h))
  | insert a s ha ih =>
    have := Expands.mul hh (hAF a (Finset.mem_insert_self a s)) (ih fun i hi => hAF i (Finset.mem_insert_of_mem hi))
    simpa [Finset.prod_insert ha] using this

end SExpPi

namespace SExpPi

open ModularCurve Complex Filter Finset
open scoped Topology Real

theorem isIntegral_intCast (m : ℤ) : IsIntegral ℤ (m : ℂ) :=
  ⟨Polynomial.X - Polynomial.C m, Polynomial.monic_X_sub_C m, by simp⟩

theorem qParam_pow_eq (N : ℕ) (τ : ℂ) (n : ℕ) :
    Function.Periodic.qParam (N : ℝ) τ ^ n = cexp (2 * π * Complex.I * (n : ℂ) * τ / (N : ℂ)) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem val_cast_lt {N : ℕ} [NeZero N] (r : ZMod N) : ((r.val : ℤ)) < (N : ℤ) := by
  exact_mod_cast ZMod.val_lt r

theorem val_cast_eq_zero_iff {N : ℕ} [NeZero N] (r : ZMod N) : ((r.val : ℤ)) = 0 ↔ r = 0 := by
  rw [Int.natCast_eq_zero, ZMod.val_eq_zero]

theorem not_dvd_val {N : ℕ} [NeZero N] {s : ZMod N} (hs : s ≠ 0) : ¬ ((N : ℤ) ∣ (s.val : ℤ)) := by
  intro h
  apply hs
  rw [Int.natCast_dvd_natCast] at h
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt s)

theorem exp_val_ne_one {N : ℕ} [NeZero N] {s : ZMod N} (hs : s ≠ 0) :
    cexp (2 * π * Complex.I * (s.val : ℂ) / (N : ℂ)) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  apply not_dvd_val hs
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hπ : (2 * (π : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h1 : ((s.val : ℤ) : ℂ) = ((n * N : ℤ) : ℂ) := by
    push_cast
    field_simp at hn
    linear_combination hn
  exact ⟨n, by have := (Int.cast_injective (α := ℂ)) h1; rw [this]; ring⟩

end SExpPi

namespace SExpPi

open ModularCurve Complex Filter Finset
open scoped Topology Real

set_option maxHeartbeats 12800000 in
theorem main (N : ℕ) [NeZero N] (e : ZMod N → ZMod N → ℕ) (he : e 0 0 = 0) :
    ∃ (C : ℂ) (d : ℕ → ℂ), C ^ N = 1 ∧ (∀ n : ℕ, IsIntegral ℤ (d n)) ∧
      d 0 = ∏ s : ZMod N,
        (1 - cexp (2 * π * Complex.I * (s.val : ℂ) / (N : ℂ))) ^ (12 * N * e 0 s) ∧
      d 0 ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ (12 * N * ∑ r : ZMod N, ∑ s : ZMod N, e r s) * (d 0)⁻¹) ∧
      (∀ τ : UpperHalfPlane,
        HasSum
          (fun n : ℕ => d n * cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ) / (N : ℂ)))
          ((∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
            (C * cexp (2 * π * Complex.I *
              ((∑ r : ZMod N, ∑ s : ZMod N,
                  (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ))))) ∧
      Tendsto
        (fun τ : UpperHalfPlane =>
          (∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
            (C * cexp (2 * π * Complex.I *
              ((∑ r : ZMod N, ∑ s : ZMod N,
                  (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ))))
        UpperHalfPlane.atImInfty (𝓝 (d 0)) := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

  let ρ : ZMod N → ZMod N → ℂ := fun r s =>
    -cexp (π * Complex.I * ((s.val : ℤ) : ℂ) * (((r.val : ℤ) : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2)
  let E : ZMod N → UpperHalfPlane → ℂ := fun r τ =>
    cexp (2 * π * Complex.I * (6 * ((r.val : ℤ) : ℂ) ^ 2 - 6 * ((r.val : ℤ) : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * (τ : ℂ) /
      (12 * (N : ℂ) ^ 2))
  let Q : ZMod N → ZMod N → UpperHalfPlane → ℂ := fun r s τ =>
    siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) / (ρ r s * E r τ)
  let k : ZMod N → ZMod N → ℕ := fun r s => 12 * N * e r s
  have hk00 : k 0 0 = 0 := by simp [k, he]
  have hdata : ∀ r s : ZMod N, ∃ c : ℕ → ℂ,
      (¬ (r = 0 ∧ s = 0) →
        (∀ n : ℕ, IsIntegral ℤ (c n)) ∧
        c 0 = (if ((r.val : ℤ)) = 0 then 1 - cexp (2 * π * Complex.I * ((s.val : ℤ) : ℂ) / (N : ℂ)) else 1) ∧
        IsIntegral ℤ ((N : ℂ) * (c 0)⁻¹) ∧
        (∀ τ : UpperHalfPlane, HasSum
          (fun n : ℕ => c n * cexp (2 * π * Complex.I * (n : ℂ) * (τ : ℂ) / (N : ℂ))) (Q r s τ)) ∧
        Tendsto (Q r s) UpperHalfPlane.atImInfty (𝓝 (c 0))) ∧
      ((r = 0 ∧ s = 0) → c = fun n => if n = 0 then 1 else 0) := by
    intro r s
    by_cases h00 : r = 0 ∧ s = 0
    · exact ⟨fun n => if n = 0 then 1 else 0, fun h => absurd h00 h, fun _ => rfl⟩
    · have hs : ((r.val : ℤ)) = 0 → ¬ ((N : ℤ) ∣ (s.val : ℤ)) := by
        intro hr
        rw [val_cast_eq_zero_iff] at hr
        exact not_dvd_val (fun hs0 => h00 ⟨hr, hs0⟩)
      obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ :=
        ModularCurve.SiegelUnit.exists_isIntegral_hasSum_siegelFun N (r.val : ℤ) (s.val : ℤ)
          (by positivity) (val_cast_lt r) hs
      exact ⟨c, fun _ => ⟨hc1, hc2, hc3, hc4, hc5⟩, fun h => absurd h h00⟩
  choose c hc1 hc0 using hdata

  let A : ZMod N → ZMod N → PowerSeries ℂ := fun r s => PowerSeries.mk (c r s)
  have hA_int : ∀ r s, IsIntPS (A r s) := by
    intro r s n
    rw [PowerSeries.coeff_mk]
    by_cases h00 : r = 0 ∧ s = 0
    · rw [hc0 r s h00]
      dsimp only
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · exact (hc1 r s h00).1 n
  have hA_exp : ∀ r s, ¬ (r = 0 ∧ s = 0) → Expands (N : ℝ) (A r s) (Q r s) := by
    intro r s h00 τ
    have := (hc1 r s h00).2.2.2.1 τ
    convert this using 1
    funext n
    rw [PowerSeries.coeff_mk, qParam_pow_eq]

  have hP_exp : ∀ r s, Expands (N : ℝ) (A r s ^ k r s) (fun τ => Q r s τ ^ k r s) := by
    intro r s
    by_cases h00 : r = 0 ∧ s = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [hk00]
      simpa using (Expands.one (h := (N : ℝ)))
    · exact Expands.pow hNpos (hA_exp r s h00) (k r s)

  let Pser : PowerSeries ℂ := ∏ r : ZMod N, ∏ s : ZMod N, A r s ^ k r s
  have hPser_exp : Expands (N : ℝ) Pser (fun τ => ∏ r : ZMod N, ∏ s : ZMod N, Q r s τ ^ k r s) := by
    refine Expands.prod hNpos Finset.univ (A := fun r => ∏ s : ZMod N, A r s ^ k r s)
      (F := fun r τ => ∏ s : ZMod N, Q r s τ ^ k r s) fun r _ => ?_
    exact Expands.prod hNpos Finset.univ (A := fun s => A r s ^ k r s) (F := fun s τ => Q r s τ ^ k r s)
      fun s _ => hP_exp r s
  have hPser_int : IsIntPS Pser :=
    IsIntPS.prod _ _ fun r _ => IsIntPS.prod _ _ fun s _ => (hA_int r s).pow _

  have hPser0 : PowerSeries.coeff 0 Pser = ∏ r : ZMod N, ∏ s : ZMod N, (c r s 0) ^ k r s := by
    simp only [Pser, A, PowerSeries.coeff_zero_eq_constantCoeff, map_prod, map_pow, PowerSeries.constantCoeff_mk]
  have hc0_of_ne : ∀ r s, r ≠ 0 → c r s 0 = 1 := by
    intro r s hr
    rw [(hc1 r s (fun h => hr h.1)).2.1, if_neg (by rw [val_cast_eq_zero_iff]; exact hr)]
  have hc0_zero : ∀ s, s ≠ 0 → c 0 s 0 = 1 - cexp (2 * π * Complex.I * (s.val : ℂ) / (N : ℂ)) := by
    intro s hs
    rw [(hc1 0 s (fun h => hs h.2)).2.1, if_pos (by simp)]
    push_cast; rfl
  have hc00 : c 0 0 0 = 1 := by rw [hc0 0 0 ⟨rfl, rfl⟩]; simp
  have hd0 : PowerSeries.coeff 0 Pser =
      ∏ s : ZMod N, (1 - cexp (2 * π * Complex.I * (s.val : ℂ) / (N : ℂ))) ^ (12 * N * e 0 s) := by
    rw [hPser0, Finset.prod_eq_single (0 : ZMod N)]
    · refine Finset.prod_congr rfl fun s _ => ?_
      by_cases hs : s = 0
      · subst hs; simp [k, he]
      · rw [hc0_zero s hs]
    · intro r _ hr
      exact Finset.prod_eq_one fun s _ => by rw [hc0_of_ne r s hr, one_pow]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hd0_ne : PowerSeries.coeff 0 Pser ≠ 0 := by
    rw [hd0, Finset.prod_ne_zero_iff]
    intro s _
    by_cases hs : s = 0
    · subst hs; simp [he]
    · exact pow_ne_zero _ (sub_ne_zero.mpr (exp_val_ne_one hs).symm)

  have hinv : IsIntegral ℤ ((N : ℂ) ^ (12 * N * ∑ r : ZMod N, ∑ s : ZMod N, e r s) * (PowerSeries.coeff 0 Pser)⁻¹) := by
    have hpow : (N : ℂ) ^ (12 * N * ∑ r : ZMod N, ∑ s : ZMod N, e r s) = ∏ r : ZMod N, ∏ s : ZMod N, (N : ℂ) ^ k r s := by
      simp only [k, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
    rw [hpow, hPser0, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine IsIntegral.prod _ fun r _ => ?_
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine IsIntegral.prod _ fun s _ => ?_
    rw [← inv_pow, ← mul_pow]
    refine IsIntegral.pow ?_ _
    by_cases h00 : r = 0 ∧ s = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [hc00, inv_one, mul_one]
      exact_mod_cast isIntegral_intCast N
    · exact (hc1 r s h00).2.2.1

  let Cst : ℂ := ∏ r : ZMod N, ∏ s : ZMod N, ρ r s ^ k r s
  have hCst : Cst ^ N = 1 := by
    simp only [Cst, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun r _ => Finset.prod_eq_one fun s _ => ?_
    rw [← pow_mul]
    have heven : Even (k r s * N) := ⟨6 * N * e r s * N, by simp [k]; ring⟩
    simp only [ρ]
    rw [Even.neg_pow heven, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨6 * (e r s : ℤ) * (s.val : ℤ) * ((r.val : ℤ) - N), ?_⟩
    simp only [k]
    push_cast
    field_simp
    ring

  have hE : ∀ r s (τ : UpperHalfPlane), E r τ ^ k r s =
      cexp (2 * π * Complex.I * ((e r s : ℂ) * (6 * ((r.val : ℤ) : ℂ) ^ 2 - 6 * (N : ℂ) * ((r.val : ℤ) : ℂ) + (N : ℂ) ^ 2)) *
        (τ : ℂ) / (N : ℂ)) := by
    intro r s τ
    simp only [E, k, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hρE : ∀ r s (τ : UpperHalfPlane), ρ r s * E r τ ≠ 0 := fun r s τ =>
    mul_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
  have key : ∀ τ : UpperHalfPlane,
      (∏ r : ZMod N, ∏ s : ZMod N, siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
        (Cst * cexp (2 * π * Complex.I *
          ((∑ r : ZMod N, ∑ s : ZMod N,
              (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ))) =
      ∏ r : ZMod N, ∏ s : ZMod N, Q r s τ ^ k r s := by
    intro τ
    have hexp : cexp (2 * π * Complex.I *
          ((∑ r : ZMod N, ∑ s : ZMod N,
              (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ)) =
        ∏ r : ZMod N, ∏ s : ZMod N, E r τ ^ k r s := by
      simp only [hE, ← Complex.exp_sum]
      congr 1
      push_cast
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    rw [hexp]
    simp only [Q, div_pow, mul_pow, Cst, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    rfl

  refine ⟨Cst, fun n => PowerSeries.coeff n Pser, hCst, hPser_int, hd0, hd0_ne, hinv, fun τ => ?_, ?_⟩
  · rw [key τ]
    have := hPser_exp τ
    simpa only [qParam_pow_eq] using this
  · have hfun : (fun τ : UpperHalfPlane =>
        (∏ r : ZMod N, ∏ s : ZMod N, siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
          (Cst * cexp (2 * π * Complex.I *
            ((∑ r : ZMod N, ∑ s : ZMod N,
                (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ)))) =
        fun τ => ∏ r : ZMod N, ∏ s : ZMod N, Q r s τ ^ k r s := funext key
    rw [hfun]
    show Tendsto _ UpperHalfPlane.atImInfty (𝓝 (PowerSeries.coeff 0 Pser))
    rw [hPser0]
    refine tendsto_finset_prod _ fun r _ => tendsto_finset_prod _ fun s _ => ?_
    by_cases h00 : r = 0 ∧ s = 0
    · obtain ⟨rfl, rfl⟩ := h00
      simp only [hk00, pow_zero]
      exact tendsto_const_nhds
    · exact ((hc1 r s h00).2.2.2.2).pow (k r s)

end SExpPi

open ModularCurve in
theorem solution (N : ℕ) [NeZero N]
    (e : ZMod N → ZMod N → ℕ) (he : e 0 0 = 0) :
    ∃ (C : ℂ) (d : ℕ → ℂ), C ^ N = 1 ∧ (∀ n : ℕ, IsIntegral ℤ (d n)) ∧
      d 0 = ∏ s : ZMod N,
        (1 - Complex.exp (2 * Real.pi * Complex.I * (s.val : ℂ) / (N : ℂ))) ^ (12 * N * e 0 s) ∧
      d 0 ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ (12 * N * ∑ r : ZMod N, ∑ s : ZMod N, e r s) * (d 0)⁻¹) ∧
      (∀ τ : UpperHalfPlane,
        HasSum
          (fun n : ℕ => d n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (N : ℂ)))
          ((∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
            (C * Complex.exp (2 * Real.pi * Complex.I *
              ((∑ r : ZMod N, ∑ s : ZMod N,
                  (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ))))) ∧
      Filter.Tendsto
        (fun τ : UpperHalfPlane =>
          (∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
            (C * Complex.exp (2 * Real.pi * Complex.I *
              ((∑ r : ZMod N, ∑ s : ZMod N,
                  (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (N : ℂ))))
        UpperHalfPlane.atImInfty (nhds (d 0)) :=
  SExpPi.main N e he

#print axioms solution

end

end S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow (solution)
