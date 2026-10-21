-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.subst_liftLogSeries_of_X_zero
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:15:25.515361+00:00
-- url     : https://prove2.me/submissions/6ddf5adf-7924-4355-9170-def871a4625c

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Equiv

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution {m : ℕ} (F : PowerSeries ℂ)
    (a : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (ha : MvPowerSeries.HasSubst a) (h0 : a 0 = MvPowerSeries.X 0) :
    MvPowerSeries.subst a (liftLogSeries m F) = liftLogSeries m F := by
  have hcoeff : ∀ (D : PowerSeries ℂ) (k : ℕ) (x : Fin m →₀ ℕ),
      MvPowerSeries.coeff (Finsupp.cons k x) (liftLogSeries m D) =
        if x = 0 then PowerSeries.coeff k D else 0 := by
    intro D k x
    have hfin : MvPowerSeries.finSuccEquiv ℂ m (liftLogSeries m D) =
        PowerSeries.map MvPowerSeries.C D := by
      simp [liftLogSeries]
    have h := MvPowerSeries.coeff_coeff_finSuccEquiv (liftLogSeries m D) (k := k) (x := x)
    rw [hfin, PowerSeries.coeff_map, MvPowerSeries.coeff_C] at h
    exact h.symm
  have hcoeff_tail : ∀ (D : PowerSeries ℂ) (α : Fin (m + 1) →₀ ℕ),
      MvPowerSeries.coeff α (liftLogSeries m D) =
        if Finsupp.tail α = 0 then PowerSeries.coeff (α 0) D else 0 := by
    intro D α
    conv_lhs => rw [← Finsupp.cons_tail α]
    exact hcoeff D (α 0) (Finsupp.tail α)
  have key : ∀ (d : Fin (m + 1) →₀ ℕ), (∀ j : Fin m, d j.succ = 0) →
      d = Finsupp.single 0 (d 0) := by
    intro d hd
    ext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      rw [Finsupp.single_apply, hd j, if_neg (fun h => (Fin.succ_ne_zero j) h.symm)]
  -- tail of a single-coordinate vector vanishes
  have htail_single : ∀ t : ℕ, Finsupp.tail (Finsupp.single (0 : Fin (m + 1)) t : Fin (m + 1) →₀ ℕ) = 0 := by
    intro t
    ext j
    rw [Finsupp.tail_apply]
    simp
  -- tail nonzero from a nonzero successor coordinate
  have htail_ne : ∀ d : Fin (m + 1) →₀ ℕ, (∃ j : Fin m, d j.succ ≠ 0) → Finsupp.tail d ≠ 0 := by
    intro d hd h
    obtain ⟨j, hj⟩ := hd
    apply hj
    rw [← Finsupp.tail_apply j d, h]
    simp
  -- product over the support of a single-coordinate vector
  have hprod_single : ∀ (t : ℕ),
      (Finsupp.single (0 : Fin (m + 1)) t).prod (fun s n => a s ^ n) =
        (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) ℂ) ^ t := by
    intro t
    have h1 : (Finsupp.single (0 : Fin (m + 1)) t).prod (fun s n => a s ^ n) = a 0 ^ t := by
      rw [Finsupp.prod_single_index (by simp)]
    rw [h1, h0]
  ext e
  by_cases htail : ∃ j : Fin m, e j.succ ≠ 0
  · have het : Finsupp.tail e ≠ 0 := htail_ne e htail
    rw [hcoeff_tail F e, if_neg het]
    rw [MvPowerSeries.coeff_subst ha]
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    by_cases hd : ∃ j : Fin m, d j.succ ≠ 0
    · rw [hcoeff_tail F d, if_neg (htail_ne d hd), zero_smul]
    · push Not at hd
      have hd' : d = Finsupp.single 0 (d 0) := key d hd
      have hprod : d.prod (fun s n => a s ^ n) =
          (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) ℂ) ^ (d 0) := by
        rw [hd']
        simpa using hprod_single (d 0)
      rw [hprod, MvPowerSeries.coeff_X_pow]
      have hne : e ≠ Finsupp.single (0 : Fin (m + 1)) (d 0) := by
        intro he
        obtain ⟨j, hj⟩ := htail
        rw [he] at hj
        simp at hj
      rw [if_neg hne]
      simp
  · push Not at htail
    have het : Finsupp.tail e = 0 := by
      ext j
      rw [Finsupp.tail_apply]
      exact htail j
    have he' : e = Finsupp.single (0 : Fin (m + 1)) (e 0) := key e htail
    rw [he']
    rw [hcoeff_tail F (Finsupp.single (0 : Fin (m + 1)) (e 0)), if_pos (htail_single (e 0))]
    rw [MvPowerSeries.coeff_subst ha]
    rw [finsum_eq_single _ (Finsupp.single (0 : Fin (m + 1)) (e 0))]
    · rw [hprod_single (e 0), MvPowerSeries.coeff_X_pow]
      rw [hcoeff_tail F (Finsupp.single (0 : Fin (m + 1)) (e 0)), if_pos (htail_single (e 0))]
      simp
    · intro d hd
      by_cases hdt : ∃ j : Fin m, d j.succ ≠ 0
      · rw [hcoeff_tail F d, if_neg (htail_ne d hdt), zero_smul]
      · push Not at hdt
        have hd' : d = Finsupp.single 0 (d 0) := key d hdt
        rw [hd', hprod_single (d 0), MvPowerSeries.coeff_X_pow]
        have hne : (Finsupp.single (0 : Fin (m + 1)) (e 0) : Fin (m + 1) →₀ ℕ) ≠
            Finsupp.single 0 (d 0) := by
          intro heq
          apply hd
          rw [hd', heq]
        rw [if_neg hne]
        simp
