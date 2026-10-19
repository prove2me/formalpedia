-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:20:04.60839+00:00
-- url     : https://prove2.me/submissions/de27a4fc-d184-4622-9e8d-01e9fe29a964

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
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

/-- Upper bounds on the transverse exponents, with the top case pinning the `X 0` exponent. -/
def pieR {m : ℕ} (c0 : ℕ) (c : Fin m → ℕ) (f : MvPowerSeries (Fin (m + 1)) ℂ) : Prop :=
  ∀ e, MvPowerSeries.coeff e f ≠ 0 → (∀ k, e k.succ ≤ c k) ∧ ((∀ k, e k.succ = c k) → e 0 = c0)

theorem pieR_one {m : ℕ} : pieR (m := m) 0 0 1 := by
  intro e he
  rw [MvPowerSeries.coeff_one] at he
  split_ifs at he with h
  · subst h; simp
  · exact absurd rfl he

theorem pieR_mul {m : ℕ} {c0 d0 : ℕ} {c d : Fin m → ℕ} {f g : MvPowerSeries (Fin (m + 1)) ℂ}
    (hf : pieR c0 c f) (hg : pieR d0 d g) : pieR (c0 + d0) (c + d) (f * g) := by
  classical
  intro e he
  rw [MvPowerSeries.coeff_mul] at he
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  obtain ⟨h1, h1'⟩ := hf x.1 (left_ne_zero_of_mul hne)
  obtain ⟨h2, h2'⟩ := hg x.2 (right_ne_zero_of_mul hne)
  subst hx
  refine ⟨fun k => by simp only [Finsupp.add_apply, Pi.add_apply]; exact Nat.add_le_add (h1 k) (h2 k),
    fun hk => ?_⟩
  have a1 : ∀ k, x.1 k.succ = c k := fun k => by
    have := hk k; simp only [Finsupp.add_apply, Pi.add_apply] at this; have := h1 k; have := h2 k; omega
  have a2 : ∀ k, x.2 k.succ = d k := fun k => by
    have := hk k; simp only [Finsupp.add_apply, Pi.add_apply] at this; have := h1 k; have := h2 k; omega
  simp only [Finsupp.add_apply, h1' a1, h2' a2]

theorem pieR_pow {m : ℕ} {c0 : ℕ} {c : Fin m → ℕ} {f : MvPowerSeries (Fin (m + 1)) ℂ}
    (hf : pieR c0 c f) (n : ℕ) : pieR (n * c0) (n • c) (f ^ n) := by
  induction n with
  | zero => simpa using pieR_one
  | succ n ih =>
    rw [pow_succ, succ_nsmul, Nat.succ_mul]
    exact pieR_mul ih hf

theorem pieR_prod {m : ℕ} {ι : Type*} (s : Finset ι) (c0 : ι → ℕ) (c : ι → Fin m → ℕ)
    (f : ι → MvPowerSeries (Fin (m + 1)) ℂ) (hf : ∀ i ∈ s, pieR (c0 i) (c i) (f i)) :
    pieR (∑ i ∈ s, c0 i) (∑ i ∈ s, c i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pieR_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact pieR_mul (hf a (Finset.mem_insert_self _ _)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a b : Fin (m + 1) → ℕ)
    (hne : InterpolationMatrix.exponentVector a ≠ InterpolationMatrix.exponentVector b)
    (hcoeff : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (formalShear delta (MvPolynomial.monomial (InterpolationMatrix.exponentVector b) 1)) ≠ 0) :
    (∀ k : Fin m, (InterpolationMatrix.exponentVector a) k.succ ≤
      (InterpolationMatrix.exponentVector b) k.succ) ∧
    (∃ k : Fin m, (InterpolationMatrix.exponentVector a) k.succ <
      (InterpolationMatrix.exponentVector b) k.succ) := by
  classical
  have hX0 : pieR (m := m) 1 0 (MvPowerSeries.X 0) := by
    intro e he
    rw [MvPowerSeries.coeff_X] at he
    split_ifs at he with h
    · subst h; simp [Finsupp.single_apply, Fin.succ_ne_zero]
    · exact absurd rfl he
  have hgk : ∀ k : Fin m, pieR 0 (Pi.single k 1)
      (MvPowerSeries.X k.succ + liftLogSeries m (delta k)) := by
    intro k e he
    rw [map_add, pie_coeff_lift, MvPowerSeries.coeff_X] at he
    by_cases h : e = Finsupp.single k.succ 1
    · subst h
      refine ⟨fun j => ?_, fun _ => by simp [Finsupp.single_apply, Fin.succ_ne_zero]⟩
      by_cases hj : j = k
      · subst hj; simp
      · simp [Finsupp.single_apply, Pi.single_apply, hj, Ne.symm hj]
    · rw [if_neg h, zero_add] at he
      split_ifs at he with ht
      · have htail : ∀ j : Fin m, e j.succ = 0 := fun j => by
          have := DFunLike.congr_fun ht j
          simpa [Finsupp.tail, Fin.tail] using this
        refine ⟨fun j => by simp [htail j], fun hall => ?_⟩
        have := hall k
        simp [htail k] at this
      · exact absurd rfl he
  have hshear : formalShear delta (MvPolynomial.monomial (InterpolationMatrix.exponentVector b) 1) =
      MvPowerSeries.X 0 ^ b 0 *
        ∏ k : Fin m, (MvPowerSeries.X k.succ + liftLogSeries m (delta k)) ^ b k.succ := by
    rw [formalShear, MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_succ]
    simp [InterpolationMatrix.exponentVector]
  have hR := pieR_mul (pieR_pow hX0 (b 0))
    (pieR_prod Finset.univ (fun _ => 0) (fun k => b k.succ • Pi.single k 1) _
      (fun k _ => by simpa using pieR_pow (hgk k) (b k.succ)))
  rw [← hshear] at hR
  obtain ⟨h1, h2⟩ := hR _ hcoeff
  have hc : ∀ k : Fin m, ((b 0 • (0 : Fin m → ℕ)) +
      ∑ j : Fin m, b j.succ • (Pi.single j 1 : Fin m → ℕ)) k = b k.succ := by
    intro k
    simp [Finset.sum_apply, Pi.single_apply]
  have hc0 : b 0 * 1 + ∑ _i : Fin m, (0 : ℕ) = b 0 := by simp
  rw [hc0] at h2
  simp only [hc] at h1 h2
  refine ⟨fun k => by simpa [InterpolationMatrix.exponentVector] using h1 k, ?_⟩
  by_contra hno
  push Not at hno
  have heq : ∀ k : Fin m, (InterpolationMatrix.exponentVector a) k.succ = b k.succ := fun k =>
    le_antisymm (by simpa [InterpolationMatrix.exponentVector] using h1 k)
      (by simpa [InterpolationMatrix.exponentVector] using hno k)
  have h0 := h2 heq
  apply hne
  ext i
  induction i using Fin.cases with
  | zero => simpa [InterpolationMatrix.exponentVector] using h0
  | succ k => simpa [InterpolationMatrix.exponentVector] using heq k
