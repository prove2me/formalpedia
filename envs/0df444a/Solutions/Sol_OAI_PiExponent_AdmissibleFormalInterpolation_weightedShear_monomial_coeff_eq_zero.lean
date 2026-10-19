-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_monomial_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:21:55.813076+00:00
-- url     : https://prove2.me/submissions/aa4c7776-64b0-447f-b6a8-e98535e0da68

import Mathlib
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators
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

theorem pie_lw_mul {σ : Type*} {φ : (σ →₀ ℕ) → ℝ} (hφ : ∀ x y, φ (x + y) = φ x + φ y)
    {B B' : ℝ} {f g : MvPowerSeries σ ℂ}
    (hf : ∀ b, MvPowerSeries.coeff b f ≠ 0 → B ≤ φ b)
    (hg : ∀ b, MvPowerSeries.coeff b g ≠ 0 → B' ≤ φ b) :
    ∀ b, MvPowerSeries.coeff b (f * g) ≠ 0 → B + B' ≤ φ b := by
  classical
  intro b hb
  rw [MvPowerSeries.coeff_mul] at hb
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, hφ]
  exact add_le_add (hf _ (left_ne_zero_of_mul hne)) (hg _ (right_ne_zero_of_mul hne))

theorem pie_aeval_mono_zero
    {n : ℕ} (w : Fin n → ℝ)
    (F : Fin n → MvPowerSeries (Fin n) ℂ)
    (hF : ∀ (i : Fin n) (α : Fin n →₀ ℕ),
      (∑ j, w j * (α j : ℝ)) < w i →
        MvPowerSeries.coeff α (F i) = 0)
    (a b : Fin n → ℕ)
    (hab : (∑ i, w i * (b i : ℝ)) <
      (∑ i, w i * (a i : ℝ))) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (MvPolynomial.aeval F
        (MvPolynomial.monomial (R := ℂ) (InterpolationMatrix.exponentVector a) 1)) = 0 := by
  classical
  let φ : (Fin n →₀ ℕ) → ℝ := fun α => ∑ j, w j * (α j : ℝ)
  have hφ : ∀ x y, φ (x + y) = φ x + φ y := by
    intro x y; simp only [φ, Finsupp.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  have hFi : ∀ i, ∀ α, MvPowerSeries.coeff α (F i) ≠ 0 → w i ≤ φ α := by
    intro i α hα
    by_contra h
    push Not at h
    exact hα (hF i α h)
  have hpow : ∀ i (k : ℕ), ∀ α, MvPowerSeries.coeff α (F i ^ k) ≠ 0 → (k : ℝ) * w i ≤ φ α := by
    intro i k
    induction k with
    | zero =>
      intro α hα
      rw [pow_zero, MvPowerSeries.coeff_one] at hα
      split_ifs at hα with h
      · subst h; simp [φ]
      · exact absurd rfl hα
    | succ k ih =>
      intro α hα
      rw [pow_succ] at hα
      have := pie_lw_mul hφ ih (hFi i) α hα
      push_cast; linarith
  have hprod : ∀ s : Finset (Fin n), ∀ α,
      MvPowerSeries.coeff α (∏ i ∈ s, F i ^ a i) ≠ 0 → (∑ i ∈ s, (a i : ℝ) * w i) ≤ φ α := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro α hα
      rw [Finset.prod_empty, MvPowerSeries.coeff_one] at hα
      split_ifs at hα with h
      · subst h; simp [φ]
      · exact absurd rfl hα
    | insert x s hx ih =>
      intro α hα
      rw [Finset.prod_insert hx] at hα
      rw [Finset.sum_insert hx]
      exact pie_lw_mul hφ (hpow x (a x)) ih α hα
  by_contra hne
  have hmono : MvPolynomial.aeval F (MvPolynomial.monomial (R := ℂ) (InterpolationMatrix.exponentVector a) 1) =
      ∏ i, F i ^ a i := by
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    rfl
  rw [hmono] at hne
  have := hprod Finset.univ _ hne
  have e1 : φ (InterpolationMatrix.exponentVector b) = ∑ i, w i * (b i : ℝ) := by
    simp [φ, InterpolationMatrix.exponentVector]
  rw [e1] at this
  have e2 : ∑ i, (a i : ℝ) * w i = ∑ i, w i * (a i : ℝ) := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  linarith

theorem pie_gen_ws
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ)
    (L : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hL : ∀ i α,
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i →
        MvPowerSeries.coeff α (L i) = 0) :
    ∀ (i : Fin (m + 1)) (α : Fin (m + 1) →₀ ℕ),
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < Fin.cases v0 u i →
        MvPowerSeries.coeff α
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + L i) i) = 0 := by
  classical
  intro i α hα
  have hsingle : ∀ k : Fin (m + 1), α = Finsupp.single k 1 →
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) = Fin.cases v0 u k := by
    intro k hk
    subst hk
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  induction i using Fin.cases with
  | zero =>
    simp only [Fin.cases_zero, MvPowerSeries.coeff_X]
    split_ifs with h
    · have := hsingle 0 h
      simp only [Fin.cases_zero] at hα this
      linarith
    · rfl
  | succ k =>
    simp only [Fin.cases_succ] at hα ⊢
    rw [map_add, MvPowerSeries.coeff_X, hL k α hα, add_zero]
    split_ifs with h
    · have := hsingle k.succ h
      simp only [Fin.cases_succ] at this
      linarith
    · rfl

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (T : Fin m → ℕ) (delta : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hT : ∀ i, u i ≤ (T i : ℝ) * v0)
    (hdelta : ∀ i (n : ℕ), n < T i → PowerSeries.coeff n (delta i) = 0)
    (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (a : ↥(strictWeightedSimplex (Fin.cases v0 u) H))
    (b : Fin (m + 1) → ℕ)
    (hb : b ∉ strictWeightedSimplex (Fin.cases v0 u) H) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
      (formalShear delta
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector b) 1)) = 0 := by
  classical
  let w : Fin (m + 1) → ℝ := Fin.cases v0 u
  have hwpos : ∀ i, 0 < w i := by
    intro i; induction i using Fin.cases with
    | zero => exact hv0
    | succ k => exact hu k
  -- the lifted tails only have high weight
  have hL : ∀ (i : Fin m) (α : Fin (m + 1) →₀ ℕ),
      (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i →
        MvPowerSeries.coeff α (liftLogSeries m (delta i)) = 0 := by
    intro i α hα
    rw [pie_coeff_lift]
    split_ifs with ht
    · have htail : ∀ j : Fin m, α j.succ = 0 := fun j => by
        have := DFunLike.congr_fun ht j
        simpa [Finsupp.tail, Fin.tail] using this
      apply hdelta i
      by_contra hge
      push Not at hge
      rw [Fin.sum_univ_succ] at hα
      simp only [htail, Nat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero,
        Fin.cases_zero] at hα
      have h1 := hT i
      have h2 : (T i : ℝ) ≤ α 0 := by exact_mod_cast hge
      nlinarith
    · rfl
  have hgen := pie_gen_ws v0 u (fun i => liftLogSeries m (delta i)) hL
  -- weight of b is at least H
  have hbH : H ≤ ∑ i, w i * (b i : ℝ) := by
    by_contra hlt
    push Not at hlt
    apply hb
    simp only [strictWeightedSimplex, realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
      Finset.mem_range]
    refine ⟨⟨fun i => ?_, hlt.le⟩, hlt⟩
    have hsingle : w i * (b i : ℝ) ≤ ∑ j, w j * (b j : ℝ) :=
      Finset.single_le_sum (f := fun j => w j * (b j : ℝ))
        (fun j _ => mul_nonneg (hwpos j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
    have : (b i : ℝ) ≤ H / w i := by
      rw [le_div_iff₀ (hwpos i)]; linarith
    exact Nat.lt_succ_of_le (Nat.le_floor this)
  have haH : ∑ i, w i * ((a.val i : ℕ) : ℝ) < H := by
    have := a.2
    simp only [strictWeightedSimplex, Finset.mem_filter] at this
    exact this.2
  have hab : ∑ i, w i * ((a.val i : ℕ) : ℝ) < ∑ i, w i * (b i : ℝ) := by linarith
  rw [formalShear]
  exact pie_aeval_mono_zero w _ hgen b a.val hab
