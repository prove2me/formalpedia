-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_produces_weighted_monic_relations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T21:58:43.396385+00:00
-- url     : https://prove2.me/submissions/2c20c82c-fce9-4616-9a3d-ce4aaf81e517
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_power_membership_iff_polynomialJet_coefficients
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_eventual_polynomialJet_interpolation
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FunProp

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

private theorem smaller_strict_capacity (n : ℕ) {R S : ℝ}
    (hR : 0 < R) (hc : S ^ n < 2 * R ^ n) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ S ^ n < 2 * r ^ n := by
  have hopen : IsOpen ({x : ℝ | 0 < x} ∩ {x : ℝ | S ^ n < 2 * x ^ n}) :=
    isOpen_Ioi.inter (isOpen_lt continuous_const (by fun_prop))
  obtain ⟨l, u, ⟨hlR, hRu⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds ⟨hR, hc⟩)
  obtain ⟨r, hlr, hrR⟩ := exists_between hlR
  have hr := hsub ⟨hlr, hrR.trans hRu⟩
  exact ⟨r, hr.1, hrR, hr.2⟩

theorem solution
    {nu : ℝ} (d : FixedData nu) (R S : ℝ)
    (e : Fin (d.m + 1) → ℕ) (T : Fin d.m → ℕ)
    (hR : 0 < R) (hRS : R < S)
    (he : ∀ i, 0 < e i)
    (hcommon : ∀ i, S = (e i : ℝ) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (hcapacity : 2 * R ^ (d.m + 1 : ℕ) > S ^ (d.m + 1 : ℕ))
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ <
      (T i : ℝ) * (d.v0 : ℝ)) :
    ∃ k : ℕ, 0 < k ∧
      ∃ a : ℝ, 0 < a ∧ a < R ∧
        ∃ b : Fin (d.m + 1) → ℕ, (∀ i, 0 < b i) ∧
          ∃ F : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) ℂ,
            (∀ i, F i ∈
              (simultaneousJetIdeal d.K
                (MatrixArithmetic.rationalCenters (finiteNumerators d)
                  (finiteDenominators d)) T e) ^ k) ∧
            (∀ i, InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                (b i : ℝ) ≤ (k : ℝ) * a) ∧
            (∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
              (∑ j, InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) j *
                (u j : ℝ)) <
              InterpolationMatrix.columnWeights d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) i *
                (b i : ℝ)) := by
  classical
  obtain ⟨r, hr, hrR, hrcap⟩ :=
    smaller_strict_capacity (d.m + 1) hR hcapacity
  obtain ⟨N, hinterp⟩ :=
    strict_capacity_eventual_polynomialJet_interpolation d r S e T hr
      (hrR.trans hRS) he hcommon hrcap hT
  let w : Fin (d.m + 1) → ℝ :=
    InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d))
  have hw : ∀ i, 0 < w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 < (d.w0 : ℝ)
      exact d.w0_pos
    · change 0 < (Nat.ceil (Real.log (d.q j.val)) : ℝ)
      have hq : (1 : ℝ) < (d.q j.val : ℝ) := by
        have hq' : 1 < d.q j.val := lt_of_lt_of_le (by norm_num) (d.approximations j.val).1
        exact_mod_cast hq'
      exact (Real.log_pos hq).trans_le (Nat.le_ceil _)
  have hcenters : ∃ i, MatrixArithmetic.rationalCenters
      (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
    let i : Fin d.m := ⟨0, lt_of_lt_of_le (by norm_num) d.m_pos⟩
    refine ⟨i, ?_⟩
    have hp : (d.p i.val : ℂ) ≠ 0 := by
      exact_mod_cast (d.approximations i.val).2.1
    have hq' : d.q i.val ≠ 0 := by
      have hq := (d.approximations i.val).1
      omega
    have hq : (d.q i.val : ℂ) ≠ 0 := by exact_mod_cast hq'
    change 2 * Complex.I * (d.p i.val : ℂ) / (d.q i.val : ℂ) ≠ 0
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
  let a : ℝ := (r + R) / 2
  have hra : r < a := by dsimp [a]; linarith
  have haR : a < R := by dsimp [a]; linarith
  have ha : 0 < a := hr.trans hra
  have hgap : 0 < a - r := sub_pos.mpr hra
  let C : ℝ := ∑ i, w i
  obtain ⟨k, hk⟩ := exists_nat_gt (max (N : ℝ) (max 0 (C / (a - r))))
  have hkN' : (N : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
  have hkN : N ≤ k := by exact_mod_cast hkN'.le
  have hkrest : max 0 (C / (a - r)) < (k : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hk
  have hkpos' : 0 < (k : ℝ) := lt_of_le_of_lt (le_max_left _ _) hkrest
  have hkpos : 0 < k := by exact_mod_cast hkpos'
  have hkC : C / (a - r) < (k : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hkrest
  have hCk : C < (k : ℝ) * (a - r) := (div_lt_iff₀ hgap).mp hkC
  have hwi : ∀ i, w i < (k : ℝ) * (a - r) := by
    intro i
    have hi : w i ≤ C :=
      Finset.single_le_sum (fun j _ => (hw j).le) (Finset.mem_univ i)
    exact hi.trans_lt hCk
  let b : Fin (d.m + 1) → ℕ := fun i => Nat.floor ((k : ℝ) * r / w i) + 1
  have hbpos : ∀ i, 0 < b i := by
    intro i
    dsimp [b]
    omega
  have hblower : ∀ i, (k : ℝ) * r < w i * (b i : ℝ) := by
    intro i
    have hi : (k : ℝ) * r / w i < (b i : ℝ) := by
      simpa [b] using Nat.lt_floor_add_one ((k : ℝ) * r / w i)
    simpa [mul_comm] using (div_lt_iff₀ (hw i)).mp hi
  have hbupper : ∀ i, w i * (b i : ℝ) ≤ (k : ℝ) * a := by
    intro i
    have hf : (Nat.floor ((k : ℝ) * r / w i) : ℝ) ≤ (k : ℝ) * r / w i :=
      Nat.floor_le (div_nonneg (mul_nonneg hkpos'.le hr.le) (hw i).le)
    have hf' : w i * (Nat.floor ((k : ℝ) * r / w i) : ℝ) ≤ (k : ℝ) * r := by
      simpa [mul_comm] using (le_div_iff₀ (hw i)).mp hf
    have hbi : (b i : ℝ) = (Nat.floor ((k : ℝ) * r / w i) : ℝ) + 1 := by simp [b]
    rw [hbi, mul_add, mul_one]
    nlinarith [hwi i]
  have hQ : ∀ i : Fin (d.m + 1),
      ∃ Q : MvPolynomial (Fin (d.m + 1)) ℂ,
        (∀ u ∈ Q.support, (∑ j, w j * (u j : ℝ)) ≤ (k : ℝ) * r) ∧
        (∀ j : Fin d.K, ∀ u : Fin (d.m + 1) →₀ ℕ,
          (∑ l, u l / e l) < k →
            MvPolynomial.coeff u
              (polynomialJet (fun l => (j.val : ℂ) *
                MatrixArithmetic.rationalCenters (finiteNumerators d)
                  (finiteDenominators d) l) T Q) =
            MvPolynomial.coeff u
              (polynomialJet (fun l => (j.val : ℂ) *
                MatrixArithmetic.rationalCenters (finiteNumerators d)
                  (finiteDenominators d) l) T (MvPolynomial.X i ^ b i))) := by
    intro i
    exact hinterp k hkN (fun j u => MvPolynomial.coeff u
      (polynomialJet (fun l => (j.val : ℂ) *
        MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) l) T (MvPolynomial.X i ^ b i)))
  choose Q hQweight hQcoeff using hQ
  let F : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) ℂ :=
    fun i => MvPolynomial.X i ^ b i - Q i
  refine ⟨k, hkpos, a, ha, haR, b, hbpos, F, ?_, hbupper, ?_⟩
  · intro i
    apply (power_membership_iff_polynomialJet_coefficients d.K
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      T e hcenters he k (F i)).2
    intro j u hu
    dsimp only [F]
    rw [map_sub, MvPolynomial.coeff_sub, hQcoeff i j u hu, sub_self]
  · intro i u hu
    have hrem : MvPolynomial.X i ^ b i - F i = Q i := by
      dsimp [F]
      ring
    rw [hrem] at hu
    exact (hQweight i u hu).trans_lt (hblower i)
