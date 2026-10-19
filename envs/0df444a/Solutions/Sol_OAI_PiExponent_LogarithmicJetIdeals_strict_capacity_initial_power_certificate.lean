-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.strict_capacity_initial_power_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:58:27.556884+00:00
-- url     : https://prove2.me/submissions/03c29bc8-4883-4db1-9c82-6fc69ec0c95d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_capacity_bounded_power_representatives
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_pure_leading_powers_of_bounded_representatives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

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
    ∃ (ρ : ℝ) (a : ℕ) (N : Fin (d.m + 1) → ℕ)
      (o : MonomialOrder (Fin (d.m + 1)))
      (f : Fin (d.m + 1) → MvPolynomial (Fin (d.m + 1)) ℂ),
      0 < ρ ∧ ρ < R ∧ 0 < a ∧
      (∀ i, 0 < N i) ∧
      (∀ i, f i ∈ (simultaneousJetIdeal d.K
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T e) ^ a) ∧
      (∀ i, o.leadingCoeff (f i) = 1) ∧
      (∀ i, o.degree (f i) = Finsupp.single i (N i)) ∧
      (∀ i, (N i : ℝ) *
        InterpolationMatrix.columnWeights d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) i ≤
        (a : ℝ) * ρ) := by
  classical
  let w : Fin (d.m + 1) → ℝ :=
    InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d))
  let I : Ideal (MvPolynomial (Fin (d.m + 1)) ℂ) :=
    simultaneousJetIdeal d.K
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d)) T e
  have hw : ∀ i, 0 < w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 < (d.w0 : ℝ)
      exact d.w0_pos
    · change 0 < MatrixArithmetic.logWeights (finiteDenominators d) j
      have hx : (0 : ℝ) < d.x (j.val + 1) :=
        lt_of_lt_of_le zero_lt_one (d.x_one_le (j.val + 1))
      rw [d.x_log] at hx
      simpa only [MatrixArithmetic.logWeights, finiteDenominators] using hx
  obtain ⟨δ, hδ, hδR, A, hrep⟩ :=
    strict_capacity_bounded_power_representatives
      d R S e T hR hRS he hcommon hcapacity hT
  let ρ : ℝ := (δ + R) / 2
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    linarith
  have hρR : ρ < R := by
    dsimp only [ρ]
    linarith
  have hgap : 0 < ρ - δ := by
    dsimp only [ρ]
    linarith
  let W : ℝ := ∑ i, w i
  obtain ⟨a, ha⟩ := exists_nat_gt (max (A : ℝ) (W / (ρ - δ)))
  have haAreal : (A : ℝ) < (a : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) ha
  have haA : A ≤ a := by
    exact_mod_cast haAreal.le
  have hapos : 0 < a := by
    have haposReal : (0 : ℝ) < (a : ℝ) :=
      lt_of_le_of_lt (Nat.cast_nonneg A) haAreal
    exact_mod_cast haposReal
  have hratio : W / (ρ - δ) < (a : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) ha
  have hlarge : W < (a : ℝ) * (ρ - δ) :=
    (div_lt_iff₀ hgap).mp hratio
  have hbounded : ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
      ∃ Q : MvPolynomial (Fin (d.m + 1)) ℂ,
        P - Q ∈ I ^ a ∧
        ∀ b ∈ Q.support, ∑ i, w i * (b i : ℝ) ≤ (a : ℝ) * δ :=
    hrep a haA
  obtain ⟨N, o, f, hN, hf, hmonic, hdegree, hweight⟩ :=
    pure_leading_powers_of_bounded_representatives
      d.m w hw (I ^ a) ((a : ℝ) * δ)
      (mul_nonneg (Nat.cast_nonneg _) hδ.le) hbounded
  refine ⟨ρ, a, N, o, f, hρ, hρR, hapos, hN, hf, hmonic, hdegree, ?_⟩
  intro i
  change (N i : ℝ) * w i ≤ (a : ℝ) * ρ
  have hwi : w i ≤ W := by
    exact Finset.single_le_sum (fun j _ => (hw j).le) (Finset.mem_univ i)
  calc
    (N i : ℝ) * w i ≤ (a : ℝ) * δ + w i := hweight i
    _ ≤ (a : ℝ) * δ + W := add_le_add (le_refl ((a : ℝ) * δ)) hwi
    _ ≤ (a : ℝ) * δ + (a : ℝ) * (ρ - δ) :=
      add_le_add (le_refl ((a : ℝ) * δ)) hlarge.le
    _ = (a : ℝ) * ρ := by ring
