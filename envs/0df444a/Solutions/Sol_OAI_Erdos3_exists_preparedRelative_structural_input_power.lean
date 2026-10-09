-- Prove2me | solution 1 for OAI.Erdos3.exists_preparedRelative_structural_input_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T12:09:56.501975+00:00
-- url     : https://prove2.me/submissions/59264530-c9d5-4329-89a3-b0bfe196da58

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem early_preparationCoordinateCap_bound {s m D : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hm : m ≤ s) (hD : (D : ℝ) ≤ p) :
    (preparationCoordinateCap m D (m * D) : ℝ) ≤
      p * ((s : ℝ) * p + 1) ^ s + p + (s : ℝ) * p + 1 := by
  have hT : (m : ℝ) * D ≤ (s : ℝ) * p :=
    mul_le_mul (Nat.cast_le.mpr hm) hD (Nat.cast_nonneg D) (Nat.cast_nonneg s)
  have hpowers : ((m : ℝ) * D + 1) ^ m ≤ ((s : ℝ) * p + 1) ^ s :=
    (pow_le_pow_left₀ (by positivity) (add_le_add hT le_rfl) m).trans
      (pow_le_pow_right₀ (by nlinarith [mul_nonneg (Nat.cast_nonneg s) hp]) hm)
  have hmul := mul_le_mul hD hpowers (by positivity : 0 ≤ ((m : ℝ) * D + 1) ^ m) hp
  simp only [preparationCoordinateCap, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
  linarith

theorem exists_prepared_early_structural_power_budget (s paddingDepth : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ m D nX : ℕ, m ≤ s → (D : ℝ) ≤ p → (nX : ℝ) ≤ p →
        let M := preparationCoordinateCap m D (m * D)
        let q := max m paddingDepth
        let Jalloc := modularInitialBlockCount q (nX + q * M)
        (M : ℝ) + Jalloc + enlargedPreparedCommonSamplerDimension q M Jalloc +
          allocatedUniformChartLog (M : ℝ) ≤ (p + 2) ^ C := by
  classical
  let K := max s paddingDepth
  let A : ℕ := ∑ r : Fin (K + 1),
    (2 ^ r.val * (2 ^ (2 * r.val) * r.val.factorial + 1) + 1)
  let B : ℕ := ∑ r : Fin (K + 1), ∑ j : Fin r.val, preparedCommonBlockCount r.val j
  let Mpoly : Polynomial ℕ :=
    Polynomial.X * (Polynomial.C s * Polynomial.X + 1) ^ s + Polynomial.X +
      Polynomial.C s * Polynomial.X + 1
  let Jpoly : Polynomial ℕ :=
    Polynomial.C A * (Polynomial.X + Polynomial.C K * Mpoly + 11)
  let P : Polynomial ℕ :=
    Mpoly + Jpoly +
      (Polynomial.C ((K + 1) * (K + 3)) + Mpoly * Polynomial.C K * Polynomial.C B +
        Mpoly + Polynomial.C K + 2 +
        (Polynomial.C (K + 2) + Mpoly * Polynomial.C K * Polynomial.C K) * Jpoly) +
      20 * (Mpoly + 1) ^ 3
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp m D nX hm hD hnX
  dsimp only
  let M := preparationCoordinateCap m D (m * D)
  let q := max m paddingDepth
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let Mup := p * ((s : ℝ) * p + 1) ^ s + p + (s : ℝ) * p + 1
  let Jup := (A : ℝ) * (p + (K : ℝ) * Mup + 11)
  have hp0 : 0 ≤ p := by linarith
  have hMup : 0 ≤ Mup := by dsimp [Mup]; positivity
  have hJup : 0 ≤ Jup := by dsimp [Jup]; positivity
  have hq : q ≤ K := max_le_max hm le_rfl
  have hqR : (q : ℝ) ≤ K := Nat.cast_le.mpr hq
  have hA : 2 ^ q * (2 ^ (2 * q) * q.factorial + 1) + 1 ≤ A := by
    exact Finset.single_le_sum
      (f := fun r : Fin (K + 1) =>
        2 ^ r.val * (2 ^ (2 * r.val) * r.val.factorial + 1) + 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨q, Nat.lt_succ_of_le hq⟩)
  have hB : (∑ j : Fin q, preparedCommonBlockCount q j) ≤ B := by
    exact Finset.single_le_sum
      (f := fun r : Fin (K + 1) => ∑ j : Fin r.val, preparedCommonBlockCount r.val j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨q, Nat.lt_succ_of_le hq⟩)
  have hM : (M : ℝ) ≤ Mup := early_preparationCoordinateCap_bound hp0 hm hD
  have hJnat : Jalloc ≤ A * (nX + q * M + 11) :=
    (modularInitialBlockCount_linear_bound q (nX + q * M)).trans
      (Nat.mul_le_mul_right _ hA)
  have hJ : (Jalloc : ℝ) ≤ Jup := by
    have hJreal : (Jalloc : ℝ) ≤ (A : ℝ) * ((nX : ℝ) + (q : ℝ) * M + 11) := by
      exact_mod_cast hJnat
    refine hJreal.trans ?_
    dsimp only [Jup]
    gcongr
  have hdim : (enlargedPreparedCommonSamplerDimension q M Jalloc : ℝ) ≤
      ((K : ℝ) + 1) * (K + 3) + Mup * K * B + Mup + K + 2 +
        (K + 2 + Mup * K * K) * Jup := by
    rw [enlargedPreparedCommonSamplerDimension_polynomial]
    simp only [preparedCommonSamplerDimension, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat]
    have hBR : ((∑ j : Fin q, preparedCommonBlockCount q j : ℕ) : ℝ) ≤ B :=
      Nat.cast_le.mpr hB
    gcongr
  have hchart : allocatedUniformChartLog (M : ℝ) ≤ 20 * (Mup + 1) ^ 3 := by
    unfold allocatedUniformChartLog
    gcongr
  have htotal : Mup + Jup +
      (((K : ℝ) + 1) * (K + 3) + Mup * K * B + Mup + K + 2 +
        (K + 2 + Mup * K * K) * Jup) + 20 * (Mup + 1) ^ 3 ≤ (p + 2) ^ C := by
    simpa [P, Mpoly, Jpoly, Mup, Jup, Polynomial.eval₂_pow,
      Nat.cast_add, Nat.cast_mul] using hbound p hp0
  exact (add_le_add (add_le_add (add_le_add hM hJ) hdim) hchart).trans htotal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeInitializerScalarInputs
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {m s D nX : ℕ}

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

theorem exists_preparedRelative_structural_input_power (s : ℕ) :
    ∃ relativePower : ℕ, 2 ≤ relativePower ∧ ∀ {p : ℝ}, 2 ≤ p →
    ∀ D nX : ℕ, (D : ℝ) ≤ p → (nX : ℝ) ≤ p →
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      let pRelative := (p + 2) ^ relativePower
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative := by
  obtain ⟨C, _, hstruct⟩ := exists_prepared_early_structural_power_budget s s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 2) ^ C + X + Polynomial.C (s + 3) + 2
  obtain ⟨relativePower, hpower, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨relativePower, hpower, ?_⟩
  intro p hp D nX hD hnX M Jalloc dim pRelative
  have hp0 : 0 ≤ p := by linarith
  have hb : (p + 2) ^ C + p + ((s : ℝ) + 3) + 2 ≤ pRelative := by
    simpa [P, X, Polynomial.eval₂_pow, Nat.cast_add] using hbound p hp0
  have hs := hstruct p hp s D nX le_rfl hD hnX
  simp only [max_self] at hs
  change (M : ℝ) + Jalloc + dim + allocatedUniformChartLog (M : ℝ) ≤ (p + 2) ^ C at hs
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hJ : (0 : ℝ) ≤ Jalloc := Nat.cast_nonneg _
  have hdim : (0 : ℝ) ≤ dim := Nat.cast_nonneg _
  have hchart : 0 ≤ allocatedUniformChartLog (M : ℝ) := by
    unfold allocatedUniformChartLog
    positivity
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hC0 : 0 ≤ (p + 2) ^ C := by positivity
  clear_value pRelative M Jalloc dim
  exact ⟨by linarith only [hb, hC0, hs0], by linarith only [hb, hC0, hp0],
    by linarith only [hb, hs, hJ, hdim, hchart, hp0, hs0],
    by linarith only [hb, hs, hM, hdim, hchart, hp0, hs0],
    by linarith only [hb, hs, hM, hJ, hchart, hp0, hs0],
    by linarith only [hb, hs, hM, hJ, hdim, hp0, hs0]⟩

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.exists_preparedRelative_structural_input_power := @OAI.Erdos3.exists_preparedRelative_structural_input_power
