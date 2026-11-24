-- Prove2me | solution 1 for Hermite1DimdLEAN.highAnnulusDegreeBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:20.222246+00:00
-- url     : https://prove2.me/submissions/25e793b6-8b85-4dbc-b705-0c59731be0ec

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private theorem coord_le_annulusRadius {d : ℕ} (j : MultiIndex d) (q : Fin d) :
    j q ≤ annulusRadius j :=
  Finset.le_sup (s := Finset.univ) (f := fun q : Fin d => j q) (Finset.mem_univ q)
private theorem annulusRadius_exists_coord
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) :
    ∃ q : Fin d, j q = annulusRadius j := by
  let q1 : Fin d := ⟨0, hd⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨q1, by simp⟩
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup
      (s := (Finset.univ : Finset (Fin d))) hne (f := fun q : Fin d => j q)
  exact ⟨q, hq.symm⟩
private theorem highAnnulusDegreeLowerBound
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : M + 1 ≤ annulusRadius j) :
    (annulusRadius j - M) ^ 2 ≤ degreeIntervalLower j M := by
  rcases annulusRadius_exists_coord (hd := hd) (j := j) with ⟨q0, hq0⟩
  have hsq : (max (annulusRadius j) M - M) ^ 2 = (annulusRadius j - M) ^ 2 := by
    rw [max_eq_left (by omega : M ≤ annulusRadius j)]
  dsimp [degreeIntervalLower]
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun q : Fin d => (max (j q) M - M) ^ 2) (by simp : q0 ∈ Finset.univ)]
  simp_all
private theorem coordGapEqInt
    (n M : ℕ) (hMn : M ≤ n) :
    (((((n + M + 1) ^ 2 - 1) - (n - M) ^ 2 + 1 : ℕ) : ℤ)) =
      (2 * M + 1) * (2 * n + 1) := by
  have h1 : 1 ≤ (n + M + 1) ^ 2 := by exact Nat.succ_le_of_lt (Nat.pow_pos (by omega))
  have h2 : (n - M) ^ 2 ≤ (n + M + 1) ^ 2 - 1 := by
    have hklt : n - M < n + M + 1 := by omega
    have hsq : (n - M) ^ 2 < (n + M + 1) ^ 2 := Nat.pow_lt_pow_left hklt (by decide : 2 ≠ 0)
    omega
  rw [Nat.cast_add, Int.ofNat_sub h2, Int.ofNat_sub h1]
  push_cast
  rw [Int.ofNat_sub hMn]
  ring_nf
private theorem coordGapMainLe
    (n M R : ℕ) (hMn : M ≤ n) (hnR : n ≤ R) :
    ((n + M + 1) ^ 2 - 1) - (n - M) ^ 2 + 1 ≤ (2 * M + 1) * (2 * R + 1) := by
  have hz :
      (((((n + M + 1) ^ 2 - 1) - (n - M) ^ 2 + 1 : ℕ) : ℤ)) ≤
        (2 * M + 1) * (2 * R + 1) := by
    rw [coordGapEqInt n M hMn]
    exact_mod_cast Nat.mul_le_mul_left (2 * M + 1) (by omega : 2 * n + 1 ≤ 2 * R + 1)
  exact_mod_cast hz
private theorem coordGapLe
    (n M R : ℕ) (hnR : n ≤ R) (hMR : M + 1 ≤ R) :
    ((n + M + 1) ^ 2 - 1) - (max n M - M) ^ 2 ≤ (2 * M + 1) * (2 * R + 1) := by
  by_cases h : n ≤ M
  · simp only [max_eq_right h, tsub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, tsub_zero, tsub_le_iff_right]
    have hsq : (n + M + 1) ^ 2 ≤ (2 * M + 1) ^ 2 := by
      refine Nat.pow_le_pow_left ?_ 2
      omega
    have hmul : (2 * M + 1) ^ 2 ≤ (2 * M + 1) * (2 * R + 1) := by
      simpa [pow_two] using
        Nat.mul_le_mul_left (2 * M + 1) (by omega : 2 * M + 1 ≤ 2 * R + 1)
    omega
  · have hMn : M ≤ n := by omega
    rw [max_eq_left hMn]
    have hmain := coordGapMainLe n M R hMn hnR
    exact le_trans (by omega) hmain
private theorem degreeWidth_eq_gap_sum
    {d : ℕ} (j : MultiIndex d) (M : ℕ) :
    degreeWidth j M =
      (∑ q : Fin d, (((j q + M + 1) ^ 2 - 1) - (max (j q) M - M) ^ 2)) + 1 := by
  dsimp [degreeWidth, degreeIntervalUpper, degreeIntervalLower]
  have hfg :
      ∀ x ∈ (Finset.univ : Finset (Fin d)),
        (max (j x) M - M) ^ 2 ≤ ((j x + M + 1) ^ 2 - 1) := by
    intro x hx
    by_cases h : j x ≤ M
    · simp [max_eq_right h]
    · have hMx : M ≤ j x := by omega
      rw [max_eq_left hMx]
      have hklt : j x - M < j x + M + 1 := by omega
      have hsq : (j x - M) ^ 2 < (j x + M + 1) ^ 2 := Nat.pow_lt_pow_left hklt (by decide : 2 ≠ 0)
      omega
  have hdistrib :
      (∑ q : Fin d, (((j q + M + 1) ^ 2 - 1) - (max (j q) M - M) ^ 2)) =
        (∑ q : Fin d, ((j q + M + 1) ^ 2 - 1)) -
          (∑ q : Fin d, (max (j q) M - M) ^ 2) := by
    simpa using
      (Finset.sum_tsub_distrib (s := Finset.univ)
        (f := fun q : Fin d => ((j q + M + 1) ^ 2 - 1))
        (g := fun q : Fin d => (max (j q) M - M) ^ 2) hfg)
  rw [hdistrib]
end Hermite1DimdLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : M + 1 ≤ annulusRadius j) :
    (annulusRadius j - M) ^ 2 ≤ degreeIntervalLower j M ∧
      degreeWidth j M ≤ d * (2 * M + 1) * (2 * annulusRadius j + 1) := by
  let R := annulusRadius j
  let C := (2 * M + 1) * (2 * R + 1)
  have hMR : M + 1 ≤ R := by exact hj
  have hlower : (annulusRadius j - M) ^ 2 ≤ degreeIntervalLower j M :=
    highAnnulusDegreeLowerBound (hd := hd) (j := j) (M := M) hj
  rcases annulusRadius_exists_coord (hd := hd) (j := j) with ⟨q0, hq0⟩
  have hR : ∀ q : Fin d, j q ≤ R := fun q => coord_le_annulusRadius j q
  let gap : Fin d → ℕ := fun q =>
    (((j q + M + 1) ^ 2 - 1) - (max (j q) M - M) ^ 2)
  let gap' : Fin d → ℕ := fun q => if q = q0 then gap q + 1 else gap q
  have hgap'_eq : (∑ q : Fin d, gap' q) = (∑ q : Fin d, gap q) + 1 := by
    classical
    calc
      (∑ q : Fin d, gap' q)
          = ∑ q : Fin d, (gap q + if q = q0 then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              by_cases h : q = q0 <;> simp [gap', h]
      _ = (∑ q : Fin d, gap q) + ∑ q : Fin d, (if q = q0 then 1 else 0) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ q : Fin d, gap q) + 1 := by
            simp_all
  have hpointwise : ∀ q : Fin d, gap' q ≤ C := by
    intro q
    by_cases hqq : q = q0
    · subst hqq
      dsimp [gap', gap]
      rw [if_pos rfl, hq0, max_eq_left (by omega : M ≤ R)]
      exact coordGapMainLe R M R (by omega) le_rfl
    · dsimp [gap', gap]
      rw [if_neg hqq]
      exact coordGapLe (j q) M R (hR q) hMR
  have hwidth : degreeWidth j M ≤ d * C := by
    rw [degreeWidth_eq_gap_sum, ← hgap'_eq]
    calc
      (∑ q : Fin d, gap' q) ≤ ∑ q : Fin d, C := by exact Finset.sum_le_sum fun q _ => hpointwise q
      _ = d * C := by simp
  exact ⟨hlower, by simpa [C, R, Nat.mul_assoc] using hwidth⟩
end Hermite1DimdLEAN
