-- Prove2me | solution 1 for Hermite1DimdLEAN.localDegreeInterval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:10.084418+00:00
-- url     : https://prove2.me/submissions/6841d08e-8dde-4489-a25e-6688cd69525c

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    (∀ n ∈ localDegreeSet j M G, degreeIntervalLower j M ≤ n ∧ n ≤ degreeIntervalUpper j M) ∧
      (localDegreeSet j M G).card ≤ degreeWidth j M := by
  /-
  Scaffolding guidance:
  keep the degree interval explicit and finite; later files need the support
  cardinality as a literal bound on Fourier support length.
  -/
  classical
  have hcoord_bounds :
      ∀ α ∈ localCoeffSet j M G, ∀ q : Fin d,
        (max (j q) M - M) ^ 2 ≤ α q ∧ α q ≤ (j q + M + 1) ^ 2 - 1 := by
    intro α hα q
    have hdist : blockDistance j (blockIndexMulti α) ≤ M := (Finset.mem_filter.mp hα).2
    have hqdist : Nat.dist (j q) (blockIndexMulti α q) ≤ M := by
      have hle : Nat.dist (j q) (blockIndexMulti α q) ≤ blockDistance j (blockIndexMulti α) := by
        dsimp [blockDistance]
        exact Finset.le_sup (s := Finset.univ)
          (f := fun q : Fin d => Nat.dist (j q) (blockIndexMulti α q)) (by simp)
      exact le_trans hle hdist
    have hidx_upper : blockIndexMulti α q ≤ j q + M := by
      have htri : blockIndexMulti α q ≤ j q + Nat.dist (blockIndexMulti α q) (j q) :=
        Nat.dist_tri_right' (blockIndexMulti α q) (j q)
      have hdist' : Nat.dist (blockIndexMulti α q) (j q) ≤ M := by
        simpa [Nat.dist_comm] using hqdist
      exact le_trans htri (Nat.add_le_add_left hdist' _)
    have hidx_lower : j q ≤ blockIndexMulti α q + M := by
      have htri : j q ≤ blockIndexMulti α q + Nat.dist (j q) (blockIndexMulti α q) :=
        Nat.dist_tri_right' (j q) (blockIndexMulti α q)
      exact le_trans htri (Nat.add_le_add_left hqdist _)
    constructor
    · by_cases hjm : j q ≤ M
      · simp [hjm]
      · have hjgt : M < j q := lt_of_not_ge hjm
        have hidx : j q - M ≤ blockIndexMulti α q := by omega
        have hsq : (j q - M) ^ 2 ≤ (blockIndexMulti α q) ^ 2 := by exact Nat.pow_le_pow_left hidx 2
        have hsqrt : (blockIndexMulti α q) ^ 2 ≤ α q := by
          simpa [blockIndexMulti, HermiteLEAN.blockIndex, pow_two] using Nat.sqrt_le' (α q)
        have hle : (j q - M) ^ 2 ≤ α q := hsq.trans hsqrt
        simpa [max_eq_left (le_of_lt hjgt)] using hle
    · have hlt : α q < (blockIndexMulti α q + 1) ^ 2 := by
        simpa [blockIndexMulti, HermiteLEAN.blockIndex, pow_two] using Nat.lt_succ_sqrt' (α q)
      have hmono : (blockIndexMulti α q + 1) ^ 2 ≤ (j q + M + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.succ_le_succ hidx_upper) 2
      omega
  have hsubset :
      localDegreeSet j M G ⊆
        Finset.Icc (degreeIntervalLower j M) (degreeIntervalUpper j M) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨α, hα, rfl⟩
    have hsum_lower : degreeIntervalLower j M ≤ totalDegree α := by
      dsimp [degreeIntervalLower, totalDegree]
      exact Finset.sum_le_sum fun q _ => (hcoord_bounds α hα q).1
    have hsum_upper :
        totalDegree α ≤ ∑ q : Fin d, ((j q + M + 1) ^ 2 - 1) := by
      dsimp [totalDegree]
      exact Finset.sum_le_sum fun q _ => (hcoord_bounds α hα q).2
    have hsum_upper' : totalDegree α ≤ degreeIntervalUpper j M := by
      simpa [degreeIntervalUpper] using hsum_upper
    exact Finset.mem_Icc.mpr ⟨hsum_lower, hsum_upper'⟩
  have hcard :
      (localDegreeSet j M G).card ≤
        (Finset.Icc (degreeIntervalLower j M) (degreeIntervalUpper j M)).card :=
    Finset.card_le_card hsubset
  constructor
  · intro n hn
    exact Finset.mem_Icc.mp (hsubset hn)
  · have hIcc :
      (Finset.Icc (degreeIntervalLower j M) (degreeIntervalUpper j M)).card ≤ degreeWidth j M := by
      dsimp [degreeWidth]
      rw [Nat.card_Icc]
      omega
    exact le_trans hcard hIcc
end Hermite1DimdLEAN
