-- Prove2me | solution 1 for Hermite1DimdLEAN.lowAnnulusDegreeWidthBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:40.951005+00:00
-- url     : https://prove2.me/submissions/6085a8a1-2d44-403f-9cc9-009a3639e853

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
private theorem degreeWidth_le_upper_succ
    {d : ℕ} (j : MultiIndex d) (M : ℕ) :
    degreeWidth j M ≤ degreeIntervalUpper j M + 1 := by
  dsimp [degreeWidth]
  omega
private theorem degreeWidth_le_of_coord_bound
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M Y : ℕ) (hY : 0 < Y)
    (hb : ∀ q : Fin d, j q + M + 1 ≤ Y) :
    degreeWidth j M ≤ d * Y ^ 2 := by
  have hupper_sum : degreeIntervalUpper j M ≤ d * (Y ^ 2 - 1) := by
    dsimp [degreeIntervalUpper]
    calc
      ∑ q : Fin d, ((j q + M + 1) ^ 2 - 1)
          ≤ ∑ q : Fin d, (Y ^ 2 - 1) :=
            Finset.sum_le_sum fun q _ => by
              have hsquare : (j q + M + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left (hb q) 2
              omega
      _ = d * (Y ^ 2 - 1) := by simp
  have hA : 1 ≤ Y ^ 2 := Nat.succ_le_of_lt (Nat.pow_pos hY)
  have hfinal : d * (Y ^ 2 - 1) + 1 ≤ d * Y ^ 2 := by
    calc
      d * (Y ^ 2 - 1) + 1 ≤ d * (Y ^ 2 - 1) + d := Nat.add_le_add_left hd _
      _ = d * ((Y ^ 2 - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = d * Y ^ 2 := by rw [Nat.sub_add_cancel hA]
  calc
    degreeWidth j M ≤ degreeIntervalUpper j M + 1 := degreeWidth_le_upper_succ j M
    _ ≤ d * (Y ^ 2 - 1) + 1 := Nat.add_le_add_right hupper_sum 1
    _ ≤ d * Y ^ 2 := hfinal
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
    (_hj : annulusRadius j < M + 1) :
    degreeWidth j M ≤ d * (annulusRadius j + M + 1) ^ 2 :=
  degreeWidth_le_of_coord_bound hd j M (annulusRadius j + M + 1) (by omega)
    (fun q => by have := coord_le_annulusRadius j q; omega)
end Hermite1DimdLEAN
