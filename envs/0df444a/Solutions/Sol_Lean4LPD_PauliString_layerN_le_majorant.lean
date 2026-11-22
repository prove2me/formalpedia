-- Prove2me | solution 1 for Lean4LPD.PauliString.layerN_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:03:34.182409+00:00
-- url     : https://prove2.me/submissions/3efacc22-b8e0-4e1d-8945-3e3fc15f5c51

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Theorems.Thm_Lean4LPD_epsJump_nonneg_all
public import Theorems.Thm_Lean4LPD_MultiLadder_le_majorant


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((Ls T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ Ls T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ Ls T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (T m : ℕ) (hm : 1 ≤ m) :
    layerN Ls S O ko kh m T ≤ MultiLadder.majorant
      (epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a)
      (entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) (pauliNorm O) m T := by
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  exact (pauliMultiLadder Ls S O hkh hL hherm ha hsin hb hloc).le_majorant
    (epsJump_nonneg_all hkh1 (div_nonneg (Nat.cast_nonneg _) hkh1.le) ha) T m hm
end Lean4LPD.PauliString
