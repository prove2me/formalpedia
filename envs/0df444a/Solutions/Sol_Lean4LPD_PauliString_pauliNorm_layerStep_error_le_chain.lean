-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_layerStep_error_le_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:16:09.956922+00:00
-- url     : https://prove2.me/submissions/f0c813ea-0cee-45e3-ac92-470c3cbd8954

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
public import Theorems.Thm_Lean4LPD_PauliString_sum_pauliNorm_discardedLayerStep_le_chain
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_layerStep_error_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a) (hm : 1 ≤ m)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (r : ℕ) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh m) O r) ≤
      pauliNorm O * ∑ k ∈ range m,
        ((((r : ℝ) + 1) * Γ) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
          chain (epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a)
            (entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) (k + 1) m :=
  (pauliNorm_layerStep_error_le layers hherm Γ _ O r).trans
    (sum_pauliNorm_discardedLayerStep_le_chain layers Γ O hΓ hkh hL hherm ha hsin hm hb hloc r)
end Lean4LPD.PauliString
