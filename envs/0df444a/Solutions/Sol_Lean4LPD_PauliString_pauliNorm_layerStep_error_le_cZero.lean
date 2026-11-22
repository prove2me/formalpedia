-- Prove2me | solution 1 for Lean4LPD.PauliString.pauliNorm_layerStep_error_le_cZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:18:51.906573+00:00
-- url     : https://prove2.me/submissions/a2ecb51f-d14b-4162-989a-4aeaae6600eb

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_layerStep_error_le
public import Theorems.Thm_Lean4LPD_PauliString_sum_pauliNorm_discardedLayerStep_le_cZero

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m r : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a A : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a ≤ 1 / 2)
    (hA : 0 ≤ A) (hr : 1 ≤ r) (haA : a ≤ A / (r : ℝ))
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh (m + 1)) O r) ≤
      (cZero (r : ℝ) (m : ℝ) (Γ : ℝ)
          (4 * Real.exp 1 * betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) * Γ * A) ^ (m + 1) *
        (∏ j ∈ range (m + 1), rungW (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) (j + 2)) /
          (Nat.factorial (m + 1) : ℝ) * pauliNorm O :=
  (pauliNorm_layerStep_error_le layers hherm Γ _ O r).trans
    (sum_pauliNorm_discardedLayerStep_le_cZero layers Γ O hΓ hkh hL hherm ha hsin hb hA hr haA hloc)
end Lean4LPD.PauliString
