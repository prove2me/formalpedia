-- Prove2me | solution 1 for Lean4LPD.PauliString.local_flow_k_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:18.097303+00:00
-- url     : https://prove2.me/submissions/4e8c6ed0-f7e4-465d-b907-fcb29f8cd190

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Defs
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Weighted
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ} {G : PauliString n} {p : PauliIndex n} {kh w w' : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution {ko m : ℕ} (hG : IsSelfAdjoint G) (hk : weight G ≤ kh) (hm : 2 ≤ m)
    (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm (rungWeight ko kh m) (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      ≤ highNorm (rungWeight ko kh m) O
        + |Real.sin θ| * highNorm (rungWeight ko kh (m - 1)) O := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  refine highNorm_conj_le_highNorm hG hk ?_ θ O
  rw [show k + 2 - 1 = k + 1 from by omega]
  exact (rungWeight_add_two ko kh k).ge
end Lean4LPD.PauliString
