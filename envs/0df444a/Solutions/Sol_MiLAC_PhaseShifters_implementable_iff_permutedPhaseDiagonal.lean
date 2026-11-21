-- Prove2me | solution 1 for MiLAC.PhaseShifters.implementable_iff_permutedPhaseDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:53.724975+00:00
-- url     : https://prove2.me/submissions/4e544aee-cae7-49c3-b6cd-6f956fc357fb

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
public import Theorems.Thm_MiLAC_PhaseShifters_implementable_if_permutedPhaseDiagonal
public import Theorems.Thm_MiLAC_PhaseShifters_implementable_only_if_permutedPhaseDiagonal

set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.PhaseShifters
namespace MiLAC.PhaseShifters
theorem _root_.solution {n : ℕ} {S : Network n} :
    Implementable S ↔
    ∃ φ : Fin n → ℝ, ∃ σ : Equiv.Perm (Fin n), S = permutedPhaseDiagonal φ σ := by
  constructor
  · exact implementable_only_if_permutedPhaseDiagonal
  · rintro ⟨φ, σ, rfl⟩
    exact implementable_if_permutedPhaseDiagonal φ σ
end MiLAC.PhaseShifters
