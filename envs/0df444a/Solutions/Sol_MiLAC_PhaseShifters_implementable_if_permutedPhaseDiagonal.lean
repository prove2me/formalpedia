-- Prove2me | solution 1 for MiLAC.PhaseShifters.implementable_if_permutedPhaseDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:55.417689+00:00
-- url     : https://prove2.me/submissions/48a5e9d4-9067-4e8b-bcfe-bdf9587fd684

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
public import Theorems.Thm_MiLAC_PhaseShifters_implementable_if_phaseDiagonal


set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.PhaseShifters
namespace MiLAC.PhaseShifters
theorem _root_.solution {n : ℕ}
    (φ : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    Implementable (permutedPhaseDiagonal φ σ) := by
  change Implementable (series (phaseDiagonal φ) (permutationNetwork σ))
  exact Implementable.series
    (implementable_if_phaseDiagonal φ)
    (Implementable.pn σ)
end MiLAC.PhaseShifters
