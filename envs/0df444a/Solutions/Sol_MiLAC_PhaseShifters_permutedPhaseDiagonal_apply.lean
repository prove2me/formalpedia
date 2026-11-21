-- Prove2me | solution 1 for MiLAC.PhaseShifters.permutedPhaseDiagonal_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:36:29.553793+00:00
-- url     : https://prove2.me/submissions/355bb519-dac3-40eb-8d2f-eed5dabc2aca

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters

set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.PhaseShifters
namespace MiLAC.PhaseShifters
theorem _root_.solution {n : ℕ} (φ : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permutedPhaseDiagonal φ σ i j =
      if σ i = j then Complex.exp (φ (σ i) * Complex.I) else 0 := by
  unfold permutedPhaseDiagonal
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rfl
end MiLAC.PhaseShifters
