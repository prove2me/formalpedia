-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.block_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:27.489659+00:00
-- url     : https://prove2.me/submissions/894ebb49-04f9-4ced-a44a-5313b95c88e6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution {α : Type} [Fintype α] [DecidableEq α] {S : Set α} [Fintype S] [DecidableEq S] (g : GL α R)
    (hg : g ∈ stab R S) : IsUnit ((g : Matrix α α R).submatrix (Subtype.val : S → α) Subtype.val).det := by
  have h := sub_mul_of (Subtype.val : S → α) Subtype.val_injective (g : Matrix α α R)
    ((g⁻¹ : GL α R) : Matrix α α R) (fun x y m hm => by
      have hm' : m ∉ S := fun h => hm ⟨⟨m, h⟩, rfl⟩
      rw [(hg m hm' y.1 y.2).2, mul_zero])
  rw [Units.mul_inv, Matrix.submatrix_one _ Subtype.val_injective] at h
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_one, Matrix.det_mul] at h2
  exact isUnit_iff_exists_inv.2 ⟨_, h2.symm⟩
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
