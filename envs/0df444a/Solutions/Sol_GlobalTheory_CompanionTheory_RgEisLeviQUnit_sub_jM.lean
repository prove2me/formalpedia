-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.sub_jM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:23.963533+00:00
-- url     : https://prove2.me/submissions/26b5eae3-237d-4983-96ff-0aafa30bae97

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_sub_eq

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
variable {α κ β : Type} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution {e : κ → α} (he : Function.Injective e) (m : Matrix κ κ R) :
    (jM e m).submatrix e e = m := by
  rw [sub_eq]
  unfold jM
  have : (Pm R e)ᵀ * (Pm R e * m * (Pm R e)ᵀ + Dm R e) * Pm R e =
      ((Pm R e)ᵀ * Pm R e) * m * ((Pm R e)ᵀ * Pm R e) + (Pm R e)ᵀ * Dm R e * Pm R e := by
    rw [Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
  rw [this, Pmt_Pm he, Pmt_Dm]
  simp
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
