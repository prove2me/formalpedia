-- Prove2me | solution 1 for GlobalTheory.HeisenbergGaussianSeries.swap_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:41.52289+00:00
-- url     : https://prove2.me/submissions/fdc3c708-6732-4180-bc5f-20fb2640f701

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.HeisenbergGaussianSeries
namespace GlobalTheory.HeisenbergGaussianSeries
theorem _root_.solution {G : Type} [AddCommGroup G] (β : G → G → ℂ)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (x y : G) : β x y * β y x = 1 := by
  have := hd (x + y)
  rw [hl, hr, hr, hd, hd] at this
  simpa using this
end GlobalTheory.HeisenbergGaussianSeries
