-- Prove2me | solution 1 for GlobalTheory.Mem.Capelli.adjoin_gelfA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:33:43.858855+00:00
-- url     : https://prove2.me/submissions/e730e247-66d1-4762-a3ef-0b1522783446

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq
import Theorems.Thm_GlobalTheory_SmoothForms_gelfA_eq_sum_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
namespace GlobalTheory.Mem.Capelli
theorem _root_.solution (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA E)) = trAlg (Matrix.of E) := by
  rw [trAlg]
  congr 2
  funext k
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]
  rfl
end GlobalTheory.Mem.Capelli
