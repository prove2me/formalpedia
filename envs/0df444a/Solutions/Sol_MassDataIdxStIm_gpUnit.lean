-- Prove2me | solution 1 for MassDataIdxStIm.gpUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:50.337402+00:00
-- url     : https://prove2.me/submissions/70f0466b-786f-4adc-9419-6af3805226f1

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_LeviEmbeddingBlock32

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open MassDataIdxStIm
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
namespace MassDataIdxStIm
theorem _root_.solution : GP (fun h : Matrix (Fin k) (Fin k) A => IsUnit h.det) where
  one := by simp
  mul := by intro h h' a b; rw [Matrix.det_mul]; exact a.mul b
  inv := by intro h a; exact Matrix.isUnit_nonsing_inv_det h a
  unit := fun a => a
end MassDataIdxStIm
