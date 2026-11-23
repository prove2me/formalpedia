-- Prove2me | solution 1 for MassDataIdxStIm.gpUni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:13.706447+00:00
-- url     : https://prove2.me/submissions/94d371f4-2966-4a0a-9a90-3b4822b03dd1

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
theorem _root_.solution : GP (IsUpUni : Matrix (Fin k) (Fin k) A → Prop) where
  one := isUpUni_one A
  mul := fun a b => isUpUni_mul A a b
  inv := fun a => isUpUni_inv A a
  unit := by intro h a; rw [isUpUni_det A a]; exact isUnit_one
end MassDataIdxStIm
