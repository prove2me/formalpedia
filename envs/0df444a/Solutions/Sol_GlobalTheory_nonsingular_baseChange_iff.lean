-- Prove2me | solution 1 for GlobalTheory.nonsingular_baseChange_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:42.396118+00:00
-- url     : https://prove2.me/submissions/99191d90-d67d-4579-b5ae-4f525b6e483e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Field K] {W : WeierstrassCurve K} [W.IsElliptic]
    {L : Type*} [Field L] [Algebra K L] {x y : L} :
    (W.baseChange L).toAffine.Nonsingular x y ↔ (W.baseChange L).toAffine.Equation x y :=
  haveI : (W.baseChange L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic
  equation_iff_nonsingular.symm
end GlobalTheory
