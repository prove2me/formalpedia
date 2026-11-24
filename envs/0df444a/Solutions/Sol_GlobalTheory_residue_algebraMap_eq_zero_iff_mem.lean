-- Prove2me | solution 1 for GlobalTheory.residue_algebraMap_eq_zero_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:46.933751+00:00
-- url     : https://prove2.me/submissions/93d7345d-5c89-4656-a132-2d1932cf6887

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationSplitKaehlerDSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GenericResidueLinearIndependence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime R q] (x : A) :
    residue R (algebraMap A R x) = 0 ↔ x ∈ q := by
  rw [residue_eq_zero_iff]
  conv_rhs => rw [← IsLocalization.AtPrime.under_maximalIdeal R q]
  rfl
end GlobalTheory
