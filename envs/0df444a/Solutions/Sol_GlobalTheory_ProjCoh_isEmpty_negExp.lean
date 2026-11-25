-- Prove2me | solution 1 for GlobalTheory.ProjCoh.isEmpty_negExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:07:05.050525+00:00
-- url     : https://prove2.me/submissions/fba9b552-b968-4fec-9dc7-94971a0ef52c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.ProjCoh
namespace GlobalTheory.ProjCoh
theorem _root_.solution (N : ℕ) {n : ℤ} (hn : -(N : ℤ) ≤ n) : IsEmpty (NegExp N n) :=
  ⟨fun a => by
    have h := (negExpEquiv N n a).2
    have : 0 ≤ ∑ i, ((negExpEquiv N n a).1 i : ℤ) :=
      Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
    omega⟩
end GlobalTheory.ProjCoh
