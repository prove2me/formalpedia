-- Prove2me | solution 1 for GlobalTheory.CompactHowe.weight_fst_eq_mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:32.8698+00:00
-- url     : https://prove2.me/submissions/8eff2056-cffe-4bc3-96e0-e6dacea60bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe
namespace GlobalTheory.CompactHowe
theorem _root_.solution {ι κ : Type} (k : ι × κ →₀ ℕ) :
    Finsupp.weight (fun p : ι × κ => (Finsupp.single p.1 1 : ι →₀ ℕ)) k = Finsupp.mapDomain Prod.fst k := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain]
  refine Finsupp.sum_congr fun p _ => ?_
  simp
end GlobalTheory.CompactHowe
