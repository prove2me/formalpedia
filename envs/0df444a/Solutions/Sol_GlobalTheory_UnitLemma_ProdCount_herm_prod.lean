-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.herm_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:59:00.411785+00:00
-- url     : https://prove2.me/submissions/f46f3ccb-9046-452b-8707-a57589820b36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {K : UQ}
namespace GlobalTheory.UnitLemma.ProdCount
theorem _root_.solution (B₁ B₂ : InvAlg K) (x y z : B₁.A × B₂.A) :
    (B₁.prod B₂).herm x y z = B₁.herm x.1 y.1 z.1 + B₂.herm x.2 y.2 z.2 :=
  Algebra.trace_prod_apply (R := K.E) (S := B₁.A) (T := B₂.A) _
end GlobalTheory.UnitLemma.ProdCount
