-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.quotPowBasisSelf_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:50.249993+00:00
-- url     : https://prove2.me/submissions/5c69a77a-224f-4964-b4b5-8bec63a51410

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSMulRegularQuotIffMemNonZeroDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {f : ι → R}
  {A : Type*} [CommRing A] [Algebra A R]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution (h : IsQuasiRegularSeq R f)
    {κ : Type*} (b : Module.Basis κ A (R ⧸ Ideal.span (Set.range f)))
    (r : κ → R) (hr : ∀ j, Ideal.Quotient.mk _ (r j) = b j) (k : ℕ) (p : MonoDegLE ι k × κ) :
    h.quotPowBasisSelf b r hr k p = Ideal.Quotient.mk _ (monoVal f p.1.1 * r p.2) := by
  rw [IsQuasiRegularSeq.quotPowBasisSelf, Module.Basis.map_apply,
    IsQuasiRegularSeq.quotPowBasis_apply, quotSMulTopEquivQuotOver_mk, smul_eq_mul]
end IsQuasiRegularSeq
end GlobalTheory
