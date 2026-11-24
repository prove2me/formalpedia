-- Prove2me | solution 1 for GlobalTheory.ResidueExtension.exists_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:56:38.352687+00:00
-- url     : https://prove2.me/submissions/6878540b-e670-4be8-8b1e-355f89949e0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open GlobalTheory.ResidueExtension
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
namespace GlobalTheory.ResidueExtension
theorem _root_.solution (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) :
    ∃ r' : AdicCompletion (maximalIdeal O) O →+* Ω,
      r'.comp (algebraMap O _) = r ∧ RingHom.ker r' = maximalIdeal _ := by
  let rb : ResidueField O →+* Ω :=
    Ideal.Quotient.lift (maximalIdeal O) r fun x hx => by rwa [← hr] at hx
  let e := RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective O)
  refine ⟨(rb.comp e.symm.toRingHom).comp (residue _), RingHom.ext fun x => ?_, ?_⟩
  · have : e.symm (residue _ (algebraMap O _ x)) = residue O x := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    change rb (e.symm (residue _ (algebraMap O _ x))) = r x
    rw [this]
    rfl
  · rw [RingHom.ker_comp_of_injective _ (RingHom.injective _), ker_residue]
end GlobalTheory.ResidueExtension
