-- Prove2me | solution 1 for GlobalTheory.DiscrJacobianBlocks.map_eq_zero_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:50.085456+00:00
-- url     : https://prove2.me/submissions/7a4193a6-d5df-4e44-937e-768f9cba9e07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsFactorAssociatedJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.DiscrJacobianBlocks
namespace GlobalTheory.DiscrJacobianBlocks
theorem _root_.solution {O A ι : Type} [CommRing O] [CommRing A] [Algebra O A]
    (e : A →ₐ[O] O) (F : ι → A) (h : ∀ i, e (F i) = 0) {G : A}
    (hG : G ∈ Ideal.span (Set.range F)) : e G = 0 := by
  have : Ideal.span (Set.range F) ≤ RingHom.ker e := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  exact this hG
end GlobalTheory.DiscrJacobianBlocks
