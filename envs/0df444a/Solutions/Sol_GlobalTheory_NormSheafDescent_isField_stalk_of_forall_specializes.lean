-- Prove2me | solution 1 for GlobalTheory.NormSheafDescent.isField_stalk_of_forall_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:44:40.51637+00:00
-- url     : https://prove2.me/submissions/b08c7fd4-948e-455c-b651-e2021d0c23fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFieldStalkImageOfGenericPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheafDescent
namespace GlobalTheory.NormSheafDescent
theorem _root_.solution {Z : Scheme.{0}} (ζ : Z) [IsDomain (Z.presheaf.stalk ζ)]
    (h : ∀ z : Z, z ⤳ ζ → z = ζ) : IsField (Z.presheaf.stalk ζ) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  let p : Spec (Z.presheaf.stalk ζ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Z.presheaf.stalk ζ))
  have hp : Z.fromSpecStalk ζ p ∈ Set.range (Z.fromSpecStalk ζ) := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  have h1 : Z.fromSpecStalk ζ p = Z.fromSpecStalk ζ (IsLocalRing.closedPoint _) :=
    (h _ hp).trans Scheme.fromSpecStalk_closedPoint.symm
  have h2 := (Z.fromSpecStalk ζ).isEmbedding.injective h1
  exact (congrArg PrimeSpectrum.asIdeal h2).symm
end GlobalTheory.NormSheafDescent
