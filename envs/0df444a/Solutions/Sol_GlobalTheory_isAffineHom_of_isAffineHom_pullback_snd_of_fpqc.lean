-- Prove2me | solution 1 for GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:34.059831+00:00
-- url     : https://prove2.me/submissions/3031721c-5b06-46f5-8a1e-ca77b18b3398

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsAffineHomOfIsAffineHomPullbackSndOfFpqc
import Theorems.Thm_GlobalTheory_isAffineHom_descendsAlong_fpqc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory
open CategoryTheory Limits AlgebraicGeometry
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (X Y Y' : Scheme.{0}) (f : X ⟶ Y) (g : Y' ⟶ Y), Surjective g → Flat g → QuasiCompact g →
      IsAffineHom (pullback.snd f g) → IsAffineHom f := by
  intro X Y Y' f g hs hf hq h
  haveI := _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc
  exact MorphismProperty.DescendsAlong.of_isPullback (P := @IsAffineHom)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (IsPullback.of_hasPullback f g).flip
    ⟨⟨hs, hf⟩, hq⟩ h
end _root_.GlobalTheory
end GlobalTheory
