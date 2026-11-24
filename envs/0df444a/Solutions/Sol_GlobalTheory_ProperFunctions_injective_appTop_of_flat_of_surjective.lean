-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.injective_appTop_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:47.53879+00:00
-- url     : https://prove2.me/submissions/817dd4b3-38a1-490b-9947-ac70aa84a6e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (p : X ⟶ S) [IsAffine S] [Flat p] [Surjective p]
    [QuasiCompact p] : Function.Injective p.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
  have : MorphismProperty.ContainsIdentities @Flat.{u} := ⟨fun _ ↦ inferInstance⟩
  obtain ⟨T, i, _, hi, _⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @Flat
  have := ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (i ≫ p)).mp
    ⟨inferInstance, inferInstance⟩).injective
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp] at this
  exact this.of_comp
end GlobalTheory.ProperFunctions
