-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isIso_morphismRestrict_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:05.40828+00:00
-- url     : https://prove2.me/submissions/429290a9-3d27-4927-a088-32842d375f39

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
universe u
noncomputable section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {U U' : Y.Opens} (h : U' ≤ U) [IsIso (f ∣_ U)] :
    IsIso (f ∣_ U') := by
  have h1 : IsPullback (f ∣_ U') (f ⁻¹ᵁ U').ι U'.ι f := isPullback_morphismRestrict f U'
  have h2 : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := isPullback_morphismRestrict f U
  have hU : Y.homOfLE h ≫ U.ι = U'.ι := Y.homOfLE_ι h
  have hX : X.homOfLE (f.preimage_mono h) ≫ (f ⁻¹ᵁ U).ι = (f ⁻¹ᵁ U').ι := X.homOfLE_ι _
  have hsq : X.homOfLE (f.preimage_mono h) ≫ f ∣_ U = f ∣_ U' ≫ Y.homOfLE h := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, Category.assoc, hU,
      morphismRestrict_ι, ← Category.assoc, hX]
  have h3 : IsPullback (X.homOfLE (f.preimage_mono h)) (f ∣_ U') (f ∣_ U) (Y.homOfLE h) := by
    refine IsPullback.of_right ?_ hsq h2.flip
    rw [hX, hU]
    exact h1.flip
  exact h3.isIso_snd_of_isIso
end GroundTheory.Arith.SchemeCoh
