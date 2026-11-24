-- Prove2me | solution 1 for GlobalTheory.ExtUnique.spec_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:17:54.873448+00:00
-- url     : https://prove2.me/submissions/01623e11-6548-4eaa-857f-60d470bb8f47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_GlobalTheory_ExtUnique_isSchemeTheoreticallyDominant_spec_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
namespace GlobalTheory.ExtUnique
theorem _root_.solution (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K] :
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  ⟨inferInstance, isSchemeTheoreticallyDominant_spec_of_injective _ (IsFractionRing.injective R K)⟩
end GlobalTheory.ExtUnique
