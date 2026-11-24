-- Prove2me | solution 1 for GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:52:00.483776+00:00
-- url     : https://prove2.me/submissions/0023a6bc-9d02-4deb-a214-4b109de67de7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Theorems.Thm_GlobalTheory_SchemeDominantSpecMap_appTop_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.SchemeDominantSpecMap
namespace GlobalTheory.SchemeDominantSpecMap
theorem _root_.solution {R A : CommRingCat.{u_1}} (φ : R ⟶ A)
    (h : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    (RingHom.injective_iff_ker_eq_bot (Spec.map φ).appTop.hom).1 (appTop_injective φ h),
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_bot]
end GlobalTheory.SchemeDominantSpecMap
