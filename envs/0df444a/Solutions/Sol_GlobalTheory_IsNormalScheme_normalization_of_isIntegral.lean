-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.normalization_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:44.37182+00:00
-- url     : https://prove2.me/submissions/c9d15ac2-adbe-4b62-a224-7a95562aa25d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Theorems.Thm_GlobalTheory_IsNormalScheme_spec_of_isIntegrallyClosedIn_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] IsNormalScheme.isDomain_stalk IsNormalScheme.isIntegrallyClosed_stalk
open GlobalTheory.IsNormalScheme
namespace GlobalTheory.IsNormalScheme
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] [IsNormalScheme X] [IsIntegral X] : IsNormalScheme f.normalization :=
  (iff_of_openCover f.normalizationOpenCover).mpr fun U ↦
    letI := (f.app U.1).hom.toAlgebra
    spec_of_isIntegrallyClosedIn_of_isIntegral (f ⁻¹ᵁ U.1)
      (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
end GlobalTheory.IsNormalScheme
