-- Prove2me | solution 1 for GlobalTheory.ProjModFinIso.projective_of_isTorsionFree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:32.678806+00:00
-- url     : https://prove2.me/submissions/8dde6537-acbf-4767-b909-eb4cf8b44bcd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModFinIso
theorem _root_.solution (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Projective R M :=
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  Module.Flat.projective_of_finitePresentation
end GlobalTheory.ProjModFinIso
