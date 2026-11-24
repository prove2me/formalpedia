-- Prove2me | solution 1 for GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:14.432576+00:00
-- url     : https://prove2.me/submissions/533b266c-5d45-4496-a1af-d31109d58280

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
open AlgebraicGeometry CategoryTheory Limits
universe u
namespace GlobalTheory.TangentCrit
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  refine ⟨fun {U} hU {V} hV e => ?_⟩
  have h₁ := f.formallyUnramified_appLE hU hV e
  have h₂ := f.finiteType_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)
end GlobalTheory.TangentCrit
