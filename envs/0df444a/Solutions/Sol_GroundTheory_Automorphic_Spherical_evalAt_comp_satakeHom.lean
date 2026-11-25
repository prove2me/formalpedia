-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.evalAt_comp_satakeHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:32.423911+00:00
-- url     : https://prove2.me/submissions/86b5ff88-6d34-4138-a928-d9c7caf8a17b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalPrincipal
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalLaurent
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra AddMonoidAlgebra
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (w : Fin n → ℂˣ) :
    (evalAt w).comp (satakeHom μ) = sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w) :=
  AlgHom.ext fun h => evalAt_satake w h
end GroundTheory.Automorphic.Spherical
