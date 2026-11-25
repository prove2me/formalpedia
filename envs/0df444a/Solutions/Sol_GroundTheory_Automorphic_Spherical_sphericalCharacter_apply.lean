-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.sphericalCharacter_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:55:20.533107+00:00
-- url     : https://prove2.me/submissions/f3272857-c09d-4151-a89b-15d608f98173

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalCommutative
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalPrincipal

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
open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {χ : levi F n (id : Fin n → Fin n) →* ℂ}
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (hχ : IsUnramified χ) (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalCharacter μ hχ h = sphericalEigen χ μ h := rfl
end GroundTheory.Automorphic.Spherical
