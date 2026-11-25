-- Prove2me | solution 1 for GroundTheory.Automorphic.Spherical.fixedVectors_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:46.674643+00:00
-- url     : https://prove2.me/submissions/47ec129d-d71b-41a8-bf05-fbd8e5c97524

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
namespace GroundTheory.Automorphic.Spherical
theorem _root_.solution (hχ : IsUnramified χ) :
    fixedVectors (principalSeries F n χ) (integralGL F n) = ℂ ∙ sphericalVector hχ := by
  refine le_antisymm (fun f hf => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    exact ⟨_, (eq_smul_sphericalVector hχ hf).symm⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact sphericalVector_mem_fixedVectors hχ
end GroundTheory.Automorphic.Spherical
