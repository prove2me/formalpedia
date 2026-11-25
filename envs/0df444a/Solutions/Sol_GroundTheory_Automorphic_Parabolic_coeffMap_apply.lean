-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.coeffMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:49:39.102288+00:00
-- url     : https://prove2.me/submissions/559e84e5-e8c7-4b3e-882e-d34bba3f6b1b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GL (Fin n) F) V) (ρ : Representation ℂ (GL (Fin n) F) U)
variable {π ρ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V} {u : U}
  {ω : GL (Fin n) F → ℂ}
variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hKo : IsOpen (K : Set (GL (Fin n) F)))
  (hωπ : HasCentralChar π ω) (hωρ : HasCentralChar ρ ω)
  (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
  (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hu : u ∈ fixedVectors ρ K)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (w : V) :
    coeffMap hπ hsc hKo hωπ hωρ hω hf hu w = coeffSum π ρ K f u w := rfl
end GroundTheory.Automorphic.Parabolic
