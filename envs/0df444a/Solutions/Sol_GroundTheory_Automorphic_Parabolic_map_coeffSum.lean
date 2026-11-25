-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.map_coeffSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:34.080334+00:00
-- url     : https://prove2.me/submissions/7656e795-ad1a-4cc8-9b30-acc9abb3ba30

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
omit hωπ hωρ hω hu
include hπ hsc hKo hf
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {σ : Representation ℂ (GL (Fin n) F) W}
    (p : Representation.IntertwiningMap ρ σ) (w : V) :
    p (coeffSum π ρ K f u w) = coeffSum π σ K f (p u) w := by
  unfold coeffSum quotSum
  rw [← Representation.IntertwiningMap.toLinearMap_apply,
    linearMap_finsum _ (finite_support_coeffSum hπ hsc hKo hf w)]
  refine finsum_congr fun q => ?_
  rw [Representation.IntertwiningMap.toLinearMap_apply, map_smul,
    Representation.IntertwiningMap.isIntertwining]
end GroundTheory.Automorphic.Parabolic
