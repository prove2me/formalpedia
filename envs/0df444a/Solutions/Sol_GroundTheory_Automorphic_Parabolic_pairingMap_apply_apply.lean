-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.pairingMap_apply_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:32:16.202486+00:00
-- url     : https://prove2.me/submissions/5ae76a14-1204-4ded-b827-303de47c4337

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin n) F) V}
  {ρ : Representation ℂ (GL (Fin n) F) U} {σ : Representation ℂ (GL (Fin n) F) W}
  {ω : GL (Fin n) F → ℂ}
variable {K : Subgroup (GL (Fin n) F)} {ψ : Module.Dual ℂ W} {v : V}
variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω)
  (hωσ : HasCentralChar σ ω) (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
  (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
  (hv : v ∈ fixedVectors π K)
include hπ hsc hωπ hωσ hω hKo hψ hv
omit hπ hsc hωπ hωσ hω hKo hψ hv
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hωπ : HasCentralChar π ω) (hωσ : HasCentralChar σ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
    (hv : v ∈ fixedVectors π K) (hσ : IsSmooth σ) (b : W)
    (ũ : smoothVectors (Representation.dual π)) :
    ((pairingMap hπ hsc hωπ hωσ hω hKo hψ hv hσ b :
      smoothVectors (Representation.dual (contragredient π))) :
        Module.Dual ℂ (smoothVectors (Representation.dual π))) ũ = pairingSum π σ K ψ v b ũ := rfl
end GroundTheory.Automorphic.Parabolic
