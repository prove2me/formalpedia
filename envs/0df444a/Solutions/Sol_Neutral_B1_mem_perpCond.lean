-- Prove2me | solution 1 for Neutral.B1.mem_perpCond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:52:03.16236+00:00
-- url     : https://prove2.me/submissions/6367d1a1-04bb-40e8-9016-caaa6d936bcb

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]
variable {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ)
namespace Neutral.B1
theorem _root_.solution {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    (phi : ∀ i, D i →* Γ) (hrho : ∀ i, ContAction (rho.comp (phi i)))
    (L : ∀ i, Submodule R (H1 (rho.comp (phi i)))) (i : I) (y : H1 ((twDual χ rho).comp (phi i))) :
    y ∈ perpCond χ rho phi hrho L i ↔ ∀ x ∈ L i, cupH1H1TwistedDual χ rho (phi i) (hrho i) y x = 0 := by
  simp [perpCond, Submodule.mem_iInf]
end Neutral.B1
