-- Prove2me | solution 1 for GlobalTheory.T.finite_continuous_crossed_homomorphisms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:16:58.62166+00:00
-- url     : https://prove2.me/submissions/3d3e4e8f-f519-4d1e-a754-309da11ba783

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteContinuousCrossedHomomorphisms
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteContinuousCrossedHomomorphismsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Cocycles_finite_cocycles


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], Finite A.V → (∀ N : ℕ, {H : Subgroup G | IsOpen (H : Set G) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite) → {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Cocycles.finite_cocycles | exact GlobalTheory.CompanionTheory.Cocycles.finite_cocycles | (intros; apply GlobalTheory.CompanionTheory.Cocycles.finite_cocycles <;> assumption)
end _root_.GlobalTheory.T
