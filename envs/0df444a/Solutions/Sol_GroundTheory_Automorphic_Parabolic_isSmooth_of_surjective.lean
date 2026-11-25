-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isSmooth_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:30:25.424845+00:00
-- url     : https://prove2.me/submissions/b4ae9447-37e1-4310-aac7-badf2f0eee3e

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
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hρ : IsSmooth ρ) (p : Representation.IntertwiningMap ρ σ)
    (hp : Surjective p) : IsSmooth σ := by
  intro y
  obtain ⟨u, rfl⟩ := hp y
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hρ u)
  rw [mem_stabilizerOf] at hg ⊢
  rw [← Representation.IntertwiningMap.isIntertwining, hg]
end GroundTheory.Automorphic.Parabolic
