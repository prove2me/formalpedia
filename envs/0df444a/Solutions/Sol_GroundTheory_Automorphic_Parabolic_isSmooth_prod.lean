-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isSmooth_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:03:24.898347+00:00
-- url     : https://prove2.me/submissions/c63e46fa-a093-486c-bf8f-9bed42a5dc0b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingIsotypic

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
open Function Topology
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ : IsSmooth π) (hρ : IsSmooth ρ) : IsSmooth (π.prod ρ) := by
  intro x
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf π x.1 ⊓ stabilizerOf ρ x.2) (fun g hg => ?_)
    ((hπ x.1).inter (hρ x.2))
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hg
  rw [mem_stabilizerOf] at h1 h2 ⊢
  exact Prod.ext h1 h2
end GroundTheory.Automorphic.Parabolic
