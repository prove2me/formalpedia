-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.coinvariantsKer_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:22.327238+00:00
-- url     : https://prove2.me/submissions/ca59701b-e05d-433d-900b-882f46883476

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {H H' : Subgroup G} (h : H ≤ H') :
    coinvariantsKer ρ H ≤ coinvariantsKer ρ H' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨x, v⟩, rfl⟩
  exact sub_mem_coinvariantsKer (h x.2) v
end GroundTheory.Automorphic.Parabolic
