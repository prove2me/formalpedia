-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.transvection_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:50.14003+00:00
-- url     : https://prove2.me/submissions/44df513a-8ba0-4ed0-9246-6246a954ae44

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice

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
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {i j : Fin n} {c : F} (hc : c ∈ 𝒪[F]) (a b : Fin n) :
    Matrix.transvection i j c a b ∈ 𝒪[F] := by
  rw [Matrix.transvection, Matrix.add_apply]
  refine Subring.add_mem _ ?_ ?_
  · rw [Matrix.one_apply]
    split_ifs <;> simp
  · rw [Matrix.single_apply]
    split_ifs
    · exact hc
    · exact Subring.zero_mem _
end GroundTheory.Automorphic.GLnLocal
