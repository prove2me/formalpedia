-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.pairwise_disjoint_doubleCoset_affineWeylGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:30.244013+00:00
-- url     : https://prove2.me/submissions/bdc03e6b-3cbb-4faa-84a4-8f073cebd86f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_doubleCoset_affineWeylGL_injective

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
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution :
    Pairwise (Function.onFun Disjoint fun w : ExtendedAffineWeyl n =>
      doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n)) := by
  intro w w' hww'
  rw [Function.onFun, Set.disjoint_left]
  intro g hw hw'
  exact hww' (doubleCoset_affineWeylGL_injective F n hw hw')
end GroundTheory.Automorphic.GLnLocal
