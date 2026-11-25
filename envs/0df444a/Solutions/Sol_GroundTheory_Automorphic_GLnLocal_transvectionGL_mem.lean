-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.transvectionGL_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:57:52.900312+00:00
-- url     : https://prove2.me/submissions/8779fd85-5c26-4677-b460-968b2e47fbb3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_transvection_mem_integer

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
theorem _root_.solution {i j : Fin n} (hij : i ≠ j) : transvectionGL F n hij ∈ integralGL F n :=
  (mem_integralGL_iff F n).mpr ⟨transvection_mem_integer F n (Subring.one_mem _),
    transvection_mem_integer F n (Subring.neg_mem _ (Subring.one_mem _))⟩
end GroundTheory.Automorphic.GLnLocal
