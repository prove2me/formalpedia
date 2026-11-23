-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:44.079794+00:00
-- url     : https://prove2.me/submissions/11a4b459-8cf6-4bb6-bc25-435eadb0acdb

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
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (g : GL (Fin n) F) :
    quotientEquivLattice F n (g : GL (Fin n) F ⧸ integralGL F n) = g • standard F n :=
  rfl
end GroundTheory.Automorphic.GLnLocal
