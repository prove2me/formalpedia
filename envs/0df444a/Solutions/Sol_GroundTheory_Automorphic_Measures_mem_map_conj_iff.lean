-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.mem_map_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:10.408037+00:00
-- url     : https://prove2.me/submissions/c496b8e3-8b09-4c2f-9db2-4bc4e6531109

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution {K : Subgroup G} {g k : G} :
    k ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * k * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
end GroundTheory.Automorphic.Measures
