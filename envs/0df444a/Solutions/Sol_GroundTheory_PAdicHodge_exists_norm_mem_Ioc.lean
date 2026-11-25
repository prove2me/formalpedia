-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_norm_mem_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:45.693479+00:00
-- url     : https://prove2.me/submissions/0d699c09-14af-43c1-acf4-dd94c51e7ee1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_mem_Ioc_of_dense

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
open GroundTheory GroundTheory.PAdicHodge
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ x : K, a < ‖x‖ ∧ ‖x‖ ≤ b :=
  exists_norm_mem_Ioc_of_dense (IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p)) ha hab
end GroundTheory.PAdicHodge
