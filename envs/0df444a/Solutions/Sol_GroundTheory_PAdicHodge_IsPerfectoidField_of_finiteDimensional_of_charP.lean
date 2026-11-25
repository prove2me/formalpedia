-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.of_finiteDimensional_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:16:22.256913+00:00
-- url     : https://prove2.me/submissions/3c1969f3-45a2-48d7-9ace-10d9611a2b5c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCharP
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_of_perfectRing
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_perfectRing


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
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] [CharP K p]
    (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] : IsPerfectoidField L p := by
  have := IsPerfectoidField.completeSpace (K := K) p
  have : CompleteSpace L := FiniteDimensional.complete K L
  have : PerfectRing K p := IsPerfectoidField.perfectRing p
  have : PerfectField K := PerfectRing.toPerfectField K p
  have : PerfectField L := Algebra.IsAlgebraic.perfectField (K := K)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : PerfectRing L p := PerfectField.toPerfectRing p
  refine IsPerfectoidField.of_perfectRing p fun r hr => ?_
  obtain ⟨x, hx1, hx2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r hr
  exact ⟨algebraMap K L x, by rwa [norm_algebraMap'], by rwa [norm_algebraMap']⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
