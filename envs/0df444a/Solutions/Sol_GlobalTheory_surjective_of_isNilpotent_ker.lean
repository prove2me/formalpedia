-- Prove2me | solution 1 for GlobalTheory.surjective_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:52.104117+00:00
-- url     : https://prove2.me/submissions/f7d3a89a-d09d-4785-94f5-de4059aa2afd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {T₀ T : Scheme.{u}} (i : T₀ ⟶ T) [IsClosedImmersion i]
    (hi : IsNilpotent i.ker) : Surjective i := by
  have : IsDominant i := by
    obtain ⟨n, hn⟩ := hi
    rw [isDominant_iff, denseRange_iff_closure_range, ← i.support_ker,
      ← i.ker.support_pow (n + 1) (by simp), pow_succ, hn]
    simp
  exact surjective_of_isDominant_of_isClosed_range _ i.isClosedEmbedding.isClosed_range
end GlobalTheory
