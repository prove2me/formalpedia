-- Prove2me | solution 1 for GlobalTheory.SimpleRoots.nodup_roots_of_derivative_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:49:11.712848+00:00
-- url     : https://prove2.me/submissions/c2d55b1e-fca6-49a7-a7e7-76623df48481

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
open GlobalTheory GlobalTheory.SimpleRoots
variable {d : ℕ}
namespace GlobalTheory.SimpleRoots
theorem _root_.solution {P : ℂ[X]} (hP : P ≠ 0)
    (h : ∀ y, P.eval y = 0 → P.derivative.eval y ≠ 0) : P.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro y
  rw [count_roots]
  by_contra hy
  obtain ⟨h1, h2⟩ := (one_lt_rootMultiplicity_iff_isRoot hP).mp (not_le.mp hy)
  exact h y h1 h2
end GlobalTheory.SimpleRoots
