-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.disjoint_cellUnion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:34:55.984402+00:00
-- url     : https://prove2.me/submissions/f3856012-c845-435c-aac6-3075a6b85f29

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_cellUnion

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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {X : Type*} {k : ℕ} (C : Fin k → Set X)
variable {C}
variable [TopologicalSpace X]
variable (hdisj : Pairwise fun i j => Disjoint (C i) (C j)) (hcov : ∀ x, ∃ l, x ∈ C l)
  (hcl : ∀ j, closure (C j) ⊆ ⋃ l : Fin k, ⋃ (_ : j ≤ l), C l)
include hdisj hcov hcl
omit [TopologicalSpace X] hcov hcl
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (j : Fin k) : Disjoint (C j) (cellUnion C j) := by
  rw [Set.disjoint_left]
  intro x hx hxu
  obtain ⟨l, hl, hxl⟩ := (mem_cellUnion C).1 hxu
  have hne : l ≠ j := fun h => by rw [h] at hl; exact lt_irrefl _ hl
  exact Set.disjoint_left.1 (hdisj hne) hxl hx
end GroundTheory.Automorphic.Parabolic
