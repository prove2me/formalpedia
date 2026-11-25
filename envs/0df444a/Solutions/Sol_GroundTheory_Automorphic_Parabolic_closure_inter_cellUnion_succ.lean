-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.closure_inter_cellUnion_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:17.61492+00:00
-- url     : https://prove2.me/submissions/b29bdf4c-d71d-431d-9e7e-4d8ff81c256f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_cellUnion
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellUnion_succ

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
omit hcov
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (j : Fin k) :
    closure (C j) ∩ cellUnion C ((j : ℕ) + 1) = C j := by
  apply subset_antisymm
  · rintro x ⟨hx, hxu⟩
    obtain ⟨l, hl, hxl⟩ := (mem_cellUnion C).1 hxu
    obtain ⟨l', hjl', hx'⟩ := mem_iUnion₂.1 (hcl j hx)
    have : l' = l := by
      by_contra hne
      exact Set.disjoint_left.1 (hdisj hne) hx' hxl
    subst this
    have : j = l' := Fin.ext (by have : (j : ℕ) ≤ l' := hjl'; omega)
    subst this
    exact hx'
  · intro x hx
    refine ⟨subset_closure hx, ?_⟩
    rw [cellUnion_succ (C := C) j]
    exact Or.inr hx
end GroundTheory.Automorphic.Parabolic
