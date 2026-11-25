-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.cellUnion_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:34:03.068232+00:00
-- url     : https://prove2.me/submissions/dbe268cb-5a4b-489b-81e0-49c1811c1c9e

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
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {i j : ℕ} (h : i ≤ j) : cellUnion C i ⊆ cellUnion C j := fun x hx => by
  obtain ⟨l, hl, hx⟩ := (mem_cellUnion C).1 hx
  exact (mem_cellUnion C).2 ⟨l, lt_of_lt_of_le hl h, hx⟩
end GroundTheory.Automorphic.Parabolic
