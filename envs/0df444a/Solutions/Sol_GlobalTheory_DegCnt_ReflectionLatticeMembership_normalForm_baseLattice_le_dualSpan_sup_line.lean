-- Prove2me | solution 1 for GlobalTheory.DegCnt.ReflectionLatticeMembership.normalForm_baseLattice_le_dualSpan_sup_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:44.006289+00:00
-- url     : https://prove2.me/submissions/38d6cd6b-9861-4fea-ae05-e53a238e9bfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ReferenceLatticeMemOfMemInnerSpan
import Theorems.Thm_GlobalTheory_DegCnt_ReflectionLatticeMembership_line_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open Formalism.HermitianLatticeCounting.P
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.ReflectionLatticeMembership
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
namespace GlobalTheory.DegCnt.ReflectionLatticeMembership
theorem _root_.solution : N.P0 ≤ rs (𝓞 K) (Sg N) ⊔ line 1 N.F.z := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le ?_ ?_) le_sup_right) ?_
  · refine iSup_le fun a => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
  · refine iSup_le fun a => iSup_le fun _ => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
  · refine iSup_le fun a => iSup_le fun h => le_sup_of_le_left (line_le ?_)
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, h, rfl⟩)
end GlobalTheory.DegCnt.ReflectionLatticeMembership
