-- Prove2me | solution 1 for GlobalTheory.FinEt.isSplitOfRank_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:10.008986+00:00
-- url     : https://prove2.me/submissions/a7f44791-7294-4085-a3a7-494835d5e463

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
theorem _root_.solution {X S : Scheme.{u}} (p : X ⟶ S) :
    IsSplitOfRank p 0 ↔ IsEmpty X := by
  rw [isSplitOfRank_iff]
  constructor
  · rintro ⟨s, -, -, hx⟩
    exact ⟨fun x ↦ (hx x).exists.choose.elim0⟩
  · intro h
    exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun x ↦ h.elim x⟩
end GlobalTheory.FinEt
