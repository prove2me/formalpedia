-- Prove2me | solution 1 for GlobalTheory.GluedOrbit.gluedS_zero_eq_lastPair_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:36:00.357998+00:00
-- url     : https://prove2.me/submissions/39e3af91-6a52-44e3-a20c-8bc82c36783c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiesOnRamOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCases
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LatPair_glue_lat
import Theorems.Thm_GlobalTheory_LevelUnfold_glue_mem_gluedS
import Theorems.Thm_GlobalTheory_LevelUnfold_gluedS_le_iff
import Theorems.Thm_GlobalTheory_LevelUnfold_mem_gluedS
import Theorems.Thm_GlobalTheory_LevelUnfold_mul_inv_q
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)
noncomputable section
open GlobalTheory GlobalTheory.GluedOrbit
open GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration (interX)
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
namespace GlobalTheory.GluedOrbit
theorem _root_.solution (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    gluedS q 1 L 0 = (lastPair q L).lat := by
  change _ = (glue (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last q L)).lat
  rw [glue_lat]
  refine le_antisymm (GlobalTheory.LevelUnfold.gluedS_le_iff.2 ⟨fun y hy => ?_, ?_, fun i hi => absurd hi (by omega)⟩)
    (sup_le (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_))
  · refine Submodule.mem_sup_left (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa [inX] using hy, ?_⟩)
    simp [inX]
  · rw [map_zero, add_zero]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · obtain ⟨h1, h2⟩ := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy
    refine GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨⟨(q.1 : k) * y (Sum.inr 0), mul_mem q.1.2 h2⟩, by simpa using h1,
      fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))
    rw [← mul_assoc, mul_comm q.inv, GlobalTheory.LevelUnfold.mul_inv_q, one_mul]
  · have := GlobalTheory.LevelUnfold.glue_mem_gluedS (q := q) (c := 1) L (0 : n → k)
    rwa [map_zero, add_zero] at this
end GlobalTheory.GluedOrbit
