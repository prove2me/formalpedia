-- Prove2me | solution 1 for GlobalTheory.CoverSB.exists_isClopen_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:15.457056+00:00
-- url     : https://prove2.me/submissions/85f43803-6543-43dc-999a-6c5930c76edc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnity
import Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_box_subset
import Theorems.Thm_GlobalTheory_LocMod_Inhab_isOpen_box


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CoverSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CoverSB
theorem _root_.solution {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    {U : Set (Matrix A D k)} (hU : IsOpen U) {x : Matrix A D k} (hx : x ∈ U) :
    ∃ V : Set (Matrix A D k), IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  have h0 : (fun y => x + y) ⁻¹' U ∈ 𝓝 (0 : Matrix A D k) := by
    refine (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using hU.mem_nhds hx
  obtain ⟨a, ha⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset h0
  have hBo := GlobalTheory.LocMod.Inhab.isOpen_box (Y := A) (Y' := D) a
  have hBc : IsClosed ((GlobalTheory.LocMod.Inhab.box A D a : AddSubgroup (Matrix A D k)) : Set (Matrix A D k)) :=
    AddSubgroup.isClosed_of_isOpen _ hBo
  refine ⟨(fun y => y - x) ⁻¹' (GlobalTheory.LocMod.Inhab.box A D a : Set (Matrix A D k)),
    ⟨hBc.preimage (continuous_id.sub continuous_const), hBo.preimage (continuous_id.sub continuous_const)⟩,
    by simpa using (GlobalTheory.LocMod.Inhab.box A D a).zero_mem, fun y hy => ?_⟩
  have := ha _ hy
  simpa using this
end GlobalTheory.CoverSB
