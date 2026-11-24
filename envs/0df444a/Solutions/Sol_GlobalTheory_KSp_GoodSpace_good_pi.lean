-- Prove2me | solution 1 for GlobalTheory.KSp.GoodSpace.good_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:52.981929+00:00
-- url     : https://prove2.me/submissions/c14be3ac-f53b-4b64-bbdf-cb83b04688e5

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactOpenSubgroupExhaustion
import Theorems.Thm_GlobalTheory_KSp_GoodSpace_cball_mono
import Theorems.Thm_GlobalTheory_KSp_GoodSpace_mem_some_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isOpen_box
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.GoodSpace
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.KSp.GoodSpace
theorem _root_.solution (n : Type) [Fintype n] [DecidableEq n] : Good (n → F) := by
  haveI := secondCountable F
  haveI := t2Space F
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro K hK
    obtain ⟨s, hs⟩ := hK.elim_directed_cover (fun s : Fˣ => box n s) (fun s => isOpen_box s)
      (fun x _ => Set.mem_iUnion.mpr (mem_some_box n x)) (by
        intro s t
        rcases le_total (valuation F (s : F)) (valuation F (t : F)) with h | h
        · exact ⟨t, fun x hx i _ => cball_mono h (hx i trivial), le_rfl⟩
        · exact ⟨s, le_rfl, fun x hx i _ => cball_mono h (hx i trivial)⟩)
    exact ⟨boxSub n s, isCompact_box s, isOpen_box s, hs⟩
  · intro U hU
    obtain ⟨s, hs⟩ := exists_box_subset hU
    exact ⟨boxSub n s, isCompact_box s, isOpen_box s, hs⟩
end GlobalTheory.KSp.GoodSpace
