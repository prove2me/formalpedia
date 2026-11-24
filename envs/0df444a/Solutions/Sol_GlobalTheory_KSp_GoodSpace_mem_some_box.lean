-- Prove2me | solution 1 for GlobalTheory.KSp.GoodSpace.mem_some_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:39:06.12591+00:00
-- url     : https://prove2.me/submissions/80e748c7-c103-42da-b512-c30d280dbf38

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactOpenSubgroupExhaustion
import Theorems.Thm_GlobalTheory_KSp_GoodSpace_cball_mono
import Theorems.Thm_GlobalTheory_KSp_GoodSpace_mem_some_cball

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
theorem _root_.solution (n : Type) [Fintype n] [DecidableEq n] (x : n → F) : ∃ s : Fˣ, x ∈ box n s := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, fun i => isEmptyElim i⟩
  · choose u hu using fun i => mem_some_cball (x i)
    obtain ⟨j, hj⟩ := Finite.exists_max fun i => valuation F (u i : F)
    exact ⟨u j, fun i _ => cball_mono (hj i) (hu i)⟩
end GlobalTheory.KSp.GoodSpace
