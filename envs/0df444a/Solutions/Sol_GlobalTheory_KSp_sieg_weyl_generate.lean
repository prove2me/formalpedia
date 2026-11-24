-- Prove2me | solution 1 for GlobalTheory.KSp.sieg_weyl_generate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:53:06.789948+00:00
-- url     : https://prove2.me/submissions/d84351be-3a3c-4cb1-92a4-dfda71b22f34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsTranslateInCellStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelParabolicWeylElementGenerateUnitary
import Theorems.Thm_GlobalTheory_KSp_mem_of_inCell
import Theorems.Thm_P2M_GlobalTheory_T_exists_translate_inCell__7d37710349e6


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
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))),
    sieg c ν ≤ U → weyl c ν ∈ U → U = ⊤ := by
  intro F _ _ E _ _ c δ hE ν _ _ U hP hw
  classical
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_translate_inCell' F E c δ hE ν {1, g}
  have h1 : u ∈ U := by
    simpa using mem_of_inCell c U hP hw (hu 1 (by simp))
  have h2 : g * u ∈ U := mem_of_inCell c U hP hw (hu g (by simp))
  simpa using U.mul_mem h2 (U.inv_mem h1)
end GlobalTheory.KSp
