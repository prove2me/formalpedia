-- Prove2me | solution 1 for GlobalTheory.RankFibre.fibre_omA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:11:36.991674+00:00
-- url     : https://prove2.me/submissions/2daabd9b-0ec6-4945-8a42-0face632ac5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Theorems.Thm_GlobalTheory_SplitFlip_omA_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM
open GlobalTheory GlobalTheory.RankFibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.RankFibre
theorem _root_.solution (ν β : kˣ →* ℂˣ) (a b : ℕ) (h : GL (Fin (a + b)) k) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (x : GL (Fin (a + b)) k) : fibre ν β a b (omA ν β 1 h Φ) x = fibre ν β a b Φ (x * h) := by
  unfold fibre
  congr 1
  funext g
  rw [← omA_mul, one_mul]
end GlobalTheory.RankFibre
