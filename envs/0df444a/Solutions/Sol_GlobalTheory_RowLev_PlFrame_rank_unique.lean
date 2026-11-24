-- Prove2me | solution 1 for GlobalTheory.RowLev.PlFrame.rank_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:56.26064+00:00
-- url     : https://prove2.me/submissions/549235af-c351-4bb2-a69e-558a6ea21db3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_prime
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_card_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.PlFrame
variable {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
include fr
namespace GlobalTheory.RowLev.PlFrame
theorem _root_.solution {N' : ℕ} (fr' : PlFrame I N' p w) : N = N' :=
  Nat.pow_right_injective fr.prime.two_le (fr.card_quot.symm.trans fr'.card_quot)
end GlobalTheory.RowLev.PlFrame
