-- Prove2me | solution 1 for GlobalTheory.RowLev.PlFrame.absNorm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:58.019299+00:00
-- url     : https://prove2.me/submissions/5d2e963d-dfbd-49db-932a-707e3b95fecb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction

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
theorem _root_.solution : Ideal.absNorm w.asIdeal = p := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr fr.residueEquiv.toEquiv, Nat.card_zmod]
end GlobalTheory.RowLev.PlFrame
