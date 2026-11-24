-- Prove2me | solution 1 for GlobalTheory.RowLev.PlFrame.prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:01:29.047215+00:00
-- url     : https://prove2.me/submissions/36ab9260-226f-4d7c-800b-7aa53071ec32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_absNorm_eq

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
theorem _root_.solution : p.Prime := by
  have h0 : p ≠ 0 := by
    rw [← fr.absNorm_eq, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  haveI := w.isPrime
  haveI : IsDomain (ZMod p) := fr.residueEquiv.symm.toMulEquiv.isDomain
  exact (CharP.char_is_prime_or_zero (ZMod p) p).resolve_right h0
end GlobalTheory.RowLev.PlFrame
