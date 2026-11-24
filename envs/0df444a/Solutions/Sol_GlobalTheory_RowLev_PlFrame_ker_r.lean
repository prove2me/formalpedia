-- Prove2me | solution 1 for GlobalTheory.RowLev.PlFrame.ker_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:37.423218+00:00
-- url     : https://prove2.me/submissions/b9911a5f-93a8-4f52-8c1e-9928663f4781

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_Inhab_ker_eq_extId
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_prime

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
namespace GlobalTheory.RowLev.PlFrame
theorem _root_.solution : RingHom.ker fr.r = extId I w.asIdeal := ker_eq_extId fr.prime.ne_zero fr.r fr.r_psi
end GlobalTheory.RowLev.PlFrame
