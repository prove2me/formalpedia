-- Prove2me | solution 1 for GlobalTheory.RowLev.PlFrame.c_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:42:14.970843+00:00
-- url     : https://prove2.me/submissions/18432ca1-ad8c-4d36-b118-7bdf58202948

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
namespace GlobalTheory.RowLev.PlFrame
theorem _root_.solution (y : I.Lf) :
    fr.c y = 0 ↔ y ∈ extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf) :=
  (fr.c_ker y).trans (Submodule.mem_smul_top_iff _ _ y).symm
end GlobalTheory.RowLev.PlFrame
