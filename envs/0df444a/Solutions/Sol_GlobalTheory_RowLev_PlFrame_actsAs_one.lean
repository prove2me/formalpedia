-- Prove2me | solution 1 for GlobalTheory.RowLev.PlFrame.actsAs_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:44:00.055902+00:00
-- url     : https://prove2.me/submissions/a8096afb-e498-4f32-9493-8205458c25be

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
theorem _root_.solution : fr.ActsAs 1 1 := by
  intro y hy
  rw [Matrix.one_mulVec]
  exact congrArg fr.c (Subtype.ext (by
    show I.fmat 1 *ᵥ (y : Fin I.n → _) = (y : Fin I.n → _)
    rw [fmat_one, Matrix.one_mulVec]))
end GlobalTheory.RowLev.PlFrame
