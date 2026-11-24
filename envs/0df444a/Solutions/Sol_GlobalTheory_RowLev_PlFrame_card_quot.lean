-- Prove2me | solution 1 for GlobalTheory.RowLev.PlFrame.card_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:36.625466+00:00
-- url     : https://prove2.me/submissions/ad0d2834-c137-420b-b846-177af0dcd9f4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_c_eq_zero_iff

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
theorem _root_.solution :
    Nat.card (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf))) = p ^ N := by
  have hk : (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)).toAddSubgroup = fr.c.toAddMonoidHom.ker :=
    AddSubgroup.ext fun y => (fr.c_eq_zero_iff y).symm
  have e : (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)).toAddSubgroup) ≃ (Fin N → ZMod p) :=
    ((QuotientAddGroup.quotientAddEquivOfEq hk).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective fr.c.toAddMonoidHom fr.c_surj)).toEquiv
  show Nat.card (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf)).toAddSubgroup) = _
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
end GlobalTheory.RowLev.PlFrame
