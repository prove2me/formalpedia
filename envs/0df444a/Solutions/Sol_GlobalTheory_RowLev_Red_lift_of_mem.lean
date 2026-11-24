-- Prove2me | solution 1 for GlobalTheory.RowLev.Red.lift_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:43:17.810801+00:00
-- url     : https://prove2.me/submissions/7bc13884-f2a1-4eb9-9500-346297c85e8e

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
open GlobalTheory.RowLev.Red
variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)
namespace GlobalTheory.RowLev.Red
theorem _root_.solution (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) {x : I.Gf} (hx : x ∈ I.Kset) :
    ρ.lift μf a x = a.coeff (ρ.toFun x) / ((μf (I.Kg g)).toReal : ℂ) := by
  unfold Red.lift
  exact if_pos hx
end GlobalTheory.RowLev.Red
