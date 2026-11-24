-- Prove2me | solution 1 for GlobalTheory.RowLev.Red.lift_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:45:15.082067+00:00
-- url     : https://prove2.me/submissions/9f6d967d-d691-4a6b-ab80-47ed5871028c

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
theorem _root_.solution (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) {x : I.Gf} (hx : x ∉ I.Kset) :
    ρ.lift μf a x = 0 := by
  unfold Red.lift
  exact if_neg hx
end GlobalTheory.RowLev.Red
