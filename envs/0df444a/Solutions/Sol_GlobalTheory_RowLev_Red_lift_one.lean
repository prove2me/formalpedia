-- Prove2me | solution 1 for GlobalTheory.RowLev.Red.lift_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:06:17.472524+00:00
-- url     : https://prove2.me/submissions/fec1c2ca-e1bb-4393-985c-d312cd0e340d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_Red_lift_of_mem
import Theorems.Thm_GlobalTheory_RowLev_Red_lift_of_notMem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



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
theorem _root_.solution (μf : Measure I.Gf) (x : I.Gf) :
    ρ.lift μf 1 x = (I.Kg g).indicator (fun _ => (((μf (I.Kg g)).toReal : ℂ))⁻¹) x := by
  classical
  by_cases hx : x ∈ I.Kset
  · rw [ρ.lift_of_mem μf _ hx]
    by_cases h : x ∈ I.Kg g
    · rw [Set.indicator_of_mem h, (ρ.ker x hx).2 h]
      simp [MonoidAlgebra.one_def]
    · rw [Set.indicator_of_notMem h]
      have : ρ.toFun x ≠ 1 := fun e => h ((ρ.ker x hx).1 e)
      simp [MonoidAlgebra.one_def, this.symm]
  · rw [ρ.lift_of_notMem μf _ hx, Set.indicator_of_notMem (fun h => hx h.1)]
end GlobalTheory.RowLev.Red
