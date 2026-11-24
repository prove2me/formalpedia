-- Prove2me | solution 1 for GlobalTheory.RowLev.Red.lift_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:57.055697+00:00
-- url     : https://prove2.me/submissions/26a59ba7-0aaf-4fe5-8881-19342fe63e11

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_Red_map_inv
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
theorem _root_.solution (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (ha : IsSA a) (x : I.Gf) :
    ρ.lift μf a x⁻¹ = star (ρ.lift μf a x) := by
  by_cases hx : x ∈ I.Kset
  · have hx' : x⁻¹ ∈ I.Kset := (Ksub I).inv_mem hx
    rw [ρ.lift_of_mem μf a hx, ρ.lift_of_mem μf a hx', ρ.map_inv hx, ha]
    simp
  · have hx' : x⁻¹ ∉ I.Kset := fun h => hx (by have := (Ksub I).inv_mem h; rwa [inv_inv] at this)
    rw [ρ.lift_of_notMem μf a hx, ρ.lift_of_notMem μf a hx', star_zero]
end GlobalTheory.RowLev.Red
