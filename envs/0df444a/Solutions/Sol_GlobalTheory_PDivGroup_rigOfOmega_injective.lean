-- Prove2me | solution 1 for GlobalTheory.PDivGroup.rigOfOmega_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:26:10.222174+00:00
-- url     : https://prove2.me/submissions/ab06f891-01bb-4918-904d-adbe5c5cd6a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Theorems.Thm_GlobalTheory_PDivGroup_eq_zero_of_cobOne_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)
namespace GlobalTheory.PDivGroup
theorem _root_.solution [IsDomain O] (hp : (p : O) ≠ 0) :
    Function.Injective G.rigOfOmega := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hw
  have h0 : b = 0 := Subtype.ext (funext fun n => G.eq_zero_of_cobOne_eq_zero hp n
    (congrArg (fun x : G.cocycles × G.omega => x.1.1 n) hb))
  rw [h0, map_zero] at hb
  exact (congrArg Prod.snd hb).symm
end GlobalTheory.PDivGroup
