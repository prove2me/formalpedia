-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:40:20.152102+00:00
-- url     : https://prove2.me/submissions/19599333-f591-47b2-a403-085ef5efeb76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
theorem _root_.solution {E : Type} [Field E] [NumberField E] (s : ℕ) (χ : HChar E) (y : (Af E)ˣ) : lamF s χ y ≠ 0 := by
  have h : 0 < modF y := by
    unfold modF
    refine finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos ?_ _
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.pos_of_ne_zero this
  exact mul_ne_zero (Units.ne_zero _) (by exact_mod_cast (pow_pos h s).ne')
end GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
