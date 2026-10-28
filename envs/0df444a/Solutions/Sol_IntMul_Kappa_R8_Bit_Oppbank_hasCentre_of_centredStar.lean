-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.hasCentre_of_centredStar
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:44:49.060762+00:00
-- url     : https://prove2.me/submissions/1560891c-1f77-42e0-a2e0-b4ea345a4bb6

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCent
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentStarBit
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Cent
open IntMul.Kappa.R8.Bit.Oppbank.CentStarBit
open IntMul.Kappa.R8.Bit.Oppbank.NetFB

private theorem sum_tvQ_Pnd {T : ℕ} (hT : T < 1771) :
    ∑ p : Fin 23, tvQ T p = 3 := by
  have htri : triL T = IntMul.Kappa.R8.Bit.Oppbank.ProjB.tri T := by
    unfold triL IntMul.Kappa.R8.Bit.Oppbank.ProjB.tri ptsL
      IntMul.Kappa.R8.Bit.Oppbank.ProjB.pts
    rfl
  have htv : tvQ T = IntMul.Kappa.R8.Bit.Oppbank.ProjB.tvQ T := by
    funext p
    simp only [tvQ, IntMul.Kappa.R8.Bit.Oppbank.ProjB.tvQ, htri]
  rw [htv]
  exact sum_tvQ hT

theorem solution {sup c : ℕ} (hc : c < 23)
    (h : centredStar sup c = true)
    (hbnd : ∀ i, (sup.testBit i = true) → i < 1771) :
    HasCentre sup := by
  refine ⟨c, hc, fun i hi => ?_⟩
  have hi' := hbnd i hi
  refine ⟨hi', ?_, sum_tvQ_Pnd hi'⟩
  have hland : (sup &&& starC c) = sup := by
    simpa [Nat.land_eq] using centredStar_eq h
  have hbit : ((sup &&& starC c).testBit i = true) := by
    rw [hland]; exact hi
  have hstar : (starC c).testBit i = true := by
    rw [Nat.testBit_land, Bool.and_eq_true] at hbit
    exact hbit.2
  have heq := starC_bit hc ⟨i, hi'⟩
  simpa [Fin.val_mk] using (heq ▸ hstar)
