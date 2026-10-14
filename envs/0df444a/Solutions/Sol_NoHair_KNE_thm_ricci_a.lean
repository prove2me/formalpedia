-- Prove2me | solution 1 for NoHair.KNE.thm_ricci_a
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T08:28:43.44028+00:00
-- url     : https://prove2.me/submissions/a963173e-d1da-4027-9509-795b687a0b85

import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci1
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci2

set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem solution (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    RicS a m e R K1 K2 K3 W 0 0 = RicA a m e R K1 K2 K3 W 0 0 ∧
    RicS a m e R K1 K2 K3 W 0 1 = RicA a m e R K1 K2 K3 W 0 1 ∧
    RicS a m e R K1 K2 K3 W 0 2 = RicA a m e R K1 K2 K3 W 0 2 ∧
    RicS a m e R K1 K2 K3 W 0 3 = RicA a m e R K1 K2 K3 W 0 3 :=
  ⟨NoHair.KNE.ricS_00 a m e R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_01 a m e R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_02 a m e R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_03 a m e R K1 K2 K3 W hrel hW⟩
