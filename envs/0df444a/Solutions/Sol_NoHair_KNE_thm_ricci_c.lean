-- Prove2me | solution 1 for NoHair.KNE.thm_ricci_c
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T08:32:06.662967+00:00
-- url     : https://prove2.me/submissions/057f2242-36cb-4219-adc2-c38ee2eeb1ad

import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci5
import Definitions.Def_NoHair_KerrNewmanEinstein_Ricci6

set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem solution (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    RicS a m e R K1 K2 K3 W 1 3 = RicA a m e R K1 K2 K3 W 1 3 ∧
    RicS a m e R K1 K2 K3 W 2 2 = RicA a m e R K1 K2 K3 W 2 2 ∧
    RicS a m e R K1 K2 K3 W 2 3 = RicA a m e R K1 K2 K3 W 2 3 ∧
    RicS a m e R K1 K2 K3 W 3 3 = RicA a m e R K1 K2 K3 W 3 3 :=
  ⟨NoHair.KNE.ricS_13 a m e R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_22 a m e R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_23 a m e R K1 K2 K3 W hrel hW, NoHair.KNE.ricS_33 a m e R K1 K2 K3 W hrel hW⟩
