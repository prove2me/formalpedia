-- Prove2me | solution 1 for NoHair.KNE.thm_maxwell
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T08:33:16.450598+00:00
-- url     : https://prove2.me/submissions/7ea719d8-3b1a-4bb5-ac68-ea53acd19207

import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_KerrNewmanEinstein_MaxwellF
import Definitions.Def_NoHair_KerrNewmanEinstein_MaxwellT

set_option autoImplicit false

open scoped BigOperators
open NoHair NoHair.KNE

theorem solution (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    (∀ μ ν, FS a e R K1 K2 K3 W μ ν = FA a e R K1 K2 K3 W μ ν) ∧
    (∀ α β, ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W α μ * ginvA a m e R K1 K2 K3 W β ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W α β) ∧
    (∑ α, ∑ β, FA a e R K1 K2 K3 W α β * FupA a m e R K1 K2 K3 W α β = FFA a m e R K1 K2 K3 W) ∧
    (∀ μ ν, TS a m e R K1 K2 K3 W μ ν = RicA a m e R K1 K2 K3 W μ ν) :=
  ⟨NoHair.KNE.fS a e R K1 K2 K3 W hrel hW, NoHair.KNE.fU a m e R K1 K2 K3 W hrel hW, NoHair.KNE.fF a m e R K1 K2 K3 W hrel hW, NoHair.KNE.tS a m e R K1 K2 K3 W hrel hW⟩
