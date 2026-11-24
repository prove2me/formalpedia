-- Prove2me | solution 1 for GlobalTheory.BK.Descent.Hom.app_mem_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:07.005085+00:00
-- url     : https://prove2.me/submissions/5b1858c3-4d8d-4ffc-9f4a-96dea1b6df91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
open GlobalTheory.BK.Descent.Hom
variable {Δ₁ : Descent P} {Δ₂ : Descent Q} {Δ₃ : Descent T} (F : Hom Δ₁ Δ₂)
omit [NeZero e]
namespace GlobalTheory.BK.Descent.Hom
theorem _root_.solution {v : Vec K a ι} (hv : v ∈ Δ₁.inv) : F.app v ∈ Δ₂.inv :=
  fun g => by rw [← F.app_act, hv g]
end GlobalTheory.BK.Descent.Hom
