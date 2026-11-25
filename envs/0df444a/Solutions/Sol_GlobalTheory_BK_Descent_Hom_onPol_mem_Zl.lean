-- Prove2me | solution 1 for GlobalTheory.BK.Descent.Hom.onPol_mem_Zl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:44:19.451884+00:00
-- url     : https://prove2.me/submissions/2ca4f892-cd05-4448-a358-64474e6366ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_Descent_Hom_onPol_act
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_mem_PolEta


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
namespace GlobalTheory.BK.Descent.Hom
theorem _root_.solution {η : ℕ} {w : P.Pol} (hw : w ∈ Δ₁.Zl η) : F.onPol w ∈ Δ₂.Zl η :=
  ⟨F.onPol_mem_PolEta hw.1, fun g => by rw [← F.onPol_act, hw.2 g]⟩
end GlobalTheory.BK.Descent.Hom
