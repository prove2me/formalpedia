-- Prove2me | solution 1 for GlobalTheory.BK.Descent.Hom.onPol_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:07.682618+00:00
-- url     : https://prove2.me/submissions/963e9534-c8cf-4705-9678-b61ae9eee805

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls



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
theorem _root_.solution (g : TameGal K l e a) (w : P.Pol) :
    F.onPol (Δ₁.actPol g w) = Δ₂.actPol g (F.onPol w) := by
  obtain ⟨y, rfl⟩ := P.Man.mkQ_surjective w
  rw [actPol_cls, BK.Hom.onPol_cls, BK.Hom.onPol_cls, actPol_cls, F.app_act]
end GlobalTheory.BK.Descent.Hom
