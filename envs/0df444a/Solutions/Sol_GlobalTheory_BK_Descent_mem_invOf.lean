-- Prove2me | solution 1 for GlobalTheory.BK.Descent.mem_invOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:30:57.032105+00:00
-- url     : https://prove2.me/submissions/52b9edc7-028b-42b5-ae88-acefcef1f7e5

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
variable {P : PhiMod O K l e a ι} (Δ : Descent P)
omit [NeZero e]
namespace GlobalTheory.BK.Descent
theorem _root_.solution {B : Subalgebra O K⟦X⟧} {W : Submodule B (Vec K a ι)} {v : Vec K a ι} :
    v ∈ Δ.invOf W ↔ v ∈ W ∧ ∀ g, Δ.act g v = v := Iff.rfl
end GlobalTheory.BK.Descent
