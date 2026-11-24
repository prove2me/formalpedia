-- Prove2me | solution 1 for GlobalTheory.BK.Descent.plus_act_join
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:11:09.063742+00:00
-- url     : https://prove2.me/submissions/622bd85b-a8ff-4165-b0bd-58c92789b19d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree

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
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a]
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P) (g : TameGal K l e a)
namespace GlobalTheory.BK.Descent
theorem _root_.solution [NeZero e] {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K)))
    (hinv : y ∈ Δ.inv) (v : Vec K a ι) (f : ZMod a → K⟦X⟧) :
    (Δ.plus hy hinv).act g (join v f) = join (Δ.act g v) (ringAct g f) := rfl
end GlobalTheory.BK.Descent
