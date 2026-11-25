-- Prove2me | solution 1 for GlobalTheory.BK.Descent.vPol_mem_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:07.496234+00:00
-- url     : https://prove2.me/submissions/82eb96f7-98f3-4768-8448-4117c4ffbec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_Descent_mem_Z
import Theorems.Thm_GlobalTheory_BK_Descent_act_X_pow_smul


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
namespace GlobalTheory.BK.Descent
theorem _root_.solution {η : ℕ} {w : P.Pol} (hw : w ∈ Δ.Z η) : P.vPol w ∈ Δ.Z η := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := Δ.mem_Z.1 hw
  refine ⟨⟨_, (P.EM η).smul_mem (uIn (A O K) ^ e) hy, rfl⟩, fun g => ?_⟩
  rw [PhiMod.vPol_cls, actPol_cls, act_X_pow_smul, ← PhiMod.vPol_cls, ← actPol_cls, h g,
    PhiMod.vPol_cls]
end GlobalTheory.BK.Descent
