-- Prove2me | solution 1 for GlobalTheory.BK.Descent.mem_Zl_of_mem_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:33:18.488562+00:00
-- url     : https://prove2.me/submissions/b55e32c4-045b-490e-98dd-7882500c62ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_PhiMod_cls_mem_PolEta


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
theorem _root_.solution {η : ℕ} {w : P.Pol} (hw : w ∈ Δ.Z η) : w ∈ Δ.Zl η := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := hw
  exact ⟨P.cls_mem_PolEta hy, h⟩
end GlobalTheory.BK.Descent
