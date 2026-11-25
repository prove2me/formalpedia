-- Prove2me | solution 1 for GlobalTheory.BK.BKHom.onPol_Lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:25:27.77316+00:00
-- url     : https://prove2.me/submissions/fe16bd03-0947-46e5-876c-f8af2b4063ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_Hom_app_EN
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
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
open GlobalTheory.BK.BKDat
variable (D : BKDat O K l e a ι η H)
namespace GlobalTheory.BK.BKDat
namespace _root_.GlobalTheory.BK.BKHom
theorem _root_.solution {D : BKDat O K l e a ι η H} {D' : BKDat O K l e a κ η' H'}
    (F : BKHom D D') (w : D.Pol) : F.onPol (D.Lc w) = D'.Lc (F.onPol w) := by
  obtain ⟨y, rfl⟩ := D.Man.mkQ_surjective w
  rw [Lc_cls, Hom.onPol_cls, Hom.onPol_cls, Lc_cls, Hom.app_EN]
end _root_.GlobalTheory.BK.BKHom
end GlobalTheory.BK.BKDat
