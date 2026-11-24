-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.zpow_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:52:00.009829+00:00
-- url     : https://prove2.me/submissions/2f1b478f-94cb-4532-bec7-e20155225771

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution (a : K.O) (n : ℤ) (hn : 0 ≤ n) (y : B.A) :
    al K a ^ n • y = algebraMap K.O B.A (a ^ n.toNat) * y := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [zpow_natCast, Int.toNat_natCast, Algebra.smul_def, IsScalarTower.algebraMap_apply K.O K.E B.A]
  simp only [map_pow]
end GlobalTheory.UnitLemma.Desc.Window
