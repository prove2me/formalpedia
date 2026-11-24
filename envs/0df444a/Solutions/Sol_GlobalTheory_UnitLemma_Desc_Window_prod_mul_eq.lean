-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.prod_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:51:58.421866+00:00
-- url     : https://prove2.me/submissions/1af0687b-4b8e-499b-888f-909068ac300e

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
theorem _root_.solution (a : K.O) (P x : B.A) (k : ℕ) :
    P * (x * algebraMap K.O B.A a ^ (2 * k)) = al K a ^ ((2 * k : ℕ) : ℤ) • (P * x) := by
  rw [zpow_natCast, Algebra.smul_def, IsScalarTower.algebraMap_apply K.O K.E B.A]
  simp only [map_pow]; ring
end GlobalTheory.UnitLemma.Desc.Window
