-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.tk_qTriv_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:44:36.123798+00:00
-- url     : https://prove2.me/submissions/ee588639-8632-457d-97dd-25b58fb26b59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Theorems.Thm_GlobalTheory_Ex_NumD_Gt_pow_s


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution {k : ℕ} (p : N.QT k) (z : N.X) : N.tk (N.qTriv k z) p = p.1.2.s z ^ k := by
  rw [← Gt.pow_s, N.mem_QT.1 p.2, io_s, N.τ_symm]
  rfl
end GlobalTheory.Ex.NumD
