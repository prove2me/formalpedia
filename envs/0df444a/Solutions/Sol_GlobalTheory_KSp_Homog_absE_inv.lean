-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.absE_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:41.711089+00:00
-- url     : https://prove2.me/submissions/bcf65d7d-eb1f-4b4b-b108-3ed2aab389bc

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Homog
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.KSp.Homog
theorem _root_.solution {x : F} (hx : x ≠ 0) : absE x⁻¹ = (absE x)⁻¹ := by
  simp only [absE, dif_neg hx, dif_neg (inv_ne_zero hx)]
  rw [← ENNReal.coe_inv (distribHaarChar_pos (A := F) (g := Units.mk0 x hx)).ne', ← map_inv]
  congr 3
  ext; simp
end GlobalTheory.KSp.Homog
