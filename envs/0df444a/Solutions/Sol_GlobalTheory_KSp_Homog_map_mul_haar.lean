-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.map_mul_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:46.216354+00:00
-- url     : https://prove2.me/submissions/2e58f7cf-3892-48f4-8b9d-2fc141aff9ef

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


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
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.KSp.Homog
theorem _root_.solution (lam : Measure F) [lam.IsAddHaarMeasure] {x : F} (hx : x ≠ 0) :
    lam.map (fun y ↦ x * y) = (absE x)⁻¹ • lam := by
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  ext s hs
  rw [Measure.map_apply (measurable_const_mul x) hs, Measure.smul_apply, smul_eq_mul]
  have hset : (fun y ↦ x * y) ⁻¹' s = (Units.mk0 x hx)⁻¹ • s := by
    ext y
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def,
      Units.val_mk0, smul_eq_mul]
  rw [hset, ← distribHaarChar_mul, absE, dif_neg hx, map_inv,
    ENNReal.coe_inv (distribHaarChar_pos (A := F) (g := Units.mk0 x hx)).ne']
end GlobalTheory.KSp.Homog
