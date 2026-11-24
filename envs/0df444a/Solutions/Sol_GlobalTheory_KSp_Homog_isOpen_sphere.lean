-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.isOpen_sphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:25:59.268246+00:00
-- url     : https://prove2.me/submissions/7e822c7b-b092-4433-b5a8-55f9971e0a9c

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
theorem _root_.solution {γ : ValueGroupWithZero F} (hγ : γ ≠ 0) :
    IsOpen {y : F | valuation F y = γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun z hz ↦ ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hz hy ⊢
  have : z = y + (z - y) := by ring
  rw [this, (valuation F).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]
end GlobalTheory.KSp.Homog
