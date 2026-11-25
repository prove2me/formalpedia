-- Prove2me | solution 1 for GlobalTheory.IdealChain.nabs_det_eq_of_act_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:32.584577+00:00
-- url     : https://prove2.me/submissions/c0d04bc2-e57d-405c-b235-052ce4702549

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Theorems.Thm_GlobalTheory_IdealChain_exists_act_stdLat
import Theorems.Thm_GlobalTheory_IdealChain_act_stdLat_eq_iff
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_iff
import Theorems.Thm_GlobalTheory_StepData_valuation_det_of_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IdealChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
namespace GlobalTheory.IdealChain
theorem _root_.solution {g h : GL ι k} {L : Submodule 𝒪[k] (ι → k)} (hL : L.IsLattice k)
    (e : act g L = act h L) :
    nabs k (Matrix.GeneralLinearGroup.det g) = nabs k (Matrix.GeneralLinearGroup.det h) := by
  obtain ⟨u, rfl⟩ := exists_act_stdLat hL
  have h1 : act ((h * u)⁻¹ * (g * u)) (stdLat k ι) = stdLat k ι := by
    rw [act_mul, act_mul g, e, ← act_mul h, ← act_mul, inv_mul_cancel, act_one]
  have h2 := valuation_det_of_mem_KO (act_stdLat_eq_iff.1 h1)
  rw [nabs_eq_iff]
  have : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h *
      Matrix.GeneralLinearGroup.det ((h * u)⁻¹ * (g * u)) := by
    simp only [map_mul, map_inv]
    rw [_root_.mul_inv_rev, mul_comm (Matrix.GeneralLinearGroup.det g)]
    group
    rw [mul_comm (Matrix.GeneralLinearGroup.det h)]
    group
  rw [this, Units.val_mul, map_mul, h2, mul_one]
end GlobalTheory.IdealChain
