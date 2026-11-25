-- Prove2me | solution 1 for GlobalTheory.LGrp.cosetInd_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:43.1239+00:00
-- url     : https://prove2.me/submissions/a4319264-baf5-4b0d-8dce-248e8ce4ea4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.lFactor_zero
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun

set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open ValuativeRel GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable [MeasurableSpace (GL n k)]
variable {μ : Measure (GL n k)} {Ξ : Matrix n n k → ℂ} {c : GL n k → ℂ}
omit [MeasurableSpace (GL n k)]
namespace GlobalTheory.LGrp
theorem _root_.solution (g : GL n k) : cosetInd g ∈ SB (Matrix n n k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have e : {x : GL n k | g⁻¹ * x ∈ KO k n} = (Homeomorph.mulLeft g⁻¹) ⁻¹' (KO k n : Set (GL n k)) := rfl
  have hc : IsCompact (Units.val '' {x : GL n k | g⁻¹ * x ∈ KO k n}) :=
    (e ▸ (Homeomorph.isCompact_preimage _).2 SplitFlip.isCompact_KO).image Units.continuous_val
  have hr : IsOpen (Set.range fun x : GL n k => x.val) := by
    have : (Set.range fun x : GL n k => x.val) = {A | A.det ≠ 0} := by
      ext A
      exact ⟨fun ⟨x, hx⟩ => hx ▸ x.det_ne_zero, fun h => ⟨GeneralLinearGroup.mkOfDetNeZero A h, rfl⟩⟩
    rw [this]
    exact isOpen_ne_fun continuous_id.matrix_det continuous_const
  have ho : IsOpen (Units.val '' {x : GL n k | g⁻¹ * x ∈ KO k n}) :=
    (Topology.IsOpenEmbedding.mk SplitFlip.isEmbedding_val_GL hr).isOpenMap _
      (SplitFlip.isOpen_KO.preimage (continuous_const_mul _))
  exact ⟨(LocallyConstant.charFn ℂ ⟨hc.isClosed, ho⟩).isLocallyConstant,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
end GlobalTheory.LGrp
