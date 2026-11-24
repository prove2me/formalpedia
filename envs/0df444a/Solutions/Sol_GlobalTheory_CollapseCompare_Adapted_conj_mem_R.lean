-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.Adapted.conj_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:57.057866+00:00
-- url     : https://prove2.me/submissions/0c70a07a-517e-468b-b113-216401fff80f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
import Theorems.Thm_GlobalTheory_CollapseCompare_Adapted_mem_N
import Theorems.Thm_GlobalTheory_RootEx_Radical_exists_of_mem_R
import Theorems.Thm_GlobalTheory_RootEx_VolN_exists_of_mem_R


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CollapseCompare
namespace Adapted
theorem _root_.solution {t : GL (n ⊕ Fin c) k} (ht : Adapted t) {u : GL (n ⊕ Fin c) k} (hu : u ∈ R k n c 1) :
    t * u * t⁻¹ ∈ R k n c 1 := by
  obtain ⟨x, w, hw, rfl⟩ := VolN.exists_of_mem_R hu
  rw [show t * (embX c x * w) * t⁻¹ = (t * embX c x * t⁻¹) * (t * w * t⁻¹) by group, ht.comm]
  exact mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right (ht.mem_N.2 hw))
end Adapted
end GlobalTheory.CollapseCompare
