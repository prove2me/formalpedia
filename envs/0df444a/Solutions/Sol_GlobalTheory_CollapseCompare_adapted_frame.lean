-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.adapted_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:01.335826+00:00
-- url     : https://prove2.me/submissions/ddc682c8-526a-4bf5-8703-770184497b6a

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
import Theorems.Thm_GlobalTheory_CollapseCompare_frame_conj_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_ConjVol_mem_normalizer_of_tri
import Theorems.Thm_GlobalTheory_RootEx_VolN_val_embX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical (frame)
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CollapseCompare
theorem _root_.solution (b : ℕ → kˣ) : Adapted (frame n c b) := by
  refine ⟨ConjVol.mem_normalizer_of_tri ?_ ?_, fun g => Units.ext ?_⟩
  · rw [show (frame n c b).val = Matrix.diagonal (Sum.elim (fun _ : n => (1 : k))
      (fun i : Fin c => (b (i.val + 1) : k))) from by rw [← Matrix.fromBlocks_diagonal]; rfl]
    exact blockTriangular_diagonal _
  · rw [show ((frame n c b)⁻¹).val = Matrix.diagonal (Sum.elim (fun _ : n => (1 : k))
      (fun i : Fin c => (((b (i.val + 1))⁻¹ : kˣ) : k))) from by rw [← Matrix.fromBlocks_diagonal]; rfl]
    exact blockTriangular_diagonal _
  · ext r s
    rw [frame_conj_apply]
    rcases r with r | r <;> rcases s with s | s <;> simp [VolN.val_embX]
    by_cases h : r = s <;> simp [h]
end GlobalTheory.CollapseCompare
