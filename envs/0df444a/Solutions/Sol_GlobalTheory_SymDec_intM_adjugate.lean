-- Prove2me | solution 1 for GlobalTheory.SymDec.intM_adjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:18:56.665031+00:00
-- url     : https://prove2.me/submissions/567b3389-776d-47aa-9d09-2251d3ed6eba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SymDec
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n k} (h : IntM A) : IntM A.adjugate := by
  let B : Matrix n n 𝒪[k] := fun i j => ⟨A i j, h i j⟩
  have hB : A = (algebraMap 𝒪[k] k).mapMatrix B := by ext i j; rfl
  intro i j
  rw [hB, ← RingHom.map_adjugate]
  exact (B.adjugate i j).2
end GlobalTheory.SymDec
