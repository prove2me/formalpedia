-- Prove2me | solution 1 for GlobalTheory.SymSupport.exists_int_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:57.527357+00:00
-- url     : https://prove2.me/submissions/19f42f10-c449-43e0-b9d3-d06e07257279

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymSupport
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SymSupport
theorem _root_.solution {U : Matrix n n k} (hU : IntM U) (hd : U.det = 1) : ∃ V, IntM V ∧ U * V = 1 := by
  let U₀ : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨U i j, hU i j⟩
  have e : U = (algebraMap 𝒪[k] k).mapMatrix U₀ := rfl
  refine ⟨U.adjugate, fun i j => ?_, by rw [mul_adjugate, hd, one_smul]⟩
  rw [e, ← RingHom.map_adjugate]
  exact (U₀.adjugate i j).2
end GlobalTheory.SymSupport
