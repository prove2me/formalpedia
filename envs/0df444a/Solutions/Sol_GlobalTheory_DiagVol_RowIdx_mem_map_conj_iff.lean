-- Prove2me | solution 1 for GlobalTheory.DiagVol.RowIdx.mem_map_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:23:48.18864+00:00
-- url     : https://prove2.me/submissions/7453d68b-2397-4b80-83c5-8a60b9fd3752

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.DiagVol GlobalTheory.DiagVol.RowIdx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.DiagVol.RowIdx
theorem _root_.solution (g : GL ι k) (K : Subgroup (GL ι k)) (z : GL ι k) :
    z ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * z * g ∈ K := by
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa [mul_assoc] using hw
  · intro h; exact ⟨_, h, by simp [mul_assoc]⟩
end GlobalTheory.DiagVol.RowIdx
