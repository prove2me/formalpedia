-- Prove2me | solution 1 for GlobalTheory.T.induced_scalar_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:18:41.86667+00:00
-- url     : https://prove2.me/submissions/8e1dad36-7602-43ec-85d8-32275c62d691

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InducedScalarIrreducible
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InducedScalarIrreducibleStatement
import Theorems.Thm_GlobalTheory_RankFibre_indScal_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M := by
  first | exact @GlobalTheory.RankFibre.indScal_irreducible | exact GlobalTheory.RankFibre.indScal_irreducible | (intros; apply GlobalTheory.RankFibre.indScal_irreducible <;> assumption)
end _root_.GlobalTheory.T
