-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSamePart.dGL_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:50:29.383947+00:00
-- url     : https://prove2.me/submissions/e085ebe6-1a52-4e8a-a913-ad863c99d38f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSamePart
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
namespace GlobalTheory.CompanionTheory.TyFinSamePart
theorem _root_.solution {s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s')
    (hb : ∀ i j, b' j < b' i → b j ≠ b i) (L : ∀ c, GL {i // b i = c} K) : dGL b L ∈ parab K b' :=
  ⟨show IsBlockUT K b' (bd b fun c => (L c).1) from isBlockUT_bd b b' hb _,
    show IsBlockUT K b' (bd b fun c => ((L c)⁻¹ : GL _ K).1) from isBlockUT_bd b b' hb _⟩
end GlobalTheory.CompanionTheory.TyFinSamePart
