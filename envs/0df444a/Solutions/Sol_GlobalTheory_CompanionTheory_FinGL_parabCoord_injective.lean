-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.parabCoord_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:31:28.380359+00:00
-- url     : https://prove2.me/submissions/150625ef-c0aa-4aa0-8ba6-d58c7b84b2ab

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGL
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
namespace GlobalTheory.CompanionTheory.FinGL
theorem _root_.solution : Function.Injective (parabCoord K b) := by
  intro x y h
  have h1 := congrFun (congrArg Prod.fst h)
  have h2 := fun c => congrArg (fun g : GL {i // b i = c} K => (g : Matrix {i // b i = c} {i // b i = c} K))
    (congrFun (congrArg Prod.snd h) c)
  apply Subtype.ext
  apply Units.ext
  ext i j
  rcases lt_trichotomy (b i) (b j) with hij | hij | hij
  · exact h1 ⟨(i, j), hij⟩
  · exact congrFun (congrFun (h2 (b j)) ⟨i, hij⟩) ⟨j, rfl⟩
  · rw [x.2.1 i j hij, y.2.1 i j hij]
end GlobalTheory.CompanionTheory.FinGL
