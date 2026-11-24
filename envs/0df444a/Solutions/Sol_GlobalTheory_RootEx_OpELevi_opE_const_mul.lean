-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.opE_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:19.646557+00:00
-- url     : https://prove2.me/submissions/9b20febf-af18-4b9f-bd65-af3e3c67594b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
omit [DecidableEq n] [DecidableEq n'] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [BorelSpace k]
namespace GlobalTheory.RootEx.OpELevi
theorem _root_.solution (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k) (a : ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun x => a * Φ x) x₀ = a * opE ψ ν p Φ x₀ := by
  unfold opE
  rw [← integral_const_mul]
  simp only [mul_assoc]
end GlobalTheory.RootEx.OpELevi
