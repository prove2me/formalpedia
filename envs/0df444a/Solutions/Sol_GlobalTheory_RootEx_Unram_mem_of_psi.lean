-- Prove2me | solution 1 for GlobalTheory.RootEx.Unram.mem_of_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:06.691249+00:00
-- url     : https://prove2.me/submissions/520b6cc8-93cb-4a2e-bc71-9c581c20ba92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open MeasureTheory ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.RootEx.Unram
namespace _root_.GlobalTheory.RootEx.Unram
theorem _root_.solution {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {x : k}
    (hx : ∀ t ∈ 𝒪[k], ψ (t * x) = 1) : x ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff]
  have hmain := (hψ x).mp ?_
  · simpa using hmain
  intro y hy
  by_cases hx0 : x = 0
  · subst hx0
    have hy0 : y = 0 := by simpa using hy
    simp [hy0]
  · have hv : valuation k (y / x) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hy zero_le'
    have hyx := hx (y / x) ((Valuation.mem_integer_iff _ _).mpr hv)
    rwa [div_mul_cancel₀ y hx0] at hyx
end _root_.GlobalTheory.RootEx.Unram
end GlobalTheory.RootEx.Unram
