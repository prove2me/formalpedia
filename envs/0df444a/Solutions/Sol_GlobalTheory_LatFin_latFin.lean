-- Prove2me | solution 1 for GlobalTheory.LatFin.latFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:31:10.672794+00:00
-- url     : https://prove2.me/submissions/7995d2a4-5709-4239-8b2f-b9c213055da3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Theorems.Thm_GlobalTheory_LatFin_finite_vectors
import Theorems.Thm_GlobalTheory_LatFin_finite_automorphisms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LatFin
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LatFin
theorem _root_.solution : ((∀ (r : ℕ) (X : Data E r) (R : ℝ), {v : Fin r → E | v ∈ X.Λ ∧ ∀ (τ : X.Ψ) (a : Fin r), ‖τ.1 (v a)‖ ≤ R}.Finite) ∧ (∀ (r : ℕ) (X : Data E r) (R : ℝ), {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r), ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite)) :=
  ⟨finite_vectors, finite_automorphisms⟩
end GlobalTheory.LatFin
