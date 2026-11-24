-- Prove2me | solution 1 for GlobalTheory.LatFin.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:46.375723+00:00
-- url     : https://prove2.me/submissions/de5b4534-807f-4c8b-b994-fba2246289f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Theorems.Thm_GlobalTheory_IntegralMultiples_main


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
omit [IsCMField E]
namespace GlobalTheory.LatFin
theorem _root_.solution {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntegralMultiples.main
  | exact _root_.GlobalTheory.IntegralMultiples.main
  | (apply _root_.GlobalTheory.IntegralMultiples.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultiples.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultiples.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultiples.main ..)
end GlobalTheory.LatFin
