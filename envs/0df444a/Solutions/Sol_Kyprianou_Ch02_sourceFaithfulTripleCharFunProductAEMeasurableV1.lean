-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulTripleCharFunProductAEMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:13:44.475809+00:00
-- url     : https://prove2.me/submissions/c2564d49-c513-4a22-923d-b46ce485fc96

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall)
    (t : ℝ≥0) (ξ : ℝ)
    (hMG : AEMeasurable (Xgauss t) P)
    (hML : AEMeasurable (Xlarge t) P)
    (hMS : AEMeasurable (Xsmall t) P) :
    charFun (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
        charFun (P.map (Xgauss t)) ξ *
        charFun (P.map (Xlarge t)) ξ *
        charFun (P.map (Xsmall t)) ξ  := by
  let G : Fin 3 → Ω → ℝ := fun i ω =>
    if i = 0 then Xgauss t ω else if i = 1 then Xlarge t ω else Xsmall t ω
  have hG : iIndepFun G P :=
    hind.comp (fun (_ : Fin 3) (x : ℝ≥0 → ℝ) => x t) (fun _ => measurable_pi_apply t)
  have hG0 : G 0 = Xgauss t := rfl
  have hG1 : G 1 = Xlarge t := rfl
  have hG2 : G 2 = Xsmall t := rfl
  have hm : ∀ i, AEMeasurable (G i) P := by
    intro i
    fin_cases i
    · exact hMG
    · exact hML
    · exact hMS
  have h01 : IndepFun (Xgauss t) (Xlarge t) P := by
    rw [← hG0, ← hG1]
    exact hG.indepFun (by decide)
  have h012 : IndepFun (fun ω => Xgauss t ω + Xlarge t ω) (Xsmall t) P := by
    have hh := hG.indepFun_finsetSum_of_notMem₀ hm (s := {0, 1}) (i := 2) (by decide)
    rw [hG2] at hh
    convert hh using 1
    funext ω
    simp [Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide), G]
  have hGL : AEMeasurable (fun ω => Xgauss t ω + Xlarge t ω) P := hMG.add hML
  rw [h012.charFun_map_fun_add_eq_mul hGL hMS, Pi.mul_apply,
    h01.charFun_map_fun_add_eq_mul hMG hML, Pi.mul_apply]
