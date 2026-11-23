-- Prove2me | solution 4 for Kyprianou.Ch02.sourceFaithfulLevyItoTripleExponentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:19:06.243116+00:00
-- url     : https://prove2.me/submissions/98bb7c24-6408-45a9-97da-611168f8102b

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftCharFunV1
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyTripleExponentAlgebraV1
import Theorems.Thm_Kyprianou_largeJumpProcessLevy
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
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : ∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ))
    (hlarge : ∀ t ω, Xlarge t ω = Kyprianou.largeJumpProcess P levyMeasure N t ω)
    (hsmall : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (Xsmall t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in Set.Ioo (-1 : ℝ) 1,
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        Kyprianou.Ch01.levyTripleExponent
          ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ) := by
  intro t ξ
  have hmeasG : AEMeasurable (Xgauss t) P := by
    have hgeq :
        Xgauss t = fun ω => (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ) := by
      funext ω; exact hgauss t ω
    rw [hgeq]
    exact ((measurable_const.mul (B.measurable_eval (t : ℝ))).sub
      measurable_const).aemeasurable
  have hmeasL : AEMeasurable (Xlarge t) P := by
    have hleq : Xlarge t = Kyprianou.largeJumpProcess P levyMeasure N t := by
      funext ω; exact hlarge t ω
    rw [hleq]
    have hLevy :=
      (Kyprianou.largeJumpProcessLevy P levyMeasure hlevyMeasure N).1
    have hstat :=
      (hLevy.stationary_increments 0 t).aemeasurable_fst
    have hpath :
        ProbabilityTheory.increment
          (Kyprianou.largeJumpProcess P levyMeasure N) 0 (0 + t) =
        Kyprianou.largeJumpProcess P levyMeasure N t := by
      funext ω; simp [ProbabilityTheory.increment, hLevy.start_zero]
    rwa [hpath] at hstat
  have hmeasS : AEMeasurable (Xsmall t) P := by
    have hmap_ne : P.map (Xsmall t) ≠ 0 := by
      intro hzero
      have hchar := hsmall t 0
      rw [hzero, MeasureTheory.charFun_zero_measure] at hchar
      exact (Complex.exp_ne_zero _) hchar.symm
    exact aemeasurable_of_map_neZero
      (⟨hmap_ne⟩ : NeZero (P.map (Xsmall t)))
  let G : Fin 3 → Ω → ℝ := fun i ω =>
    if i = 0 then Xgauss t ω else if i = 1 then Xlarge t ω else Xsmall t ω
  have hG : iIndepFun G P :=
    hind.comp (fun (_ : Fin 3) (x : ℝ≥0 → ℝ) => x t)
      (fun _ => measurable_pi_apply t)
  have hG0 : G 0 = Xgauss t := rfl
  have hG1 : G 1 = Xlarge t := rfl
  have hG2 : G 2 = Xsmall t := rfl
  have hm : ∀ i, AEMeasurable (G i) P := by
    intro i
    fin_cases i
    · exact hmeasG
    · exact hmeasL
    · exact hmeasS
  have h01 : IndepFun (Xgauss t) (Xlarge t) P := by
    rw [← hG0, ← hG1]
    exact hG.indepFun (by decide)
  have h012 : IndepFun
      (fun ω => Xgauss t ω + Xlarge t ω) (Xsmall t) P := by
    have hsum := hG.indepFun_finsetSum_of_notMem₀ hm
      (s := {0, 1}) (i := 2) (by decide)
    rw [hG2] at hsum
    convert hsum using 1
    funext ω
    simp [Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide), G]
  have hfactor :
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      charFun (P.map (Xgauss t)) ξ *
      charFun (P.map (Xlarge t)) ξ *
      charFun (P.map (Xsmall t)) ξ := by
    have hgl : AEMeasurable
        (fun ω => Xgauss t ω + Xlarge t ω) P := hmeasG.add hmeasL
    rw [h012.charFun_map_fun_add_eq_mul hgl hmeasS, Pi.mul_apply,
      h01.charFun_map_fun_add_eq_mul hmeasG hmeasL, Pi.mul_apply]
  rw [hfactor,
    Kyprianou.Ch02.sourceFaithfulGaussianDriftCharFunV1
      a σ P B Xgauss hgauss t ξ]
  have hlarge_eq :
      Xlarge t = Kyprianou.largeJumpProcess P levyMeasure N t := by
    funext ω
    exact hlarge t ω
  rw [hlarge_eq, (Kyprianou.largeJumpProcessLevy
    P levyMeasure hlevyMeasure N).2 t ξ, hsmall t ξ]
  exact Kyprianou.Ch02.sourceFaithfulLevyTripleExponentAlgebraV1
    a σ levyMeasure hlevyMeasure t ξ
