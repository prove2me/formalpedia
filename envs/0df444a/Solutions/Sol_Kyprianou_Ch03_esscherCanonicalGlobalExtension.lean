-- Prove2me | solution 1 for Kyprianou.Ch03.esscherCanonicalGlobalExtension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:45:25.211808+00:00
-- url     : https://prove2.me/submissions/10039e9e-aa61-43c6-b507-2aaa489a5246
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_canonicalConsistentDensityExtensionV1
import Theorems.Thm_Kyprianou_Ch03_esscherCanonicalRawDensityConsistencyV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

theorem solution
(P : Measure {path : NNReal → ℝ // path 0 = 0})
    [IsProbabilityMeasure P]
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t omega, X t omega = omega.val t)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : ℝ)
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (beta * x))
      {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    let k := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P);
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0},
      Q Set.univ = 1 ∧
      ∀ (t : NNReal) (A : Set {path : NNReal → ℝ // path 0 = 0}),
        MeasurableSet[PerfCorrMSQ.natFiltr X t] A →
          Q A = ENNReal.ofReal
            (∫ omega, Set.indicator A
              (esscherDensity X beta k t) omega ∂P) := by
  dsimp only
  have h := esscherCanonicalRawDensityConsistencyV1 P X hCoordinate hX T hLK beta hBeta
  dsimp only at h
  exact canonicalConsistentDensityExtensionV1 P X hCoordinate
    (esscherDensity X beta (Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)))
    (fun t omega => Real.exp_nonneg _) (fun t => (h.1 t).1)
    (fun t => (h.1 t).2) h.2
