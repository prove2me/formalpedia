-- Prove2me | solution 1 for Kyprianou.Ch03.esscherDensityFiniteCutV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:45:44.034438+00:00
-- url     : https://prove2.me/submissions/7cafc58f-464d-4ea5-84f5-d9b4a1a7bf19

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_esscherDensityMartingaleRightContinuousV1
import Theorems.Thm_Kyprianou_Ch03_finiteCutStopClockV1
import Theorems.Thm_Kyprianou_Ch03_boundedStoppingDensityEventV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real)
    (hBeta : IntegrableOn
      (fun x : Real => Real.exp (beta * x))
      {x : Real | 1 <= abs x} T.levyMeasure)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity X beta
                (Real.log
                  (∫ eta, Real.exp (beta * X 1 eta) ∂P))
                t omega) omega ∂P))
    (tau : Omega -> WithTop NNReal)
    (hStopping : IsStoppingTime F tau)
    (tauFinite : Omega -> NNReal)
    (hTauFinite : forall omega, tau omega != ⊤ ->
      tau omega = (tauFinite omega : WithTop NNReal)) :
    ∀ (A : Set Omega),
      (∀ t : NNReal, MeasurableSet[F t] (A ∩ {omega : Omega | tau omega ≤ (t : WithTop NNReal)})) →
      ∀ n : ℕ, Integrable ((A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}).indicator (fun eta : Omega => esscherDensity X beta (Real.log (∫ z, Real.exp (beta * X 1 z) ∂P)) (tauFinite eta) eta)) P ∧
        Q (A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}) = ENNReal.ofReal (∫ omega, (A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}).indicator (fun eta : Omega => esscherDensity X beta (Real.log (∫ z, Real.exp (beta * X 1 z) ∂P)) (tauFinite eta) eta) omega ∂P) := by 
  classical
  intro A hA n
  let k := Real.log (∫ z, Real.exp (beta * X 1 z) ∂P)
  let Z := esscherDensity X beta k
  let B := A ∩ {w | tau w ≤ ((n : NNReal) : WithTop NNReal)}
  obtain ⟨rho, hs, hb, hB, he⟩ :=
    finiteCutStopClockV1 F tau hStopping tauFinite
      (fun w hw => hTauFinite w (by simpa using hw)) A hA (n : NNReal)
  obtain ⟨hm, hr⟩ := esscherDensityMartingaleRightContinuousV1 P F X hX hNatural T hLK beta hBeta
  obtain ⟨hi, heq⟩ := boundedStoppingDensityEventV1 P F Z hm hr rho hs (n : NNReal) hb B hB
  have hz : B.indicator (fun w => Z (rho w) w) = B.indicator (fun w => Z (tauFinite w) w) := by
    funext w
    by_cases hw : w ∈ B
    · simp [Set.indicator_apply, hw, he w hw]
    · simp [Set.indicator_apply, hw]
  rw [hz] at hi heq
  exact ⟨hi, (hEsscher (n : NNReal) B (hA n)).trans (congrArg ENNReal.ofReal heq.symm)⟩
