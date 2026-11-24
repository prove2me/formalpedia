-- Prove2me | solution 1 for Kyprianou.Ch03.esscherStoppingFiniteCutDensityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:31:17.414808+00:00
-- url     : https://prove2.me/submissions/69da4bfc-ee88-48c0-a432-a2c6b9f23100

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_esscherDensityFiniteCutV1
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
      tau omega = (tauFinite omega : WithTop NNReal))
    (A : Set Omega)
    (hA : forall t : NNReal,
      MeasurableSet[F t] (A ∩ {omega : Omega | tau omega ≤ (t : WithTop NNReal)}))
    (n : Nat) :
    let B := A ∩ {omega : Omega | tau omega ≤ ((n : NNReal) : WithTop NNReal)}
    let g := fun eta : Omega => esscherDensity X beta
      (Real.log (∫ z, Real.exp (beta * X 1 z) ∂P)) (tauFinite eta) eta
    AEMeasurable (Set.indicator B g) P ∧
      Q B = ∫⁻ omega, ENNReal.ofReal (Set.indicator B g omega) ∂P := by
  dsimp only
  obtain ⟨hi, he⟩ := Kyprianou.Ch03.esscherDensityFiniteCutV1 P Q F X hX hNatural T hLK beta hBeta
    hEsscher tau hStopping tauFinite hTauFinite A hA n
  refine ⟨hi.aestronglyMeasurable.aemeasurable, he.trans ?_⟩
  apply ofReal_integral_eq_lintegral_ofReal hi
  exact Filter.Eventually.of_forall (Set.indicator_nonneg (fun w _ => Real.exp_nonneg _))
