-- Prove2me | solution 1 for Kyprianou.Ch03.esscherDensityMartingaleRightContinuousV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:45:44.642695+00:00
-- url     : https://prove2.me/submissions/4a2fc7fc-d389-49dc-81ed-555cb02295b5

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_esscherExponentialDensityConsistent
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

open Filter
open scoped Topology

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
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
    : let k := Real.log (∫ w, Real.exp (beta * X 1 w) ∂P)
    let Z := esscherDensity X beta k
    Martingale Z F P ∧
      (∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => Z u w) (Set.Ici t) t) := by 
  dsimp only
  let k := Real.log (∫ w, Real.exp (beta * X 1 w) ∂P)
  let Z := esscherDensity X beta k
  have h := esscherExponentialDensityConsistent P F X hX hNatural T hLK beta hBeta
  have hAdapt (t : NNReal) : Measurable[F t] (Z t) := by
    have hXt : Measurable[F t] (X t) := by
      apply (comap_measurable (X t)).mono _ le_rfl
      rw [hNatural t]
      exact le_sup_of_le_left (le_iSup₂_of_le t le_rfl le_rfl)
    exact ((measurable_const.mul hXt).sub measurable_const).exp
  constructor
  · constructor
    · exact fun t => (hAdapt t).stronglyMeasurable
    · intro s t hst
      symm
      apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (h.1 t).1
      · exact fun B hB _ => (h.1 s).1.integrableOn
      · intro B hB _
        have hb := F.le s B hB
        simpa only [integral_indicator hb] using (h.2 s t hst B hB).symm
      · exact (hAdapt s).stronglyMeasurable.aestronglyMeasurable
  · filter_upwards [hX.cadlag_ae] with w hw
    intro t
    exact ((continuousWithinAt_const.mul (hw t).1).sub
      (continuousWithinAt_const.mul NNReal.continuous_coe.continuousWithinAt)).rexp
