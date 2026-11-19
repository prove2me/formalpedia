-- Prove2me | solution 1 for Kyprianou.Ch03.esscherTripletWitness_property3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:40:00.145574+00:00
-- url     : https://prove2.me/submissions/bb0c8e58-0b13-4b32-871b-8df3af55ec0f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
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
              Kyprianou.Ch03.esscherDensity X beta
                (Real.log
                  (∫ eta, Real.exp (beta * X 1 eta) ∂P))
                t omega) omega ∂P)) :
    forall (Tbeta : ProbabilityTheory.LevyKhintchineTriple),
      (Tbeta.drift =
        T.drift + beta * (T.gaussianVariance : Real) +
          ∫ x in {x : Real | abs x < 1},
            (Real.exp (beta * x) - 1) * x ∂T.levyMeasure ∧ Tbeta.gaussianVariance = T.gaussianVariance ∧ Tbeta.levyMeasure =
        T.levyMeasure.withDensity
          (fun x : Real => ENNReal.ofReal (Real.exp (beta * x)))) ->
      (forall theta : Real,
        Integrable (fun omega => Real.exp ((theta + beta) * X 1 omega)) P ->
        Real.log (∫ omega, Real.exp (theta * X 1 omega) ∂Q) =
          Real.log
            (∫ omega, Real.exp ((theta + beta) * X 1 omega) ∂P) -
          Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)) := by
  intro Tbeta _ theta hint
  set M : ℝ := ∫ eta, Real.exp (beta * X 1 eta) ∂P with hM
  set D : Omega → ℝ := fun ω => Kyprianou.Ch03.esscherDensity X beta (Real.log M) 1 ω with hD
  -- X 1 is F 1-measurable
  have hX1F : Measurable[F 1] (X 1) := by
    apply Measurable.of_comap_le
    rw [hNatural 1]
    refine le_trans ?_ le_sup_left
    exact le_iSup₂ (f := fun (u : NNReal) (_ : u ≤ 1) =>
      MeasurableSpace.comap (X u) inferInstance) 1 le_rfl
  have hX1 : Measurable (X 1) := hX1F.mono (F.le 1) le_rfl
  have hDm : Measurable D := by
    simp only [hD, Kyprianou.Ch03.esscherDensity]; fun_prop
  have hDpos : ∀ ω, 0 < D ω := fun ω => Real.exp_pos _
  have hQuniv := hEsscher 1 Set.univ MeasurableSet.univ
  simp only [Set.indicator_univ, measure_univ] at hQuniv
  -- integrability of exp(β X 1)
  have hIb : Integrable (fun ω => Real.exp (beta * X 1 ω)) P := by
    by_contra hni
    have hM0 : M = 0 := integral_undef hni
    have hDeq : D = fun ω => Real.exp (beta * X 1 ω) := by
      funext ω; simp [hD, Kyprianou.Ch03.esscherDensity, hM0]
    have : ∫ ω, D ω ∂P = 0 := by rw [hDeq]; exact integral_undef hni
    rw [← hD, this] at hQuniv
    simp at hQuniv
  have hMpos : 0 < M := integral_exp_pos hIb
  have hDform : ∀ ω, D ω = Real.exp (beta * X 1 ω) / M := by
    intro ω
    simp only [hD, Kyprianou.Ch03.esscherDensity, NNReal.coe_one, mul_one]
    rw [Real.exp_sub, Real.exp_log hMpos]
  have hDint : Integrable D P := by
    have : D = fun ω => Real.exp (beta * X 1 ω) / M := funext hDform
    rw [this]; exact hIb.div_const M
  -- Q and P.withDensity D agree on σ(X 1)
  set fD : Omega → ℝ≥0∞ := fun ω => ENNReal.ofReal (D ω) with hfD
  have hfDm : Measurable fD := hDm.ennreal_ofReal
  have hmap : Q.map (X 1) = (P.withDensity fD).map (X 1) := by
    ext B hB
    rw [Measure.map_apply hX1 hB, Measure.map_apply hX1 hB,
      withDensity_apply _ (hX1 hB)]
    have hAF : MeasurableSet[F 1] (X 1 ⁻¹' B) := hX1F hB
    rw [hEsscher 1 _ hAF, integral_indicator (hX1 hB), ← hD,
      ofReal_integral_eq_lintegral_ofReal hDint.integrableOn
        (Filter.Eventually.of_forall fun ω => (hDpos ω).le)]
  have hQint : ∫ ω, Real.exp (theta * X 1 ω) ∂Q =
      (∫ ω, Real.exp ((theta + beta) * X 1 ω) ∂P) / M := by
    have h1 : ∫ ω, Real.exp (theta * X 1 ω) ∂Q = ∫ x, Real.exp (theta * x) ∂(Q.map (X 1)) :=
      (integral_map (f := fun x : ℝ => Real.exp (theta * x)) hX1.aemeasurable
        (by fun_prop : Measurable fun x : ℝ => Real.exp (theta * x)).aestronglyMeasurable).symm
    have h2 : ∫ x, Real.exp (theta * x) ∂((P.withDensity fD).map (X 1)) =
        ∫ ω, Real.exp (theta * X 1 ω) ∂(P.withDensity fD) :=
      integral_map (f := fun x : ℝ => Real.exp (theta * x)) hX1.aemeasurable
        (by fun_prop : Measurable fun x : ℝ => Real.exp (theta * x)).aestronglyMeasurable
    rw [h1, hmap, h2, integral_withDensity_eq_integral_toReal_smul hfDm
      (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
    rw [← integral_div]
    congr 1
    funext ω
    simp only [hfD, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hDpos ω).le, hDform]
    rw [add_mul, Real.exp_add]
    ring
  have hApos : 0 < ∫ ω, Real.exp ((theta + beta) * X 1 ω) ∂P := integral_exp_pos hint
  rw [hQint, Real.log_div hApos.ne' hMpos.ne']
