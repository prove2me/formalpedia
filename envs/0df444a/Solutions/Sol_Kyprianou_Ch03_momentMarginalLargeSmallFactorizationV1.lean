-- Prove2me | solution 1 for Kyprianou.Ch03.momentMarginalLargeSmallFactorizationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:51:43.044422+00:00
-- url     : https://prove2.me/submissions/b832fda9-610f-44f7-bb27-409b8cf73036

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_levyItoDecompositionCorrected
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_largeJumpProcessLevy
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftCharFunV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (t : NNReal) (ht : 0 < t) :
    ∃ (mu nu : Measure Real), IsProbabilityMeasure mu ∧ IsProbabilityMeasure nu ∧
      P.map (X t) = (mu.prod nu).map (fun p : Real × Real => p.1 + p.2) ∧
      (∀ xi : Real, charFun mu xi = Complex.exp (((t : Real) : Complex) *
        ∫ x in {x : Real | 1 ≤ |x|},
          (Complex.exp (Complex.I * (((xi * x : Real) : Complex))) - 1) ∂T.levyMeasure)) ∧
      (∀ xi : Real, charFun nu xi = Complex.exp (((t : Real) : Complex) *
          (Complex.I * ((T.drift * xi : Real) : Complex) -
          (((T.gaussianVariance : Real) * xi ^ 2 / 2 : Real) : Complex) +
          ∫ x in Set.Ioo (-1 : Real) 1,
            ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure))) := by
  let a : ℝ := -T.drift
  let s : NNReal := NNReal.sqrt T.gaussianVariance
  have hs : s ^ 2 = T.gaussianVariance := NNReal.sq_sqrt _
  obtain ⟨hσ, Ω, m, Q, hQ, B, N, G, L, S, ℱ, hGdef, hLdef,
    hG, hL, hS, _, _, _, _, hSchar, hind, hsum, hchar⟩ :=
    Kyprianou.levyItoDecompositionCorrected a s T.levyMeasure T.levyMeasure_isLevyMeasure
  letI : MeasurableSpace Ω := m
  letI : IsProbabilityMeasure Q := hQ
  letI : SigmaFinite T.levyMeasure := hσ
  let Y (ω : Ω) := G t ω + S t ω
  have hMG := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 Q G hG t
  have hML := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 Q L hL t
  have hMS := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 Q S hS t
  have hMY : AEMeasurable Y Q := hMG.add hMS
  let F : Fin 3 → Ω → ℝ := fun i ω =>
    if i = 0 then G t ω else if i = 1 then L t ω else S t ω
  have hF : iIndepFun F Q :=
    hind.comp (fun (_ : Fin 3) (x : NNReal → ℝ) => x t) (fun _ => measurable_pi_apply t)
  have hMF : ∀ i, AEMeasurable (F i) Q := by
    intro i
    fin_cases i
    · exact hMG
    · exact hML
    · exact hMS
  have hGS : IndepFun (G t) (S t) Q := hF.indepFun (show (0 : Fin 3) ≠ 2 by decide)
  have hYL : IndepFun Y (L t) Q := by
    have hh := hF.indepFun_finsetSum_of_notMem₀ hMF (s := {0, 2}) (i := 1) (by decide)
    convert hh using 1
    · funext ω
      simp [Finset.sum_pair (show (0 : Fin 3) ≠ 2 by decide), F, Y]
    · funext ω
      simp [F]
  let mu := Q.map (L t)
  let nu := Q.map Y
  letI : IsProbabilityMeasure mu := Measure.isProbabilityMeasure_map hML
  letI : IsProbabilityMeasure nu := Measure.isProbabilityMeasure_map hMY
  have hT : (⟨-a, s ^ 2, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩ :
      ProbabilityTheory.LevyKhintchineTriple) = T := by
    cases T
    simp [a, hs]
  have hmx := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t
  letI : IsProbabilityMeasure (P.map (X t)) := Measure.isProbabilityMeasure_map hmx
  have hmy := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 Q _ hsum t
  letI : IsProbabilityMeasure (Q.map (fun ω => G t ω + L t ω + S t ω)) :=
    Measure.isProbabilityMeasure_map hmy
  have he : P.map (X t) = Q.map (fun ω => G t ω + L t ω + S t ω) := by
    apply Measure.ext_of_charFun
    funext xi
    rw [hLK t xi, hchar t xi, hT]
  refine ⟨mu, nu, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · have hj := hYL.symm.map_prod_eq_prod_map_map hML hMY
    rw [he, ← hj]
    have hpair := hML.prodMk hMY
    let A : ℝ × ℝ → ℝ := fun p => p.1 + p.2
    have hA : Measurable A := measurable_fst.add measurable_snd
    change Q.map (fun ω => G t ω + L t ω + S t ω) = (Q.map (fun ω => (L t ω, Y ω))).map A
    rw [AEMeasurable.map_map_of_aemeasurable hA.aemeasurable hpair]
    congr 1
    funext ω
    dsimp [A, Y, Function.comp_def]
    ring
  · intro xi
    change charFun (Q.map (L t)) xi = _
    rw [show L t = Kyprianou.largeJumpProcess Q T.levyMeasure N t from funext (hLdef t)]
    exact (Kyprianou.largeJumpProcessLevy Q T.levyMeasure T.levyMeasure_isLevyMeasure N).2 t xi
  · intro xi
    change charFun (Q.map (fun ω => G t ω + S t ω)) xi = _
    rw [hGS.charFun_map_fun_add_eq_mul hMG hMS, Pi.mul_apply,
      Kyprianou.Ch02.sourceFaithfulGaussianDriftCharFunV1 a s Q B G hGdef t xi,
      hSchar t xi, ← Complex.exp_add]
    have hsR : (s : ℝ) ^ 2 = (T.gaussianVariance : ℝ) := by exact_mod_cast hs
    rw [hsR]
    simp only [a, Complex.ofReal_neg, Complex.ofReal_mul]
    congr 1
    ring
