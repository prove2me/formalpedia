-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteVectorShiftCountLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:56:03.775354+00:00
-- url     : https://prove2.me/submissions/b97f59c1-cb52-4802-ace4-eeafba3b16b2

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
import Theorems.Thm_Kyprianou_Ch02_prmTimeShiftedWindowCountLawV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (n : ℕ) (C : Fin n → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hfinite : ∀ i, ν (C i) < ⊤)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (s t : ℝ≥0) :
    P.map (fun (ω : Ω) (i : Fin n) =>
      N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ C i)) =
    P.map (fun (ω : Ω) (i : Fin n) =>
      N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C i)) := by
  classical
  let A : Fin n → Set (ℝ × ℝ) := fun i =>
    Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ C i
  let B : Fin n → Set (ℝ × ℝ) := fun i =>
    Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C i
  have hmA : ∀ i, MeasurableSet (A i) :=
    fun i => measurableSet_Ioc.prod (hC i)
  have hmB : ∀ i, MeasurableSet (B i) :=
    fun i => measurableSet_Ioc.prod (hC i)
  have hdA : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp (hdisj hij) hp.2 hq.2
  have hdB : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp (hdisj hij) hp.2 hq.2
  have hiA : iIndepFun (fun i ω => N.N ω (A i)) P :=
    N.independent_disjoint A hmA hdA
  have hiB : iIndepFun (fun i ω => N.N ω (B i)) P :=
    N.independent_disjoint B hmB hdB
  have hma : ∀ i, AEMeasurable (fun ω => N.N ω (A i)) P :=
    fun i => (N.measurable_eval (hmA i)).aemeasurable
  have hmb : ∀ i, AEMeasurable (fun ω => N.N ω (B i)) P :=
    fun i => (N.measurable_eval (hmB i)).aemeasurable
  change P.map (fun ω i => N.N ω (A i)) =
    P.map (fun ω i => N.N ω (B i))
  calc
    P.map (fun ω i => N.N ω (A i)) =
        Measure.pi (fun i => P.map (fun ω => N.N ω (A i))) :=
      (iIndepFun_iff_map_fun_eq_pi_map hma).1 hiA
    _ = Measure.pi (fun i => P.map (fun ω => N.N ω (B i))) := by
      congr 1
      funext i
      exact Kyprianou.Ch02.prmTimeShiftedWindowCountLawV1
        P ν N (C i) (hC i) (hfinite i) s t
    _ = P.map (fun ω i => N.N ω (B i)) :=
      ((iIndepFun_iff_map_fun_eq_pi_map hmb).1 hiB).symm
