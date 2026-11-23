-- Prove2me | solution 1 for Kyprianou.Ch02.prmKLSFiniteDisjointWeightedCountCharV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:31:07.009143+00:00
-- url     : https://prove2.me/submissions/6a21b7ad-9f8e-426e-b8ac-ac8e720e380f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonCountCharacteristicV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Characteristic functions of finite independent weighted Poisson count sums factor. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (n : ℕ) (C : Fin n → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hfinite : ∀ i, ν (C i) < ⊤)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (w : Fin n → ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (fun (ω : Ω) =>
      ∑ i : Fin n, w i *
        (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C i)).toReal)) ξ =
      Complex.exp (∑ i : Fin n,
        ((((t : ℝ) * (ν (C i)).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * w i : ℝ) : ℂ))) - 1))) := by
  classical
  let A : Fin n → Set (ℝ × ℝ) :=
    fun i => Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C i
  let F : Fin n → Ω → ℝ :=
    fun i ω => w i * (N.N ω (A i)).toReal
  have hmA : ∀ i, MeasurableSet (A i) :=
    fun i => measurableSet_Ioc.prod (hC i)
  have hdA : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp (hdisj hij) hp.2 hq.2
  have hindep : iIndepFun F P := by
    have hcounts : iIndepFun (fun i ω => N.N ω (A i)) P :=
      N.independent_disjoint A hmA hdA
    exact hcounts.comp (fun i (v : ℝ≥0∞) => w i * v.toReal)
      (fun i => measurable_const.mul ENNReal.measurable_toReal)
  have hmeas (i : Fin n) : Measurable (F i) :=
    measurable_const.mul
      (ENNReal.measurable_toReal.comp (N.measurable_eval (hmA i)))
  have hrate (i : Fin n) :
      (LevyStochCalc.Poisson.referenceIntensity ν (A i)).toReal =
        (t : ℝ) * (ν (C i)).toReal := by
    unfold A LevyStochCalc.Poisson.referenceIntensity
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
    have hsub : Set.Ioc (0 : ℝ) (t : ℝ) ∩ Set.Ici (0 : ℝ) =
        Set.Ioc (0 : ℝ) (t : ℝ) :=
      Set.inter_eq_left.mpr fun _ hx => le_of_lt hx.1
    rw [hsub, Real.volume_Ioc, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal t.coe_nonneg]
  have hscalar (i : Fin n) :
      charFun (P.map (F i)) ξ =
        Complex.exp (((((t : ℝ) * (ν (C i)).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * w i : ℝ) : ℂ))) - 1))) := by
    let g : ℝ → ℂ := fun x =>
      Complex.exp ((((ξ * x : ℝ) : ℂ)) * Complex.I)
    have hg : Continuous g := by dsimp [g]; fun_prop
    have hmap : charFun (P.map (F i)) ξ =
        ∫ ω, g (F i ω) ∂P := by
      rw [charFun_apply_real]
      simpa only [g, Complex.ofReal_mul] using
        (integral_map (hmeas i).aemeasurable hg.aestronglyMeasurable)
    have hchange :
        (∫ ω, g (F i ω) ∂P) =
        ∫ ω, Complex.exp (Complex.I *
          (((ξ * w i) * (N.N ω (A i)).toReal : ℝ) : ℂ)) ∂P := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun ω => ?_
      dsimp [F, g]
      congr 1
      push_cast
      ring
    have hcount :=
      Kyprianou.Ch02.finiteRegionPoissonCountCharacteristicV1
        P ν N (C i) (hC i) (hfinite i) t (ξ * w i)
    rw [hmap, hchange]
    change (∫ ω, Complex.exp (Complex.I *
      (((ξ * w i) * (N.N ω (A i)).toReal : ℝ) : ℂ)) ∂P) = _
    rw [hcount, hrate]
  have hsum : (fun (ω : Ω) =>
      ∑ i : Fin n, w i * (N.N ω (A i)).toReal) =
      (∑ i ∈ Finset.univ, F i) := by
    funext ω
    simp only [Finset.sum_apply, F]
  rw [hsum]
  have hchar := ProbabilityTheory.iIndepFun.charFun_map_finset_sum_eq_prod
    (s := (Finset.univ : Finset (Fin n))) (X := F)
    (fun i _ => (hmeas i).aemeasurable)
    (hindep.restrict Finset.univ)
  calc
    charFun (P.map (∑ i ∈ Finset.univ, F i)) ξ =
      ∏ i ∈ Finset.univ, charFun (P.map (F i)) ξ :=
        by simpa only [Finset.prod_apply] using congrFun hchar ξ
    _ = ∏ i ∈ Finset.univ,
        Complex.exp (((((t : ℝ) * (ν (C i)).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * w i : ℝ) : ℂ))) - 1))) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hscalar i
    _ = Complex.exp (∑ i : Fin n,
        ((((t : ℝ) * (ν (C i)).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * w i : ℝ) : ℂ))) - 1))) := by
        exact (Complex.exp_sum Finset.univ _).symm
