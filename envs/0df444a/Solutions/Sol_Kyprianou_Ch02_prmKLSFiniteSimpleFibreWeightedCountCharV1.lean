-- Prove2me | solution 1 for Kyprianou.Ch02.prmKLSFiniteSimpleFibreWeightedCountCharV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:37:38.928126+00:00
-- url     : https://prove2.me/submissions/e187d783-1145-4fc0-9b1f-2ef0acc7f58f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmKLSFiniteDisjointWeightedCountCharV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Reindex the finite independent weighted-Poisson exponent over simple-mark fibres. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : SimpleFunc ℝ ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (fun (ω : Ω) =>
      ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∑ x ∈ f.range, ((((ν (B ∩ {y : ℝ | f y = x})).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1))) := by
  classical
  let e : {x : ℝ // x ∈ f.range} ≃ Fin f.range.card :=
    Finset.equivFin f.range
  let C : Fin f.range.card → Set ℝ := fun i =>
    B ∩ {y : ℝ | f y = (e.symm i).1}
  let w : Fin f.range.card → ℝ := fun i => (e.symm i).1
  have hC : ∀ i, MeasurableSet (C i) := by
    intro i
    exact hB.inter
      ((measurableSet_singleton (w i)).preimage f.measurable)
  have hfin : ∀ i, ν (C i) < ⊤ := by
    intro i
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfinite
  have hd : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    have heq : (e.symm i).1 = (e.symm j).1 :=
      hyi.2.symm.trans hyj.2
    exact hij (e.symm.injective (Subtype.ext heq))
  have hsum (ω : Ω) :
      (∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal) =
      ∑ i : Fin f.range.card, w i *
        (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C i)).toReal := by
    calc
      _ = ∑ x ∈ f.range.attach, x.1 * (N.N ω
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
            (B ∩ {y : ℝ | f y = x.1}))).toReal :=
            (Finset.sum_attach f.range _).symm
      _ = ∑ i ∈ Finset.univ, w i * (N.N ω
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C i)).toReal := by
        apply Finset.sum_equiv e
        · intro x
          simp
        · intro x hx
          simp only [w, C, e.symm_apply_apply]
      _ = _ := by simp
  have hfinlaw :=
    Kyprianou.Ch02.prmKLSFiniteDisjointWeightedCountCharV1
      P ν N f.range.card C hC hfin hd w t ξ
  have hweight :
      (∑ i : Fin f.range.card,
        ((((ν (C i)).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * w i : ℝ) : ℂ))) - 1))) =
      ∑ x ∈ f.range, ((((ν (B ∩ {y : ℝ | f y = x})).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1)) := by
    calc
      _ = ∑ x ∈ f.range.attach, ((((ν (B ∩
          {y : ℝ | f y = x.1})).toReal : ℝ) : ℂ) *
            (Complex.exp (Complex.I * (((ξ * x.1 : ℝ) : ℂ))) - 1)) := by
        symm
        apply Finset.sum_equiv e
        · intro x
          simp
        · intro x hx
          simp only [C, w, e.symm_apply_apply]
      _ = _ := by
        let g : ℝ → ℂ := fun x =>
          ((((ν (B ∩ {y : ℝ | f y = x})).toReal : ℝ) : ℂ) *
            (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1))
        simpa only [g, Complex.ofReal_mul] using
          (Finset.sum_attach f.range g)
  calc
    charFun (P.map (fun (ω : Ω) =>
      ∑ x ∈ f.range, x * (N.N ω
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
          (B ∩ {y : ℝ | f y = x}))).toReal)) ξ =
      charFun (P.map (fun (ω : Ω) =>
        ∑ i : Fin f.range.card, w i *
          (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C i)).toReal)) ξ := by
        congr 1
        exact congrArg (fun g : Ω → ℝ => P.map g)
          (funext fun ω => hsum ω)
    _ = Complex.exp (∑ i : Fin f.range.card,
        ((((t : ℝ) * (ν (C i)).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * w i : ℝ) : ℂ))) - 1))) := hfinlaw
    _ = Complex.exp ((((t : ℝ) : ℂ)) *
        ∑ x ∈ f.range, ((((ν (B ∩ {y : ℝ | f y = x})).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1))) := by
      congr 1
      rw [← hweight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      ring
