-- Prove2me | solution 1 for OAI.IsingPerceptron.variationalValue_real_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:13:10.804038+00:00
-- url     : https://prove2.me/submissions/e7a3a9a0-2394-4151-8959-a3a40800d750

import Mathlib
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ4Ip000

section
-- module Solutions.OAIQ4_Ip.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_PoissonCloud
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson Cloud. -/

noncomputable section



 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

 
namespace IsingPerceptron

lemma poisson_probability_generating (r : ℝ≥0) (q : ℝ) :
    (∫ n : ℕ, q ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (q - 1)) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    (∑' n : ℕ, (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)) * q^n) =
        Real.exp (-(r : ℝ)) * ∑' n : ℕ, ((r : ℝ)*q)^n / (n.factorial : ℝ) := by
      rw [← tsum_mul_left]
      congr 1
      ext n
      rw [mul_pow]
      ring
    _ = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ)*q) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*q)).tsum_eq,
        ← Real.exp_eq_exp_ℝ]
    _ = Real.exp ((r : ℝ)*(q-1)) := by rw [← Real.exp_add]; congr 1; ring

variable {E : Type*} [MeasurableSpace E]

lemma measurable_cloudSum {ψ : E → ℝ} (hψ : Measurable ψ) :
    Measurable (cloudSum ψ) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun y : ℕ → E => ∑ i : Fin n, ψ (y i))
  exact Finset.measurable_sum (Finset.univ : Finset (Fin n))
    (fun i _ => hψ.comp (measurable_pi_apply (i : ℕ)))

lemma iid_finite_laplace (μ : Measure E) [IsProbabilityMeasure μ]
    {ψ : E → ℝ} (hψ : Measurable ψ) (n : ℕ) :
    (∫ ω : ℕ → E, Real.exp (-(∑ i : Fin n, ψ (ω i)))
      ∂Measure.infinitePi (fun _ : ℕ => μ)) =
    (∫ x, Real.exp (-ψ x) ∂μ)^n := by
  let X : ℕ → (ℕ → E) → ℝ := fun i ω => Real.exp (-ψ (ω i))
  have hind : iIndepFun X (Measure.infinitePi (fun _ : ℕ => μ)) :=
    iIndepFun_infinitePi (fun _ => hψ.neg.exp)
  have hind' : iIndepFun (fun i : Fin n => X i) (Measure.infinitePi (fun _ : ℕ => μ)) :=
    hind.precomp Fin.val_injective
  have hm (i : Fin n) : AEStronglyMeasurable (X i)
      (Measure.infinitePi (fun _ : ℕ => μ)) :=
    ((hψ.neg.exp).comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable
  have he i : (∫ ω, X i ω ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫ x, Real.exp (-ψ x) ∂μ := by
    have mp := measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i
    exact mp.hasLaw.integral_comp hψ.neg.exp.aestronglyMeasurable
  have hh := hind'.integral_fun_prod_eq_prod_integral hm
  simpa only [X, ← Real.exp_sum, ← Finset.sum_neg_distrib, he, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using hh

 
theorem finitePoissonCloud_laplace (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {ψ : E → ℝ} (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ p, Real.exp (-cloudSum ψ p) ∂finitePoissonCloud r μ) =
      Real.exp ((r : ℝ) * ((∫ x, Real.exp (-ψ x) ∂μ) - 1)) := by
  have hi : Integrable (fun p => Real.exp (-cloudSum ψ p)) (finitePoissonCloud r μ) := by
    apply Integrable.of_bound (measurable_cloudSum hψ |>.neg.exp.aestronglyMeasurable) 1
    apply ae_of_all
    intro p
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => hpos _))
  rw [finitePoissonCloud, integral_prod _ hi]
  simp_rw [cloudSum, iid_finite_laplace μ hψ]
  exact poisson_probability_generating r _

lemma negExp_injective : Function.Injective negExp := by
  intro x y h
  apply EReal.coe_ennreal_injective
  apply neg_injective
  apply EReal.exp_strictMono.injective
  exact (ENNReal.toReal_eq_toReal_iff' (enegExp_ne_top x) (enegExp_ne_top y)).mp h
lemma negExp_ofReal {x : ℝ} (hx : 0 ≤ x) :
    negExp (ENNReal.ofReal x) = Real.exp (-x) := by
  simp [negExp, enegExp, EReal.coe_ennreal_ofReal, max_eq_left hx,
    ← EReal.coe_neg, Real.exp_nonneg]
lemma enegExp_add (x y : ℝ≥0∞) : enegExp (x+y) = enegExp x * enegExp y := by
  by_cases hx : x = ∞
  · simp [hx]
  by_cases hy : y = ∞
  · simp [hy]
  rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_toReal hy]
  rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  simp only [enegExp, EReal.coe_ennreal_ofReal]
  rw [max_eq_left (by positivity), max_eq_left (by positivity), max_eq_left (by positivity)]
  rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_neg, EReal.exp_coe,
    EReal.exp_coe, EReal.exp_coe, neg_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]
lemma negExp_add (x y : ℝ≥0∞) : negExp (x+y) = negExp x * negExp y := by
  simp only [negExp, enegExp_add, ENNReal.toReal_mul]
lemma negExp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    negExp (∑ i ∈ s, f i) = ∏ i ∈ s, negExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, negExp_add, ih]
lemma negExp_nat_mul (n : ℕ) (x : ℝ≥0∞) : negExp (n*x) = negExp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, negExp_add, ih, pow_succ]


lemma finiteCloudMeasure_lintegral (p : ℕ × (ℕ → E)) {ψ : E → ℝ≥0∞}
    (hψ : Measurable ψ) : (∫⁻ x, ψ x ∂finiteCloudMeasure p) = ∑ i : Fin p.1, ψ (p.2 i) := by
  simp [finiteCloudMeasure, lintegral_finsetSum_measure, lintegral_dirac' _ hψ]

variable [Nonempty E]


lemma finiteMeasure_mass_normalize (μ : FiniteMeasure E) :
    (μ : Measure E) = (μ.mass : ℝ≥0∞) • (μ.normalize : Measure E) := by
  ext s hs
  simpa using congrArg (fun m : FiniteMeasure E => (m : Measure E) s)
    μ.self_eq_mass_smul_normalize

lemma finitePoissonLaw_laplace (μ : FiniteMeasure E) {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂finitePoissonLaw μ) =
      negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ : Measure E)) := by
  have hcost : ∀ x, 0 ≤ 1-Real.exp (-ψ x) := fun x =>
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
  have hi : Integrable (fun x => Real.exp (-ψ x)) (μ.normalize : Measure E) := by
    apply Integrable.of_bound hψ.neg.exp.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
  have hicost : Integrable (fun x => 1-Real.exp (-ψ x)) (μ.normalize : Measure E) :=
    (integrable_const 1).sub hi
  have hmeas : Measurable (fun ν : Measure E => negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [finitePoissonLaw, integral_map measurable_finiteCloudMeasure.aemeasurable
    hmeas.aestronglyMeasurable]
  have hs (p : ℕ × (ℕ → E)) :
      negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) =
        Real.exp (-cloudSum ψ p) := by
    rw [finiteCloudMeasure_lintegral p hψ.ennreal_ofReal,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (fun (i : Fin p.1) _ => hpos (p.2 i)), negExp_ofReal]
    · rfl
    · exact Finset.sum_nonneg (fun i _ => hpos (p.2 i))
  simp_rw [hs]
  rw [finitePoissonCloud_laplace μ.mass _ hψ hpos]
  rw [finiteMeasure_mass_normalize μ, lintegral_smul_measure]
  rw [← ofReal_integral_eq_lintegral_ofReal hicost (ae_of_all _ hcost)]
  rw [smul_eq_mul, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul μ.mass.coe_nonneg,
    negExp_ofReal (mul_nonneg μ.mass.coe_nonneg (integral_nonneg hcost))]
  rw [integral_sub (integrable_const 1) hi, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  ring


omit [Nonempty E] in
lemma laplace_partial_tendsto (P : Measure (ℕ → Measure E)) [IsFiniteMeasure P]
    {a : Measure E → ℝ≥0∞} (ha : Measurable a) :
    Tendsto (fun n => ∫ ω, negExp (∑ i : Fin n, a (ω i)) ∂P)
      atTop (𝓝 (∫ ω, negExp (∑' i, a (ω i)) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    have hm : Measurable (fun ω : ℕ → Measure E => ∑ i : Fin n, a (ω i)) :=
      Finset.measurable_sum (Finset.univ : Finset (Fin n))
        (fun i _ => ha.comp (measurable_pi_apply (i : ℕ)))
    exact (continuous_negExp.measurable.comp hm).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]
      exact negExp_le_one _
  · exact ae_of_all _ fun ω => by
      simp_rw [Fin.sum_univ_eq_sum_range (fun i => a (ω i))]
      exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)

lemma poissonProductLaw_laplace_partial (μ : Measure E) [SFinite μ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) (n : ℕ) :
    (∫ ω, negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (ψ x) ∂ω i) ∂poissonProductLaw μ) =
      negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂sfiniteSeq μ i) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hind : iIndepFun (fun i (ω : ℕ → Measure E) => negExp (a (ω i))) (poissonProductLaw μ) :=
    iIndepFun_infinitePi (fun _ => heval)
  have hh := (hind.precomp Fin.val_injective).integral_fun_prod_eq_prod_integral
    (fun i : Fin n => (heval.comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable)
  have hei (i : ℕ) :
      (∫ ω, negExp (a (ω i)) ∂poissonProductLaw μ) =
        negExp (∫⁻ x, c x ∂sfiniteSeq μ i) := by
    calc
      _ = ∫ ν, negExp (a ν) ∂poissonComponentLaw μ i :=
        (measurePreserving_eval_infinitePi (poissonComponentLaw μ) i).hasLaw.integral_comp
          heval.aestronglyMeasurable
      _ = _ := finitePoissonLaw_laplace ⟨sfiniteSeq μ i, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩ hψ hpos
  simpa only [negExp_sum, hei] using hh

 

theorem poissonLaw_laplace (μ : Measure E) [SFinite μ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂poissonLaw μ) =
      negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂μ) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hlim := laplace_partial_tendsto (poissonProductLaw μ) ha
  have hr : Tendsto (fun n => negExp (∑ i : Fin n, ∫⁻ x, c x ∂sfiniteSeq μ i))
      atTop (𝓝 (negExp (∫⁻ x, c x ∂μ))) := by
    have hsum : (∑' i, ∫⁻ x, c x ∂sfiniteSeq μ i) = ∫⁻ x, c x ∂μ := by
      rw [← lintegral_sum_measure, sum_sfiniteSeq]
    simp_rw [Fin.sum_univ_eq_sum_range (fun i => ∫⁻ x, c x ∂sfiniteSeq μ i)]
    rw [← hsum]
    exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)
  rw [poissonLaw, integral_map measurable_measureSum.aemeasurable
    heval.aestronglyMeasurable]
  change (∫ ω, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂Measure.sum ω) ∂poissonProductLaw μ) = _
  simp_rw [lintegral_sum_measure]
  exact tendsto_nhds_unique (by
    simpa only [a, poissonProductLaw_laplace_partial μ hψ hpos] using hlim) hr


lemma laplace_finite_coordinates_unique {ι : Type*} [Fintype ι]
    (P Q : Measure (ι → ℝ≥0∞)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ k : ι → ℕ,
      (∫ x, negExp (∑ i, (k i : ℝ≥0∞) * x i) ∂P) =
      ∫ x, negExp (∑ i, (k i : ℝ≥0∞) * x i) ∂Q) : P = Q := by
  classical
  let g : ι → ((ι → ℝ≥0∞) →ᵇ ℝ) := fun i =>
    negExpBCF.compContinuous ⟨fun x => x i, continuous_apply i⟩
  let ev : MvPolynomial ι ℝ →ₐ[ℝ] ((ι → ℝ≥0∞) →ᵇ ℝ) := MvPolynomial.aeval g
  let A : StarSubalgebra ℝ ((ι → ℝ≥0∞) →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hap (i : ι) (x : ι → ℝ≥0∞) : g i x = negExp (x i) := rfl
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by contrapose! hxy; exact funext hxy
    refine ⟨g i, ?_, ?_⟩
    · refine ⟨(g i).toContinuousMap, ?_, rfl⟩
      exact ⟨g i, ⟨MvPolynomial.X i, by simp [ev]⟩, rfl⟩
    · simpa only [hap] using
        (fun h => hi (negExp_injective h))
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p, rfl⟩ := hf
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, BoundedContinuousFunction.coe_add, Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial k r =>
    have hev (x : ι → ℝ≥0∞) : ev (MvPolynomial.monomial k r) x =
        r * negExp (∑ i, (k i : ℝ≥0∞) * x i) := by
      simp only [ev, MvPolynomial.aeval_monomial]
      rw [negExp_sum]
      simp only [negExp_nat_mul]
      simp [Finsupp.prod_fintype, hap]
    change (∫ x, ev (MvPolynomial.monomial k r) x ∂P) =
      ∫ x, ev (MvPolynomial.monomial k r) x ∂Q
    simp only [hev, integral_const_mul]
    exact congrArg (r * ·) (h fun i => k i)

lemma measure_eq_of_map_eq_comap {E F : Type*} [mE : MeasurableSpace E]
    [mF : MeasurableSpace F] {f : E → F}
    (hf : mE = mF.comap f) {P Q : Measure E} (h : P.map f = Q.map f) : P = Q := by
  have hfm : Measurable f := measurable_iff_comap_le.mpr hf.ge
  ext s hs
  rw [hf] at hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  exact (Measure.map_apply hfm ht).symm.trans ((congrArg (fun μ : Measure F => μ t) h).trans
    (Measure.map_apply hfm ht))

omit [Nonempty E] in
lemma measurable_measureCoordinates : Measurable (measureCoordinates (E := E)) :=
  Measurable.of_eval fun coordinate => Measure.measurable_coe coordinate.2

omit [Nonempty E] in
lemma measureSpace_eq_comap_coordinates :
    (inferInstance : MeasurableSpace (Measure E)) =
      MeasurableSpace.comap measureCoordinates (inferInstance : MeasurableSpace
        ({s : Set E // MeasurableSet s} → ℝ≥0∞)) := by
  apply le_antisymm
  · let m := MeasurableSpace.comap (measureCoordinates (E := E)) inferInstance
    have hc : @Measurable (Measure E) _ m _ measureCoordinates :=
      measurable_iff_comap_le.mpr le_rfl
    have hi : @Measurable (Measure E) (Measure E) m Measure.instMeasurableSpace id := by
      apply @Measure.measurable_of_measurable_coe E (Measure E) _ m id
      intro s hs
      change @Measurable (Measure E) ℝ≥0∞ m _
        (fun ν => measureCoordinates ν ⟨s, hs⟩)
      exact (measurable_pi_apply ⟨s, hs⟩).comp hc
    simpa only [MeasurableSpace.comap_id] using hi.comap_le
  · exact measurable_measureCoordinates.comap_le

omit [Nonempty E] in
 
theorem randomMeasure_laplace_unique (P Q : Measure (Measure E))
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ ψ : E → ℝ, Measurable ψ → (∀ x, 0 ≤ ψ x) →
      (∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂P) =
      ∫ ν, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) ∂Q) : P = Q := by
  classical
  apply measure_eq_of_map_eq_comap measureSpace_eq_comap_coordinates
  apply IsProjectiveLimit.unique (P := fun I =>
    (P.map measureCoordinates).map I.restrict) (fun _ => rfl)
  intro I
  change (Q.map measureCoordinates).map I.restrict = (P.map measureCoordinates).map I.restrict
  rw [Measure.map_map I.measurable_restrict
      measurable_measureCoordinates,
    Measure.map_map I.measurable_restrict
      measurable_measureCoordinates]
  let e : Measure E → (I → ℝ≥0∞) := fun ν i => ν i.1.1
  have he : Measurable e := Measurable.of_eval fun coordinate =>
    Measure.measurable_coe coordinate.1.2
  change Q.map e = P.map e
  apply laplace_finite_coordinates_unique
  intro k
  let ψ : E → ℝ := fun x => ∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ)) x
  have hposi (i : I) (x : E) : 0 ≤ i.1.1.indicator (fun _ => (k i : ℝ)) x := by
    apply indicator_nonneg
    intro _ _
    positivity
  have hpos (x : E) : 0 ≤ ψ x := Finset.sum_nonneg (fun i _ => hposi i x)
  have hm : Measurable ψ := Finset.measurable_sum _ (fun i _ =>
    measurable_const.indicator i.1.2)
  have hoint (ν : Measure E) :
      (∫⁻ x, ENNReal.ofReal (ψ x) ∂ν) = ∑ i : I, (k i : ℝ≥0∞) * e ν i := by
    have ho (x : E) : ENNReal.ofReal (ψ x) =
        ∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ≥0∞)) x := by
      change ENNReal.ofReal (∑ i : I, i.1.1.indicator (fun _ => (k i : ℝ)) x) = _
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hposi i x)]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : x ∈ i.1.1 <;> simp [hx]
    simp_rw [ho]
    rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator i.1.2)]
    apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_indicator i.1.2, lintegral_const, Measure.restrict_apply_univ]
  have hcm : Measurable (fun x : I → ℝ≥0∞ => negExp (∑ i, (k i : ℝ≥0∞) * x i)) :=
    continuous_negExp.measurable.comp (Finset.measurable_sum _
      (fun i _ => measurable_const.mul (measurable_pi_apply i)))
  rw [integral_map he.aemeasurable hcm.aestronglyMeasurable,
    integral_map he.aemeasurable hcm.aestronglyMeasurable]
  simpa only [hoint] using (h ψ hm hpos).symm

end IsingPerceptron

 
namespace IsingPerceptron

 

theorem poissonLaw_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : Measure E) [SFinite μ] {T : E → F}
    (hT : Measurable T) [SFinite (μ.map T)] :
    (poissonLaw μ).map (fun ν => ν.map T) = poissonLaw (μ.map T) := by
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  have hm : Measurable (fun ν : Measure F => negExp (∫⁻ y, ENNReal.ofReal (ψ y) ∂ν)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [integral_map (Measure.measurable_map T hT).aemeasurable hm.aestronglyMeasurable]
  simp_rw [lintegral_map hψ.ennreal_ofReal hT]
  rw [poissonLaw_laplace μ (ψ := fun x => ψ (T x)) (hψ.comp hT) (fun x => hpos (T x)),
    poissonLaw_laplace (μ.map T) hψ hpos,
    lintegral_map (by fun_prop) hT]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_LabeledSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labeled Sampling. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
open Function

lemma measurable_lintegral_pointwiseFinite {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel A B) (hκ : ∀ a, IsFiniteMeasure (κ a))
    {f : A × B → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a,b) ∂κ a) := by
  classical
  let F : ℕ → SimpleFunc (A × B) ℝ≥0∞ := SimpleFunc.eapprox f
  have h : ∀ a b, ⨆ n, F n (a,b) = f (a,b) :=
    fun a b => SimpleFunc.iSup_eapprox_apply hf (a,b)
  simp_rw [← h]
  have he (a : A) : (∫⁻ b, ⨆ n, F n (a,b) ∂κ a) =
      ⨆ n, ∫⁻ b, F n (a,b) ∂κ a := by
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox f hij _
  simp_rw [he]
  refine Measurable.iSup fun n => ?_
  refine SimpleFunc.induction (motive := fun g =>
    Measurable (fun a => ∫⁻ b, g (a,b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    have hi (a : A) : (∫⁻ b, t.indicator (fun _ => c) (a,b) ∂κ a) =
        c * κ a (Prod.mk a ⁻¹' t) := by
      simp_rw [← indicator_comp_right (Prod.mk a)]
      rw [lintegral_indicator (ht.preimage measurable_prodMk_left)]
      simp only [Function.comp_apply, lintegral_const, Measure.restrict_apply_univ]
    change Measurable (fun a => ∫⁻ b, t.indicator (fun _ => c) (a,b) ∂κ a)
    simp_rw [hi]
    exact measurable_const.mul (Kernel.measurable_kernel_prodMk_left_of_finite ht hκ)
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have ha (a : A) : (∫⁻ b, g₁ (a,b) + g₂ (a,b) ∂κ a) =
        (∫⁻ b, g₁ (a,b) ∂κ a) + ∫⁻ b, g₂ (a,b) ∂κ a :=
      lintegral_add_left (g₁.measurable.comp measurable_prodMk_left) _
    simp_rw [ha]
    exact hm₁.add hm₂


lemma finitePartKernel_finite {E : Type*} [MeasurableSpace E] (ν : Measure E) :
    IsFiniteMeasure (finitePartKernel ν) := by
  by_cases h : ν univ < ∞
  · change IsFiniteMeasure (if ν univ < ∞ then ν else 0)
    simp only [ite_eq_left h]
    exact ⟨h⟩
  · change IsFiniteMeasure (if ν univ < ∞ then ν else 0)
    simp only [ite_eq_right h]
    infer_instance

lemma measurable_finitePart_lintegral {E : Type*} [MeasurableSpace E]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun ν : Measure E => ∫⁻ x, F (x,ν) ∂finitePartKernel ν) :=
  measurable_lintegral_pointwiseFinite finitePartKernel finitePartKernel_finite
    (hF.comp measurable_swap)

lemma infinitePi_indep_eval_rest {ι E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)] (i : ι) :
    IndepFun (fun ω : ι → E => ω i)
      (fun ω : ι → E => fun j : {j : ι // j ≠ i} => ω j) (Measure.infinitePi P) := by
  let m : ι → MeasurableSpace (ι → E) := fun j =>
    MeasurableSpace.comap (fun ω => ω j) inferInstance
  have hi : iIndep m (Measure.infinitePi P) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have h := indep_iSup_of_disjoint (m := m) (fun j => (measurable_pi_apply j).comap_le) hi
    (S := {i}) (T := {j | j ≠ i}) (by simp)
  change Indep (MeasurableSpace.comap (fun ω : ι → E => ω i) inferInstance)
    (MeasurableSpace.comap (fun ω : ι → E => fun j : {j : ι // j ≠ i} => ω j)
      inferInstance) (Measure.infinitePi P)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_ofPred_eq, m] using h

lemma infinitePi_eval_rest_map {ι E : Type*} [MeasurableSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)] (i : ι) :
    (Measure.infinitePi P).map (fun ω : ι → E =>
      (ω i, fun j : {j : ι // j ≠ i} => ω j)) =
      (P i).prod (Measure.infinitePi (fun j : {j : ι // j ≠ i} => P j)) := by
  have hmap := IndepFun.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable
    (Measurable.of_eval fun j : {j : ι // j ≠ i} =>
      measurable_pi_apply (j : ι)).aemeasurable (infinitePi_indep_eval_rest P i)
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective] at hmap
  exact hmap

lemma measureSum_eq_eval_add_rest {E : Type*} [MeasurableSpace E]
    (ω : ℕ → Measure E) (i : ℕ) :
    Measure.sum ω = ω i + Measure.sum (fun j : {j : ℕ // j ≠ i} => ω j) := by
  classical
  ext s hs
  simp only [Measure.sum_apply _ hs, Measure.add_apply]
  rw [ENNReal.tsum_eq_add_tsum_ite i]
  congr 1
  trans ∑' j : ℕ, {j : ℕ | j ≠ i}.indicator (fun j => ω j s) j
  · apply tsum_congr
    intro j
    by_cases h : j = i <;> simp [h]
  · exact (tsum_subtype {j : ℕ | j ≠ i} (fun j => ω j s)).symm

variable {E : Type*} [MeasurableSpace E]

lemma measurable_atomCloud (n : ℕ) : Measurable (atomCloud (E := E) (n := n)) := by
  exact Finset.measurable_sum _ (fun i _ => Measure.measurable_dirac.comp
    (measurable_pi_apply i))

lemma atomCloud_insertNth {n : ℕ} (i : Fin (n+1)) (x : E) (ω : Fin n → E) :
    atomCloud (i.insertNth x ω) = Measure.dirac x + atomCloud ω := by
  classical
  rw [atomCloud, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rfl

lemma atomCloud_lintegral {n : ℕ} (ω : Fin n → E) {f : E → ℝ≥0∞}
    (hf : Measurable f) : (∫⁻ x, f x ∂atomCloud ω) = ∑ i, f (ω i) := by
  simp [atomCloud, lintegral_finsetSum_measure, lintegral_dirac' _ hf]

lemma iid_point_insertion (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (i : Fin (n+1)) :
    (∫⁻ ω : Fin (n+1) → E, F (ω i, atomCloud ω) ∂Measure.pi (fun _ => μ)) =
      ∫⁻ x, ∫⁻ ω : Fin n → E, F (x, Measure.dirac x + atomCloud ω)
        ∂Measure.pi (fun _ => μ) ∂μ := by
  have hm : Measurable (fun p : E × (Fin n → E) =>
      F (p.1, Measure.dirac p.1 + atomCloud p.2)) :=
    hF.comp (measurable_fst.prodMk ((Measure.measurable_dirac.comp measurable_fst).add
      ((measurable_atomCloud n).comp measurable_snd)))
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
    |>.lintegral_comp (hF.comp ((measurable_pi_apply i).prodMk
      (measurable_atomCloud (n+1))))
  simp only [Function.comp_apply] at h
  have he (p : E × (Fin n → E)) :
      F (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) i).symm p) i,
        atomCloud ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) i).symm p)) =
      F (p.1, Measure.dirac p.1 + atomCloud p.2) := by
    change F ((i.insertNth (α := fun _ => E) p.1 p.2) i,
      atomCloud (i.insertNth (α := fun _ => E) p.1 p.2)) = _
    rw [Fin.insertNth_apply_same, atomCloud_insertNth]
  simp_rw [he] at h
  exact h.symm.trans (lintegral_prod _ hm.aemeasurable)

lemma iid_sum_point_insertion (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) (n : ℕ) :
    (∫⁻ ω : Fin (n+1) → E, ∑ i, F (ω i, atomCloud ω) ∂Measure.pi (fun _ => μ)) =
      (n+1 : ℝ≥0∞) * ∫⁻ x, ∫⁻ ω : Fin n → E, F (x, Measure.dirac x + atomCloud ω)
        ∂Measure.pi (fun _ => μ) ∂μ := by
  rw [lintegral_finsetSum Finset.univ (f := fun i (ω : Fin (n+1) → E) => F (ω i, atomCloud ω)) (fun i _ =>
    (hF.comp ((measurable_pi_apply i).prodMk (measurable_atomCloud (n+1)))))]
  simp only [iid_point_insertion μ hF n, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

lemma poissonWeight_succ (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℝ≥0∞) = r * poissonWeight r n := by
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n+1 : ℝ) ≠ 0 := by positivity
  have he : (Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / ((n+1).factorial : ℝ)) * (n+1) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hh := congrArg ENNReal.ofReal he
  simpa only [poissonWeight, ENNReal.ofReal_mul (by positivity :
      0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / ((n+1).factorial : ℝ)),
    ENNReal.ofReal_add (by positivity : 0 ≤ (n : ℝ)) (by positivity : 0 ≤ (1 : ℝ)),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_mul r.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] using hh

lemma iid_restrict_lintegral (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ)
    {H : (Fin n → E) → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ ω : ℕ → E, H (fun i => ω i) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ ω : Fin n → E, H ω ∂Measure.pi (fun _ => μ) := by
  have hp : MeasurePreserving (fun ω : ℕ → E => fun i : Fin n => ω i)
      (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : Fin n => μ)) := by
    refine ⟨Measurable.of_eval fun index => measurable_pi_apply (index : ℕ), ?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  exact hp.lintegral_comp hH

lemma lintegral_finitePoissonCloud (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {H : Measure E → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ p, H (finiteCloudMeasure p) ∂finitePoissonCloud r μ) =
      ∑' n, poissonWeight r n * ∫⁻ ω : Fin n → E, H (atomCloud ω)
        ∂Measure.pi (fun _ => μ) := by
  rw [finitePoissonCloud, lintegral_prod (fun p => H (finiteCloudMeasure p)) (hH.comp measurable_finiteCloudMeasure).aemeasurable]
  have hi (n : ℕ) :
      (∫⁻ ω : ℕ → E, H (finiteCloudMeasure (n, ω))
        ∂Measure.infinitePi (fun _ : ℕ => μ)) =
      ∫⁻ ω : Fin n → E, H (atomCloud ω) ∂Measure.pi (fun _ => μ) :=
    iid_restrict_lintegral μ n (hH.comp (measurable_atomCloud n))
  simp_rw [hi]
  rw [poissonMeasure, lintegral_sum_measure]
  simp [lintegral_smul_measure, poissonWeight, smul_eq_mul, lintegral_dirac]

 

theorem finitePoissonCloud_insertion (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F)
    :
    (∫⁻ p, ∫⁻ x, F (x, finiteCloudMeasure p) ∂finitePartKernel (finiteCloudMeasure p)
      ∂finitePoissonCloud r μ) =
      r * ∫⁻ x, ∫⁻ p, F (x, Measure.dirac x + finiteCloudMeasure p)
        ∂finitePoissonCloud r μ ∂μ := by
  rw [lintegral_finitePoissonCloud r μ (measurable_finitePart_lintegral hF)]
  have hm (x : E) : Measurable (fun ν : Measure E => F (x, Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  simp_rw [lintegral_finitePoissonCloud r μ (hm _)]
  have hi (n : ℕ) (ω : Fin n → E) : (∫⁻ x, F (x, atomCloud ω) ∂finitePartKernel (atomCloud ω)) =
      ∑ i, F (ω i, atomCloud ω) := by
    have hfin : IsFiniteMeasure (atomCloud ω) := by unfold atomCloud; infer_instance
    have he : finitePartKernel (atomCloud ω) = atomCloud ω :=
      ite_eq_left (measure_lt_top _ _)
    rw [he]
    exact atomCloud_lintegral ω (hF.comp (measurable_id.prodMk measurable_const))
  simp_rw [hi]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Fin.sum_univ_zero, lintegral_zero, mul_zero, zero_add]
  simp_rw [iid_sum_point_insertion μ hF, ← mul_assoc, poissonWeight_succ]
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have hmj (n : ℕ) : Measurable (fun p : E × (Fin n → E) =>
      F (p.1, Measure.dirac p.1 + atomCloud p.2)) :=
    hF.comp (measurable_fst.prodMk ((Measure.measurable_dirac.comp measurable_fst).add
      ((measurable_atomCloud n).comp measurable_snd)))
  have hmi (n : ℕ) : Measurable (fun x => ∫⁻ ω : Fin n → E,
      F (x, Measure.dirac x + atomCloud ω) ∂Measure.pi (fun _ => μ)) :=
    (hmj n).lintegral_prod_right
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    rw [lintegral_const_mul _ (hmi n)]
  · intro n
    exact (measurable_const.mul (hmi n)).aemeasurable

lemma measurable_measureSum_countable {ι : Type*} [Countable ι] :
    Measurable (Measure.sum : (ι → Measure E) → Measure E) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun i => (Measure.measurable_coe hs).comp (measurable_pi_apply i)

lemma measurable_finitePart_param {A : Type*} [MeasurableSpace A]
    {N : A → Measure E} (hN : Measurable N) {F : A × E → ℝ≥0∞}
    (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂finitePartKernel (N a)) := by
  let κ : Kernel A E := ⟨fun a => finitePartKernel (N a),
    finitePartKernel.measurable.comp hN⟩
  exact measurable_lintegral_pointwiseFinite κ
    (fun a => finitePartKernel_finite (N a)) hF

variable [Nonempty E]

lemma finitePoissonLaw_finite (μ : FiniteMeasure E) :
    ∀ᵐ ν ∂finitePoissonLaw μ, ν univ < ∞ := by
  rw [finitePoissonLaw, ae_map_iff measurable_finiteCloudMeasure.aemeasurable
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)]
  exact ae_of_all _ fun p => by
    have : IsFiniteMeasure (finiteCloudMeasure p) := by
      unfold finiteCloudMeasure
      first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
    exact measure_lt_top _ _

lemma finitePoissonLaw_insertion (μ : FiniteMeasure E)
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ν, ∫⁻ x, F (x,ν) ∂finitePartKernel ν ∂finitePoissonLaw μ) =
      ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν) ∂finitePoissonLaw μ ∂(μ : Measure E) := by
  have hm (x : E) : Measurable (fun ν : Measure E => F (x,Measure.dirac x + ν)) :=
    hF.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  rw [finitePoissonLaw, lintegral_map (measurable_finitePart_lintegral hF)
    measurable_finiteCloudMeasure]
  simp_rw [lintegral_map (hm _) measurable_finiteCloudMeasure]
  rw [finiteMeasure_mass_normalize μ, lintegral_smul_measure, smul_eq_mul]
  exact finitePoissonCloud_insertion μ.mass _ hF

 
lemma poissonComponent_insertion (μ : Measure E) [SFinite μ] (i : ℕ)
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ x, F (x, Measure.sum ω) ∂finitePartKernel (ω i)
      ∂poissonProductLaw μ) =
      ∫⁻ x, ∫⁻ ω, F (x, Measure.dirac x + Measure.sum ω)
        ∂poissonProductLaw μ ∂sfiniteSeq μ i := by
  let R := {j : ℕ // j ≠ i}
  let P := poissonComponentLaw μ
  let rest : (R → Measure E) → Measure E := Measure.sum
  have hrest : Measurable rest := measurable_measureSum_countable
  let joint := fun ω : ℕ → Measure E => (ω i, fun j : R => ω j)
  have hjoint : Measurable joint := (measurable_pi_apply i).prodMk
    (Measurable.of_eval fun index : R => measurable_pi_apply (index : ℕ))
  have hjlaw : (poissonProductLaw μ).map joint =
      (P i).prod (Measure.infinitePi (fun j : R => P j)) :=
    infinitePi_eval_rest_map P i
  have hI : Measurable (fun p : Measure E × (R → Measure E) =>
      ∫⁻ x, F (x,p.1 + rest p.2) ∂finitePartKernel p.1) := by
    apply measurable_finitePart_param measurable_fst (F := fun p => F (p.2,p.1.1 + rest p.1.2))
    exact hF.comp (measurable_snd.prodMk
      ((measurable_fst.comp measurable_fst).add
        (hrest.comp (measurable_snd.comp measurable_fst))))
  have hR (x : E) : Measurable (fun p : Measure E × (R → Measure E) =>
      F (x,Measure.dirac x + (p.1 + rest p.2))) :=
    hF.comp (measurable_const.prodMk (measurable_const.add
      (measurable_fst.add (hrest.comp measurable_snd))))
  have he (ω : ℕ → Measure E) : Measure.sum ω = (joint ω).1 + rest (joint ω).2 :=
    measureSum_eq_eval_add_rest ω i
  simp_rw [he]
  rw [← lintegral_map hI hjoint, hjlaw,
    lintegral_prod_symm _ hI.aemeasurable]
  simp_rw [← lintegral_map (hR _) hjoint, hjlaw]
  have hFp (ω : R → Measure E) : Measurable (fun p : E × Measure E =>
      F (p.1,p.2 + rest ω)) :=
    hF.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))
  have hins (ω : R → Measure E) :
      (∫⁻ ν, ∫⁻ x, F (x,ν + rest ω) ∂finitePartKernel ν ∂P i) =
        ∫⁻ x, ∫⁻ ν, F (x,Measure.dirac x + ν + rest ω) ∂P i ∂sfiniteSeq μ i :=
    finitePoissonLaw_insertion ⟨sfiniteSeq μ i, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩ (hFp ω)
  simp_rw [hins]
  have hJ : Measurable (fun p : (R → Measure E) × E =>
      ∫⁻ ν, F (p.2,Measure.dirac p.2 + ν + rest p.1) ∂P i) := by
    have hm : Measurable (fun p : ((R → Measure E) × E) × Measure E =>
        F (p.1.2,Measure.dirac p.1.2 + p.2 + rest p.1.1)) :=
      hF.comp ((measurable_snd.comp measurable_fst).prodMk
        (((Measure.measurable_dirac.comp (measurable_snd.comp measurable_fst)).add
          measurable_snd).add (hrest.comp (measurable_fst.comp measurable_fst))))
    exact hm.lintegral_prod_right
  rw [lintegral_lintegral_swap hJ.aemeasurable]
  congr 1
  funext x
  rw [lintegral_prod_symm _ (hR x).aemeasurable]
  simp only [add_assoc]

lemma poissonProductLaw_finite (μ : Measure E) [SFinite μ] :
    ∀ᵐ ω ∂poissonProductLaw μ, ∀ i, ω i univ < ∞ := by
  rw [ae_all_iff]
  intro i
  have h := finitePoissonLaw_finite (⟨sfiniteSeq μ i, by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩ : FiniteMeasure E)
  have he : (poissonProductLaw μ).map (fun ω => ω i) = poissonComponentLaw μ i :=
    Measure.infinitePi_map_eval _ i
  change ∀ᵐ ν ∂poissonComponentLaw μ i, ν univ < ∞ at h
  rw [← he] at h
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)).mp h

 
theorem poissonProductLaw_insertion (μ : Measure E) [SFinite μ]
    {F : E × Measure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, ∫⁻ x, F (x, Measure.sum ω) ∂Measure.sum ω ∂poissonProductLaw μ) =
      ∫⁻ x, ∫⁻ ω, F (x, Measure.dirac x + Measure.sum ω)
        ∂poissonProductLaw μ ∂μ := by
  have ha : (fun ω : ℕ → Measure E => ∫⁻ x, F (x,Measure.sum ω) ∂Measure.sum ω) =ᵐ[
      poissonProductLaw μ] (fun ω => ∑' i, ∫⁻ x, F (x,Measure.sum ω) ∂finitePartKernel (ω i)) := by
    filter_upwards [poissonProductLaw_finite μ] with ω hω
    rw [lintegral_sum_measure]
    apply tsum_congr
    intro i
    rw [show finitePartKernel (ω i) = ω i from ite_eq_left (hω i)]
  rw [lintegral_congr_ae ha, lintegral_tsum]
  · simp_rw [poissonComponent_insertion μ _ hF]
    rw [← lintegral_sum_measure, sum_sfiniteSeq]
  · intro i
    apply Measurable.aemeasurable
    apply measurable_finitePart_param (measurable_pi_apply i)
      (F := fun p => F (p.2,Measure.sum p.1))
    exact hF.comp (measurable_snd.prodMk (measurable_measureSum.comp measurable_fst))

lemma poissonProductLaw_mean_count (μ : Measure E) [SFinite μ]
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ ω, Measure.sum ω s ∂poissonProductLaw μ) = μ s := by
  have hF : Measurable (fun p : E × Measure E => s.indicator (fun _ => (1 : ℝ≥0∞)) p.1) :=
    (measurable_const.indicator hs).comp measurable_fst
  have h := poissonProductLaw_insertion μ hF
  simpa only [lintegral_indicator_const hs, one_mul, lintegral_const,
    measure_univ, mul_one] using h

lemma poissonLaw_mean_count (μ : Measure E) [SFinite μ]
    {s : Set E} (hs : MeasurableSet s) :
    (∫⁻ ν, ν s ∂poissonLaw μ) = μ s := by
  rw [poissonLaw, lintegral_map (Measure.measurable_coe hs) measurable_measureSum]
  exact poissonProductLaw_mean_count μ hs

omit [Nonempty E] in
lemma measurable_measureRestrict {s : Set E} (hs : MeasurableSet s) :
    Measurable (fun ν : Measure E => ν.restrict s) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hs)



lemma sigmaPart_eq_ae (μ : Measure E) [SigmaFinite μ] :
    ∀ᵐ ν ∂poissonLaw μ, sigmaPart μ ν = ν := by
  have ha : ∀ n, ∀ᵐ ν ∂poissonLaw μ,
      ν (disjointed (spanningSets μ) n) < ∞ := by
    intro n
    have hm := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
    apply ae_lt_top (Measure.measurable_coe hm)
    rw [poissonLaw_mean_count μ hm]
    exact ((measure_mono (disjointed_subset _ _)).trans_lt
      (measure_spanningSets_lt_top μ n)).ne
  filter_upwards [ae_all_iff.mpr ha] with ν hν
  unfold sigmaPart
  calc
    _ = Measure.sum (fun n => ν.restrict (disjointed (spanningSets μ) n)) := by
      congr 1
      funext n
      apply ite_eq_left
      simpa only [Measure.restrict_apply_univ] using hν n
    _ = ν := sum_restrict_disjointed_spanningSets ν μ

omit [Nonempty E] in
lemma measurable_sigmaPart_param (μ : Measure E) [SigmaFinite μ]
    {A : Type*} [MeasurableSpace A] {N : A → Measure E} (hN : Measurable N)
    {F : A × E → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun a => ∫⁻ x, F (a,x) ∂sigmaPart μ (N a)) := by
  simp only [sigmaPart, lintegral_sum_measure]
  apply Measurable.tsum
  intro n
  exact measurable_finitePart_param
    ((measurable_measureRestrict (MeasurableSet.disjointed (measurableSet_spanningSets μ) n)).comp hN) hF

end IsingPerceptron


end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_MapWithDensityEquiv
attribute [-instance] _root_.OAI.IsingPerceptron.powerIntensity_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Map With Density Equiv. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma map_withDensity_equiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (e : E ≃ᵐ F) (μ : Measure E) {w : E → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w).map e = (μ.map e).withDensity (w ∘ e.symm) := by
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    _ = ∫⁻ x, w x * f (e x) ∂μ := by
      rw [lintegral_map hf e.measurable]
      exact lintegral_withDensity_eq_lintegral_mul μ hw
        (show Measurable (fun x => f (e x)) from hf.comp e.measurable)
    _ = ∫⁻ x, (w (e.symm x) * f x) ∂μ.map e := by
      simpa only [Pi.mul_apply, Function.comp_apply, e.symm_apply_apply] using
        (lintegral_map (μ := μ) ((hw.comp e.symm.measurable).mul hf) e.measurable).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _
      (hw.comp e.symm.measurable) hf).symm

lemma measurable_powerIntensityDensity (b : ℝ) : Measurable (powerIntensityDensity b) := by
  unfold powerIntensityDensity
  apply Measurable.ennreal_ofReal
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · fun_prop
  · fun_prop

lemma powerIntensityDensity_scale {b c : ℝ} (hc : 0 < c) (x : ℝ) :
    ENNReal.ofReal c⁻¹ * powerIntensityDensity b (c⁻¹ * x) =
      ENNReal.ofReal (c ^ b) * powerIntensityDensity b x := by
  have hpos : 0 < c⁻¹ * x ↔ 0 < x := mul_pos_iff_of_pos_left (inv_pos.mpr hc)
  unfold powerIntensityDensity
  by_cases hx : 0 < x
  · simp only [ite_eq_left hx, ite_eq_left (hpos.mpr hx)]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le b)]
    congr 1
    rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hx.le,
      Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
    have he : c⁻¹ * c ^ (-(-1-b)) = c ^ b := by
      rw [show -(-1-b) = b + 1 by ring, Real.rpow_add hc]
      simp only [Real.rpow_one]
      field_simp
    calc
       c⁻¹ * (b * (c ^ (-(-1-b)) * x ^ (-1-b))) =
           b * (c⁻¹ * c ^ (-(-1-b))) * x ^ (-1-b) := by ring
       _ = c ^ b * (b * x ^ (-1-b)) := by rw [he]; ring
  · simp only [ite_eq_right hx, ite_eq_right (fun h => hx (hpos.mp h)), ENNReal.ofReal_zero,
      mul_zero]

theorem map_powerIntensity_mul {b c : ℝ} (hc : 0 < c) :
    (powerIntensity b).map (fun x => c*x) =
      ENNReal.ofReal (c ^ b) • powerIntensity b := by
  let e := MeasurableEquiv.mulLeft₀ c hc.ne'
  have hm := map_withDensity_equiv e volume (measurable_powerIntensityDensity b)
  change (volume.withDensity (powerIntensityDensity b)).map e = _
  rw [hm]
  change (volume.map (fun x => c*x)).withDensity
    (fun x => powerIntensityDensity b (c⁻¹*x)) = _
  unfold powerIntensity
  rw [Real.map_volume_mul_left hc.ne', abs_of_pos (inv_pos.mpr hc),
    withDensity_smul_measure, ← withDensity_smul (ENNReal.ofReal c⁻¹)
      (show Measurable (fun x => powerIntensityDensity b (c⁻¹*x)) from
        (measurable_powerIntensityDensity b).comp (measurable_const_mul c⁻¹)),
    ← withDensity_smul (ENNReal.ofReal (c^b)) (measurable_powerIntensityDensity b)]
  congr 1
  funext x
  exact powerIntensityDensity_scale hc x

lemma poissonLaw_congr {E : Type*} [MeasurableSpace E] [Nonempty E]
    {μ ν : Measure E} [SFinite μ] [SFinite ν] (h : μ = ν) : poissonLaw μ = poissonLaw ν := by
  subst ν
  rfl

open Set

lemma integrable_power_min {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable (fun x : ℝ => min 1 (max x 0)) (powerIntensity b) := by
  rw [powerIntensity, integrable_withDensity_iff (measurable_powerIntensityDensity b)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hi : IntegrableOn (fun x : ℝ => x ^ (-b)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have hj : IntegrableOn (fun x : ℝ => x ^ (-1-b)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have H₁ : Integrable ((Ioc (0:ℝ) 1).indicator (fun x => b * x ^ (-b))) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (hi.const_mul b)
  have H₂ : Integrable ((Ioi (1:ℝ)).indicator (fun x => b * x ^ (-1-b))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (hj.const_mul b)
  have H := H₁.add H₂
  apply H.congr
  apply ae_of_all
  intro x
  symm
  simp only [Pi.add_apply]
  by_cases hx : 0 < x
  · simp only [powerIntensityDensity, ite_eq_left hx,
      ENNReal.toReal_ofReal (mul_nonneg hb.le (Real.rpow_nonneg hx.le _)), max_eq_left hx.le]
    by_cases hx1 : x ≤ 1
    · rw [min_eq_right hx1, indicator_of_mem (show x ∈ Ioc (0:ℝ) 1 from ⟨hx,hx1⟩),
        indicator_of_notMem (show x ∉ Ioi (1:ℝ) from not_lt.mpr hx1), add_zero]
      have hp : x * x ^ (-1-b) = x ^ (-b) := by
        calc
          x * x ^ (-1-b) = x ^ (1 + (-1-b)) := by rw [Real.rpow_add hx, Real.rpow_one]
          _ = x ^ (-b) := by congr 1; ring
      nlinarith [hp]
    · rw [min_eq_left (le_of_lt (lt_of_not_ge hx1)), one_mul,
        indicator_of_notMem (show x ∉ Ioc (0:ℝ) 1 from fun h => hx1 h.2),
        indicator_of_mem (show x ∈ Ioi (1:ℝ) from lt_of_not_ge hx1), zero_add]
  · simp [powerIntensityDensity, hx, max_eq_right (le_of_not_gt hx),
      indicator_of_notMem (show x ∉ Ioi (1:ℝ) from fun h => hx (lt_trans zero_lt_one h))]

lemma measurable_stableLaplaceCost : Measurable stableLaplaceCost := by
  unfold stableLaplaceCost
  fun_prop

lemma stableLaplaceCost_nonneg (x : ℝ) : 0 ≤ stableLaplaceCost x := by
  unfold stableLaplaceCost
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right _ _)))

lemma stableLaplaceCost_le_min (x : ℝ) : stableLaplaceCost x ≤ min 1 (max x 0) := by
  unfold stableLaplaceCost
  exact le_min (by linarith [Real.exp_pos (-max x 0)])
    (by linarith [Real.add_one_le_exp (-max x 0)])

lemma integrable_stableLaplaceCost {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    Integrable stableLaplaceCost (powerIntensity b) := by
  apply (integrable_power_min hb hb1).mono' measurable_stableLaplaceCost.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (stableLaplaceCost_nonneg x)]
    exact stableLaplaceCost_le_min x

lemma stableLaplaceConstant_lt_top {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b < ∞ := by
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ stableLaplaceCost_nonneg)).mp
    (integrable_stableLaplaceCost hb hb1).hasFiniteIntegral

lemma stableLaplaceConstant_pos {b : ℝ} (hb : 0 < b) : 0 < stableLaplaceConstant b := by
  unfold stableLaplaceConstant powerIntensity
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_powerIntensityDensity b)
    measurable_stableLaplaceCost.ennreal_ofReal]
  apply (lintegral_pos_iff_support ((measurable_powerIntensityDensity b).mul
    measurable_stableLaplaceCost.ennreal_ofReal)).mpr
  have hs : Function.support (powerIntensityDensity b * (fun x => ENNReal.ofReal (stableLaplaceCost x))) =
      Ioi (0:ℝ) := by
    ext x
    by_cases hx : 0 < x
    · have hp : 0 < b * x ^ (-1-b) := mul_pos hb (Real.rpow_pos_of_pos hx _)
      have hc : 0 < 1 - Real.exp (-x) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx))
      simp [Function.mem_support, powerIntensityDensity, stableLaplaceCost, hx,
        max_eq_left hx.le, ne_of_gt (ENNReal.ofReal_pos.mpr hp), ne_of_gt (ENNReal.ofReal_pos.mpr hc)]
    · simp [Function.mem_support, powerIntensityDensity, hx]
  rw [hs]
  simp

end IsingPerceptron

namespace IsingPerceptron

lemma integrable_negExp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ≥0∞} (hX : Measurable X) : Integrable (fun ω => negExp (X ω)) P := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (continuous_negExp.measurable.comp hX).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change ‖negExp (X ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (negExp_nonneg _)]
    exact negExp_le_one _

lemma measure_zero_of_integral_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {f : ℕ → Ω → ℝ} (hfi : ∀ n, Integrable (f n) P)
    (hfpos : ∀ n ω, 0 ≤ f n ω) (hb : ∀ n ω, ω ∈ A → 1 ≤ f n ω)
    (ht : Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 0)) : P A = 0 := by
  apply (measureReal_eq_zero_iff (μ := P) (s := A)).mp
  apply le_antisymm _ measureReal_nonneg
  apply ge_of_tendsto' ht
  intro n
  rw [← integral_indicator_one hA]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator hA) (hfi n)
  intro ω
  by_cases hω : ω ∈ A
  · simpa only [indicator_of_mem hω, Pi.one_apply] using hb n ω hω
  · simpa only [indicator_of_notMem hω] using hfpos n ω

theorem stable_laplace_finite_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞}
    (hX : Measurable X) {C b : ℝ} (hC : 0 < C) (hb : 0 < b)
    (hl : ∀ t : ℝ, 0 < t →
      (∫ ω, negExp (ENNReal.ofReal t * X ω) ∂P) = Real.exp (-C * t ^ b)) :
    ∀ᵐ ω ∂P, 0 < X ω ∧ X ω < ∞ := by
  have hi (t : ℝ) : Integrable (fun ω => negExp (ENNReal.ofReal t * X ω)) P :=
    integrable_negExp P (measurable_const.mul hX)
  have hfinite : P {ω | X ω = ∞} = 0 := by
    let t : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
    have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
    apply measure_zero_of_integral_tests P (hX (measurableSet_singleton ∞))
      (f := fun n ω => 1 - negExp (ENNReal.ofReal (t n) * X ω))
    · intro n
      exact (integrable_const 1).sub (hi (t n))
    · intro n ω
      exact sub_nonneg.mpr (negExp_le_one _)
    · intro n ω hω
      change X ω = ∞ at hω
      simp [hω, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (htpos n)))]
    · have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hr : Tendsto (fun n => (t n)^b) atTop (𝓝 0) := by
        simpa only [Function.comp_def, Real.zero_rpow hb.ne'] using (Real.continuous_rpow_const hb.le).continuousAt.tendsto.comp ht
      have he : Tendsto (fun n => 1 - Real.exp (-C * (t n)^b)) atTop (𝓝 0) := by
        simpa only [Function.comp_def, mul_zero, Real.exp_zero, sub_self] using
          (tendsto_const_nhds (x := (1:ℝ))).sub (Real.continuous_exp.continuousAt.tendsto.comp (hr.const_mul (-C)))
      convert he using 1
      all_goals try with_reducible_and_instances rfl
      ext n
      rw [integral_sub (integrable_const 1) (hi (t n)), hl _ (htpos n), integral_const]
      simp
  have hpositive : P {ω | X ω = 0} = 0 := by
    let t : ℕ → ℝ := fun n => (n:ℝ)+1
    have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
    apply measure_zero_of_integral_tests P (hX (measurableSet_singleton 0))
      (f := fun n ω => negExp (ENNReal.ofReal (t n) * X ω))
    · exact fun n => hi (t n)
    · exact fun _ _ => negExp_nonneg _
    · intro n ω hω
      change X ω = 0 at hω
      simp [hω]
    · have ht : Tendsto t atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      have hr := (tendsto_rpow_atTop hb).comp ht
      have he := Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hC hr))
      simpa only [hl _ (htpos _), Function.comp_def, neg_mul] using he
  have hf : ∀ᵐ ω ∂P, X ω ≠ ∞ := by simpa only [ae_iff, not_not] using hfinite
  have hp : ∀ᵐ ω ∂P, X ω ≠ 0 := by simpa only [ae_iff, not_not] using hpositive
  filter_upwards [hf, hp] with ω hf hp
  exact ⟨pos_iff_ne_zero.mpr hp, lt_top_iff_ne_top.mpr hf⟩

lemma stableLaplaceCost_scale (t x : ℝ) (ht : 0 ≤ t) :
    stableLaplaceCost (t*x) = 1-Real.exp (-t * max x 0) := by
  have hm : max (t*x) 0 = t * max x 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg x 0 ht).symm
  rw [stableLaplaceCost, hm]
  congr 2
  ring

lemma powerIntensity_laplace_scale {b t : ℝ} (ht : 0 < t) :
    (∫⁻ x, ENNReal.ofReal (1-Real.exp (-t * max x 0)) ∂powerIntensity b) =
    ENNReal.ofReal (t^b) * stableLaplaceConstant b := by
  simp_rw [← stableLaplaceCost_scale t _ ht.le]
  rw [← lintegral_map measurable_stableLaplaceCost.ennreal_ofReal
    (measurable_const_mul t), map_powerIntensity_mul ht, lintegral_smul_measure]
  rfl

lemma integrable_exp_neg_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => Real.exp (-t * X ω)) P := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [hpos] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hω)

lemma measureReal_mul_le_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    {f : Ω → ℝ} (hf : Integrable f P) (hfpos : 0 ≤ᵐ[P] f) (c : ℝ)
    (hc : ∀ᵐ ω ∂P, ω ∈ A → c ≤ f ω) : P.real A * c ≤ ∫ ω, f ω ∂P := by
  rw [← smul_eq_mul, ← integral_indicator_const c hA]
  apply integral_mono_ae ((integrable_const c).indicator hA) hf
  filter_upwards [hfpos, hc] with ω hp hb
  by_cases hω : ω ∈ A
  · simpa only [indicator_of_mem hω] using hb hω
  · simpa only [indicator_of_notMem hω, Pi.zero_apply] using hp

lemma stable_laplace_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {C b : ℝ}
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b))
    {s : ℝ} (hs : 0 < s) :
    P {ω | s < X ω} ≤ ENNReal.ofReal (C / (1-Real.exp (-1)) * s^(-b)) := by
  have hc : 0 < 1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hi := integrable_exp_neg_mul P hX hpos (inv_nonneg.mpr hs.le)
  have h := measureReal_mul_le_integral P (measurableSet_lt measurable_const hX)
    ((integrable_const 1).sub hi) (by
      filter_upwards [hpos] with ω hω
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [inv_nonneg.mpr hs.le])))
    (1-Real.exp (-1)) (by
      filter_upwards [] with ω hω
      apply sub_le_sub_left
      apply Real.exp_le_exp.mpr
      have hmul : 1 < s⁻¹ * X ω := by
        rw [← div_eq_inv_mul, lt_div_iff₀ hs]
        simpa using hω
      linarith)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const 1) hi, integral_const, hl _ (inv_pos.mpr hs)] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  have hbnd : P.real {ω | s < X ω} ≤ C / (1-Real.exp (-1)) * s^(-b) := by
    have he := Real.add_one_le_exp (-C * (s⁻¹)^b)
    have hp : (s⁻¹)^b = s^(-b) := by rw [Real.inv_rpow hs.le, Real.rpow_neg hs.le]
    rw [hp] at h he
    apply (le_of_mul_le_mul_right _ hc)
    calc
      _ ≤ 1-Real.exp (-C * s^(-b)) := h
      _ ≤ C * s^(-b) := by linarith
      _ = (C / (1-Real.exp (-1)) * s^(-b)) * (1-Real.exp (-1)) := by field_simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hbnd

lemma stable_laplace_inverse_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {C b : ℝ}
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b))
    {s : ℝ} (hs : 0 < s) :
    P {ω | s < (X ω)⁻¹} ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-C*s^b)) := by
  have hi := integrable_exp_neg_mul P hX (hpos.mono fun _ h => h.le) hs.le
  have h := measureReal_mul_le_integral P (measurableSet_lt measurable_const hX.inv) hi
    (ae_of_all _ fun _ => (Real.exp_pos _).le) (Real.exp (-1)) (by
      filter_upwards [hpos] with ω hp hω
      apply Real.exp_le_exp.mpr
      have hmul : s * X ω < 1 := by
        simpa only [mul_one] using (lt_inv_mul_iff₀' hp).mp (show s < (X ω)⁻¹ * 1 by simpa using hω)
      linarith)
  rw [hl _ hs] at h
  have hbnd : P.real {ω | s < (X ω)⁻¹} ≤ Real.exp 1 * Real.exp (-C*s^b) := by
    apply le_of_mul_le_mul_right _ (Real.exp_pos (-1))
    calc
      _ ≤ Real.exp (-C*s^b) := h
      _ = (Real.exp 1 * Real.exp (-C*s^b)) * Real.exp (-1) := by
        rw [mul_comm (Real.exp 1), mul_assoc, ← Real.exp_add]
        simp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hbnd

lemma integrable_rpow_of_power_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω)
    {K b r : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hrb : r < b)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t < X ω} ≤ ENNReal.ofReal (K*t^(-b))) :
    Integrable (fun ω => X ω ^ r) P := by
  have hpow : ∀ᵐ ω ∂P, 0 ≤ X ω ^ r := hpos.mono fun _ h => Real.rpow_nonneg h _
  refine ⟨(hX.pow measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpow, lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hX.aemeasurable hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  let B : ℝ → ℝ := fun t => (Ioc (0:ℝ) 1).indicator (fun u => u^(r-1)) t +
    (Ioi (1:ℝ)).indicator (fun u => K*u^(r-b-1)) t
  have h₁ : IntegrableOn (fun t : ℝ => t^(r-1)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have h₂ : IntegrableOn (fun t : ℝ => K*t^(r-b-1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul K
  have hB : Integrable B (volume.restrict (Ioi 0)) :=
    (((integrable_indicator_iff measurableSet_Ioc).mpr h₁).add
      ((integrable_indicator_iff measurableSet_Ioi).mpr h₂)).restrict
  have hBpos : ∀ t, 0 ≤ B t := by
    intro t
    apply add_nonneg
    · exact (indicator_nonneg (s := Ioc (0:ℝ) 1) (fun u hu => Real.rpow_nonneg hu.1.le (r-1))) t
    · exact (indicator_nonneg (s := Ioi (1:ℝ)) (fun u hu => mul_nonneg hK (Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hu)) (r-b-1)))) t
  have hfin := (hasFiniteIntegral_iff_ofReal (ae_of_all _ hBpos)).mp hB.hasFiniteIntegral
  apply lt_of_le_of_lt _ hfin
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  by_cases ht1 : t ≤ 1
  · have hb : B t = t^(r-1) := by
      simp only [B, indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht0,ht1⟩),
        indicator_of_notMem (show t ∉ Ioi (1:ℝ) from not_lt.mpr ht1), add_zero]
    rw [hb]
    exact mul_le_of_le_one_left' prob_le_one
  · have hb : B t = K*t^(r-b-1) := by
      simp only [B, indicator_of_notMem (show t ∉ Ioc (0:ℝ) 1 from fun h => ht1 h.2),
        indicator_of_mem (show t ∈ Ioi (1:ℝ) from lt_of_not_ge ht1), zero_add]
    rw [hb]
    calc
      _ ≤ ENNReal.ofReal (K*t^(-b)) * ENNReal.ofReal (t^(r-1)) :=
        mul_le_mul_of_nonneg_right (htail t ht0) zero_le
      _ = ENNReal.ofReal (K*t^(r-b-1)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.rpow_nonneg ht0.le _)),
          mul_assoc, ← Real.rpow_add ht0]
        rw [show -b + (r-1) = r-b-1 by ring]

lemma integrable_rpow_of_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω)
    {K C b r : ℝ} (hK : 0 ≤ K) (hC : 0 < C) (hb : 0 < b) (hr : 0 < r)
    (htail : ∀ t : ℝ, 0 < t →
      P {ω | t < X ω} ≤ ENNReal.ofReal (K*Real.exp (-C*t^b))) :
    Integrable (fun ω => X ω ^ r) P := by
  have hpow : ∀ᵐ ω ∂P, 0 ≤ X ω ^ r := hpos.mono fun _ h => Real.rpow_nonneg h _
  refine ⟨(hX.pow measurable_const).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hpow, lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hX.aemeasurable hr]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  have hi : IntegrableOn (fun t : ℝ => K * (t^(r-1) * Real.exp (-C*t^b))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) hb hC).const_mul K
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ K * (t^(r-1) * Real.exp (-C*t^b)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hK (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
  apply lt_of_le_of_lt _ ((hasFiniteIntegral_iff_ofReal hnonneg).mp hi.hasFiniteIntegral)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  calc
    _ ≤ ENNReal.ofReal (K*Real.exp (-C*t^b)) * ENNReal.ofReal (t^(r-1)) :=
      mul_le_mul_of_nonneg_right (htail t ht) zero_le
    _ = ENNReal.ofReal (K*(t^(r-1)*Real.exp (-C*t^b))) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_nonneg _))]
      congr 1
      ring

lemma log_sq_le_powers {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    (Real.log x)^2 ≤ (2/r)^2 * (x^r + (x⁻¹)^r) := by
  have he : 0 < r/2 := by positivity
  have hpow (y : ℝ) (hy : 0 ≤ y) : (y^(r/2)/(r/2))^2 = (2/r)^2 * y^r := by
    rw [div_pow, ← Real.rpow_mul_natCast hy]
    norm_num
    field_simp
  by_cases hlog : 0 ≤ Real.log x
  · have h := (sq_le_sq₀ hlog (div_nonneg (Real.rpow_nonneg hx.le _) he.le)).mpr
      (Real.log_le_rpow_div hx.le he)
    rw [hpow x hx.le] at h
    nlinarith [Real.rpow_nonneg (inv_nonneg.mpr hx.le) r, sq_nonneg (2/r)]
  · have hlog' : 0 ≤ Real.log x⁻¹ := by rw [Real.log_inv]; linarith
    have h := (sq_le_sq₀ hlog' (div_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hx.le) _) he.le)).mpr
      (Real.log_le_rpow_div (inv_nonneg.mpr hx.le) he)
    rw [hpow x⁻¹ (inv_nonneg.mpr hx.le), Real.log_inv, neg_sq] at h
    nlinarith [Real.rpow_nonneg hx.le r, sq_nonneg (2/r)]

theorem integrable_log_sq_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω) {r : ℝ} (hr : 0 < r)
    (hi : Integrable (fun ω => X ω ^ r) P)
    (hj : Integrable (fun ω => (X ω)⁻¹ ^ r) P) :
    Integrable (fun ω => (Real.log (X ω))^2) P := by
  apply ((hi.add hj).const_mul ((2/r)^2)).mono' ((hX.log.pow_const 2).aestronglyMeasurable)
  filter_upwards [hpos] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact log_sq_le_powers hω hr

lemma stable_positive_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 ≤ X ω) {C b r : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hrb : r < b)
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b)) :
    Integrable (fun ω => X ω ^ r) P := by
  apply integrable_rpow_of_power_tail P hX hpos (K := C/(1-Real.exp (-1)))
    (div_nonneg hC.le (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))) hr hrb
  exact fun _ ht => stable_laplace_upper_tail P hX hpos hl ht

lemma stable_negative_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {C b r : ℝ}
    (hC : 0 < C) (hb : 0 < b) (hr : 0 < r)
    (hl : ∀ t : ℝ, 0 < t → (∫ ω, Real.exp (-t * X ω) ∂P) = Real.exp (-C*t^b)) :
    Integrable (fun ω => (X ω)⁻¹ ^ r) P := by
  apply integrable_rpow_of_exp_tail P hX.inv (hpos.mono fun _ h => (inv_pos.mpr h).le)
    (Real.exp_nonneg 1) hC hb hr
  exact fun _ ht => stable_laplace_inverse_tail P hX hpos hl ht

lemma negExp_eq_exp_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : negExp x = Real.exp (-x.toReal) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hx, negExp_ofReal ENNReal.toReal_nonneg]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_LintegralGammaKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lintegral Gamma Kernel. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron.Marked

variable {E : Type} [MeasurableSpace E] [Nonempty E]

lemma poissonGood_ae (μ : Measure E) [SigmaFinite μ] :
    ∀ᵐ ν ∂poissonLaw μ, PoissonGood μ ν := by
  rw [show (fun ν => PoissonGood μ ν) =
    (fun ν => ∀ n, ν (disjointed (spanningSets μ) n) < ∞) from rfl, ae_all_iff]
  intro n
  have hm := MeasurableSet.disjointed (measurableSet_spanningSets μ) n
  apply ae_lt_top (Measure.measurable_coe hm)
  rw [poissonLaw_mean_count μ hm]
  exact ((measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top μ n)).ne

omit [Nonempty E] in
lemma sigmaPart_eq_of_good (μ : Measure E) [SigmaFinite μ] {ν : Measure E}
    (hν : PoissonGood μ ν) : sigmaPart μ ν = ν := by
  unfold sigmaPart
  calc
    _ = Measure.sum (fun n => ν.restrict (disjointed (spanningSets μ) n)) := by
      congr 1
      funext n
      apply ite_eq_left
      simpa only [Measure.restrict_apply_univ] using hν n
    _ = ν := sum_restrict_disjointed_spanningSets ν μ

end IsingPerceptron.Marked

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_MarkedPartitionNumerator
attribute [-instance] _root_.OAI.IsingPerceptron.noiseChildKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Marked Partition Numerator. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable {E : Type*} [MeasurableSpace E] [Nonempty E]

lemma poissonLaw_ae_intensity (μ : Measure E) [SFinite μ] {p : E → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ ν ∂poissonLaw μ, ∀ᵐ x ∂ν, p x := by
  have he : (∫⁻ ν, ν {x | ¬ p x} ∂poissonLaw μ) = 0 := by
    exact (poissonLaw_mean_count μ (show MeasurableSet {x | ¬p x} from hp.compl)).trans (ae_iff.mp h)
  have hz := (lintegral_eq_zero_iff (Measure.measurable_coe hp.compl)).mp he
  filter_upwards [hz] with ν hν
  exact ae_iff.mpr hν

lemma weightedPoissonTotal_real_eq_ae (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞) {t : ℝ} (ht : 0 ≤ t) :
    (fun ν => ∫⁻ p : ℝ × E, ENNReal.ofReal (t * max p.1 0 * (a p.2).toReal) ∂ν) =ᵐ[
      poissonLaw ((powerIntensity b).prod μ)]
      (fun ν => ENNReal.ofReal t * weightedPoissonTotal a ν) := by
  have hprod : ∀ᵐ p : ℝ × E ∂(powerIntensity b).prod μ, a p.2 < ∞ :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_lt (ha.comp measurable_snd) measurable_const)).mpr
      (ae_of_all _ fun _ => hfin)
  filter_upwards [poissonLaw_ae_intensity ((powerIntensity b).prod μ)
    (measurableSet_lt (ha.comp measurable_snd) measurable_const) hprod] with ν hν
  rw [weightedPoissonTotal, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [hν] with p hp
  change a p.2 < ∞ at hp
  rw [ENNReal.ofReal_mul (mul_nonneg ht (le_max_right _ _)), ENNReal.ofReal_mul ht,
    ENNReal.ofReal_toReal hp.ne, mul_assoc]

omit [Nonempty E] in
lemma weightedPower_laplace_cost (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    {t : ℝ} (ht : 0 < t) :
    (∫⁻ p : ℝ × E, ENNReal.ofReal (1-Real.exp (-(t * max p.1 0 * (a p.2).toReal)))
      ∂(powerIntensity b).prod μ) =
      ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b := by
  rw [lintegral_prod_symm _ (by fun_prop)]
  have he : (fun y => ∫⁻ x, ENNReal.ofReal
      (1-Real.exp (-(t * max x 0 * (a y).toReal))) ∂powerIntensity b) =ᵐ[μ]
      (fun y => ENNReal.ofReal (t^b) * ENNReal.ofReal ((a y).toReal^b) * stableLaplaceConstant b) := by
    filter_upwards [hpos] with y hy
    have hmul (x : ℝ) : t * max x 0 * (a y).toReal = (t*(a y).toReal)*max x 0 := by ring
    simp_rw [hmul]
    have hs := powerIntensity_laplace_scale (b := b) (mul_pos ht hy)
    simp only [neg_mul] at hs ⊢
    rw [hs, Real.mul_rpow ht.le hy.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  rw [lintegral_congr_ae he, lintegral_mul_const _ (by fun_prop),
    lintegral_const_mul _ (by fun_prop)]

lemma weightedPoissonTotal_laplace (b : ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal) {t : ℝ} (ht : 0 < t) :
    (∫ ν, negExp (ENNReal.ofReal t * weightedPoissonTotal a ν)
      ∂poissonLaw ((powerIntensity b).prod μ)) =
      negExp (ENNReal.ofReal (t^b) * (∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ) *
        stableLaplaceConstant b) := by
  have h := poissonLaw_laplace ((powerIntensity b).prod μ)
    (ψ := fun p => t * max p.1 0 * (a p.2).toReal) (by fun_prop)
    (fun p => mul_nonneg (mul_nonneg ht.le (le_max_right _ _)) ENNReal.toReal_nonneg)
  rw [weightedPower_laplace_cost b μ ha hpos ht] at h
  rw [← h]
  apply integral_congr_ae
  exact ((weightedPoissonTotal_real_eq_ae b μ ha hfin ht.le).fun_comp negExp).symm

end IsingPerceptron

namespace IsingPerceptron

attribute [instance] RawTreeSpace.space

end IsingPerceptron

namespace IsingPerceptron

lemma rawCascadeLaw_succ (n : ℕ) (b : ℕ → ℝ) :
    (rawCascadeLaw (n+1) b : Measure (RawTree (n+1))) =
      poissonLaw ((powerIntensity (b 0)).prod
        (rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n))) := rfl

lemma HasStableTotal.finite_positive {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b) :
    ∀ᵐ ω ∂P, 0 < X ω ∧ X ω < ∞ := by
  obtain ⟨C, hC, hl⟩ := h
  exact stable_laplace_finite_positive P hX hC hb hl

lemma HasStableTotal.real_laplace {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      (∫ ω, Real.exp (-t * (X ω).toReal) ∂P) = Real.exp (-C*t^b) := by
  have hf := h.finite_positive hX hb
  obtain ⟨C, hC, hl⟩ := h
  refine ⟨C, hC, fun t ht => ?_⟩
  rw [← hl t ht]
  apply integral_congr_ae
  filter_upwards [hf] with ω hω
  rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.2.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le, neg_mul]

lemma HasStableTotal.positive_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b r : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b)
    (hr : 0 < r) (hrb : r < b) : Integrable (fun ω => (X ω).toReal^r) P := by
  obtain ⟨C, hC, hl⟩ := h.real_laplace hX hb
  exact stable_positive_moment P hX.ennreal_toReal
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) hC hr hrb hl

lemma HasStableTotal.negative_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} {b r : ℝ}
    (h : HasStableTotal P X b) (hX : Measurable X) (hb : 0 < b)
    (hr : 0 < r) : Integrable (fun ω => ((X ω).toReal)⁻¹^r) P := by
  obtain ⟨C, hC, hl⟩ := h.real_laplace hX hb
  apply stable_negative_moment P hX.ennreal_toReal _ hC hb hr hl
  filter_upwards [h.finite_positive hX hb] with ω hω
  exact ENNReal.toReal_pos hω.1.ne' hω.2.ne

lemma weightedPoissonTotal_stable {E : Type*} [MeasurableSpace E] [Nonempty E]
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (μ : Measure E) [IsProbabilityMeasure μ]
    {a : E → ℝ≥0∞} (ha : Measurable a) (hfin : ∀ᵐ y ∂μ, a y < ∞)
    (hpos : ∀ᵐ y ∂μ, 0 < (a y).toReal)
    (hpay : Integrable (fun y => (a y).toReal^b) μ) :
    HasStableTotal (poissonLaw ((powerIntensity b).prod μ)) (weightedPoissonTotal a) b := by
  let A := ∫⁻ y, ENNReal.ofReal ((a y).toReal^b) ∂μ
  have hA : A < ∞ := by
    exact hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
      |>.mp hpay.hasFiniteIntegral
  have hApos : 0 < A := by
    apply (lintegral_pos_iff_support (ha.ennreal_toReal.pow_const b |>.ennreal_ofReal)).mpr
    have he : (Function.support (fun y => ENNReal.ofReal ((a y).toReal^b))) =ᵐ[μ] Set.univ := by
      filter_upwards [hpos] with y hy
      apply propext
      change (ENNReal.ofReal ((a y).toReal^b) ≠ 0) ↔ True
      exact iff_true_intro (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hy _)))
    rw [measure_congr he, measure_univ]
    exact zero_lt_one
  let C := A * stableLaplaceConstant b
  have hC : C < ∞ := ENNReal.mul_lt_top hA (stableLaplaceConstant_lt_top hb hb1)
  have hCp : 0 < C := ENNReal.mul_pos hApos.ne' (stableLaplaceConstant_pos hb).ne'
  refine ⟨C.toReal, ENNReal.toReal_pos hCp.ne' hC.ne, fun t ht => ?_⟩
  rw [weightedPoissonTotal_laplace b μ ha hfin hpos ht, mul_assoc]
  change negExp (ENNReal.ofReal (t^b) * C) = _
  rw [negExp_eq_exp_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _)]
  congr 1
  ring

lemma CascadeExponents.tail {n : ℕ} {b : ℕ → ℝ} (h : CascadeExponents (n+1) b) :
    CascadeExponents n (fun i => b (i+1)) := by
  exact ⟨fun i hi => h.1 (i+1) (by omega), fun i j hij hj => h.2 (i+1) (j+1) (by omega) (by omega)⟩

theorem rawCascade_total_moments (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    (∀ᵐ T ∂(rawCascadeLaw n b : Measure (RawTree n)),
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) ∧
    (∀ r : ℝ, 0 < r → (∀ i < n, r < b i) →
      Integrable (fun T => (rawTreeTotal n T).toReal^r) (rawCascadeLaw n b : Measure (RawTree n))) ∧
    (∀ r : ℝ, 0 < r → Integrable (fun T => ((rawTreeTotal n T).toReal)⁻¹^r)
      (rawCascadeLaw n b : Measure (RawTree n))) := by
  induction n generalizing b with
  | zero =>
    refine ⟨ae_of_all _ (fun _ => by simp [rawTreeTotal]), ?_, ?_⟩
    · intro r _ _
      simp [rawTreeTotal]
    · intro r _
      simp [rawTreeTotal]
  | succ n ih =>
    have hi := ih (fun i => b (i+1)) hb.tail
    have hb0 := hb.1 0 (by omega)
    have hpos : ∀ᵐ T ∂(rawCascadeLaw n (fun i => b (i+1)) : Measure (RawTree n)),
        0 < (rawTreeTotal n T).toReal := by
      filter_upwards [hi.1] with T hT
      exact ENNReal.toReal_pos hT.1.ne' hT.2.ne
    have hm := hi.2.1 (b 0) hb0.1 (fun i hi => hb.2 0 (i+1) (by omega) (by omega))
    have hs : HasStableTotal (rawCascadeLaw (n+1) b : Measure (RawTree (n+1)))
        (rawTreeTotal (n+1)) (b 0) :=
      weightedPoissonTotal_stable hb0.1 hb0.2 _ (measurable_rawTreeTotal n)
        (hi.1.mono fun _ h => h.2) hpos hm
    exact ⟨hs.finite_positive (measurable_rawTreeTotal _) hb0.1,
      fun r hr hrb => hs.positive_moment (measurable_rawTreeTotal _) hb0.1 hr (hrb 0 (by omega)),
      fun r hr => hs.negative_moment (measurable_rawTreeTotal _) hb0.1 hr⟩

theorem rawCascade_total_log_square (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) :
    Integrable (fun T => (Real.log (rawTreeTotal n T).toReal)^2)
      (rawCascadeLaw n b : Measure (RawTree n)) := by
  cases n with
  | zero => simp [rawTreeTotal]
  | succ n =>
    have h := rawCascade_total_moments (n+1) b hb
    have hb0 := hb.1 0 (by omega)
    apply integrable_log_sq_of_moments _ (measurable_rawTreeTotal _).ennreal_toReal _
      (show 0 < b 0/2 by linarith) (h.2.1 _ (by linarith) _) (h.2.2 _ (by linarith))
    · filter_upwards [h.1] with T hT
      exact ENNReal.toReal_pos hT.1.ne' hT.2.ne
    · intro i hi
      by_cases h0 : i = 0
      · subst i; linarith
      · have := hb.2 0 i (by omega) hi; linarith

open scoped ProbabilityTheory

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_WeightedPartitionNumeratorIncrement
attribute [-instance] _root_.OAI.IsingPerceptron.noiseChildKernel_markov _root_.OAI.IsingPerceptron.noiseLeafKernel_markov _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Partition Numerator Increment. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron
variable (A : Type) [MeasurableSpace A]

variable [Nonempty A]

lemma noiseCascadeLaw_succ (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))) =
      poissonLaw ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))) := rfl

lemma noiseCascadeLaw_forget (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map (noiseTreeForget A n) = rawCascadeLaw n b := by
  induction n generalizing b μ with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_dirac' measurable_const]
  | succ n ih =>
    rw [noiseCascadeLaw_succ, rawCascadeLaw_succ]
    change (poissonLaw _).map (fun ν => ν.map (fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2))) = _
    rw [poissonLaw_map _ (T := fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2))
      (measurable_fst.prodMk
      ((measurable_noiseTreeForget A n).comp (measurable_snd.comp measurable_snd)))]
    apply poissonLaw_congr
    have he : (fun p : ℝ × (A × NoiseTree A n) => (p.1, noiseTreeForget A n p.2.2)) =
        Prod.map id (fun q : A × NoiseTree A n => noiseTreeForget A n q.2) := rfl
    rw [he, ← Measure.map_prod_map _ _ (f := id)
      (g := fun q : A × NoiseTree A n => noiseTreeForget A n q.2) measurable_id
      ((measurable_noiseTreeForget A n).comp measurable_snd), Measure.map_id]
    congr 1
    change (((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))))).map
        (noiseTreeForget A n ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_noiseTreeForget A n) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, ih]

omit [Nonempty A] in
lemma noiseTreeTotal_succ (n : ℕ) (ν : NoiseTree A (n+1)) :
    noiseTreeTotal A (n+1) ν = ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 ∂ν := by
  change (∫⁻ p, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2
    ∂ν.map (fun p => (p.1,noiseTreeForget A n p.2.2))) = _
  rw [lintegral_map]
  · rfl
  · exact (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
      ((measurable_rawTreeTotal n).comp measurable_snd)
  · exact measurable_fst.prodMk ((measurable_noiseTreeForget A n).comp (measurable_snd.comp measurable_snd))

end IsingPerceptron

namespace IsingPerceptron

lemma measurable_map_sigmaPart_param {E F P : Type*} [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace P] (μ : Measure E) [SigmaFinite μ]
    {N : P → Measure E} (hN : Measurable N) {G : P × E → F} (hG : Measurable G) :
    Measurable (fun p => (sigmaPart μ (N p)).map (fun x => G (p,x))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hf : Measurable (fun p : P × E => s.indicator (1 : F → ℝ≥0∞) (G p)) :=
    (measurable_const.indicator hs).comp hG
  convert measurable_sigmaPart_param μ hN hf using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rw [Measure.map_apply (f := fun x => G (p,x))
    (hG.comp (measurable_const.prodMk measurable_id)) hs]
  exact (lintegral_indicator_one (hs.preimage
    (hG.comp (measurable_const.prodMk measurable_id)))).symm

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma measurable_noiseTreeDisplace (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeDisplace n b μ c u p.1 p.2) := by
  induction n generalizing b μ c u with
  | zero => exact measurable_const
  | succ n ih =>
    unfold noiseTreeDisplace
    apply measurable_map_sigmaPart_param _ measurable_snd
      (G := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        (c 0 (p.1.1,p.2.2.1) * p.2.1,
          noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2))
    have hs : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.1.1) := by fun_prop
    have ha : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.2.1) := by fun_prop
    have hx : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.1) := by fun_prop
    have hv : Measurable (fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) => p.2.2.2) := by fun_prop
    exact (((hc 0).comp (hs.prodMk ha)).mul hx).prodMk
      ((ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
        (((hu 0).comp (hs.prodMk ha)).prodMk hv))

end IsingPerceptron

namespace IsingPerceptron

lemma map_powerIntensity_subtree {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (b : ℝ)
    (μ : Measure A) (P : Measure B) (Q : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {c : A → ℝ} (hc : Measurable c) (hcpos : ∀ a, 0 < c a)
    (hm : (∫⁻ a, ENNReal.ofReal (c a ^ b) ∂μ) = 1)
    {T : A × B → C} (hT : Measurable T)
    (hLaw : ∀ a, P.map (fun v => T (a,v)) = Q) :
    ((powerIntensity b).prod (μ.prod P)).map
      (fun p : ℝ × (A × B) => (c p.2.1 * p.1,T p.2)) = (powerIntensity b).prod Q := by
  have hF : Measurable (fun p : ℝ × (A × B) => (c p.2.1 * p.1,T p.2)) :=
    ((hc.comp (measurable_fst.comp measurable_snd)).mul measurable_fst).prodMk
      (hT.comp measurable_snd)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hF, lintegral_prod
    (fun p : ℝ × (A × B) => f (c p.2.1*p.1,T p.2)) (hf.comp hF).aemeasurable]
  have hv (x : ℝ) (a : A) :
      (∫⁻ v, f (c a*x,T (a,v)) ∂P) = ∫⁻ w, f (c a*x,w) ∂Q := by
    rw [← hLaw a, lintegral_map]
    · exact hf.comp (measurable_const.prodMk measurable_id)
    · exact hT.comp (measurable_const.prodMk measurable_id)
  have hp (x : ℝ) : (∫⁻ v : A × B, f (c v.1*x,T v) ∂μ.prod P) =
      ∫⁻ a, ∫⁻ w, f (c a*x,w) ∂Q ∂μ := by
    rw [lintegral_prod (fun v : A × B => f (c v.1*x,T v))
      ((hf.comp hF).comp (measurable_const.prodMk measurable_id)).aemeasurable]
    simp_rw [hv]
  simp_rw [hp]
  have hG : Measurable (fun p : ℝ × A => ∫⁻ w, f (c p.2*p.1,w) ∂Q) :=
    (hf.comp ((((hc.comp (measurable_snd.comp measurable_fst)).mul
      (measurable_fst.comp measurable_fst))).prodMk measurable_snd)).lintegral_prod_right'
  rw [lintegral_lintegral_swap hG.aemeasurable]
  have hx (a : A) : (∫⁻ x, ∫⁻ w, f (c a*x,w) ∂Q ∂powerIntensity b) =
      ENNReal.ofReal (c a ^ b) * (∫⁻ x, ∫⁻ w, f (x,w) ∂Q ∂powerIntensity b) := by
    rw [← lintegral_map hf.lintegral_prod_right' (measurable_const_mul (c a)),
      map_powerIntensity_mul (hcpos a), lintegral_smul_measure]
    rfl
  simp_rw [hx]
  rw [lintegral_mul_const _ (by fun_prop), hm, one_mul,
    ← lintegral_prod _ hf.aemeasurable]

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

theorem noiseTreeDisplace_law (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map (noiseTreeDisplace n b μ c u s) =
      rawCascadeLaw n b := by
  induction n generalizing b μ c u s with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    exact Measure.map_dirac' measurable_const _
  | succ n ih =>
    let P : Measure (NoiseTree A n) := noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1))
    let Q : Measure (RawTree n) := rawCascadeLaw n (fun j => b (j+1))
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
    let G : A × NoiseTree A n → RawTree n := fun p =>
      noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.1)) p.2
    have hG : Measurable G :=
      (measurable_noiseTreeDisplace n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
        (((hu 0).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have hGLaw (a : A) : P.map (fun v => G (a,v)) = Q :=
      ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))
        (fun i => hcpos (i+1)) (fun i => hm (i+1)) (u 0 (s,a))
    let T : ℝ × (A × NoiseTree A n) → ℝ × RawTree n :=
      fun p => (c 0 (s,p.2.1) * p.1,G p.2)
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (measurable_fst.comp measurable_snd))).mul
        measurable_fst).prodMk (hG.comp measurable_snd)
    have hI : I.map T = (powerIntensity (b 0)).prod Q :=
      map_powerIntensity_subtree (b 0) (μ 0 : Measure A) P Q (c := fun a => c 0 (s,a))
        ((hc 0).comp (measurable_const.prodMk measurable_id)) (hcpos 0 s) (hm 0 s) hG hGLaw
    rw [noiseCascadeLaw_succ, rawCascadeLaw_succ]
    change (poissonLaw I).map _ = poissonLaw ((powerIntensity (b 0)).prod Q)
    calc
      _ = (poissonLaw I).map (fun ν => ν.map T) := by
        apply Measure.map_congr
        filter_upwards [sigmaPart_eq_ae I] with ν hν
        change (sigmaPart I ν).map T = ν.map T
        rw [hν]
      _ = poissonLaw (I.map T) := poissonLaw_map I hT
      _ = _ := poissonLaw_congr hI

end IsingPerceptron

namespace IsingPerceptron

lemma integrable_of_square {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f)
    (hi : Integrable (fun x => (f x)^2) P) : Integrable f P := by
  apply ((integrable_const (1 : ℝ)).add hi).mono' hf.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs]
  change |f x| ≤ 1+(f x)^2
  have h := sq_nonneg (|f x|-1)
  nlinarith [sq_abs (f x)]

lemma integral_difference_same_law {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure E) [IsProbabilityMeasure Q]
    {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    (hXL : P.map X = Q) (hYL : P.map Y = Q)
    {g : E → ℝ} (hg : Measurable g) (hg2 : Integrable (fun v => (g v)^2) Q) :
    Integrable (fun ω => g (X ω)-g (Y ω)) P ∧
    (∫ ω, g (X ω)-g (Y ω) ∂P) = 0 ∧
    Integrable (fun ω => (g (X ω)-g (Y ω))^2) P ∧
    (∫ ω, (g (X ω)-g (Y ω))^2 ∂P) ≤ 4 * ∫ v, (g v)^2 ∂Q := by
  have hX2 : Integrable (fun ω => (g (X ω))^2) P := by
    apply (integrable_map_measure (hg.pow_const 2).aestronglyMeasurable hX.aemeasurable).mp
    rw [hXL]
    exact hg2
  have hY2 : Integrable (fun ω => (g (Y ω))^2) P := by
    apply (integrable_map_measure (hg.pow_const 2).aestronglyMeasurable hY.aemeasurable).mp
    rw [hYL]
    exact hg2
  have hXi : Integrable (fun ω => g (X ω)) P := integrable_of_square P (hg.comp hX) hX2
  have hYi : Integrable (fun ω => g (Y ω)) P := integrable_of_square P (hg.comp hY) hY2
  have hdiff : Integrable (fun ω => (g (X ω)-g (Y ω))^2) P := by
    apply ((hX2.add hY2).const_mul 2).mono'
      (((hg.comp hX).sub (hg.comp hY)).pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (g (X ω)-g (Y ω))^2 ≤ 2*((g (X ω))^2+(g (Y ω))^2)
    nlinarith [sq_nonneg (g (X ω)+g (Y ω))]
  refine ⟨hXi.sub hYi, ?_, hdiff, ?_⟩
  · rw [integral_sub hXi hYi, ← integral_map hX.aemeasurable hg.aestronglyMeasurable,
      ← integral_map hY.aemeasurable hg.aestronglyMeasurable, hXL, hYL, sub_self]
  · calc
      _ ≤ ∫ ω, 2*((g (X ω))^2+(g (Y ω))^2) ∂P :=
        integral_mono hdiff ((hX2.add hY2).const_mul 2) (fun ω => by
          nlinarith [sq_nonneg (g (X ω)+g (Y ω))])
      _ = 4 * ∫ v, (g v)^2 ∂Q := by
        rw [integral_const_mul, integral_add hX2 hY2,
          ← integral_map hX.aemeasurable (hg.pow_const 2).aestronglyMeasurable,
          ← integral_map hY.aemeasurable (hg.pow_const 2).aestronglyMeasurable, hXL, hYL]
        ring

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

theorem noiseTreeDisplace_log_ratio (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    let L := fun ν : NoiseTree A n =>
      Real.log (rawTreeTotal n (noiseTreeDisplace n b μ c u s ν)).toReal -
        Real.log (noiseTreeTotal A n ν).toReal
    Integrable L (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) ∧
    (∫ ν, L ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n))) = 0 ∧
    Integrable (fun ν => (L ν)^2) (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) ∧
    (∫ ν, (L ν)^2 ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n))) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact integral_difference_same_law (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    (rawCascadeLaw n b : Measure (RawTree n))
    (X := noiseTreeDisplace n b μ c u s) (Y := noiseTreeForget A n)
    ((measurable_noiseTreeDisplace n b μ hc hu).comp (measurable_const.prodMk measurable_id))
    (measurable_noiseTreeForget A n) (noiseTreeDisplace_law n b μ hc hu hcpos hm s)
    (noiseCascadeLaw_forget A n b μ)
    (Real.measurable_log.comp (measurable_rawTreeTotal n).ennreal_toReal)
    (rawCascade_total_log_square n b hb)

lemma measurable_noiseTreeFactor (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeFactor n b μ X u p.1 p.2) := by
  induction n generalizing b μ X u with
  | zero => exact (((hX 0).comp measurable_fst).exp).ennreal_ofReal
  | succ n ih =>
    unfold noiseTreeFactor
    apply measurable_sigmaPart_param _ measurable_snd
      (F := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        ENNReal.ofReal (max p.2.1 0) *
          noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2)
    exact (by fun_prop : Measurable (fun p : (S × NoiseTree A (n+1)) ×
      (ℝ × (A × NoiseTree A n)) => ENNReal.ofReal (max p.2.1 0))).mul
        ((ih _ _ (fun i => hX (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop)))

theorem noiseTreeDisplace_total (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (s : S) (ν : NoiseTree A n) :
    rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) =
      ENNReal.ofReal (Real.exp (-X 0 s)) * noiseTreeFactor n b μ X u s ν := by
  induction n generalizing b μ X u c s with
  | zero =>
    simp only [rawTreeTotal, noiseTreeFactor]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    let T : ℝ × (A × NoiseTree A n) → ℝ × RawTree n := fun p =>
      (c 0 (s,p.2.1)*p.1,
        noiseTreeDisplace n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2)
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (by fun_prop))).mul measurable_fst).prodMk
        ((measurable_noiseTreeDisplace n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop)))
    change (∫⁻ p, ENNReal.ofReal (max p.1 0)*rawTreeTotal n p.2 ∂(sigmaPart I ν).map T) = _
    rw [lintegral_map]
    · change (∫⁻ p, ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) *
          rawTreeTotal n (T p).2 ∂sigmaPart I ν) = _
      have he (p : ℝ × (A × NoiseTree A n)) :
          ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) * rawTreeTotal n (T p).2 =
          ENNReal.ofReal (Real.exp (-X 0 s)) * (ENNReal.ofReal (max p.1 0) *
            noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
              (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2) := by
        dsimp only [T]
        rw [ih _ _ (X := fun j => X (j+1)) (fun i => hc (i+1)) (fun i => hu (i+1)) (fun i => htel (i+1)),
          htel 0 s p.2.1]
        have hh (y x : ℝ) : max (Real.exp y*x) 0 = Real.exp y * max x 0 := by
          rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le, mul_zero]
        rw [hh, ENNReal.ofReal_mul (Real.exp_pos _).le]
        have hex (y z : ℝ) : ENNReal.ofReal (Real.exp (y-z)) * ENNReal.ofReal (Real.exp (-y)) =
            ENNReal.ofReal (Real.exp (-z)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2
          ring
        calc
          _ = (ENNReal.ofReal (Real.exp (X 1 (u 0 (s,p.2.1))-X 0 s)) *
              ENNReal.ofReal (Real.exp (-X 1 (u 0 (s,p.2.1))))) *
              (ENNReal.ofReal (max p.1 0) *
                noiseTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
                  (fun j => X (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2) := by ring
          _ = _ := by rw [hex]
      simp_rw [he]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    · exact (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_rawTreeTotal n).comp measurable_snd)
    · exact hT

lemma noiseTreeFactor_total_identity (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ X u s ν = ENNReal.ofReal (Real.exp (X 0 s)) *
      rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) := by
  rw [noiseTreeDisplace_total n b μ hc hu htel s ν, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

theorem noiseCascade_log_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S} {c : ℕ → S × A → ℝ}
    (hc : ∀ i, Measurable (c i))
    (hu : ∀ i, Measurable (u i))
    (htel : ∀ i s a, c i (s,a) = Real.exp (X (i+1) (u i (s,a))-X i s))
    (hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a) ^ b i) ∂(μ i : Measure A)) = 1)
    (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun ν : NoiseTree A n => Real.log
      ((noiseTreeFactor n b μ X u s ν).toReal / (noiseTreeTotal A n ν).toReal)
    (∀ᵐ ν ∂P, 0 < noiseTreeFactor n b μ X u s ν ∧ noiseTreeFactor n b μ X u s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = X 0 s ∧
    Integrable (fun ν => (L ν-X 0 s)^2) P ∧
    (∫ ν, (L ν-X 0 s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  dsimp only
  let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
  let L := fun ν : NoiseTree A n => Real.log
      ((noiseTreeFactor n b μ X u s ν).toReal / (noiseTreeTotal A n ν).toReal)
  let D := fun ν : NoiseTree A n => Real.log
      (rawTreeTotal n (noiseTreeDisplace n b μ c u s ν)).toReal -
        Real.log (noiseTreeTotal A n ν).toReal
  have hcpos : ∀ i s a, 0 < c i (s,a) := by intro i s a; rw [htel]; exact Real.exp_pos _
  have hT : Measurable (noiseTreeDisplace n b μ c u s) :=
    (measurable_noiseTreeDisplace n b μ hc hu).comp (measurable_const.prodMk measurable_id)
  have hgood : ∀ᵐ ν ∂P, 0 < rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) ∧
      rawTreeTotal n (noiseTreeDisplace n b μ c u s ν) < ∞ := by
    apply ae_of_ae_map (μ := P) (p := fun T : RawTree n =>
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) hT.aemeasurable
    rw [show P.map (noiseTreeDisplace n b μ c u s) = (rawCascadeLaw n b : Measure (RawTree n)) from
      noiseTreeDisplace_law n b μ hc hu hcpos hm s]
    exact (rawCascade_total_moments n b hb).1
  have hden : ∀ᵐ ν ∂P, 0 < noiseTreeTotal A n ν ∧ noiseTreeTotal A n ν < ∞ := by
    apply ae_of_ae_map (μ := P) (p := fun T : RawTree n =>
      0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞) (measurable_noiseTreeForget A n).aemeasurable
    rw [show P.map (noiseTreeForget A n) = (rawCascadeLaw n b : Measure (RawTree n)) from
      noiseCascadeLaw_forget A n b μ]
    exact (rawCascade_total_moments n b hb).1
  have he : L =ᵐ[P] fun ν => X 0 s + D ν := by
    filter_upwards [hgood, hden] with ν hν hνd
    have htpos := ENNReal.toReal_pos hν.1.ne' hν.2.ne
    have hdpos := ENNReal.toReal_pos hνd.1.ne' hνd.2.ne
    dsimp only [L, D]
    rw [noiseTreeFactor_total_identity n b μ hc hu htel s ν, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,
      Real.log_div (mul_pos (Real.exp_pos _) htpos).ne' hdpos.ne',
      Real.log_mul (Real.exp_ne_zero _) htpos.ne', Real.log_exp]
    ring
  have h := noiseTreeDisplace_log_ratio n b hb μ hc hu hcpos hm s
  change Integrable D P ∧ (∫ ν, D ν ∂P) = 0 ∧ Integrable (fun ν => (D ν)^2) P ∧ _ at h
  have hi : Integrable L P := ((integrable_const (X 0 s)).add h.1).congr he.symm
  have hec : (fun ν => L ν-X 0 s) =ᵐ[P] D := by
    filter_upwards [he] with ν hν
    rw [hν]
    ring
  have he2 : (fun ν => (L ν-X 0 s)^2) =ᵐ[P] fun ν => (D ν)^2 :=
    hec.fun_comp (fun x : ℝ => x^2)
  refine ⟨?_, hi, ?_, h.2.2.1.congr he2.symm, ?_⟩
  · filter_upwards [hgood] with ν hν
    rw [noiseTreeFactor_total_identity n b μ hc hu htel s ν]
    exact ⟨ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hν.1.ne',
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.2⟩
  · rw [integral_congr_ae he, integral_add (integrable_const _) h.1, integral_const, h.2.1]
    simp [P]
  · rw [integral_congr_ae he2]
    exact h.2.2.2

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_NoiseTreeKeep
attribute [-instance] _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.noiseTiltedLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Tree Keep. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma measurable_noiseTreeKeep (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => noiseTreeKeep n b μ c u p.1 p.2) := by
  induction n generalizing b μ c u with
  | zero => exact measurable_const
  | succ n ih =>
    unfold noiseTreeKeep
    apply measurable_map_sigmaPart_param _ measurable_snd
      (G := fun p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) =>
        (c 0 (p.1.1,p.2.2.1) * p.2.1, (p.2.2.1,
          noiseTreeKeep n (fun j => b (j+1)) (fun j => μ (j+1))
            (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2)))
    exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
      ((by fun_prop : Measurable (fun p : (S × NoiseTree A (n+1)) ×
          (ℝ × (A × NoiseTree A n)) => p.2.2.1)).prodMk
        ((ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))))

lemma noiseTreeKeep_forget (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (s : S) (ν : NoiseTree A n) :
    noiseTreeForget A n (noiseTreeKeep n b μ c u s ν) = noiseTreeDisplace n b μ c u s ν := by
  induction n generalizing b μ c u s with
  | zero => rfl
  | succ n ih =>
    unfold noiseTreeKeep noiseTreeForget noiseTreeDisplace
    rw [Measure.map_map]
    · congr 1
      funext p
      dsimp only [Function.comp_apply]
      rw [ih _ _ (fun i => hc (i+1)) (fun i => hu (i+1))]
    · exact measurable_fst.prodMk ((measurable_noiseTreeForget A n).comp (by fun_prop))
    · exact (((hc 0).comp (measurable_const.prodMk (by fun_prop))).mul
          measurable_fst).prodMk
        ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => p.2.1)).prodMk
          ((measurable_noiseTreeKeep n _ _ (fun i => hc (i+1)) (fun i => hu (i+1))).comp
            (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))))

end IsingPerceptron

namespace IsingPerceptron

lemma measurable_measure_ae {E : Type*} [MeasurableSpace E] {p : E → Prop}
    (hp : MeasurableSet {x | p x}) : MeasurableSet {ν : Measure E | ∀ᵐ x ∂ν, p x} := by
  simp only [ae_iff]
  exact measurableSet_eq_fun (Measure.measurable_coe hp.compl) measurable_const

lemma normalizeMass_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (ν : Measure E) {f : E → F} (hf : Measurable f)
    (hν : 0 < ν univ ∧ ν univ < ∞) :
    (normalizeMass ν).map f = normalizeMass (ν.map f) := by
  have ht : ν.map f univ = ν univ := by rw [Measure.map_apply hf MeasurableSet.univ]; rfl
  rw [normalizeMass, ite_eq_left hν, normalizeMass, ht, ite_eq_left hν,
    Measure.map_smul]

lemma withDensity_map_pullback {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ν : Measure E) {f : E → F} (hf : Measurable f) {w : F → ℝ≥0∞} (hw : Measurable w) :
    (ν.withDensity (fun x => w (f x))).map f = (ν.map f).withDensity w := by
  apply Measure.ext_of_lintegral
  intro g hg
  calc
    _ = ∫⁻ x, g (f x) ∂ν.withDensity (fun x => w (f x)) :=
      lintegral_map' hg.aemeasurable hf.aemeasurable
    _ = ∫⁻ x, w (f x) * g (f x) ∂ν :=
      lintegral_withDensity_eq_lintegral_mul _ (hw.comp hf) (hg.comp hf)
    _ = ∫⁻ x, w x * g x ∂ν.map f :=
      (lintegral_map' (hw.mul hg).aemeasurable hf.aemeasurable).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _ hw hg).symm

variable (A : Type) [MeasurableSpace A] [Nonempty A]

omit [Nonempty A] in
lemma measurableSet_GoodNoiseTree (n : ℕ) : MeasurableSet {ν | GoodNoiseTree A n ν} := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    exact ((measurableSet_lt measurable_const (measurable_noiseTreeTotal A (n+1))).inter
      (measurableSet_lt (measurable_noiseTreeTotal A (n+1)) measurable_const)).inter
        (measurable_measure_ae (ih.preimage (measurable_snd.comp measurable_snd)))

lemma noiseCascade_good (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)), GoodNoiseTree A n ν := by
  induction n generalizing b μ with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ n ih =>
    have htot : ∀ᵐ ν ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))),
        0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞ := by
      apply ae_of_ae_map (μ := (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))))
        (p := fun T : RawTree (n+1) => 0 < rawTreeTotal (n+1) T ∧ rawTreeTotal (n+1) T < ∞)
        (measurable_noiseTreeForget A (n+1)).aemeasurable
      rw [noiseCascadeLaw_forget]
      exact (rawCascade_total_moments (n+1) b hb).1
    have hm : MeasurableSet {p : ℝ × (A × NoiseTree A n) | GoodNoiseTree A n p.2.2} :=
      (measurableSet_GoodNoiseTree A n).preimage (by fun_prop)
    have hdesc : ∀ᵐ p ∂(powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
        (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)))), GoodNoiseTree A n p.2.2 := by
      apply (Measure.ae_prod_iff_ae_ae hm).mpr
      apply ae_of_all
      intro _
      apply (Measure.ae_prod_iff_ae_ae ((measurableSet_GoodNoiseTree A n).preimage measurable_snd)).mpr
      exact ae_of_all _ (fun _ => ih (fun j => b (j+1)) hb.tail (fun j => μ (j+1)))
    have hc := poissonLaw_ae_intensity _ hm hdesc
    filter_upwards [htot, hc] with ν ht hd
    exact ⟨ht, hd⟩

omit [Nonempty A] in
lemma noiseChildMass_univ (n : ℕ) (ν : NoiseTree A (n+1)) :
    noiseChildMass A n ν univ = noiseTreeTotal A (n+1) ν := by
  rw [noiseTreeTotal_succ]
  simp [noiseChildMass, withDensity_apply]

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable (A : Type) [MeasurableSpace A] [Nonempty A]

lemma noiseLeafKernel_succ (n : ℕ) : noiseLeafKernel A (n+1) =
    ((Kernel.id : Kernel ℝ ℝ) ∥ₖ ((Kernel.id : Kernel A A) ∥ₖ noiseLeafKernel A n)) ∘ₖ
      noiseChildKernel A n := rfl

lemma noiseLeafKernel_step (n : ℕ) (ν : NoiseTree A (n+1))
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2 ∂noiseChildKernel A n ν := by
  rw [noiseLeafKernel_succ, Kernel.lintegral_comp _ _ _ hF]
  apply lintegral_congr
  intro p
  rw [Kernel.parallelComp_apply, Kernel.id_apply, lintegral_prod _ hF.aemeasurable,
    lintegral_dirac']
  swap
  · exact hF.lintegral_prod_right'
  rw [Kernel.parallelComp_apply, Kernel.id_apply,
    lintegral_prod _ (show AEMeasurable (fun y : A × NoiseLeaf A n => F (p.1,y)) _ from
      (hF.comp measurable_prodMk_left).aemeasurable),
    lintegral_dirac']
  exact (hF.comp measurable_prodMk_left).lintegral_prod_right'

end IsingPerceptron

namespace IsingPerceptron
open scoped ProbabilityTheory
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [Nonempty A] in
lemma measurable_noiseLeafTerminal (n : ℕ) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseLeaf A n => noiseLeafTerminal n X u p.1 p.2) := by
  induction n generalizing X u with
  | zero => exact (hX 0).comp measurable_fst
  | succ n ih =>
    exact (ih (fun i => hX (i+1)) (fun i => hu (i+1))).comp
      (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))

lemma noiseChildKernel_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : ℝ × (A × NoiseTree A n) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂noiseChildKernel A n ν) = (noiseTreeTotal A (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 * F p ∂ν := by
  change (∫⁻ p, F p ∂normalizeMass (noiseChildMass A n ν)) = _
  rw [normalizeMass, ite_eq_left (by simpa only [noiseChildMass_univ] using hν),
    lintegral_smul_measure, smul_eq_mul, noiseChildMass_univ, noiseChildMass]
  congr 1
  exact lintegral_withDensity_eq_lintegral_mul ν
    (show Measurable (fun p : ℝ × (A × NoiseTree A n) =>
      ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2) from
      ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0))).mul ((measurable_noiseTreeTotal A n).comp (by fun_prop)))) hF

lemma noiseLeafKernel_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) = (noiseTreeTotal A (n+1) ν)⁻¹ *
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_step A n ν hF]
  apply noiseChildKernel_lintegral n ν hν
  exact (hF.comp (by fun_prop : Measurable (fun p :
      (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n => (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
    (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))

lemma measurable_noiseLeafIntegral (n : ℕ) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseTree A n => ∫⁻ v,
      ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u p.1 v)) ∂noiseLeafKernel A n p.2) :=
  (((measurable_noiseLeafTerminal n hX hu).comp (by fun_prop : Measurable
    (fun p : (S × NoiseTree A n) × NoiseLeaf A n => (p.1.1,p.2)))).exp.ennreal_ofReal).lintegral_kernel_prod_right'
      (κ := (noiseLeafKernel A n).comap Prod.snd measurable_snd)

theorem noiseTreeFactor_leafIntegral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)),
      noiseTreeFactor n b μ X u s ν = noiseTreeTotal A n ν *
        ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n X u s v)) ∂noiseLeafKernel A n ν := by
  induction n generalizing b μ X u s with
  | zero =>
    apply ae_of_all
    intro ν
    simp [noiseTreeFactor, noiseTreeTotal, rawTreeTotal, noiseLeafTerminal,
      noiseLeafKernel, noiseLeafKernelData, Kernel.const_apply]
  | succ n ih =>
    let bt := fun j => b (j+1)
    let μt := fun j => μ (j+1)
    let Xt := fun j => X (j+1)
    let ut := fun j => u (j+1)
    let P := (noiseCascadeLaw A n bt μt : Measure (NoiseTree A n))
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
    let E := fun p : ℝ × (A × NoiseTree A n) =>
      noiseTreeFactor n bt μt Xt ut (u 0 (s,p.2.1)) p.2.2 = noiseTreeTotal A n p.2.2 *
      ∫⁻ v, ENNReal.ofReal (Real.exp (noiseLeafTerminal n Xt ut (u 0 (s,p.2.1)) v))
        ∂noiseLeafKernel A n p.2.2
    have hme : MeasurableSet {p | E p} := by
      apply measurableSet_eq_fun
      · exact (measurable_noiseTreeFactor n bt μt (fun i => hX (i+1))
          (fun i => hu (i+1))).comp (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))
      · exact ((measurable_noiseTreeTotal A n).comp (by fun_prop)).mul
          ((measurable_noiseLeafIntegral n (fun i => hX (i+1)) (fun i => hu (i+1))).comp
            (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop)))
    have he : ∀ᵐ p ∂I, E p := by
      apply (Measure.ae_prod_iff_ae_ae hme).mpr
      apply ae_of_all
      intro x
      apply (Measure.ae_prod_iff_ae_ae (hme.preimage (measurable_const.prodMk measurable_id))).mpr
      apply ae_of_all
      intro a
      exact ih bt hb.tail μt (fun i => hX (i+1)) (fun i => hu (i+1)) (u 0 (s,a))
    have ha := poissonLaw_ae_intensity I hme he
    have hg := noiseCascade_good A n.succ b hb μ
    have hσ := sigmaPart_eq_ae I
    filter_upwards [ha,hg,hσ] with ν hν hg hσ
    rw [noiseTreeFactor]
    change (∫⁻ p, ENNReal.ofReal (max p.1 0) *
      noiseTreeFactor n bt μt Xt ut (u 0 (s,p.2.1)) p.2.2 ∂sigmaPart I ν) = _
    rw [hσ, noiseLeafKernel_lintegral n ν hg.1
      (F := fun v => ENNReal.ofReal (Real.exp (noiseLeafTerminal (n+1) X u s v)))
      (((measurable_noiseLeafTerminal (n+1) hX hu).comp
        (measurable_const.prodMk measurable_id)).exp.ennreal_ofReal)]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hg.1.1.ne' hg.1.2.ne, one_mul]
    apply lintegral_congr_ae
    filter_upwards [hν] with p hp
    rw [hp]
    exact (mul_assoc _ _ _).symm

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [Nonempty A] in
lemma measurable_noiseLeafKeep (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    Measurable (fun p : S × NoiseLeaf A n => noiseLeafKeep n c u p.1 p.2) := by
  induction n generalizing c u with
  | zero => exact measurable_const
  | succ n ih =>
    exact (((hc 0).comp (by fun_prop)).mul (by fun_prop)).prodMk
      ((by fun_prop : Measurable (fun p : S × NoiseLeaf A (n+1) => p.2.2.1)).prodMk
        ((ih (fun i => hc (i+1)) (fun i => hu (i+1))).comp
          (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))))

lemma noiseWeightedLeafMeasure_lintegral (n : ℕ) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (s : S) (ν : NoiseTree A n) {F : NoiseLeaf A n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂noiseWeightedLeafMeasure n c u s ν) = noiseTreeTotal A n ν *
      ∫⁻ v, noiseLeafProduct n c u s v * F (noiseLeafKeep n c u s v) ∂noiseLeafKernel A n ν := by
  have hp : Measurable (noiseLeafProduct n c u s) :=
    (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id)
  have hk : Measurable (noiseLeafKeep n c u s) :=
    (measurable_noiseLeafKeep n hc hu).comp (measurable_const.prodMk measurable_id)
  rw [noiseWeightedLeafMeasure, lintegral_map' hF.aemeasurable hk.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun v => noiseTreeTotal A n ν * noiseLeafProduct n c u s v) from measurable_const.mul hp)
      (show Measurable (fun v => F (noiseLeafKeep n c u s v)) from hF.comp hk)]
  change (∫⁻ v, (noiseTreeTotal A n ν * noiseLeafProduct n c u s v) *
    F (noiseLeafKeep n c u s v) ∂noiseLeafKernel A n ν) = _
  simp_rw [mul_assoc]
  exact lintegral_const_mul _ (hp.mul (hF.comp hk))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_NoiseGibbsRegular
attribute [-instance] _root_.OAI.IsingPerceptron.markedReplicaLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noise Gibbs Regular. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma measurableSet_noiseGibbsRegular (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i)) :
    MeasurableSet {p : S × NoiseTree A n | NoiseGibbsRegular n b μ c u p.1 p.2} := by
  induction n generalizing b μ c u with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    have htot : Measurable (fun p : S × NoiseTree A (n+1) => noiseTreeTotal A (n+1) p.2) :=
      (measurable_noiseTreeTotal A (n+1)).comp measurable_snd
    have hkeep : Measurable (fun p : S × NoiseTree A (n+1) =>
        noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u p.1 p.2)) :=
      (measurable_noiseTreeTotal A (n+1)).comp (measurable_noiseTreeKeep (n+1) b μ hc hu)
    have hgood : MeasurableSet {p : S × NoiseTree A (n+1) | Marked.PoissonGood I p.2} :=
      by
        simp only [Marked.PoissonGood, ofPred_forall]
        exact MeasurableSet.iInter (fun j => measurableSet_lt
          ((Measure.measurable_coe (MeasurableSet.disjointed (measurableSet_spanningSets I) j)).comp measurable_snd)
          (measurable_const (a := (∞ : ℝ≥0∞))))
    let B := {p : (S × NoiseTree A (n+1)) × (ℝ × (A × NoiseTree A n)) |
      ¬ NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1.1,p.2.2.1)) p.2.2.2}
    have hB : MeasurableSet B :=
      ((ih _ _ (fun j => hc (j+1)) (fun j => hu (j+1))).preimage
        (((hu 0).comp (by fun_prop)).prodMk (by fun_prop))).compl
    have hm : Measurable (fun p : S × NoiseTree A (n+1) =>
        ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (p,x) ∂sigmaPart I p.2) :=
      measurable_sigmaPart_param I measurable_snd (measurable_const.indicator hB)
    have he : {p : S × NoiseTree A (n+1) | ∀ᵐ x ∂sigmaPart I p.2,
        NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1,x.2.1)) x.2.2} =
        {p | (∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (p,x) ∂sigmaPart I p.2) = 0} := by
      ext p
      rw [mem_ofPred_eq, mem_ofPred_eq, ae_iff]
      change (sigmaPart I p.2) {x | (p,x) ∈ B} = 0 ↔ _
      have hh := lintegral_indicator_one (μ := sigmaPart I p.2)
        (show MeasurableSet {x : ℝ × (A × NoiseTree A n) | (p,x) ∈ B} from
          hB.preimage (measurable_const.prodMk measurable_id))
      simpa only [Set.indicator, mem_ofPred_eq, Pi.one_apply] using Iff.of_eq (congrArg (· = 0) hh).symm
    have htail : MeasurableSet {p : S × NoiseTree A (n+1) | ∀ᵐ x ∂sigmaPart I p.2,
        NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (p.1,x.2.1)) x.2.2} := by
      rw [he]
      exact measurableSet_eq_fun hm measurable_const
    exact ((measurableSet_lt measurable_const htot).inter (measurableSet_lt htot measurable_const)).inter
      (((measurableSet_lt measurable_const hkeep).inter (measurableSet_lt hkeep measurable_const)).inter
        (hgood.inter htail))

lemma noiseGibbsRegular_ae (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, ∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A) = 1) (s : S) :
    ∀ᵐ ν ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)), NoiseGibbsRegular n b μ c u s ν := by
  induction n generalizing b μ c u s with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ n ih =>
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))
    have htot := noiseCascade_good A (n+1) b hb μ
    have hkeep : ∀ᵐ ν ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))),
        0 < noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u s ν) ∧
          noiseTreeTotal A (n+1) (noiseTreeKeep (n+1) b μ c u s ν) < ∞ := by
      simp_rw [noiseTreeTotal, noiseTreeKeep_forget (n+1) b μ hc hu]
      apply ae_of_ae_map (μ := (noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))))
        (p := fun T : RawTree (n+1) => 0 < rawTreeTotal (n+1) T ∧ rawTreeTotal (n+1) T < ∞)
        ((measurable_noiseTreeDisplace (n+1) b μ hc hu).comp
          (measurable_const.prodMk measurable_id)).aemeasurable
      change ∀ᵐ y ∂(noiseCascadeLaw A (n+1) b μ : Measure (NoiseTree A (n+1))).map
        (noiseTreeDisplace (n+1) b μ c u s), 0 < rawTreeTotal (n+1) y ∧ rawTreeTotal (n+1) y < ∞
      rw [noiseTreeDisplace_law (n+1) b μ hc hu hcpos hm s]
      exact (rawCascade_total_moments (n+1) b hb).1
    let E := fun p : ℝ × (A × NoiseTree A n) =>
      NoiseGibbsRegular n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => c (j+1)) (fun j => u (j+1)) (u 0 (s,p.2.1)) p.2.2
    have hE : MeasurableSet {p | E p} :=
      (measurableSet_noiseGibbsRegular n _ _ (fun j => hc (j+1)) (fun j => hu (j+1))).preimage
        (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))
    have ha : ∀ᵐ p ∂I, E p := by
      apply (Measure.ae_prod_iff_ae_ae hE).mpr
      apply ae_of_all
      intro x
      apply (Measure.ae_prod_iff_ae_ae (hE.preimage (measurable_const.prodMk measurable_id))).mpr
      apply ae_of_all
      intro a
      exact ih _ hb.tail _ (fun j => hc (j+1)) (fun j => hu (j+1))
        (fun j => hcpos (j+1)) (fun j => hm (j+1)) (u 0 (s,a))
    have hd := poissonLaw_ae_intensity I hE ha
    filter_upwards [htot,hkeep,Marked.poissonGood_ae I,hd] with ν hν hk hg hd
    refine ⟨hν.1,hk,hg,?_⟩
    rwa [Marked.sigmaPart_eq_of_good I hg]

lemma noiseLeafKernel_unnormalized_lintegral (n : ℕ) (ν : NoiseTree A (n+1))
    (hν : 0 < noiseTreeTotal A (n+1) ν ∧ noiseTreeTotal A (n+1) ν < ∞)
    {F : NoiseLeaf A (n+1) → ℝ≥0∞} (hF : Measurable F) :
    noiseTreeTotal A (n+1) ν * (∫⁻ v, F v ∂noiseLeafKernel A (n+1) ν) =
      ∫⁻ p, ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂ν := by
  rw [noiseLeafKernel_lintegral n ν hν hF, ← mul_assoc,
    ENNReal.mul_inv_cancel hν.1.ne' hν.2.ne, one_mul]

theorem noiseWeightedLeafMeasure_eq (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a)) (s : S) (ν : NoiseTree A n)
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    noiseWeightedLeafMeasure n c u s ν =
      noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) •
        noiseLeafKernel A n (noiseTreeKeep n b μ c u s ν) := by
  induction n generalizing b μ c u s with
  | zero =>
    apply Measure.ext_of_lintegral
    intro F hF
    simp [noiseWeightedLeafMeasure_lintegral 0 hc hu s ν hF,
      noiseTreeKeep, noiseTreeTotal, rawTreeTotal, noiseLeafProduct,
      noiseLeafKeep, noiseLeafKernel, noiseLeafKernelData, Kernel.const_apply]
  | succ n ih =>
    let bt := fun j => b (j+1)
    let μt := fun j => μ (j+1)
    let ct := fun j => c (j+1)
    let ut := fun j => u (j+1)
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
      (noiseCascadeLaw A n bt μt : Measure (NoiseTree A n)))
    let T : ℝ × (A × NoiseTree A n) → ℝ × (A × NoiseTree A n) := fun p =>
      (c 0 (s,p.2.1)*p.1,(p.2.1,noiseTreeKeep n bt μt ct ut (u 0 (s,p.2.1)) p.2.2))
    have hT : Measurable T :=
      (((hc 0).comp (measurable_const.prodMk (by fun_prop))).mul measurable_fst).prodMk
        ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => p.2.1)).prodMk
          ((measurable_noiseTreeKeep n bt μt (fun j => hc (j+1)) (fun j => hu (j+1))).comp
            (((hu 0).comp (measurable_const.prodMk (by fun_prop))).prodMk (by fun_prop))))
    have hσ : sigmaPart I ν = ν := Marked.sigmaPart_eq_of_good I hν.2.2.1
    have hd : ∀ᵐ p ∂ν, NoiseGibbsRegular n bt μt ct ut (u 0 (s,p.2.1)) p.2.2 := by
      have hh : ∀ᵐ p ∂sigmaPart I ν, NoiseGibbsRegular n bt μt ct ut (u 0 (s,p.2.1)) p.2.2 := hν.2.2.2
      rwa [hσ] at hh
    have hkeep : noiseTreeKeep (n+1) b μ c u s ν = ν.map T := by
      change (sigmaPart I ν).map T = _
      rw [hσ]
    apply Measure.ext_of_lintegral
    intro F hF
    have hG : Measurable (fun v : NoiseLeaf A (n+1) =>
        noiseLeafProduct (n+1) c u s v * F (noiseLeafKeep (n+1) c u s v)) :=
      ((measurable_noiseLeafProduct (n+1) hc hu).comp (measurable_const.prodMk measurable_id)).mul
        (hF.comp ((measurable_noiseLeafKeep (n+1) hc hu).comp (measurable_const.prodMk measurable_id)))
    rw [noiseWeightedLeafMeasure_lintegral (n+1) hc hu s ν hF,
      noiseLeafKernel_unnormalized_lintegral n ν hν.1 hG,
      lintegral_smul_measure, smul_eq_mul,
      noiseLeafKernel_unnormalized_lintegral n _ hν.2.1 hF, hkeep]
    have hmF : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) :=
      (hF.comp (by fun_prop : Measurable (fun p : (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n =>
        (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
          (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))
    rw [lintegral_map' (show AEMeasurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
          ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) _ from
      (((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_noiseTreeTotal A n).comp (by fun_prop))).mul hmF).aemeasurable) hT.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [hd] with p hp
    have hFp : Measurable (fun v : NoiseLeaf A n => F (c 0 (s,p.2.1)*p.1,(p.2.1,v))) :=
      hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have he := congrArg (fun η : Measure (NoiseLeaf A n) =>
      ∫⁻ v, F (c 0 (s,p.2.1)*p.1,(p.2.1,v)) ∂η)
      (ih bt μt (fun j => hc (j+1)) (fun j => hu (j+1))
        (fun j => hcpos (j+1)) (u 0 (s,p.2.1)) p.2.2 hp)
    rw [noiseWeightedLeafMeasure_lintegral n (fun j => hc (j+1)) (fun j => hu (j+1)) _ _ hFp,
      lintegral_smul_measure, smul_eq_mul] at he
    change ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
      (∫⁻ v, (ENNReal.ofReal (c 0 (s,p.2.1)) * noiseLeafProduct n ct ut (u 0 (s,p.2.1)) v) *
        F (c 0 (s,p.2.1)*p.1,(p.2.1,noiseLeafKeep n ct ut (u 0 (s,p.2.1)) v))
          ∂noiseLeafKernel A n p.2.2) =
      ENNReal.ofReal (max (c 0 (s,p.2.1)*p.1) 0) *
        noiseTreeTotal A n (noiseTreeKeep n bt μt ct ut (u 0 (s,p.2.1)) p.2.2) *
        (∫⁻ v, F (c 0 (s,p.2.1)*p.1,(p.2.1,v))
          ∂noiseLeafKernel A n (noiseTreeKeep n bt μt ct ut (u 0 (s,p.2.1)) p.2.2))
    have hcmax : max (c 0 (s,p.2.1)*p.1) 0 = c 0 (s,p.2.1)*max p.1 0 := by
      rw [mul_max_of_nonneg _ _ (hcpos 0 s p.2.1).le, mul_zero]
    rw [hcmax, ENNReal.ofReal_mul (hcpos 0 s p.2.1).le]
    simp_rw [mul_assoc]
    have hz : Measurable (fun v : NoiseLeaf A n => noiseLeafProduct n ct ut (u 0 (s,p.2.1)) v *
        F (c 0 (s,p.2.1)*p.1,(p.2.1,noiseLeafKeep n ct ut (u 0 (s,p.2.1)) v))) :=
      (((measurable_noiseLeafProduct n (fun j => hc (j+1)) (fun j => hu (j+1))).comp
        (measurable_const.prodMk measurable_id)).mul
        (hFp.comp ((measurable_noiseLeafKeep n (fun j => hc (j+1)) (fun j => hu (j+1))).comp
          (measurable_const.prodMk measurable_id))))
    rw [lintegral_const_mul _ hz]
    calc
      _ = ENNReal.ofReal (c 0 (s,p.2.1)) * ENNReal.ofReal (max p.1 0) *
          (noiseTreeTotal A n p.2.2 * ∫⁻ v, noiseLeafProduct n ct ut (u 0 (s,p.2.1)) v *
            F (c 0 (s,p.2.1)*p.1,(p.2.1,noiseLeafKeep n ct ut (u 0 (s,p.2.1)) v))
              ∂noiseLeafKernel A n p.2.2) := by ring
      _ = _ := by rw [he]; ring

end IsingPerceptron

namespace IsingPerceptron

lemma normalizeMass_of_probability {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) [IsProbabilityMeasure ν] : normalizeMass ν = ν := by
  simp [normalizeMass, measure_univ]

lemma normalizeMass_smul {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) {c : ℝ≥0∞} (hc : 0 < c ∧ c < ∞)
    (hν : 0 < ν univ ∧ ν univ < ∞) : normalizeMass (c • ν) = normalizeMass ν := by
  have ht : 0 < (c • ν) univ ∧ (c • ν) univ < ∞ := by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ⟨ENNReal.mul_pos hc.1.ne' hν.1.ne', ENNReal.mul_lt_top hc.2 hν.2⟩
  rw [normalizeMass, ite_eq_left ht, normalizeMass, ite_eq_left hν,
    Measure.smul_apply, smul_eq_mul, smul_smul,
    ENNReal.mul_inv (Or.inl hc.1.ne') (Or.inl hc.2.ne)]
  congr 1
  calc
    c⁻¹ * (ν univ)⁻¹ * c = (c⁻¹*c)*(ν univ)⁻¹ := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hc.1.ne' hc.2.ne, one_mul]

variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [MeasurableSpace S] in
lemma NoiseGibbsRegular.masses {n : ℕ} {b : ℕ → ℝ} {μ : ℕ → ProbabilityMeasure A}
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S} {s : S} {ν : NoiseTree A n}
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    (0 < noiseTreeTotal A n ν ∧ noiseTreeTotal A n ν < ∞) ∧
      (0 < noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) ∧
        noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) < ∞) := by
  cases n with
  | zero => simp [noiseTreeTotal, rawTreeTotal]
  | succ n => exact ⟨hν.1,hν.2.1⟩

theorem noiseTiltedLeafLaw_keep (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a)) (s : S) (ν : NoiseTree A n)
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    (noiseTiltedLeafLaw n c u s ν).map (noiseLeafKeep n c u s) =
      noiseLeafKernel A n (noiseTreeKeep n b μ c u s ν) := by
  let m := (noiseLeafKernel A n ν).withDensity (noiseLeafProduct n c u s)
  have hp : Measurable (noiseLeafProduct n c u s) :=
    (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id)
  have hk : Measurable (noiseLeafKeep n c u s) :=
    (measurable_noiseLeafKeep n hc hu).comp (measurable_const.prodMk measurable_id)
  have he : (noiseTreeTotal A n ν • m).map (noiseLeafKeep n c u s) =
      noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) •
        noiseLeafKernel A n (noiseTreeKeep n b μ c u s ν) := by
    have hh := noiseWeightedLeafMeasure_eq n b μ hc hu hcpos s ν hν
    unfold noiseWeightedLeafMeasure at hh
    change Measure.map (noiseLeafKeep n c u s)
      ((noiseLeafKernel A n ν).withDensity (noiseTreeTotal A n ν • noiseLeafProduct n c u s)) = _ at hh
    rwa [withDensity_smul _ hp] at hh
  have hm : noiseTreeTotal A n ν * m univ = noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) := by
    have hh := congrArg (fun η : Measure (NoiseLeaf A n) => η univ) he
    simpa only [Measure.map_apply hk MeasurableSet.univ, preimage_univ,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using hh
  have hm0 : 0 < m univ := by
    by_contra hh
    have hz : m univ = 0 := le_antisymm (le_of_not_gt hh) bot_le
    rw [hz, mul_zero] at hm
    exact hν.masses.2.1.ne' hm.symm
  have him : m univ < ∞ := by
    have hlt : noiseTreeTotal A n ν * m univ < ∞ := hm ▸ hν.masses.2.2
    rcases ENNReal.mul_lt_top_iff.mp hlt with h | h | h
    · exact h.2
    · exact (hν.masses.1.1.ne' h).elim
    · exact (hm0.ne' h).elim
  change (normalizeMass m).map _ = _
  rw [← normalizeMass_smul m hν.masses.1 ⟨hm0,him⟩,
    normalizeMass_map _ hk (by
      simp only [Measure.smul_apply, smul_eq_mul, hm]
      exact hν.masses.2), he,
    normalizeMass_smul _ hν.masses.2 (by simp), normalizeMass_of_probability]

end IsingPerceptron

namespace IsingPerceptron

lemma infinitePi_prod_join {ι E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : ι → Measure E) (ν : ι → Measure F)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p i => (p.1 i,p.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  refine (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro I
  have hμ : MeasurePreserving I.restrict (Measure.infinitePi μ) (Measure.pi (fun i : I => μ i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict μ⟩
  have hν : MeasurePreserving I.restrict (Measure.infinitePi ν) (Measure.pi (fun i : I => ν i)) :=
    ⟨I.measurable_restrict,Measure.infinitePi_map_restrict ν⟩
  have hp := hμ.prod hν
  have hs := (measurePreserving_arrowProdEquivProdArrow E F I (fun i => μ i) (fun i => ν i)).symm
  rw [Measure.map_map I.measurable_restrict (by fun_prop)]
  exact (hs.comp hp).map_eq

lemma finitePoissonProduct_laplace_partial {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) (n : ℕ) :
    (∫ ω, negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (ψ x) ∂ω i)
      ∂Measure.infinitePi (fun i => finitePoissonLaw (μ i))) =
      negExp (∑ i : Fin n, ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ i : Measure E)) := by
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hind := iIndepFun_infinitePi (P := fun i => finitePoissonLaw (μ i)) (fun _ => heval)
  have hh := (hind.precomp Fin.val_injective).integral_fun_prod_eq_prod_integral
    (fun i : Fin n => (heval.comp (measurable_pi_apply (i : ℕ))).aestronglyMeasurable)
  have hei (i : ℕ) :
      (∫ ω, negExp (a (ω i)) ∂Measure.infinitePi (fun j => finitePoissonLaw (μ j))) =
        negExp (∫⁻ x, c x ∂(μ i : Measure E)) := by
    calc
      _ = ∫ ν, negExp (a ν) ∂finitePoissonLaw (μ i) :=
        (measurePreserving_eval_infinitePi (fun j => finitePoissonLaw (μ j)) i).hasLaw.integral_comp
          heval.aestronglyMeasurable
      _ = _ := finitePoissonLaw_laplace (μ i) hψ hpos
  simpa only [negExp_sum, hei] using hh

theorem finitePoissonProduct_sum_law {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ℕ → FiniteMeasure E) :
    (Measure.infinitePi (fun n => finitePoissonLaw (μ n))).map Measure.sum =
      poissonLaw (Measure.sum (fun n => (μ n : Measure E))) := by
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  let P := Measure.infinitePi (fun n => finitePoissonLaw (μ n))
  let a : Measure E → ℝ≥0∞ := fun ν => ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν
  let c : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1-Real.exp (-ψ x))
  have ha : Measurable a := Measure.measurable_lintegral hψ.ennreal_ofReal
  have heval : Measurable (fun ν => negExp (a ν)) := continuous_negExp.measurable.comp ha
  have hlim := laplace_partial_tendsto P ha
  have hr : Tendsto (fun n => negExp (∑ i : Fin n, ∫⁻ x, c x ∂(μ i : Measure E)))
      atTop (𝓝 (negExp (∫⁻ x, c x ∂Measure.sum (fun n => (μ n : Measure E))))) := by
    rw [lintegral_sum_measure]
    simp_rw [Fin.sum_univ_eq_sum_range (fun i => ∫⁻ x, c x ∂(μ i : Measure E))]
    exact continuous_negExp.continuousAt.tendsto.comp (ENNReal.tendsto_nat_tsum _)
  rw [poissonLaw_laplace _ hψ hpos,
    integral_map measurable_measureSum.aemeasurable heval.aestronglyMeasurable]
  change (∫ ω, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂Measure.sum ω) ∂P) = _
  simp_rw [lintegral_sum_measure]
  exact tendsto_nhds_unique (by
    simpa only [a,P,finitePoissonProduct_laplace_partial μ hψ hpos] using hlim) (by simpa only [lintegral_sum_measure] using hr)

lemma finiteCloud_laplace {E : Type*} [MeasurableSpace E] (r : ℝ≥0)
    (ρ : Measure E) [IsProbabilityMeasure ρ] {ψ : E → ℝ}
    (hψ : Measurable ψ) (hpos : ∀ x, 0 ≤ ψ x) :
    (∫ p, negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) ∂finitePoissonCloud r ρ) =
      negExp ((r : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂ρ) := by
  have hcost : ∀ x, 0 ≤ 1-Real.exp (-ψ x) := fun x =>
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x)))
  have hi : Integrable (fun x => Real.exp (-ψ x)) ρ := by
    apply Integrable.of_bound hψ.neg.exp.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hpos x))
  have hicost : Integrable (fun x => 1-Real.exp (-ψ x)) ρ := (integrable_const 1).sub hi
  have hs (p : ℕ × (ℕ → E)) :
      negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂finiteCloudMeasure p) =
        Real.exp (-cloudSum ψ p) := by
    rw [finiteCloudMeasure_lintegral p hψ.ennreal_ofReal,
      ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (fun (i : Fin p.1) _ => hpos (p.2 i)), negExp_ofReal]
    · rfl
    · exact Finset.sum_nonneg (fun i _ => hpos (p.2 i))
  simp_rw [hs]
  rw [finitePoissonCloud_laplace r ρ hψ hpos,
    ← ofReal_integral_eq_lintegral_ofReal hicost (ae_of_all _ hcost),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul r.coe_nonneg,
    negExp_ofReal (mul_nonneg r.coe_nonneg (integral_nonneg hcost)),
    integral_sub (integrable_const 1) hi, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  congr 1
  ring

lemma finiteCloud_mark_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (r : ℝ≥0) (μ : Measure E) (ν : Measure F)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((finitePoissonCloud r μ).prod (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => (p.1.1,fun i => (p.1.2 i,p.2 i))) = finitePoissonCloud r (μ.prod ν) := by
  have hj : MeasurePreserving (fun p : (ℕ → E) × (ℕ → F) => fun i => (p.1 i,p.2 i))
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => ν)))
      (Measure.infinitePi (fun _ : ℕ => μ.prod ν)) :=
    ⟨by fun_prop,infinitePi_prod_join _ _⟩
  have hp := (MeasurePreserving.id (poissonMeasure r)).prod hj
  have ha := measurePreserving_prodAssoc (poissonMeasure r)
    (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.infinitePi (fun _ : ℕ => ν))
  exact (hp.comp ha).map_eq

lemma finiteCloud_mark_measure_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : FiniteMeasure E) (ν : Measure F) [IsProbabilityMeasure ν] :
    ((finitePoissonCloud μ.mass (μ.normalize : Measure E)).prod
      (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun p => finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))) =
      finitePoissonLaw ⟨(μ : Measure E).prod ν,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩ := by
  let ξ : FiniteMeasure (E × F) := ⟨(μ : Measure E).prod ν,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  change _ = finitePoissonLaw ξ
  rw [show (fun p : (ℕ × (ℕ → E)) × (ℕ → F) =>
    finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))) =
    finiteCloudMeasure ∘ (fun p => (p.1.1,fun i => (p.1.2 i,p.2 i))) from rfl,
    ← Measure.map_map measurable_finiteCloudMeasure (by fun_prop),finiteCloud_mark_law]
  apply randomMeasure_laplace_unique
  intro ψ hψ hpos
  have hm : Measurable (fun π : Measure (E × F) => negExp (∫⁻ x, ENNReal.ofReal (ψ x) ∂π)) :=
    continuous_negExp.measurable.comp (Measure.measurable_lintegral hψ.ennreal_ofReal)
  rw [integral_map measurable_finiteCloudMeasure.aemeasurable hm.aestronglyMeasurable,
    finiteCloud_laplace _ _ hψ hpos,finitePoissonLaw_laplace ξ hψ hpos]
  change _ = negExp (∫⁻ x, ENNReal.ofReal (1-Real.exp (-ψ x)) ∂(μ : Measure E).prod ν)
  rw [finiteMeasure_mass_normalize μ,Measure.prod_smul_left,lintegral_smul_measure]
  rfl

lemma measurable_labeledMarkedMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] :
    Measurable (labeledMarkedMeasure (E := E) (F := F)) := by
  apply measurable_measureSum.comp
  apply Measurable.of_eval
  intro n
  apply measurable_finiteCloudMeasure.comp
  fun_prop

theorem labeledMarkedMeasure_law {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Nonempty E] [Nonempty F] (μ : ℕ → FiniteMeasure E)
    (ν : Measure F) [IsProbabilityMeasure ν] :
    ((labeledPoissonLaw μ).prod (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => ν)))).map labeledMarkedMeasure =
    poissonLaw ((Measure.sum (fun n => (μ n : Measure E))).prod ν) := by
  let f : (ℕ × (ℕ → E)) × (ℕ → F) → Measure (E × F) :=
    fun p => finiteCloudMeasure (p.1.1,fun i => (p.1.2 i,p.2 i))
  have hf : Measurable f := measurable_finiteCloudMeasure.comp (by fun_prop)
  have hjoin : Measurable (fun p : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F) => fun n => (p.1 n,p.2 n)) := by
    fun_prop
  have hfpi : Measurable (fun p : ℕ → (ℕ × (ℕ → E)) × (ℕ → F) => fun n => f (p n)) :=
    Measurable.of_eval (fun _ => hf.comp (measurable_pi_apply _))
  have hcomp : (labeledMarkedMeasure (E := E) (F := F)) =
    Measure.sum ∘ (fun p : ℕ → (ℕ × (ℕ → E)) × (ℕ → F) => fun n => f (p n)) ∘
      (fun p : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F) => fun n => (p.1 n,p.2 n)) := rfl
  rw [hcomp,← Function.comp_assoc,← Measure.map_map (measurable_measureSum.comp hfpi) hjoin,
    labeledPoissonLaw,infinitePi_prod_join,
    ← Measure.map_map measurable_measureSum hfpi,Measure.infinitePi_map_pi _ (fun _ => hf)]
  simp only [f,finiteCloud_mark_measure_law]
  let η : ℕ → FiniteMeasure (E × F) := fun i => ⟨(μ i : Measure E).prod ν,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  change (Measure.infinitePi (fun i => finitePoissonLaw (η i))).map Measure.sum = _
  rw [finitePoissonProduct_sum_law η]
  have hcongr {P Q : Measure (E × F)} [SFinite P] [SFinite Q] (h : P = Q) :
      poissonLaw P = poissonLaw Q := by subst Q; rfl
  apply hcongr
  exact (Measure.prod_sum_left _ _).symm

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ChildLabel
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.enrichedForestCoordinates_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledLeafEncodable _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Child Label. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma intensityComponents_sum {E : Type*} [MeasurableSpace E] (μ : Measure E) [SFinite μ] :
    Measure.sum (fun n => (intensityComponents μ n : Measure E)) = μ :=
  sum_sfiniteSeq μ

lemma labeledLeafMass_lintegral (n : ℕ) (ω : LabeledTree n) (F : LabeledLeaf n → ℝ≥0∞) :
    (∫⁻ v, F v ∂labeledLeafMass n ω) = ∑' v, labeledLeafWeight n ω v * F v := by
  rw [labeledLeafMass,lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) 
    (measurable_of_countable _),lintegral_count]
  rfl

lemma finiteCloud_tsum_weight (ω : WeightCloud) (F : ChildLabel → ℝ≥0∞) :
    (∑' a, childLabelWeight ω a * F a) =
      ∑' m, ∑ i : Fin (ω m).1, ENNReal.ofReal (max ((ω m).2 i) 0) * F (m,i) := by
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro m
  simp only [childLabelWeight,ite_mul,zero_mul]
  rw [tsum_eq_sum (s := Finset.range (ω m).1)]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [i.isLt,ite_true]
  · intro i hi
    exact ite_eq_right (by simpa using hi)

variable (A : Type) [MeasurableSpace A]

@[fun_prop] lemma measurable_labeledNoiseJoin (n : ℕ) : Measurable (labeledNoiseJoin A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) => labeledMarkedMeasure (p.1.1,fun m i =>
          ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2))))
    apply measurable_labeledMarkedMeasure.comp
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.of_eval
    intro m
    apply Measurable.of_eval
    intro i
    exact (by fun_prop : Measurable (fun p : LabeledTree (n+1) × MarkForest A (n+1) =>
      (p.2 m i).1)).prodMk (ih.comp (by fun_prop))

lemma infinitePi_prod_join2 {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)))).map
      (fun p m i => (p.1 m i,p.2 m i)) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ.prod ν)) := by
  rw [show (fun p : (ℕ → ℕ → E) × (ℕ → ℕ → F) => fun m i => (p.1 m i,p.2 m i)) =
      (fun q : ℕ → (ℕ → E) × (ℕ → F) => fun m i => ((q m).1 i,(q m).2 i)) ∘
      (fun p : (ℕ → ℕ → E) × (ℕ → ℕ → F) => fun m => (p.1 m,p.2 m)) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_prod_join,
    Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : (ℕ → E) × (ℕ → F)) => fun i => (q.1 i,q.2 i))
      (fun _ => by fun_prop)]
  simp_rw [infinitePi_prod_join]

lemma measurePreserving_swap_first_two {E F G : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]
    (μ : Measure E) (ν : Measure F) (ξ : Measure G)
    [SFinite μ] [SFinite ν] [SFinite ξ] :
    MeasurePreserving (fun p : E × (F × G) => (p.2.1,(p.1,p.2.2)))
      (μ.prod (ν.prod ξ)) (ν.prod (μ.prod ξ)) := by
  exact (measurePreserving_prodAssoc ν μ ξ).comp
    (((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ξ)).comp
      (measurePreserving_prodAssoc μ ν ξ).symm)

theorem labeledNoiseJoin_law [Nonempty A] (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure A) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw A n μ)).map (labeledNoiseJoin A n) = noiseCascadeLaw A n b μ := by
  induction n generalizing b μ with
  | zero =>
    change ((Measure.dirac (PUnit.unit : PUnit)).prod (Measure.dirac (PUnit.unit : PUnit))).map
      (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp
  | succ n ih =>
    let b' := fun j => b (j+1)
    let μ' := fun j => μ (j+1)
    let L : Measure (LabeledTree n) := labeledCascadeLaw n b'
    let M : Measure (MarkForest A n) := markForestLaw A n μ'
    let R : Measure (NoiseTree A n) := noiseCascadeLaw A n b' μ'
    let W := labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))
    have hi : MeasurePreserving (labeledNoiseJoin A n) (L.prod M) R :=
      ⟨measurable_labeledNoiseJoin A n,ih b' μ'⟩
    have hp := ((MeasurePreserving.id (μ 0 : Measure A)).prod hi).comp
      (measurePreserving_swap_first_two L (μ 0 : Measure A) M)
    have hmap : (L.prod ((μ 0 : Measure A).prod M)).map
        (fun p => (p.2.1,labeledNoiseJoin A n (p.1,p.2.2))) = (μ 0 : Measure A).prod R := hp.map_eq
    have hpi : MeasurePreserving
        (fun p : (ℕ → ℕ → LabeledTree n) × (ℕ → ℕ → A × MarkForest A n) =>
          fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1 m i,(p.2 m i).2)))
        ((Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L))).prod
          (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M))))
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod R))) := by
      refine ⟨Measurable.of_eval (fun m => Measurable.of_eval (fun i =>
        (by fun_prop : Measurable (fun p : (ℕ → ℕ → LabeledTree n) ×
            (ℕ → ℕ → A × MarkForest A n) => (p.2 m i).1)).prodMk
          ((measurable_labeledNoiseJoin A n).comp (by fun_prop)))),?_⟩
      rw [show (fun p : (ℕ → ℕ → LabeledTree n) × (ℕ → ℕ → A × MarkForest A n) =>
          fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1 m i,(p.2 m i).2))) =
          (fun q : ℕ → ℕ → LabeledTree n × (A × MarkForest A n) => fun m i =>
            ((q m i).2.1,labeledNoiseJoin A n ((q m i).1,(q m i).2.2))) ∘
          (fun p => fun m i => (p.1 m i,p.2 m i)) from rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_prod_join2,
        Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : ℕ → LabeledTree n × (A × MarkForest A n)) => fun i =>
          ((q i).2.1,labeledNoiseJoin A n ((q i).1,(q i).2.2))) (fun _ => by fun_prop)]
      simp_rw [Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (p : LabeledTree n × (A × MarkForest A n)) =>
        (p.2.1,labeledNoiseJoin A n (p.1,p.2.2))) (fun _ => hp.measurable),hmap]
    have hfull := ((MeasurePreserving.id W).prod hpi).comp
      (measurePreserving_prodAssoc W _ _)
    change ((W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M)))).map
      (labeledMarkedMeasure ∘ (fun p => (p.1.1,fun m i =>
        ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2))))) = _
    have hfm : Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) => (p.1.1,fun m i =>
          ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2)))) := hfull.measurable
    rw [← Measure.map_map measurable_labeledMarkedMeasure hfm]
    have hfe : ((W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L)))).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M)))).map
        (fun p => (p.1.1,fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2)))) =
        W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod R))) := hfull.map_eq
    rw [hfe,labeledMarkedMeasure_law,noiseCascadeLaw_succ]
    apply poissonLaw_congr
    rw [intensityComponents_sum]

end IsingPerceptron

namespace IsingPerceptron

lemma infinitePi_option_join {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (μ.prod (Measure.infinitePi ν)).map (fun p : A × (ι → A) => fun i : Option ι =>
      i.elim p.1 p.2) = Measure.infinitePi (fun i : Option ι => i.elim μ ν) := by
  classical
  let ρ : Option ι → Measure A := fun i => i.elim μ ν
  have : ∀ i, IsProbabilityMeasure (ρ i) := fun i => by cases i <;> dsimp [ρ] <;> infer_instance
  change _ = Measure.infinitePi ρ
  refine Measure.eq_infinitePi ρ (fun I t ht => ?_)
  have hm : Measurable (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop
  rw [Measure.map_apply hm (.pi I.countable_toSet (fun i _ => ht i))]
  have he : (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) ⁻¹'
      ((I : Set (Option ι)).pi t) =
      (if none ∈ I then t none else Set.univ) ×ˢ ((I.eraseNone : Set ι).pi (fun i => t (some i))) := by
    ext p
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Finset.mem_coe,Finset.mem_eraseNone]
    constructor
    · intro h
      constructor
      · split_ifs with hn
        · exact h none hn
        · trivial
      · intro i hi
        exact h (some i) hi
    · rintro ⟨ha,hb⟩ i hi
      cases i with
      | none => simpa only [ite_eq_left hi,Option.elim_none] using ha
      | some i => exact hb i hi
  rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht (some i))]
  by_cases hn : none ∈ I
  · rw [ite_eq_left hn,← Finset.prod_erase_mul _ _ hn]
    have her : I.erase none = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp
    rw [her,Finset.prod_map,mul_comm]
    rfl
  · rw [ite_eq_right hn,measure_univ,one_mul]
    have her : I = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp [hn]
    rw [her,Finset.prod_map]
    simp only [Finset.eraseNone_map_some]
    rfl

lemma infinitePi_option_split {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i : Option ι => i.elim μ ν)).map
      (fun g => (g none,fun i => g (some i))) = μ.prod (Measure.infinitePi ν) := by
  rw [← infinitePi_option_join μ ν,Measure.map_map (by fun_prop) (by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop)]
  change (μ.prod (Measure.infinitePi ν)).map id = _
  exact Measure.map_id

lemma infinitePi_triple_curry {I J K A : Type*} [MeasurableSpace A]
    (μ : I → J → K → Measure A) [∀ i j k, IsProbabilityMeasure (μ i j k)] :
    (Measure.infinitePi (fun p : I × (J × K) => μ p.1 p.2.1 p.2.2)).map
      (fun g i j k => g (i,j,k)) =
      Measure.infinitePi (fun i => Measure.infinitePi (fun j => Measure.infinitePi (μ i j))) := by
  rw [show (fun g : (I × (J × K)) → A => fun i j k => g (i,j,k)) =
      (fun q : I → (J × K → A) => fun i j k => q i (j,k)) ∘
      (MeasurableEquiv.curry I (J × K) A) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),Measure.infinitePi_map_curry
      (fun (i : I) (p : J × K) => μ i p.1 p.2)]
  rw [Measure.infinitePi_map_pi _ (f := fun (_ : I) (q : J × K → A) => fun j k => q (j,k))
    (fun _ => by fun_prop)]
  simp only [show (fun q : J × K → A => fun j k => q (j,k)) =
    MeasurableEquiv.curry J K A from rfl,Measure.infinitePi_map_curry]

variable (A : Type) [MeasurableSpace A]

theorem markForestOfCoords_law (n : ℕ) (μ : ℕ → ProbabilityMeasure A) :
    (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A))).map
      (markForestOfCoords A n) = markForestLaw A n μ := by
  induction n generalizing μ with
  | zero =>
    change (Measure.infinitePi _).map (fun _ => (PUnit.unit : PUnit)) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp
  | succ n ih =>
    let μ' := fun j => μ (j+1)
    let ν : ForestVertex n → Measure A := fun v => μ' (forestVertexDepth n v)
    have (i : Option (ForestVertex n)) : IsProbabilityMeasure (i.elim (μ 0 : Measure A) ν) := by
      cases i <;> dsimp <;> infer_instance
    have hi : MeasurePreserving (markForestOfCoords A n) (Measure.infinitePi ν)
        (markForestLaw A n μ') := ⟨measurable_markForestOfCoords A n,ih μ'⟩
    have hs : MeasurePreserving (fun g : Option (ForestVertex n) → A =>
        (g none,fun v => g (some v)))
        (Measure.infinitePi (fun v => v.elim (μ 0 : Measure A) ν))
        ((μ 0 : Measure A).prod (Measure.infinitePi ν)) :=
      ⟨by fun_prop,infinitePi_option_split (μ 0 : Measure A) ν⟩
    have hp := ((MeasurePreserving.id (μ 0 : Measure A)).prod hi).comp hs
    have hmap : (Measure.infinitePi (fun v : Option (ForestVertex n) =>
        v.elim (μ 0 : Measure A) ν)).map (fun g =>
          (g none,markForestOfCoords A n (fun v => g (some v)))) =
        (μ 0 : Measure A).prod (markForestLaw A n μ') := hp.map_eq
    have hc : (fun v : ForestVertex (n+1) => (μ (forestVertexDepth (n+1) v) : Measure A)) =
        (fun v : ℕ × (ℕ × Option (ForestVertex n)) => v.2.2.elim (μ 0 : Measure A) ν) := by
      funext v
      rcases v with ⟨m,i,v⟩
      cases v <;> rfl
    rw [hc]
    change (Measure.infinitePi (fun v : ℕ × (ℕ × Option (ForestVertex n)) =>
        v.2.2.elim (μ 0 : Measure A) ν)).map
        ((fun q : ℕ → ℕ → Option (ForestVertex n) → A => fun m i =>
          (q m i none,markForestOfCoords A n (fun v => q m i (some v)))) ∘
          (fun g m i v => g (m,i,v))) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_triple_curry
        (fun (_ _ : ℕ) (v : Option (ForestVertex n)) => v.elim (μ 0 : Measure A) ν),
      Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : ℕ → Option (ForestVertex n) → A) =>
        fun i => (q i none,markForestOfCoords A n (fun v => q i (some v)))) (fun _ => by fun_prop)]
    simp_rw [Measure.infinitePi_map_pi _
        (f := fun (_ : ℕ) (g : Option (ForestVertex n) → A) =>
          (g none,markForestOfCoords A n (fun v => g (some v)))) (fun _ => hp.measurable),hmap]
    rfl

end IsingPerceptron

namespace IsingPerceptron

theorem labeledNoiseCoordinates_law (A : Type) [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))).map
      (fun p => labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)) =
      noiseCascadeLaw A n b μ := by
  have hp := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
    (show MeasurePreserving (markForestOfCoords A n)
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))
      (markForestLaw A n μ) from ⟨measurable_markForestOfCoords A n,markForestOfCoords_law A n μ⟩)
  change _ = _
  rw [show (fun p : LabeledTree n × (ForestVertex n → A) =>
      labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)) =
      (labeledNoiseJoin A n) ∘ Prod.map id (markForestOfCoords A n) from rfl,
    ← Measure.map_map (measurable_labeledNoiseJoin A n) hp.measurable,hp.map_eq,
    labeledNoiseJoin_law]

lemma labeledMarkedMeasure_lintegral {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F))
    {G : E × F → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ p, G p ∂labeledMarkedMeasure ω) =
      ∑' m, ∑ i : Fin (ω.1 m).1, G ((ω.1 m).2 i,ω.2 m i) := by
  simp only [labeledMarkedMeasure,lintegral_sum_measure,finiteCloudMeasure_lintegral _ hG]

lemma labeledMarkedMeasure_ae {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F)) {P : E × F → Prop}
    (hP : MeasurableSet {p | P p}) (h : ∀ᵐ p ∂labeledMarkedMeasure ω, P p) :
    ∀ m (i : Fin (ω.1 m).1), P ((ω.1 m).2 i,ω.2 m i) := by
  intro m i
  have hm := (Measure.ae_sum_iff.mp h) m
  rw [finiteCloudMeasure,← Measure.sum_fintype] at hm
  exact (ae_dirac_iff hP).mp ((Measure.ae_sum_iff.mp hm) i)

variable (A : Type) [MeasurableSpace A] [Nonempty A]

theorem labeledLeafMass_noiseMap (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z))) :
    (labeledLeafMass n ω).map (labeledNoiseLeaf A n (ω,z)) =
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) •
        noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  induction n with
  | zero =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral]
    simp [labeledLeafWeight,labeledNoiseLeaf,noiseTreeTotal,
      rawTreeTotal,noiseLeafKernel,noiseLeafKernelData,Kernel.const_apply]
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral,lintegral_smul_measure,smul_eq_mul,
      noiseLeafKernel_unnormalized_lintegral n _ hgood.1 hF]
    have hinner : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) :=
      (hF.comp (by fun_prop : Measurable (fun p :
        (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n => (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
        (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))
    have hg := labeledMarkedMeasure_ae _
      ((measurableSet_GoodNoiseTree A n).preimage (by fun_prop)) hgood.2
    change (∑' v : ChildLabel × LabeledLeaf n,
      (childLabelWeight ω.1 v.1 * labeledLeafWeight n (ω.2 v.1.1 v.1.2) v.2) *
        F ((ω.1 v.1.1).2 v.1.2,((z v.1.1 v.1.2).1,
          labeledNoiseLeaf A n (ω.2 v.1.1 v.1.2,(z v.1.1 v.1.2).2) v.2))) =
      ∫⁻ p : ℝ × (A × NoiseTree A n), ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂
          labeledMarkedMeasure (ω.1,fun m i => ((z m i).1,labeledNoiseJoin A n (ω.2 m i,(z m i).2)))
    have hG : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
          (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2)) :=
      ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_noiseTreeTotal A n).comp (measurable_snd.comp measurable_snd))).mul hinner
    rw [labeledMarkedMeasure_lintegral
      (ω.1,fun m i => ((z m i).1,labeledNoiseJoin A n (ω.2 m i,(z m i).2))) hG]
    rw [ENNReal.tsum_prod']
    simp_rw [mul_assoc,ENNReal.tsum_mul_left]
    rw [finiteCloud_tsum_weight]
    apply tsum_congr
    intro m
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have he := ih (ω.2 m i) (z m i).2 (hg m i)
    have hFi : Measurable (fun v : NoiseLeaf A n => F ((ω.1 m).2 i,((z m i).1,v))) := by fun_prop
    have hh := congrArg (fun ν : Measure (NoiseLeaf A n) => ∫⁻ v, F ((ω.1 m).2 i,((z m i).1,v)) ∂ν) he
    rw [lintegral_map' hFi.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral,lintegral_smul_measure,smul_eq_mul] at hh
    exact hh

theorem labeledLeafLaw_noiseMap (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z)))
    (ht : 0 < noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) ∧
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) < ∞) :
    (labeledLeafLaw n ω).map (labeledNoiseLeaf A n (ω,z)) =
      noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  have hm := labeledLeafMass_noiseMap A n ω z hgood
  have htot : labeledLeafMass n ω Set.univ = noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) := by
    have he := congrArg (fun ν : Measure (NoiseLeaf A n) => ν Set.univ) hm
    simpa only [Measure.map_apply_of_aemeasurable (measurable_of_countable _).aemeasurable MeasurableSet.univ,
      Set.preimage_univ,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one] using he
  rw [labeledLeafLaw,normalizeMass_map _ (measurable_of_countable _) (by simpa only [htot] using ht),
    hm,normalizeMass_smul _ ht (by simp),normalizeMass_of_probability]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_GaussianIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Integration. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert h using 1 <;> try rfl
  · ext y
    simp [gaussianPDFReal]
  · norm_num [gaussianPDFReal]
    ring

lemma integrable_gaussian_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul']
  · simp [gaussianPDF, ENNReal.toReal_ofReal, gaussianPDFReal_nonneg]
  · exact measurable_gaussianPDF _ _
  · exact ae_of_all _ (fun x => by simp [gaussianPDF])

lemma gaussian_integration_by_parts {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := f') (v := gaussianPDFReal 0 1)
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardGaussianPDF x)
  have h1 : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert (integrable_gaussian_iff.mp hxf).neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x; dsimp; ring
  have h2 : Integrable (fun x => f' x * gaussianPDFReal 0 1 x) := by
    simpa [mul_comm] using integrable_gaussian_iff.mp hf'
  have h3 : Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
    simpa [mul_comm] using integrable_gaussian_iff.mp hf
  specialize hh h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul] at *
  have heq : (fun x => f x * (-x * gaussianPDFReal 0 1 x)) =
      fun x => -(gaussianPDFReal 0 1 x * (x * f x)) := by ext x; ring
  rw [heq, integral_neg] at hh
  simpa [mul_comm] using neg_injective hh

lemma gaussian_integration_by_parts_bounded {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hm' : Measurable f')
    {K K' : ℝ} (hb : ∀ x, |f x| ≤ K) (hb' : ∀ x, |f' x| ≤ K') :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hm : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hd x).continuousAt)).measurable
  have hif : Integrable f (gaussianReal 0 1) :=
    (MemLp.of_bound hm.aestronglyMeasurable K
      (ae_of_all _ (fun x => by simpa using hb x)) (p := 1)).integrable le_rfl
  have hif' : Integrable f' (gaussianReal 0 1) :=
    (MemLp.of_bound hm'.aestronglyMeasurable K'
      (ae_of_all _ (fun x => by simpa using hb' x)) (p := 1)).integrable le_rfl
  apply gaussian_integration_by_parts hd hif hif'
  exact ((memLp_id_gaussianReal 1).integrable le_rfl).mul_bdd
    hm.aestronglyMeasurable (ae_of_all _ (fun x => by simpa using hb x))

lemma gaussian_pi_integration_by_parts {n : ℕ} (i : Fin (n + 1))
    {F F' : (Fin (n + 1) → ℝ) → ℝ} (hm : Measurable F) (hm' : Measurable F')
    (hd : ∀ (g : Fin n → ℝ) (x : ℝ),
      HasDerivAt (fun y => F (i.insertNth y g)) (F' (i.insertNth x g)) x)
    {K K' : ℝ} (hb : ∀ g, |F g| ≤ K) (hb' : ∀ g, |F' g| ≤ K') :
    (∫ g, g i * F g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ g, F' g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e.symm ((gaussianReal 0 1).prod ν) μ :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i).symm
  have hF' : Integrable F' μ :=
    (MemLp.of_bound hm'.aestronglyMeasurable K'
      (ae_of_all _ (fun g => by simpa using hb' g)) (p := 1)).integrable le_rfl
  have hFi : Integrable (fun g => g i * F g) μ := by
    have hc : Integrable (fun g : Fin (n + 1) → ℝ => g i) μ :=
      (measurePreserving_eval (fun _ : Fin (n + 1) => gaussianReal 0 1) i).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)
    exact hc.mul_bdd hm.aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa using hb g))
  change (∫ g, g i * F g ∂μ) = ∫ g, F' g ∂μ
  rw [← he.integral_comp' (fun g => g i * F g), ← he.integral_comp' F']
  have hi1 : Integrable (fun v => e.symm v i * F (e.symm v))
      ((gaussianReal 0 1).prod ν) := he.integrable_comp_of_integrable hFi
  have hi2 : Integrable (fun v => F' (e.symm v))
      ((gaussianReal 0 1).prod ν) := he.integrable_comp_of_integrable hF'
  rw [integral_prod_symm _ hi1, integral_prod_symm _ hi2]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_apply_same]
  apply gaussian_integration_by_parts_bounded (hd g)
  · exact hm'.comp (measurable_pi_iff.mpr (i.forall_iff_succAbove.mpr
      ⟨by simp only [Fin.insertNth_apply_same]; exact measurable_id,
        fun j => by simp⟩))
  · exact fun x => hb _
  · exact fun x => hb' _

section FiniteGibbs
variable {S : Type*} [Fintype S]

lemma finitePartition_pos {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) :
    0 < finitePartition w H := by
  obtain ⟨x, hx⟩ := hw.2
  exact Finset.sum_pos' (fun y _ => mul_nonneg (hw.1 y) (Real.exp_pos _).le)
    ⟨x, Finset.mem_univ _, mul_pos hx (Real.exp_pos _)⟩

lemma finiteGibbs_nonneg {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) (x : S) :
    0 ≤ finiteGibbs w H x :=
  div_nonneg (mul_nonneg (hw.1 x) (Real.exp_pos _).le) (finitePartition_pos hw H).le

lemma finiteGibbs_sum {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) :
    ∑ x, finiteGibbs w H x = 1 := by
  simp only [finiteGibbs, ← Finset.sum_div]
  exact div_self (finitePartition_pos hw H).ne'

lemma finiteGibbs_le_one {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ) (x : S) :
    finiteGibbs w H x ≤ 1 := by
  rw [← finiteGibbs_sum hw H]
  exact Finset.single_le_sum (fun y _ => finiteGibbs_nonneg hw H y) (Finset.mem_univ x)

lemma finiteGibbs_average_bound {w : S → ℝ} (hw : GibbsReference w)
    (H A : S → ℝ) {K : ℝ} (hA : ∀ x, |A x| ≤ K) :
    |∑ x, finiteGibbs w H x * A x| ≤ K := by
  calc
    _ ≤ ∑ x, |finiteGibbs w H x * A x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, finiteGibbs w H x * |A x| := by
      congr 1; ext x; rw [abs_mul, abs_of_nonneg (finiteGibbs_nonneg hw H x)]
    _ ≤ ∑ x, finiteGibbs w H x * K := Finset.sum_le_sum
      (fun x _ => mul_le_mul_of_nonneg_left (hA x) (finiteGibbs_nonneg hw H x))
    _ = K := by rw [← Finset.sum_mul, finiteGibbs_sum hw H, one_mul]

lemma hasDerivAt_finitePartition {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) (w : S → ℝ) :
    HasDerivAt (fun s => finitePartition w (H s))
      (∑ x, w x * Real.exp (H t x) * dH x) t := by
  simpa only [finitePartition, mul_assoc] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => (hH x).exp.const_mul (w x)))

lemma hasDerivAt_finiteGibbs {w : S → ℝ} (hw : GibbsReference w)
    {H : ℝ → S → ℝ} {dH : S → ℝ} {t : ℝ}
    (hH : ∀ x, HasDerivAt (fun s => H s x) (dH x) t) (x : S) :
    HasDerivAt (fun s => finiteGibbs w (H s) x)
      (finiteGibbs w (H t) x *
        (dH x - ∑ y, finiteGibbs w (H t) y * dH y)) t := by
  have hd := ((hH x).exp.const_mul (w x)).div
    (hasDerivAt_finitePartition hH w) (finitePartition_pos hw (H t)).ne'
  convert hd using 1 <;> try rfl
  simp only [finiteGibbs, div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp [(finitePartition_pos hw (H t)).ne']

end FiniteGibbs

section GaussianGibbs
variable {S : Type*} [Fintype S]

lemma continuous_gaussianGibbs {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (x : S) :
    Continuous (fun g => gaussianGibbs w B C g x) := by
  unfold gaussianGibbs finiteGibbs
  apply Continuous.div
  · unfold linearGaussian; fun_prop
  · unfold finitePartition linearGaussian; fun_prop
  · exact fun g => (finitePartition_pos hw _).ne'

omit [Fintype S] in
lemma hasDerivAt_linearGaussian_insert {n : ℕ} (C : S → Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (g : Fin n → ℝ) (x : S) (t : ℝ) :
    HasDerivAt (fun y => linearGaussian C (i.insertNth y g) x) (C x i) t := by
  have he : (fun y => linearGaussian C (i.insertNth y g) x) =
      fun y => C x i * y + ∑ j : Fin n, C x (i.succAbove j) * g j := by
    funext y
    simp only [linearGaussian, i.sum_univ_succAbove, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove]
  rw [he]
  simpa using ((hasDerivAt_id t).const_mul (C x i)).add_const
    (∑ j : Fin n, C x (i.succAbove j) * g j)

lemma hasDerivAt_gaussianGibbs_insert {n : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (g : Fin n → ℝ) (x : S) (t : ℝ) :
    HasDerivAt (fun y => gaussianGibbs w B C (i.insertNth y g) x)
      (gaussianGibbs w B C (i.insertNth t g) x *
        (C x i - ∑ z, gaussianGibbs w B C (i.insertNth t g) z * C z i)) t := by
  apply hasDerivAt_finiteGibbs hw
  intro z
  exact (hasDerivAt_linearGaussian_insert C i g z t).const_add (B z)

end GaussianGibbs

section Replicas
variable {S : Type*} [Fintype S]

lemma replicaGibbs_nonneg {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) (σ : Fin r → S) :
    0 ≤ replicaGibbs w B C g σ :=
  Finset.prod_nonneg (fun l _ => finiteGibbs_nonneg hw _ (σ l))

lemma replicaGibbs_le_one {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) (σ : Fin r → S) :
    replicaGibbs w B C g σ ≤ 1 := by
  exact Finset.prod_le_one (fun replica _ => finiteGibbs_nonneg hw _ (σ replica))
    (fun l _ => finiteGibbs_le_one hw _ (σ l))

lemma replicaGibbs_sum {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (g : Fin n → ℝ) :
    ∑ σ : Fin r → S, replicaGibbs w B C g σ = 1 := by
  classical
  unfold replicaGibbs
  rw [← Fintype.prod_sum]
  simp only [gaussianGibbs, finiteGibbs_sum hw, Finset.prod_const_one]

lemma continuous_replicaGibbs {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (σ : Fin r → S) :
    Continuous (fun g => replicaGibbs w B C g σ) := by
  exact continuous_finsetProd _ (fun l _ => continuous_gaussianGibbs hw B C (σ l))

lemma hasDerivAt_replicaGibbs_insert {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (g : Fin n → ℝ) (σ : Fin r → S) (t : ℝ) :
    HasDerivAt (fun y => replicaGibbs w B C (i.insertNth y g) σ)
      (replicaGibbs w B C (i.insertNth t g) σ *
        (∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C (i.insertNth t g) z * C z i))) t := by
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun l _ => hasDerivAt_gaussianGibbs_insert hw B C i g (σ l) t)
  convert hd using 1 <;> try rfl
  simp only [smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← mul_assoc, Finset.prod_erase_mul _ _ hl]
  rfl

lemma integrable_gaussian_coordinate_mul {n : ℕ} (i : Fin n)
    {F : (Fin n → ℝ) → ℝ} (hm : Measurable F) {K : ℝ} (hK : ∀ g, |F g| ≤ K) :
    Integrable (fun g => g i * F g) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hc : Integrable (fun g : Fin n → ℝ => g i)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
      ((memLp_id_gaussianReal 1).integrable le_rfl)
  exact hc.mul_bdd hm.aestronglyMeasurable (ae_of_all _ (fun g => by simpa using hK g))

omit [Fintype S] in
lemma gaussian_pi_linear_insertion {n : ℕ} (a : Fin (n + 1) → ℝ)
    {F : (Fin (n + 1) → ℝ) → ℝ} {F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ}
    (hm : Measurable F) (hm' : ∀ i, Measurable (F' i))
    (hd : ∀ i g x, HasDerivAt (fun y => F (i.insertNth y g)) (F' i (i.insertNth x g)) x)
    {K : ℝ} {K' : Fin (n + 1) → ℝ}
    (hb : ∀ g, |F g| ≤ K) (hb' : ∀ i g, |F' i g| ≤ K' i) :
    (∫ g, (∑ i, a i * g i) * F g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ g, ∑ i, a i * F' i g ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hi i : Integrable (F' i) (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (MemLp.of_bound (hm' i).aestronglyMeasurable (K' i)
      (ae_of_all _ (fun g => by simpa using hb' i g)) (p := 1)).integrable le_rfl
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (integrable_gaussian_coordinate_mul i hm hb).const_mul _),
    integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_const_mul,
    gaussian_pi_integration_by_parts i hm (hm' i) (hd i) hb (hb' i)]

lemma gaussian_replica_insertion {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n + 1) → ℝ) (x : S) (σ : Fin r → S) :
    (∫ g, linearGaussian A g x * replicaGibbs w B C g σ
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ g, replicaGibbs w B C g σ *
      (∑ l, (gaussianCross A C x (σ l) -
        ∑ z, gaussianGibbs w B C g z * gaussianCross A C x z))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hd := gaussian_pi_linear_insertion (A x) (continuous_replicaGibbs hw B C σ).measurable
    (F' := fun i g => replicaGibbs w B C g σ *
      ∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C g z * C z i))
    (fun i => ((continuous_replicaGibbs hw B C σ).mul
      (continuous_finsetSum _ (fun l _ => continuous_const.sub
        (continuous_finsetSum _ (fun z _ =>
          (continuous_gaussianGibbs hw B C z).mul continuous_const))))).measurable)
    (fun i g t => hasDerivAt_replicaGibbs_insert hw B C i g σ t)
    (K := 1) (K' := fun i => ∑ l, (|C (σ l) i| + ∑ z, |C z i|))
    (fun g => by rw [abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)];
                 exact replicaGibbs_le_one hw B C g σ)
  have hb i g : |replicaGibbs w B C g σ *
      ∑ l, (C (σ l) i - ∑ z, gaussianGibbs w B C g z * C z i)| ≤
      ∑ l, (|C (σ l) i| + ∑ z, |C z i|) := by
    rw [abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
    apply (mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg _)).trans
    rw [one_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro l _
    exact (abs_sub _ _).trans (add_le_add le_rfl
      (finiteGibbs_average_bound hw (fun z => B z + linearGaussian C g z)
        (fun z => C z i) (fun z => Finset.single_le_sum (fun y _ => abs_nonneg (C y i))
          (Finset.mem_univ z))))
  rw [show linearGaussian A = fun g x => ∑ i, A x i * g i from rfl, hd hb]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  simp only [gaussianCross, Finset.mul_sum, mul_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro i _
    ring

end Replicas

section Perturbation
variable {S : Type*} [Fintype S]

omit [Fintype S] in
lemma integrable_linearGaussian {n : ℕ} (A : S → Fin n → ℝ) (x : S) :
    Integrable (fun g => linearGaussian A g x)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply integrable_finsetSum
  intro i _
  exact ((measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).integrable_comp_of_integrable
    ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul _

end Perturbation

variable {S : Type*} [Fintype S]

lemma replicaMean_abs_le {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) {D : (Fin r → S) → ℝ}
    {K : ℝ} (hD : ∀ σ, |D σ| ≤ K) (g : Fin n → ℝ) :
    |replicaMean w B C D g| ≤ K := by
  calc
    _ ≤ ∑ σ, replicaGibbs w B C g σ*|D σ| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
    _ ≤ ∑ σ : Fin r → S, replicaGibbs w B C g σ*K := by
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left (hD σ) (replicaGibbs_nonneg hw B C g σ)
    _ = K := by rw [← Finset.sum_mul, replicaGibbs_sum hw, one_mul]

lemma integrable_replicaMean {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (D : (Fin r → S) → ℝ) :
    Integrable (replicaMean w B C D) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply Integrable.of_bound
    (continuous_finsetSum _ (fun σ _ => (continuous_replicaGibbs hw B C σ).mul continuous_const)).aestronglyMeasurable
    (∑ σ, |D σ|)
  apply ae_of_all
  intro g
  exact replicaMean_abs_le hw B C (fun σ =>
    Finset.single_le_sum (fun τ _ => abs_nonneg (D τ)) (Finset.mem_univ σ)) g

lemma integrable_linear_mul_replica {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (x : S) (σ : Fin r → S) :
    Integrable (fun g => linearGaussian A g x*replicaGibbs w B C g σ)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  apply (integrable_linearGaussian A x).mul_bdd
    (continuous_replicaGibbs hw B C σ).aestronglyMeasurable (c := 1)
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
  exact replicaGibbs_le_one hw B C g σ

lemma integrable_replica_covariance {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin n → ℝ) (x : S) (σ : Fin r → S) :
    Integrable (fun g => replicaGibbs w B C g σ*
      (∑ l, (gaussianCross A C x (σ l)-∑ z, gaussianGibbs w B C g z*gaussianCross A C x z)))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  let K := ∑ z, |gaussianCross A C x z|
  apply Integrable.of_bound
    ((continuous_replicaGibbs hw B C σ).mul
      (continuous_finsetSum _ (fun l _ => continuous_const.sub
        (continuous_finsetSum _ (fun z _ =>
          (continuous_gaussianGibbs hw B C z).mul continuous_const))))).aestronglyMeasurable
    (∑ l, (|gaussianCross A C x (σ l)|+K))
  apply ae_of_all
  intro g
  simp only [Pi.mul_apply, Pi.sub_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
  calc
    _ ≤ 1*|∑ l, (gaussianCross A C x (σ l)-∑ z, gaussianGibbs w B C g z*gaussianCross A C x z)| :=
      mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      exact (abs_sub _ _).trans (add_le_add le_rfl
        (finiteGibbs_average_bound hw _ _ (fun z =>
          show |gaussianCross A C x z| ≤ ∑ y, |gaussianCross A C x y| from
            Finset.single_le_sum (fun y _ => abs_nonneg (gaussianCross A C x y)) (Finset.mem_univ z))))

lemma gaussian_replica_test_insertion {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (A C : S → Fin (n+1) → ℝ) (D : (Fin (r+1) → S) → ℝ) :
    (∫ g, ∑ σ : Fin (r+1) → S,
      D σ*(linearGaussian A g (σ 0)*replicaGibbs w B C g σ)
      ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
    ∫ g, ∑ σ : Fin (r+1) → S, D σ*(replicaGibbs w B C g σ*
      (∑ l, (gaussianCross A C (σ 0) (σ l)-
        ∑ z, gaussianGibbs w B C g z*gaussianCross A C (σ 0) z)))
      ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
  rw [integral_finsetSum _ (fun σ _ => (integrable_linear_mul_replica hw B A C (σ 0) σ).const_mul (D σ)),
    integral_finsetSum _ (fun σ _ => (integrable_replica_covariance hw B A C (σ 0) σ).const_mul (D σ))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_const_mul, integral_const_mul, gaussian_replica_insertion hw]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_CountableMonomialGG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

section
variable {S : Type*} [Fintype S]

lemma integrable_freshCovarianceMean {n r : ℕ} {w : S → ℝ} (hw : GibbsReference w)
    (B : S → ℝ) (C : S → Fin n → ℝ) (κ : S → S → ℝ) (D : (Fin (r+1) → S) → ℝ) :
    Integrable (freshCovarianceMean w B C κ D) (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hm : AEStronglyMeasurable (freshCovarianceMean w B C κ D)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (continuous_finsetSum _ (fun σ _ => ((continuous_replicaGibbs hw B C σ).mul continuous_const).mul
      (continuous_finsetSum _ (fun z _ => (continuous_gaussianGibbs hw B C z).mul continuous_const)))).aestronglyMeasurable
  apply Integrable.of_bound hm ((∑ σ, |D σ|)*(∑ p : S × S, |κ p.1 p.2|))
  apply ae_of_all
  intro g
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ σ, |replicaGibbs w B C g σ*D σ*(∑ z, gaussianGibbs w B C g z*κ (σ 0) z)| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ σ : Fin (r+1) → S, |D σ| *(∑ p : S × S, |κ p.1 p.2|) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul, abs_mul, abs_of_nonneg (replicaGibbs_nonneg hw B C g σ)]
      have hk := finiteGibbs_average_bound hw (fun x => B x+linearGaussian C g x)
        (κ (σ 0)) (K := ∑ p : S × S, |κ p.1 p.2|) (fun z =>
          Finset.single_le_sum (fun (p : S × S) _ => abs_nonneg (κ p.1 p.2))
            (Finset.mem_univ (σ 0,z)))
      have hprod := mul_le_mul_of_nonneg_right (replicaGibbs_le_one hw B C g σ) (abs_nonneg (D σ))
      exact mul_le_mul (by simpa only [one_mul] using hprod) hk (abs_nonneg _) (abs_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

end

lemma reference_replica_partition {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) (r : ℕ) :
    (∫ σ : Fin r → X, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ => ν)) =
      (referencePartition ν H)^r := by
  simp_rw [Real.exp_sum]
  simpa only [Fintype.card_fin,referencePartition] using
    (integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) (fun x => Real.exp (H x)))

lemma referenceReplicaMean_eq_ratio {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D =
      (∫ σ, Real.exp (∑ i, H (σ i))*D σ ∂Measure.pi (fun _ : Fin r => ν)) /
      (∫ σ, Real.exp (∑ i, H (σ i)) ∂Measure.pi (fun _ : Fin r => ν)) := by
  rw [reference_replica_partition]; rfl

lemma finite_reference_weights_sum {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν] :
    ∑ x, ν.real {x} = 1 := by
  have h := integral_fintype (μ := ν) (f := fun _ => (1:ℝ)) Integrable.of_finite
  simpa only [smul_eq_mul,mul_one,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using h.symm

lemma finite_reference_weight_pos {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν] :
    ∃ x, 0 < ν.real {x} := by
  have hsum := finite_reference_weights_sum ν
  have h := Finset.sum_pos_iff_of_nonneg (fun (x:S) (_:x ∈ Finset.univ) => (measureReal_nonneg : 0 ≤ ν.real {x}))
  obtain ⟨x, _,hx⟩ := h.mp (show 0 < ∑ x, ν.real {x} by rw [hsum]; norm_num)
  exact ⟨x,hx⟩

lemma referencePartition_finite {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsFiniteMeasure ν] (H : S → ℝ) :
    referencePartition ν H = ∑ x, ν.real {x}*Real.exp (H x) := by
  exact integral_fintype Integrable.of_finite

lemma referenceReplicaMean_finite {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsFiniteMeasure ν] (H : S → ℝ)
    {r : ℕ} (D : (Fin r → S) → ℝ) :
    referenceReplicaMean ν H D =
      ∑ σ : Fin r → S, (∏ i, ν.real {σ i}*Real.exp (H (σ i))/referencePartition ν H)*D σ := by
  classical
  rw [referenceReplicaMean, integral_fintype Integrable.of_finite, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [measureReal_def,Measure.pi_singleton,ENNReal.toReal_prod,smul_eq_mul,
    Real.exp_sum,Finset.prod_div_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  rw [Finset.prod_mul_distrib]
  ring

lemma referencePartition_map {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    {μ : Measure S} {ν : Measure X} {f : S → X} (hf : MeasurePreserving f μ ν)
    {H : X → ℝ} (hmH : Measurable H) :
    referencePartition μ (H ∘ f) = referencePartition ν H := by
  exact hf.hasLaw.integral_comp hmH.exp.aestronglyMeasurable

lemma referenceReplicaMean_map {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    {μ : Measure S} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : S → X} (hf : MeasurePreserving f μ ν)
    {H : X → ℝ} (hmH : Measurable H) {r : ℕ} {D : (Fin r → X) → ℝ}
    (hmD : Measurable D) :
    referenceReplicaMean μ (H ∘ f) (fun σ => D (fun i => f (σ i))) =
      referenceReplicaMean ν H D := by
  have hpi : MeasurePreserving (fun σ : Fin r → S => fun i => f (σ i))
      (Measure.pi (fun _ : Fin r => μ)) (Measure.pi (fun _ : Fin r => ν)) := by
    refine ⟨Measurable.of_eval (fun index => hf.measurable.comp (measurable_pi_apply index)),?_⟩
    have hmap : IsProbabilityMeasure (μ.map f) := hf.map_eq.symm ▸ inferInstance
    simpa only [hf.map_eq] using Measure.pi_map_pi (μ := fun _ : Fin r => μ) (f := fun _ : Fin r => f) (fun _ : Fin r => hf.measurable.aemeasurable)
  unfold referenceReplicaMean
  rw [referencePartition_map hf hmH]
  congr 1
  exact hpi.hasLaw.integral_comp ((by fun_prop : Measurable
    (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))*D σ)).aestronglyMeasurable)

lemma finite_reference_GibbsReference {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν] :
    GibbsReference (fun x => ν.real {x}) :=
  ⟨fun _ => measureReal_nonneg,finite_reference_weight_pos ν⟩

lemma referenceReplicaMean_eq_finite {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν]
    {n r : ℕ} (B : S → ℝ) (C : S → Fin n → ℝ) (D : (Fin r → S) → ℝ) (g : Fin n → ℝ) :
    referenceReplicaMean ν (fun x => B x+linearGaussian C g x) D =
      replicaMean (fun x => ν.real {x}) B C D g := by
  rw [referenceReplicaMean_finite]
  simp only [referencePartition_finite,replicaMean,replicaGibbs,gaussianGibbs,finiteGibbs,finitePartition]

lemma replicaMean_fresh_eq {S : Type*} [Fintype S] {n r : ℕ}
    (w B : S → ℝ) (C : S → Fin n → ℝ) (κ : S → S → ℝ)
    (D : (Fin (r+1) → S) → ℝ) (g : Fin n → ℝ) :
    replicaMean w B C (fun τ : Fin (r+1+1) → S =>
      D (Fin.tail τ)*κ ((Fin.tail τ) 0) (τ 0)) g = freshCovarianceMean w B C κ D g := by
  classical
  have hp (z:S) (σ:Fin (r+1) → S) : replicaGibbs w B C g (Fin.cons z σ) =
      gaussianGibbs w B C g z*replicaGibbs w B C g σ := by
    simp only [replicaGibbs,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  unfold replicaMean
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r+1+1) => S)),Fintype.sum_prod_type]
  change (∑ z, ∑ σ : Fin (r+1) → S,
    replicaGibbs w B C g (Fin.cons z σ : Fin (r+1+1) → S)*(D σ*κ (σ 0) z)) = _
  simp only [hp]
  rw [Finset.sum_comm]
  unfold freshCovarianceMean
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem finite_gaussian_reference_insertion {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν]
    {n r : ℕ} (B : S → ℝ) (A C : S → Fin (n+1) → ℝ) (D : (Fin (r+1) → S) → ℝ) :
    (∫ g, referenceReplicaMean ν (fun x => B x+linearGaussian C g x)
      (fun σ => linearGaussian A g (σ 0)*D σ) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
    (∫ g, referenceReplicaMean ν (fun x => B x+linearGaussian C g x)
      (fun σ => D σ*(∑ i, gaussianCross A C (σ 0) (σ i)))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean ν (fun x => B x+linearGaussian C g x)
      (fun τ : Fin (r+1+1) → S => D (Fin.tail τ)*gaussianCross A C ((Fin.tail τ) 0) (τ 0))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) := by
  classical
  let w := fun x => ν.real {x}
  have hw : GibbsReference w := finite_reference_GibbsReference ν
  simp_rw [referenceReplicaMean_eq_finite]
  have hi := gaussian_replica_test_insertion hw B A C D
  have he g : (∑ σ : Fin (r+1) → S, D σ*(replicaGibbs w B C g σ*
      (∑ i, (gaussianCross A C (σ 0) (σ i)-∑ z, gaussianGibbs w B C g z*gaussianCross A C (σ 0) z)))) =
      replicaMean w B C (fun σ => D σ*(∑ i, gaussianCross A C (σ 0) (σ i))) g -
      (r+1 : ℕ)*freshCovarianceMean w B C (gaussianCross A C) D g := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    unfold replicaMean freshCovarianceMean
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  have hleft g : (∑ σ : Fin (r+1) → S, D σ*(linearGaussian A g (σ 0)*replicaGibbs w B C g σ)) =
      replicaMean w B C (fun σ => linearGaussian A g (σ 0)*D σ) g := by
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp_rw [he,hleft] at hi
  rw [integral_sub (integrable_replicaMean hw B C _) ((integrable_freshCovarianceMean hw B C _ D).const_mul _),
    integral_const_mul] at hi
  simpa only [replicaMean_fresh_eq] using hi

lemma gaussian_weighted_sum_law {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasLaw (fun g : ι → ℝ => ∑ i, a i * g i)
      (gaussianReal 0 ((∑ i, a i ^ 2).toNNReal))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun i => fun g : ι → ℝ => a i * g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => by fun_prop)
  have hl i : HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw
  have hg := hi.hasGaussianLaw_fun_sum (fun i => (gaussianReal_const_mul (hl i) (a i)).hasGaussianLaw)
  refine ⟨(by fun_prop : Measurable (fun g : ι → ℝ => ∑ i, a i * g i)).aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal]
  congr 1
  · have hI i : Integrable (fun g : ι → ℝ => a i * g i)
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
      ((measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul (a i)
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp_rw [integral_const_mul]
    have hz i : (∫ g : ι → ℝ, g i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
      simpa using (hl i).integral_eq
    simp [hz]
  · congr 1
    have hv i : Var[fun x : ℝ => a i*x; gaussianReal 0 1] = a i^2 := by
      simpa only [id_eq, variance_id_gaussianReal, NNReal.coe_one, mul_one] using
        (variance_const_mul (a i) id (gaussianReal 0 1))
    have hvsum := variance_sum_pi (μ := fun _ : ι => gaussianReal 0 1)
      (X := fun i x => a i * x) (fun i => (memLp_id_gaussianReal 2).const_mul (a i))
    rw [show (∑ i : ι, fun ω : ι → ℝ => a i * ω i) =
      (fun ω => ∑ i, a i * ω i) from by ext; simp] at hvsum
    simpa only [hv] using hvsum

lemma gaussian_prefix_measurePreserving (n : ℕ) :
    MeasurePreserving (fun g : ℕ → ℝ => fun i : Fin n => g i)
      gaussianCoordinates (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  refine ⟨by fun_prop, ?_⟩
  have hi : iIndepFun (fun i : ℕ => fun g : ℕ → ℝ => g i) gaussianCoordinates :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hs := hi.precomp (g := fun i : Fin n => (i:ℕ)) Fin.val_injective
  have he := hs.map_fun_eq_pi_map (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [gaussianCoordinates,Measure.infinitePi_map_eval] using he

lemma cylinderField_eq_prefix (a : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) (g : ℕ → ℝ) :
    cylinderField a g = ∑ i : Fin n, a i*g i := by
  classical
  rw [cylinderField, a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun i c => c*g i) (fun _ _ => zero_mul _)]
  exact (Fin.sum_univ_eq_sum_range _ n).symm

lemma finite_family_support_bound {X : Type*} [Fintype X] (a : X → ℕ →₀ ℝ) :
    ∃ n : ℕ, ∀ x i, a x i ≠ 0 → i < n+1 := by
  classical
  let s := Finset.univ.biUnion (fun x => (a x).support)
  refine ⟨s.sup id,fun x i hi => ?_⟩
  have hm : i ∈ s := Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,Finsupp.mem_support_iff.mpr hi⟩
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)

lemma cylinderField_law (a : ℕ →₀ ℝ) :
    gaussianCoordinates.map (cylinderField a) =
      gaussianReal 0 ((a.sum (fun _ c => c^2)).toNNReal) := by
  classical
  let n := a.support.sup id+1
  have ha : ∀ i ∈ a.support, i < n := fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  have he : cylinderField a = (fun g : Fin n → ℝ => ∑ i : Fin n, a i*g i) ∘
      (fun g : ℕ → ℝ => fun i : Fin n => g i) := by
    funext g
    exact cylinderField_eq_prefix a ha g
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),
    (gaussian_prefix_measurePreserving n).map_eq,(gaussian_weighted_sum_law (fun i : Fin n => a i)).map_eq]
  congr 2
  rw [a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun _ c => c^2) (fun _ _ => by norm_num)]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => a i^2) n

lemma cylinderField_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ)
    (g : ℕ → ℝ) : cylinderField (∑ i ∈ s, a i) g = ∑ i ∈ s, cylinderField (a i) g := by
  let L : (ℕ →₀ ℝ) →+ ℝ :=
    { toFun := fun a => cylinderField a g
      map_zero' := by simp [cylinderField]
      map_add' := fun a b => by
        exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul ..) }
  exact map_sum L _ _

lemma cylinder_variance_prefix (a : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) :
    a.sum (fun _ c => c^2) = ∑ i : Fin n, (a i)^2 := by
  rw [a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun _ c => c^2) (fun _ _ => by norm_num)]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => (a i)^2) n).symm

lemma cylinder_variance_sum_le {ι : Type*} [Fintype ι] (a : ι → ℕ →₀ ℝ)
    {K : ℝ} (ha : ∀ i, (a i).sum (fun _ c => c^2) ≤ K) :
    (∑ i, a i).sum (fun _ c => c^2) ≤ (Fintype.card ι : ℝ)^2*K := by
  classical
  obtain ⟨n, hn⟩ := finite_family_support_bound a
  have hs : ∀ j ∈ (∑ i, a i).support, j < n+1 := by
    intro j hj
    by_contra hjn
    have hz i : a i j = 0 := by
      by_contra h
      exact hjn (hn i j h)
    have hz' : (∑ i, a i) j = 0 := by simp only [Finsupp.finsetSum_apply,hz,Finset.sum_const_zero]
    exact Finsupp.mem_support_iff.mp hj hz'
  rw [cylinder_variance_prefix _ hs]
  simp only [Finsupp.finsetSum_apply]
  calc
    _ ≤ ∑ j : Fin (n+1), (Fintype.card ι : ℝ)*(∑ i, (a i j)^2) := by
      apply Finset.sum_le_sum
      intro j _
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
        (fun _ => (1:ℝ)) (fun i => a i j)
    _ = (Fintype.card ι : ℝ)*∑ i, ∑ j : Fin (n+1), (a i j)^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ (Fintype.card ι : ℝ)*∑ _i : ι, K := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      rw [← cylinder_variance_prefix (a i) (fun j hj => hn i j (Finsupp.mem_support_iff.mp hj))]
      exact ha i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

lemma cylinderCross_prefix (a b : ℕ →₀ ℝ) {n : ℕ}
    (ha : ∀ i ∈ a.support, i < n) :
    cylinderCross a b = ∑ i : Fin n, a i*b i := by
  rw [cylinderCross,a.sum_of_support_subset (s := Finset.range n)
    (fun i hi => Finset.mem_range.mpr (ha i hi)) (fun i c => c*b i) (fun _ _ => zero_mul _)]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => a i*b i) n).symm

lemma abs_cylinderCross_le (a b : ℕ →₀ ℝ) :
    |cylinderCross a b| ≤ (a.sum (fun _ c => c^2)+b.sum (fun _ c => c^2))/2 := by
  classical
  let n := a.support.sup id+b.support.sup id+1
  have ha : ∀ i ∈ a.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  have hb : ∀ i ∈ b.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  rw [cylinderCross_prefix a b ha,cylinder_variance_prefix a ha,cylinder_variance_prefix b hb]
  calc
    _ ≤ ∑ i : Fin n, |a i*b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, ((a i)^2+(b i)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      nlinarith [sq_abs (a i),sq_abs (b i),sq_nonneg (|a i|-|b i|)]
    _ = _ := by rw [← Finset.sum_div,Finset.sum_add_distrib]

lemma measurable_referenceReplicaMean {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] {r : ℕ} {H : Ω × X → ℝ}
    {D : Ω × (Fin r → X) → ℝ} (hmH : Measurable H) (hmD : Measurable D) :
    Measurable (fun ω => referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D (ω,σ))) := by
  have hrep : Measurable (fun z : Ω × (Fin r → X) => ∑ i, H (z.1,z.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hmH.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  exact (hrep.exp.mul hmD).stronglyMeasurable.integral_prod_right'.measurable.div
    (hmH.exp.stronglyMeasurable.integral_prod_right'.measurable.pow_const r)

theorem finite_cylinder_reference_insertion {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsProbabilityMeasure ν]
    (a b : S → ℕ →₀ ℝ) {r : ℕ} (D : (Fin (r+1) → S) → ℝ) :
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates) =
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → S => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates) := by
  classical
  obtain ⟨n₁,hn₁⟩ := finite_family_support_bound a
  obtain ⟨n₂,hn₂⟩ := finite_family_support_bound b
  let n := n₁+n₂
  let C : S → Fin (n+1) → ℝ := fun x i => a x i
  let B : S → Fin (n+1) → ℝ := fun x i => b x i
  have ha x : ∀ i ∈ (a x).support, i < n+1 := by
    intro i hi
    have := hn₁ x i (Finsupp.mem_support_iff.mp hi)
    omega
  have hb x : ∀ i ∈ (b x).support, i < n+1 := by
    intro i hi
    have := hn₂ x i (Finsupp.mem_support_iff.mp hi)
    omega
  have hC (g : ℕ → ℝ) x : linearGaussian C (fun i : Fin (n+1) => g i) x = cylinderField (a x) g :=
    (cylinderField_eq_prefix (a x) (ha x) g).symm
  have hB (g : ℕ → ℝ) x : linearGaussian B (fun i : Fin (n+1) => g i) x = cylinderField (b x) g :=
    (cylinderField_eq_prefix (b x) (hb x) g).symm
  have hcov x y : gaussianCross B C x y = cylinderCross (b x) (a y) :=
    (cylinderCross_prefix (b x) (a y) (hb x)).symm
  have hmC : Measurable (fun z : (Fin (n+1) → ℝ) × S => linearGaussian C z.1 z.2) :=
    measurable_from_prod_countable_left (fun x => by unfold linearGaussian; fun_prop)
  have hmL : Measurable (fun z : (Fin (n+1) → ℝ) × (Fin (r+1) → S) =>
      linearGaussian B z.1 (z.2 0)*D z.2) :=
    measurable_from_prod_countable_left (fun σ => by unfold linearGaussian; fun_prop)
  have hp := (gaussian_prefix_measurePreserving (n+1)).hasLaw
  have hL := hp.integral_comp (measurable_referenceReplicaMean ν hmC hmL).aestronglyMeasurable
  have hR₁ := hp.integral_comp (measurable_referenceReplicaMean ν hmC
    (measurable_of_countable (fun σ : Fin (r+1) → S =>
      D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) |>.comp measurable_snd)).aestronglyMeasurable
  have hR₂ := hp.integral_comp (measurable_referenceReplicaMean ν hmC
    (measurable_of_countable (fun τ : Fin (r+1+1) → S =>
      D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))) |>.comp measurable_snd)).aestronglyMeasurable
  have hfinite := finite_gaussian_reference_insertion ν (fun _ => 0) B C D
  simp only [zero_add] at hfinite
  simp_rw [hcov] at hfinite
  simp only [Function.comp_apply,hB,hC] at hL hR₁ hR₂
  rw [hL,hR₁,hR₂]
  exact hfinite

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_PartitionPowLe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition Pow Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

 

lemma partition_pow_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ} (p : ℕ)
    (h1 : Integrable (fun x => Real.exp (H x)) ν)
    (hp : Integrable (fun x => Real.exp ((p:ℝ)*H x)) ν) :
    (∫ x, Real.exp (H x) ∂ν)^p ≤ ∫ x, Real.exp ((p:ℝ)*H x) ∂ν := by
  simpa only [Function.comp_def, Real.exp_nat_mul] using
    (convexOn_pow p).map_integral_le (continuous_pow p).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos (H x)).le)) h1
      (by simpa only [Function.comp_def, Real.exp_nat_mul] using hp)

lemma exp_integral_le_partition {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ}
    (hH : Integrable H ν) (he : Integrable (fun x => Real.exp (H x)) ν) :
    Real.exp (∫ x, H x ∂ν) ≤ ∫ x, Real.exp (H x) ∂ν := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) hH he

 

lemma partition_inv_pow_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {H : X → ℝ} (p : ℕ)
    (hH : Integrable H ν)
    (h1 : Integrable (fun x => Real.exp (H x)) ν)
    (hp : Integrable (fun x => Real.exp (-(p:ℝ)*H x)) ν) :
    ((∫ x, Real.exp (H x) ∂ν)^p)⁻¹ ≤ ∫ x, Real.exp (-(p:ℝ)*H x) ∂ν := by
  have hj := exp_integral_le_partition hH h1
  have hz : 0 < ∫ x, Real.exp (H x) ∂ν := (Real.exp_pos _).trans_le hj
  calc
    _ ≤ (Real.exp (∫ x, H x ∂ν)^p)⁻¹ :=
      (inv_le_inv₀ (pow_pos hz _) (pow_pos (Real.exp_pos _) _)).mpr
        (pow_le_pow_left₀ (Real.exp_pos _).le hj _)
    _ = Real.exp (∫ x, -(p:ℝ)*H x ∂ν) := by
      rw [integral_const_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      ring
    _ ≤ _ := exp_integral_le_partition (hH.const_mul _) hp

 

lemma gaussian_field_exp_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (t : ℝ) :
    Integrable (fun z => Real.exp (t*H z)) (μ.prod ν) ∧
      (∫ ω, ∫ x, Real.exp (t*H (ω,x)) ∂ν ∂μ) ≤ Real.exp (t^2*K/2) := by
  have he : Measurable (fun z => Real.exp (t*H z)) := hm.const_mul t |>.exp
  have hsec : ∀ x, Integrable (fun ω => Real.exp (t*H (ω,x))) μ := by
    intro x
    have hx : Measurable (fun ω => H (ω,x)) := hm.comp (measurable_id.prodMk measurable_const)
    apply (integrable_map_measure (g := fun y : ℝ => Real.exp (t*y)) (μ := μ) (by fun_prop) hx.aemeasurable).mp
    rw [hg x]
    exact integrable_exp_mul_gaussianReal t
  have hb (x : X) : (∫ ω, Real.exp (t*H (ω,x)) ∂μ) ≤ Real.exp (t^2*K/2) := by
    have h := mgf_gaussianReal (X := fun ω => H (ω, x))
      (hg x) t
    simp only [mgf, zero_mul, zero_add] at h
    rw [h]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (hv x) (sq_nonneg t)]
  have hi : Integrable (fun z => Real.exp (t*H z)) (μ.prod ν) := by
    apply (integrable_prod_iff' he.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
    apply Integrable.of_bound he.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
      (Real.exp (t^2*K/2))
    refine Filter.Eventually.of_forall fun x => ?_
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (integral_nonneg (μ := μ) (f := fun ω : Ω => Real.exp (t*H (ω,x))) (fun ω => (Real.exp_pos _).le))] using hb x
  refine ⟨hi, ?_⟩
  rw [integral_integral_swap hi]
  calc
    _ ≤ ∫ _ : X, Real.exp (t^2*K/2) ∂ν :=
      integral_mono hi.integral_prod_right (integrable_const _) hb
    _ = _ := by simp

lemma abs_le_exp_add_exp_neg (x : ℝ) : |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [Real.add_one_le_exp x, Real.exp_pos (-x)]
  · rw [abs_of_nonpos hx]
    linarith [Real.add_one_le_exp (-x), Real.exp_pos x]

lemma gaussian_field_integrable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) : Integrable H (μ.prod ν) := by
  have hp := (gaussian_field_exp_integrable (ν := ν) hm hg hv (1:ℝ)).1
  have hn := (gaussian_field_exp_integrable (ν := ν) hm hg hv (-1:ℝ)).1
  apply (hp.add hn).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Pi.add_apply, Real.norm_eq_abs, one_mul, neg_one_mul] using abs_le_exp_add_exp_neg (H z)

 

lemma gaussian_partition_moments {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (p : ℕ) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    Integrable (fun ω => Z ω^p) μ ∧ Integrable (fun ω => (Z ω^p)⁻¹) μ ∧
      (∫ ω, Z ω^p ∂μ) ≤ Real.exp ((p:ℝ)^2*K/2) ∧
      (∫ ω, (Z ω^p)⁻¹ ∂μ) ≤ Real.exp ((p:ℝ)^2*K/2) := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  change Integrable (fun ω => Z ω^p) μ ∧ Integrable (fun ω => (Z ω^p)⁻¹) μ ∧ _
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hH := gaussian_field_integrable (ν := ν) hm hg hv
  have h1 := (gaussian_field_exp_integrable (ν := ν) hm hg hv (1:ℝ)).1
  simp only [one_mul] at h1
  obtain ⟨hip, hbp⟩ := gaussian_field_exp_integrable (ν := ν) hm hg hv (p:ℝ)
  obtain ⟨hin, hbn⟩ := gaussian_field_exp_integrable (ν := ν) hm hg hv (-(p:ℝ))
  have hp : ∀ᵐ ω ∂μ, Z ω^p ≤ ∫ x, Real.exp ((p:ℝ)*H (ω,x)) ∂ν := by
    filter_upwards [h1.prod_right_ae, hip.prod_right_ae] with ω hω hωp
    exact partition_pow_le p hω hωp
  have hn : ∀ᵐ ω ∂μ, (Z ω^p)⁻¹ ≤ ∫ x, Real.exp (-(p:ℝ)*H (ω,x)) ∂ν := by
    filter_upwards [hH.prod_right_ae, h1.prod_right_ae, hin.prod_right_ae] with ω hω hω1 hωn
    exact partition_inv_pow_le p hω hω1 hωn
  have hz (ω) : 0 ≤ Z ω := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hpint : Integrable (fun ω => Z ω^p) μ := by
    apply hip.integral_prod_left.mono' (hmZ.pow_const p).aestronglyMeasurable
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hz _) _)] using hp
  have hnint : Integrable (fun ω => (Z ω^p)⁻¹) μ := by
    apply hin.integral_prod_left.mono' ((hmZ.pow_const p).inv).aestronglyMeasurable
    simpa only [Pi.inv_apply, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (hz _) _))] using hn
  refine ⟨hpint, hnint, (integral_mono_ae hpint hip.integral_prod_left hp).trans hbp, ?_⟩
  simpa only [neg_sq] using (integral_mono_ae hnint hin.integral_prod_left hn).trans hbn

lemma exp_weighted_abs_fourth_bound (h y : ℝ) :
    (Real.exp h*|y|)^4 ≤ Real.exp (8*h)+Real.exp (8*y)+Real.exp (-8*y) := by
  have hy : |y| ≤ Real.exp |y| := by linarith [Real.add_one_le_exp |y|]
  have hp := pow_le_pow_left₀ (abs_nonneg y) hy 4
  have he : (Real.exp |y|)^4 = Real.exp (4*|y|) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [he] at hp
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (Real.exp h)^4 by positivity)
  have heh : (Real.exp h)^4 = Real.exp (4*h) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [heh] at hm
  have hs1 : (Real.exp (4*h))^2 = Real.exp (8*h) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hs2 : (Real.exp (4*|y|))^2 = Real.exp (8*|y|) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hay : Real.exp (8*|y|) ≤ Real.exp (8*y)+Real.exp (-8*y) := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]; linarith [Real.exp_pos (-8*y)]
    · rw [abs_of_nonpos hy]
      have he : 8*(-y) = -8*y := by ring
      rw [he]; linarith [Real.exp_pos (8*y)]
  rw [mul_pow, heh]
  have hs := sq_nonneg (Real.exp (4*h)-Real.exp (4*|y|))
  have hp0 := mul_nonneg (Real.exp_pos (4*h)).le (Real.exp_pos (4*|y|)).le
  nlinarith

 

lemma gaussian_insertion_numerator_fourth {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H Y : Ω × X → ℝ} (hmH : Measurable H) (hmY : Measurable Y)
    {v w : X → NNReal} {K L : ℝ}
    (hgH : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hgY : ∀ x, μ.map (fun ω => Y (ω,x)) = gaussianReal 0 (w x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (hw : ∀ x, (w x : ℝ) ≤ L) :
    let A := fun ω => ∫ x, Real.exp (H (ω,x))*|Y (ω,x)| ∂ν
    Integrable (fun z => Real.exp (H z)*|Y z|) (μ.prod ν) ∧
    Integrable (fun ω => A ω^4) μ ∧
    (∫ ω, A ω^4 ∂μ) ≤ Real.exp (32*K)+2*Real.exp (32*L) := by
  let Q := fun z => Real.exp (8*H z)+Real.exp (8*Y z)+Real.exp (-8*Y z)
  let A := fun ω => ∫ x, Real.exp (H (ω,x))*|Y (ω,x)| ∂ν
  obtain ⟨hiH,hbH⟩ := gaussian_field_exp_integrable (ν := ν) hmH hgH hv 8
  obtain ⟨hiY,hbY⟩ := gaussian_field_exp_integrable (ν := ν) hmY hgY hw 8
  obtain ⟨hinY,hbnY⟩ := gaussian_field_exp_integrable (ν := ν) hmY hgY hw (-8)
  have hiQ : Integrable Q (μ.prod ν) := (hiH.add hiY).add hinY
  have hmA : Measurable A := (hmH.exp.mul hmY.abs).stronglyMeasurable.integral_prod_right'.measurable
  have hnp (z : Ω × X) : 0 ≤ Real.exp (H z)*|Y z| := by positivity
  have hb4 (z : Ω × X) : (Real.exp (H z)*|Y z|)^4 ≤ Q z :=
    exp_weighted_abs_fourth_bound (H z) (Y z)
  have hi4 : Integrable (fun z => (Real.exp (H z)*|Y z|)^4) (μ.prod ν) := by
    apply hiQ.mono' ((hmH.exp.mul hmY.abs).pow_const 4).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_of_nonneg (pow_nonneg (hnp z) _)] using hb4 z
  have hi1 : Integrable (fun z => Real.exp (H z)*|Y z|) (μ.prod ν) := by
    apply ((integrable_const (1:ℝ)).add hiQ).mono' (hmH.exp.mul hmY.abs).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [Pi.add_apply, Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (hnp z)]
    have ha := hnp z
    have hp : Real.exp (H z)*|Y z| ≤ 1+(Real.exp (H z)*|Y z|)^4 := by
      nlinarith [sq_nonneg (Real.exp (H z)*|Y z|),
        sq_nonneg ((Real.exp (H z)*|Y z|)^2-1),
        sq_nonneg (Real.exp (H z)*|Y z|-1)]
    linarith [hb4 z]
  have hAle : ∀ᵐ ω ∂μ, A ω^4 ≤ ∫ x, Q (ω,x) ∂ν := by
    filter_upwards [hi1.prod_right_ae, hi4.prod_right_ae, hiQ.prod_right_ae] with ω h1 h4 hQ
    have hJ := (convexOn_pow 4).map_integral_le (continuous_pow 4).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall (fun x => hnp (ω,x))) h1 h4
    exact hJ.trans (integral_mono h4 hQ (fun x => hb4 (ω,x)))
  have hiA : Integrable (fun ω => A ω^4) μ := by
    apply hiQ.integral_prod_left.mono' (hmA.pow_const 4).aestronglyMeasurable
    filter_upwards [hAle] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ A ω^4)]
    exact hω
  refine ⟨hi1, hiA, (integral_mono_ae hiA hiQ.integral_prod_left hAle).trans ?_⟩
  have he : (∫ ω, ∫ x, Q (ω,x) ∂ν ∂μ) =
      (∫ ω, ∫ x, Real.exp (8*H (ω,x)) ∂ν ∂μ) +
      (∫ ω, ∫ x, Real.exp (8*Y (ω,x)) ∂ν ∂μ) +
      (∫ ω, ∫ x, Real.exp (-8*Y (ω,x)) ∂ν ∂μ) := by
    rw [← integral_prod _ hiQ, ← integral_prod _ hiH,
      ← integral_prod _ hiY, ← integral_prod _ hinY]
    exact integral_add (hiH.add hiY) hinY |>.trans
      (congrArg (fun r => r+∫ z, Real.exp (-8*Y z) ∂μ.prod ν) (integral_add hiH hiY))
  rw [he]
  have hK : (8:ℝ)^2*K/2 = 32*K := by ring
  have hL : (8:ℝ)^2*L/2 = 32*L := by ring
  have hnL : (-8:ℝ)^2*L/2 = 32*L := by ring
  rw [hK] at hbH
  rw [hL] at hbY
  rw [hnL] at hbnY
  linarith

lemma square_product_le_fourths (x y : ℝ) : (x*y)^2 ≤ (x^4+y^4)/2 := by
  nlinarith [sq_nonneg (x^2-y^2)]

 

theorem gaussian_gibbs_abs_insertion_second {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H Y : Ω × X → ℝ} (hmH : Measurable H) (hmY : Measurable Y)
    {v w : X → NNReal} {K L : ℝ}
    (hgH : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hgY : ∀ x, μ.map (fun ω => Y (ω,x)) = gaussianReal 0 (w x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (hw : ∀ x, (w x : ℝ) ≤ L) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    let A := fun ω => ∫ x, Real.exp (H (ω,x))*|Y (ω,x)| ∂ν
    Integrable (fun ω => (A ω/Z ω)^2) μ ∧
    (∫ ω, (A ω/Z ω)^2 ∂μ) ≤
      (Real.exp (32*K)+2*Real.exp (32*L)+Real.exp (8*K))/2 := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  let A := fun ω => ∫ x, Real.exp (H (ω,x))*|Y (ω,x)| ∂ν
  obtain ⟨_,hiA,hbA⟩ := gaussian_insertion_numerator_fourth (ν := ν) hmH hmY hgH hgY hv hw
  obtain ⟨_,hiZ,_,hbZ⟩ := gaussian_partition_moments (ν := ν) hmH hgH hv 4
  change Integrable (fun ω => A ω^4) μ at hiA
  change Integrable (fun ω => (Z ω^4)⁻¹) μ at hiZ
  have hmZ : Measurable Z := hmH.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hmA : Measurable A := (hmH.exp.mul hmY.abs).stronglyMeasurable.integral_prod_right'.measurable
  have hb (ω : Ω) : (A ω/Z ω)^2 ≤ (A ω^4+(Z ω^4)⁻¹)/2 := by
    simpa only [div_eq_mul_inv, inv_pow] using square_product_le_fourths (A ω) (Z ω)⁻¹
  have hi : Integrable (fun ω => (A ω/Z ω)^2) μ := by
    apply ((hiA.add hiZ).div_const 2).mono' ((hmA.div hmZ).pow_const 2).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun ω => ?_
    simpa only [Pi.add_apply, Pi.div_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A ω/Z ω))] using hb ω
  refine ⟨hi, (integral_mono hi ((hiA.add hiZ).div_const 2) hb).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_div, integral_add hiA hiZ]
  have he : (4:ℝ)^2*K/2 = 8*K := by ring
  simp only [Nat.cast_ofNat] at hbZ
  rw [he] at hbZ
  exact div_le_div_of_nonneg_right (add_le_add hbA hbZ) (by norm_num)

lemma log_square_le_partition_moments {x : ℝ} (hx : 0 < x) :
    (Real.log x)^2 ≤ 2*(x^2+(x^2)⁻¹) := by
  have hp := Real.log_le_sub_one_of_pos hx
  have hn := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hn
  have hB : |Real.log x| ≤ x+x⁻¹ := by
    apply abs_le.mpr
    constructor <;> linarith [inv_pos.mpr hx]
  have hs := pow_le_pow_left₀ (abs_nonneg (Real.log x)) hB 2
  rw [sq_abs] at hs
  rw [← inv_pow]
  nlinarith [sq_nonneg (x-x⁻¹)]

 

lemma gaussian_log_partition_second {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    Integrable (fun ω => (Real.log (Z ω))^2) μ ∧
    (∫ ω, (Real.log (Z ω))^2 ∂μ) ≤ 4*Real.exp (2*K) := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  obtain ⟨hip,hin,hbp,hbn⟩ := gaussian_partition_moments (ν := ν) hm hg hv 2
  change Integrable (fun ω => Z ω^2) μ at hip
  change Integrable (fun ω => (Z ω^2)⁻¹) μ at hin
  have hH := gaussian_field_integrable (ν := ν) hm hg hv
  have he := (gaussian_field_exp_integrable (ν := ν) hm hg hv 1).1
  simp only [one_mul] at he
  have hb : ∀ᵐ ω ∂μ, (Real.log (Z ω))^2 ≤ 2*(Z ω^2+(Z ω^2)⁻¹) := by
    filter_upwards [hH.prod_right_ae, he.prod_right_ae] with ω hω hωe
    apply log_square_le_partition_moments
    exact (Real.exp_pos _).trans_le (exp_integral_le_partition hω hωe)
  have hi : Integrable (fun ω => (Real.log (Z ω))^2) μ := by
    apply ((hip.add hin).const_mul 2).mono' (hmZ.log.pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (Z ω)))] using hω
  refine ⟨hi, (integral_mono_ae hi ((hip.add hin).const_mul 2) hb).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add hip hin]
  have hx : (2:ℝ)^2*K/2 = 2*K := by ring
  simp only [Nat.cast_ofNat] at hbp hbn
  rw [hx] at hbp hbn
  linarith

 

lemma uniformIntegrable_of_second_moment_bound {I Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : I → Ω → ℝ} {C : ℝ}
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (fun ω => (f i ω)^2) μ)
    (hb : ∀ i, (∫ ω, (f i ω)^2 ∂μ) ≤ C) : UniformIntegrable f 1 μ := by
  apply uniformIntegrable_of le_rfl ENNReal.one_ne_top (fun i => (hm i).aestronglyMeasurable)
  intro ε hε
  have hεreal := hε
  let A := (|C|+1)/ε
  have hA : 0 < A := div_pos (by positivity) hεreal
  refine ⟨⟨A,hA.le⟩, fun i => ?_⟩
  let S := {ω : Ω | (⟨A,hA.le⟩ : NNReal) ≤ ‖f i ω‖₊}
  have hs : MeasurableSet S := by
    change MeasurableSet {ω : Ω | A ≤ ‖f i ω‖}
    exact measurableSet_le measurable_const (hm i).norm
  have hfi : Integrable (f i) μ :=
    ((memLp_two_iff_integrable_sq (hm i).aestronglyMeasurable).mpr (hi i)).integrable (by norm_num)
  have hint := hfi.indicator hs
  have hle : ∀ ω, ‖S.indicator (f i) ω‖ ≤ (f i ω)^2/A := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs]
      have ha : A ≤ |f i ω| := by exact_mod_cast hω
      apply (le_div_iff₀ hA).mpr
      nlinarith [sq_abs (f i ω), mul_le_mul_of_nonneg_left ha (abs_nonneg (f i ω))]
    · rw [Set.indicator_of_notMem hω, norm_zero]
      positivity
  change eLpNorm (S.indicator (f i)) 1 μ ≤ ENNReal.ofReal ε
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hint]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ ω, (f i ω)^2/A ∂μ := integral_mono hint.norm ((hi i).div_const A) hle
    _ = (∫ ω, (f i ω)^2 ∂μ)/A := integral_div _ _
    _ ≤ C/A := div_le_div_of_nonneg_right (hb i) hA.le
    _ ≤ ε := by
      apply (div_le_iff₀ hA).mpr
      dsimp [A]
      rw [mul_div_cancel₀ _ hεreal.ne']
      linarith [le_abs_self C]

 

lemma integral_tendsto_of_second_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (fun ω => (f i ω)^2) μ)
    (hb : ∀ i, (∫ ω, (f i ω)^2 ∂μ) ≤ C)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun i => f i ω) atTop (𝓝 (g ω))) :
    Integrable g μ ∧ Tendsto (fun i => ∫ ω, f i ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by
  have hu := uniformIntegrable_of_second_moment_bound hm hi hb
  have hg := hu.integrable_of_ae_tendsto ht
  refine ⟨hg, ?_⟩
  apply tendsto_integral_of_L1 g hg.aestronglyMeasurable
    (Eventually.of_forall (fun i => (hu.memLp i).integrable le_rfl))
  simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using
    tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1:ENNReal) ≤ 1)
      ENNReal.one_ne_top (fun i => (hm i).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hg) hu.unifIntegrable ht



lemma normalizedRestriction_probability {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] {A : Set X} (hA : ν A ≠ 0) :
    IsProbabilityMeasure (normalizedRestriction ν A) := by
  constructor
  simp only [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hA (measure_ne_top _ _)

lemma integral_normalizedRestriction {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] (A : Set X) (f : X → ℝ) :
    (∫ x, f x ∂normalizedRestriction ν A) = (∫ x in A, f x ∂ν)/(ν A).toReal := by
  rw [normalizedRestriction, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma integral_restriction_tendsto {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {A : ℕ → Set X} (hm : ∀ n, MeasurableSet (A n))
    (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) {f : X → ℝ} (hi : Integrable f ν) :
    Tendsto (fun n => ∫ x in A n, f x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
  simp_rw [← integral_indicator (hm _)]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · exact fun n => hi.aestronglyMeasurable.indicator (hm n)
  · exact hi.norm
  · exact fun n => Eventually.of_forall (fun x => norm_indicator_le_norm_self _ _)
  · refine Eventually.of_forall fun x => ?_
    exact tendsto_const_nhds.congr' ((hA x).mono (fun n hn => (indicator_of_mem hn f).symm))

lemma normalized_restriction_integral_tendsto {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν]
    {A : ℕ → Set X} (hm : ∀ n, MeasurableSet (A n))
    (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) {f : X → ℝ} (hi : Integrable f ν) :
    Tendsto (fun n => ∫ x, f x ∂normalizedRestriction ν (A n))
      atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hmass : Tendsto (fun n => (ν (A n)).toReal) atTop (𝓝 (1:ℝ)) := by
    simpa only [integral_const, Measure.restrict_apply_univ, measureReal_def,
      smul_eq_mul, mul_one, measure_univ, ENNReal.toReal_one] using
      integral_restriction_tendsto hm hA (integrable_const (1:ℝ) (μ := ν))
  have ht := (integral_restriction_tendsto hm hA hi).div hmass (by norm_num : (1:ℝ) ≠ 0)
  convert ht using 1
  · funext n
    exact integral_normalizedRestriction (A n) f
  · rw [div_one]



lemma gaussian_bounded_insertion_second {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H Y D : Ω × X → ℝ} (hmH : Measurable H) (hmY : Measurable Y)
    (hmD : Measurable D) {c : ℝ} (_hc : 0 ≤ c) (hD : ∀ z, |D z| ≤ c)
    {v w : X → NNReal} {K L : ℝ}
    (hgH : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hgY : ∀ x, μ.map (fun ω => Y (ω,x)) = gaussianReal 0 (w x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (hw : ∀ x, (w x : ℝ) ≤ L) :
    let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
    let B := fun ω => ∫ x, Real.exp (H (ω,x))*Y (ω,x)*D (ω,x) ∂ν
    Integrable (fun z => Real.exp (H z)*Y z*D z) (μ.prod ν) ∧
    Integrable (fun ω => (B ω/Z ω)^2) μ ∧
    (∫ ω, (B ω/Z ω)^2 ∂μ) ≤
      c^2*((Real.exp (32*K)+2*Real.exp (32*L)+Real.exp (8*K))/2) := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  let B := fun ω => ∫ x, Real.exp (H (ω,x))*Y (ω,x)*D (ω,x) ∂ν
  let A := fun ω => ∫ x, Real.exp (H (ω,x))*|Y (ω,x)| ∂ν
  have hiA := (gaussian_insertion_numerator_fourth (ν := ν) hmH hmY hgH hgY hv hw).1
  have hiB : Integrable (fun z => Real.exp (H z)*Y z*D z) (μ.prod ν) := by
    apply (hiA.const_mul c).mono' (hmH.exp.mul hmY |>.mul hmD).aestronglyMeasurable
    refine Eventually.of_forall fun z => ?_
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    nlinarith [mul_le_mul_of_nonneg_left (hD z) (mul_nonneg (Real.exp_pos (H z)).le (abs_nonneg (Y z)))]
  have hBA : ∀ᵐ ω ∂μ, (B ω/Z ω)^2 ≤ c^2*(A ω/Z ω)^2 := by
    filter_upwards [hiA.prod_right_ae,hiB.prod_right_ae] with ω hAω hBω
    have ha : |B ω| ≤ c*A ω := by
      calc
        _ ≤ ∫ x, |Real.exp (H (ω,x))*Y (ω,x)*D (ω,x)| ∂ν := abs_integral_le_integral_abs
        _ ≤ ∫ x, c*(Real.exp (H (ω,x))*|Y (ω,x)|) ∂ν := by
          apply integral_mono hBω.abs (hAω.const_mul c)
          intro x
          dsimp only
          rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
          nlinarith [mul_le_mul_of_nonneg_left (hD (ω,x))
            (mul_nonneg (Real.exp_pos (H (ω,x))).le (abs_nonneg (Y (ω,x))))]
        _ = c*A ω := integral_const_mul _ _
    have hz : 0 ≤ Z ω := integral_nonneg (fun _ => (Real.exp_pos _).le)
    have hb : |B ω/Z ω| ≤ c*A ω/Z ω := by
      rw [abs_div,abs_of_nonneg hz]
      exact div_le_div_of_nonneg_right ha hz
    have hs := pow_le_pow_left₀ (abs_nonneg (B ω/Z ω)) hb 2
    rw [sq_abs] at hs
    simpa only [mul_div_assoc,mul_pow] using hs
  have hi := gaussian_gibbs_abs_insertion_second (ν := ν) hmH hmY hgH hgY hv hw
  have hmB : Measurable B := (hmH.exp.mul hmY |>.mul hmD).stronglyMeasurable.integral_prod_right'.measurable
  have hmZ : Measurable Z := hmH.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hiSq : Integrable (fun ω => (B ω/Z ω)^2) μ := by
    apply (hi.1.const_mul (c^2)).mono' ((hmB.div hmZ).pow_const 2).aestronglyMeasurable
    filter_upwards [hBA] with ω hω
    simpa only [Pi.div_apply,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (B ω/Z ω))] using hω
  refine ⟨hiB,hiSq,?_⟩
  calc
    _ ≤ ∫ ω, c^2*(A ω/Z ω)^2 ∂μ := integral_mono_ae hiSq (hi.1.const_mul (c^2)) hBA
    _ = c^2*(∫ ω, (A ω/Z ω)^2 ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hi.2 (sq_nonneg c)

 

theorem gaussian_insertion_restriction_expectation_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H Y D : Ω × X → ℝ} (hmH : Measurable H) (hmY : Measurable Y)
    (hmD : Measurable D) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ z, |D z| ≤ c)
    {v w : X → NNReal} {K L : ℝ}
    (hgH : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hgY : ∀ x, μ.map (fun ω => Y (ω,x)) = gaussianReal 0 (w x))
    (hv : ∀ x, (v x : ℝ) ≤ K) (hw : ∀ x, (w x : ℝ) ≤ L)
    {A : ℕ → Set X} (hAm : ∀ n, MeasurableSet (A n))
    (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ ω, (∫ x, Real.exp (H (ω,x))*Y (ω,x)*D (ω,x)
      ∂normalizedRestriction ν (A n))/(∫ x, Real.exp (H (ω,x))
      ∂normalizedRestriction ν (A n)) ∂μ) atTop
      (𝓝 (∫ ω, (∫ x, Real.exp (H (ω,x))*Y (ω,x)*D (ω,x) ∂ν)/
        (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ)) := by
  let νn := fun n => normalizedRestriction ν (A n)
  have : ∀ n, IsProbabilityMeasure (νn n) := fun n => normalizedRestriction_probability (hpos n)
  have hmB (n) : Measurable (fun ω => (∫ x, Real.exp (H (ω,x))*Y (ω,x)*D (ω,x) ∂νn n)/
      (∫ x, Real.exp (H (ω,x)) ∂νn n)) :=
    (hmH.exp.mul hmY |>.mul hmD).stronglyMeasurable.integral_prod_right'.measurable.div
      hmH.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hi (n) := gaussian_bounded_insertion_second (ν := νn n) hmH hmY hmD hc hD hgH hgY hv hw
  apply (integral_tendsto_of_second_moment_bound hmB (fun n => (hi n).2.1)
    (fun n => (hi n).2.2) ?_).2
  have he := (gaussian_field_exp_integrable (ν := ν) hmH hgH hv 1).1
  simp only [one_mul] at he
  have hH := gaussian_field_integrable (ν := ν) hmH hgH hv
  have hB := (gaussian_bounded_insertion_second (ν := ν) hmH hmY hmD hc hD hgH hgY hv hw).1
  filter_upwards [he.prod_right_ae,hH.prod_right_ae,hB.prod_right_ae] with ω heω hHω hBω
  have hz : 0 < ∫ x, Real.exp (H (ω,x)) ∂ν :=
    (Real.exp_pos _).trans_le (exp_integral_le_partition hHω heω)
  exact (normalized_restriction_integral_tendsto hAm hA hBω).div
    (normalized_restriction_integral_tendsto hAm hA heω) hz.ne'

lemma abs_bounded_gibbs_test_le {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {H D : X → ℝ} (he : Integrable (fun x => Real.exp (H x)) ν)
    (hmD : Measurable D) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ x, |D x| ≤ c) :
    |(∫ x, Real.exp (H x)*D x ∂ν)/(∫ x, Real.exp (H x) ∂ν)| ≤ c := by
  have hi := he.mul_bdd hmD.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hD x))
  have hb : |∫ x, Real.exp (H x)*D x ∂ν| ≤ c*(∫ x, Real.exp (H x) ∂ν) := by
    calc
      _ ≤ ∫ x, |Real.exp (H x)*D x| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x, c*Real.exp (H x) ∂ν := by
        apply integral_mono hi.abs (he.const_mul c)
        intro x
        dsimp only
        rw [abs_mul,abs_of_pos (Real.exp_pos _)]
        nlinarith [mul_le_mul_of_nonneg_left (hD x) (Real.exp_pos (H x)).le]
      _ = _ := integral_const_mul _ _
  have hz : 0 ≤ ∫ x, Real.exp (H x) ∂ν := integral_nonneg (fun _ => (Real.exp_pos _).le)
  rcases hz.eq_or_lt with hz | hz
  · simp only [← hz,div_zero,abs_zero]
    exact hc
  · rw [abs_div,abs_of_pos hz]
    exact (div_le_iff₀ hz).mpr hb

 

theorem gaussian_bounded_restriction_expectation_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H D : Ω × X → ℝ} (hmH : Measurable H) (hmD : Measurable D)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ z, |D z| ≤ c)
    {v : X → NNReal} {K : ℝ}
    (hgH : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K)
    {A : ℕ → Set X} (hAm : ∀ n, MeasurableSet (A n))
    (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ ω, (∫ x, Real.exp (H (ω,x))*D (ω,x)
      ∂normalizedRestriction ν (A n))/(∫ x, Real.exp (H (ω,x))
      ∂normalizedRestriction ν (A n)) ∂μ) atTop
      (𝓝 (∫ ω, (∫ x, Real.exp (H (ω,x))*D (ω,x) ∂ν)/
        (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ)) := by
  let νn := fun n => normalizedRestriction ν (A n)
  have : ∀ n, IsProbabilityMeasure (νn n) := fun n => normalizedRestriction_probability (hpos n)
  have hmB (n) : Measurable (fun ω => (∫ x, Real.exp (H (ω,x))*D (ω,x) ∂νn n)/
      (∫ x, Real.exp (H (ω,x)) ∂νn n)) :=
    (hmH.exp.mul hmD).stronglyMeasurable.integral_prod_right'.measurable.div
      hmH.exp.stronglyMeasurable.integral_prod_right'.measurable
  apply tendsto_integral_of_dominated_convergence (fun _ => c)
  · exact fun n => (hmB n).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    have he := (gaussian_field_exp_integrable (ν := νn n) hmH hgH hv 1).1
    simp only [one_mul] at he
    filter_upwards [he.prod_right_ae] with ω heω
    rw [Real.norm_eq_abs]
    exact abs_bounded_gibbs_test_le heω (hmD.comp (measurable_const.prodMk measurable_id))
      hc (fun x => hD (ω,x))
  · have he := (gaussian_field_exp_integrable (ν := ν) hmH hgH hv 1).1
    simp only [one_mul] at he
    have hH := gaussian_field_integrable (ν := ν) hmH hgH hv
    have hB : Integrable (fun z => Real.exp (H z)*D z) (μ.prod ν) :=
      he.mul_bdd hmD.aestronglyMeasurable
        (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hD z))
    filter_upwards [he.prod_right_ae,hH.prod_right_ae,hB.prod_right_ae] with ω heω hHω hBω
    have hz : 0 < ∫ x, Real.exp (H (ω,x)) ∂ν :=
      (Real.exp_pos _).trans_le (exp_integral_le_partition hHω heω)
    exact (normalized_restriction_integral_tendsto hAm hA hBω).div
      (normalized_restriction_integral_tendsto hAm hA heω) hz.ne'

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_NormalizedRestrictionPi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Restriction Pi. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma normalizedRestriction_pi {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
    (A : ι → Set X) (hA : ∀ i, ν (A i) ≠ 0) :
    Measure.pi (fun i => normalizedRestriction ν (A i)) =
      normalizedRestriction (Measure.pi (fun _ : ι => ν)) (Set.univ.pi A) := by
  classical
  have : ∀ i, IsProbabilityMeasure (normalizedRestriction ν (A i)) :=
    fun i => normalizedRestriction_probability (hA i)
  apply Measure.pi_eq
  intro S hS
  simp only [normalizedRestriction,Measure.smul_apply,smul_eq_mul]
  rw [Measure.restrict_apply (MeasurableSet.univ_pi hS),← Set.pi_inter_distrib]
  simp_rw [Measure.pi_pi,Measure.restrict_apply (hS _)]
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (measure_ne_top _ _)),
    ← Finset.prod_mul_distrib]

lemma replica_restriction_mass_ne_zero {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
    {A : Set X} (hA : ν A ≠ 0) :
    (Measure.pi (fun _ : ι => ν)) (Set.univ.pi (fun _ => A)) ≠ 0 := by
  rw [Measure.pi_pi]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => hA)

lemma replica_restriction_eventually {ι X : Type*} [Finite ι]
    {A : ℕ → Set X} (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (σ : ι → X) :
    ∀ᶠ n in atTop, σ ∈ Set.univ.pi (fun _ : ι => A n) := by
  filter_upwards [Filter.eventually_all.mpr (fun i => hA (σ i))] with n hn
  exact Set.mem_univ_pi.mpr hn

lemma subtypeReference_preserving {X : Type*} [MeasurableSpace X]
    (ν : Measure X) {A : Set X} (hA : MeasurableSet A) :
    MeasurePreserving Subtype.val (subtypeReference ν A) (normalizedRestriction ν A) := by
  refine ⟨measurable_subtype_coe,?_⟩
  rw [subtypeReference,Measure.map_smul,
    map_comap_subtype_coe hA]
  rfl

lemma subtypeReference_probability {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {A : Set X} (hA : MeasurableSet A) (hp : ν A ≠ 0) :
    IsProbabilityMeasure (subtypeReference ν A) := by
  have : IsProbabilityMeasure (normalizedRestriction ν A) := normalizedRestriction_probability hp
  have : IsProbabilityMeasure ((subtypeReference ν A).map Subtype.val) :=
    (subtypeReference_preserving ν hA).map_eq.symm ▸ inferInstance
  exact Measure.isProbabilityMeasure_of_map (Subtype.val : A -> X)

lemma referenceReplicaMean_subtype {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] {A : Set X} (hA : MeasurableSet A) (hp : ν A ≠ 0)
    {H : X → ℝ} (hmH : Measurable H) {r : ℕ} {D : (Fin r → X) → ℝ} (hmD : Measurable D) :
    referenceReplicaMean (subtypeReference ν A) (fun x => H x)
      (fun σ => D (fun i => (σ i : X))) = referenceReplicaMean (normalizedRestriction ν A) H D := by
  have : IsProbabilityMeasure (subtypeReference ν A) := subtypeReference_probability ν hA hp
  have : IsProbabilityMeasure (normalizedRestriction ν A) := normalizedRestriction_probability hp
  exact referenceReplicaMean_map (subtypeReference_preserving ν hA) hmH hmD

lemma cylinder_replica_law {X : Type*} (a : X → ℕ →₀ ℝ) {r : ℕ} (σ : Fin r → X) :
    gaussianCoordinates.map (fun g => ∑ i, cylinderField (a (σ i)) g) =
      gaussianReal 0 (((∑ i, a (σ i)).sum (fun _ c => c^2)).toNNReal) := by
  have he : (fun g => ∑ i, cylinderField (a (σ i)) g) = cylinderField (∑ i, a (σ i)) := by
    funext g
    exact (cylinderField_finset_sum Finset.univ _ g).symm
  rw [he,cylinderField_law]

lemma cylinder_replica_variance_le {X : Type*} (a : X → ℕ →₀ ℝ) {K : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) {r : ℕ} (σ : Fin r → X) :
    ((((∑ i, a (σ i)).sum (fun _ c => c^2)).toNNReal : ℝ)) ≤ (r:ℝ)^2*K := by
  have hnonneg : 0 ≤ (∑ i, a (σ i)).sum (fun _ c => c^2) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Real.coe_toNNReal _ hnonneg]
  simpa only [Fintype.card_fin] using cylinder_variance_sum_le (fun i => a (σ i)) (fun i => ha (σ i))

theorem cylinder_replica_restriction_tendsto {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {ν : Measure X} [IsProbabilityMeasure ν]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    {r : ℕ} (D : (Fin r → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c)
    {A : ℕ → Set X} (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ g, referenceReplicaMean (normalizedRestriction ν (A n))
      (fun x => cylinderField (a x) g) D ∂gaussianCoordinates) atTop
      (𝓝 (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g) D ∂gaussianCoordinates)) := by
  have : ∀ n, IsProbabilityMeasure (normalizedRestriction ν (A n)) :=
    fun n => normalizedRestriction_probability (hpos n)
  have hmH : Measurable (fun z : (ℕ → ℝ) × (Fin r → X) =>
      ∑ i, cylinderField (a (z.2 i)) z.1) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_cylinderFields a).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have ht := gaussian_bounded_restriction_expectation_tendsto
    (ν := Measure.pi (fun _ : Fin r => ν)) hmH (measurable_of_countable D |>.comp measurable_snd)
    hc (fun z => hD z.2) (cylinder_replica_law a) (cylinder_replica_variance_le a ha)
    (A := fun n => Set.univ.pi (fun _ : Fin r => A n))
    (fun _ => MeasurableSet.univ_pi (fun _ => Set.to_countable _ |>.measurableSet))
    (replica_restriction_eventually hA) (fun n => replica_restriction_mass_ne_zero (hpos n))
  simpa only [Function.comp_apply,referenceReplicaMean_eq_ratio,← normalizedRestriction_pi (fun _ : Fin r => A _)
    (fun _ => hpos _)] using ht

theorem cylinder_replica_insertion_restriction_tendsto {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Measure X} [IsProbabilityMeasure ν] (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c)
    {A : ℕ → Set X} (hA : ∀ x, ∀ᶠ n in atTop, x ∈ A n) (hpos : ∀ n, ν (A n) ≠ 0) :
    Tendsto (fun n => ∫ g, referenceReplicaMean (normalizedRestriction ν (A n))
      (fun x => cylinderField (a x) g) (fun σ => cylinderField (b (σ 0)) g*D σ)
      ∂gaussianCoordinates) atTop
      (𝓝 (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
        (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates)) := by
  have : ∀ n, IsProbabilityMeasure (normalizedRestriction ν (A n)) :=
    fun n => normalizedRestriction_probability (hpos n)
  have hmH : Measurable (fun z : (ℕ → ℝ) × (Fin (r+1) → X) =>
      ∑ i, cylinderField (a (z.2 i)) z.1) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_cylinderFields a).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hmY : Measurable (fun z : (ℕ → ℝ) × (Fin (r+1) → X) => cylinderField (b (z.2 0)) z.1) :=
    (measurable_cylinderFields b).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have hv (σ : Fin (r+1) → X) : (((b (σ 0)).sum (fun _ c => c^2)).toNNReal : ℝ) ≤ L := by
    have hnonneg : 0 ≤ (b (σ 0)).sum (fun _ c => c^2) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [Real.coe_toNNReal _ hnonneg]
    exact hb (σ 0)
  have ht := gaussian_insertion_restriction_expectation_tendsto
    (ν := Measure.pi (fun _ : Fin (r+1) => ν)) hmH hmY
    (measurable_of_countable D |>.comp measurable_snd)
    hc (fun z => hD z.2) (cylinder_replica_law a) (fun σ => cylinderField_law (b (σ 0)))
    (cylinder_replica_variance_le a ha) hv
    (A := fun n => Set.univ.pi (fun _ : Fin (r+1) => A n))
    (fun _ => MeasurableSet.univ_pi (fun _ => Set.to_countable _ |>.measurableSet))
    (replica_restriction_eventually hA) (fun n => replica_restriction_mass_ne_zero (hpos n))
  simpa only [Function.comp_apply,mul_assoc,referenceReplicaMean_eq_ratio,
    ← normalizedRestriction_pi (fun _ : Fin (r+1) => A _) (fun _ => hpos _)] using ht

lemma countable_reference_exhaustion {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν] :
    ∃ A : ℕ → Set X, (∀ n, (A n).Finite) ∧ (∀ n, ν (A n) ≠ 0) ∧
      (∀ x, ∀ᶠ n in atTop, x ∈ A n) := by
  classical
  let := Encodable.ofCountable X
  have hx : ∃ x : X, ν {x} ≠ 0 := by
    by_contra! hn
    have hz : ν = 0 := Measure.ext_of_singleton (fun x => by simpa using hn x)
    have hu := measure_univ (μ := ν)
    simp only [hz, Measure.coe_zero, Pi.zero_apply] at hu
    exact zero_ne_one hu
  obtain ⟨x₀,hx₀⟩ := hx
  let A : ℕ → Set X := fun n => {x | Encodable.encode x ≤ n+Encodable.encode x₀}
  refine ⟨A,fun n => ?_,fun n => ?_,fun x => ?_⟩
  · exact (Set.finite_Iic _).preimage Encodable.encode_injective.injOn
  · intro hz
    apply hx₀
    exact measure_mono_null (fun x hx => by
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact Nat.le_add_left _ _) hz
  · filter_upwards [eventually_ge_atTop (Encodable.encode x)] with n hn
    exact hn.trans (Nat.le_add_right _ _)

lemma finite_restriction_cylinder_insertion {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {ν : Measure X} [IsProbabilityMeasure ν]
    {A : Set X} (hA : A.Finite) (hp : ν A ≠ 0)
    (a b : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin (r+1) → X) → ℝ) :
    (∫ g, referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates) =
    (∫ g, referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates) := by
  classical
  let := hA.fintype
  have hmA : MeasurableSet A := hA.measurableSet
  have : IsProbabilityMeasure (subtypeReference ν A) := subtypeReference_probability ν hmA hp
  have he {q : ℕ} (g : ℕ → ℝ) (F : (Fin q → X) → ℝ) :
      referenceReplicaMean (subtypeReference ν A) (fun x => cylinderField (a x) g)
        (fun σ => F (fun i => (σ i : X))) =
      referenceReplicaMean (normalizedRestriction ν A) (fun x => cylinderField (a x) g) F :=
    referenceReplicaMean_subtype hmA hp (H := fun x => cylinderField (a x) g)
      (D := F) (measurable_of_countable _) (measurable_of_countable _)
  have hi := finite_cylinder_reference_insertion (subtypeReference ν A)
    (fun x => a x) (fun x => b x) (fun σ => D (fun i => (σ i : X)))
  convert hi using 1
  · congr 1
    funext g
    exact (he g (fun σ => cylinderField (b (σ 0)) g*D σ)).symm
  · congr 1
    · congr 1
      funext g
      exact (he g (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i))))).symm
    · congr 1
      congr 1
      funext g
      exact (he g (fun τ : Fin (r+1+1) → X =>
        D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))).symm

theorem countable_cylinder_reference_insertion {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates) =
    (∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates) -
    (r+1 : ℕ)*(∫ g, referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates) := by
  classical
  obtain ⟨A,hfin,hpos,hA⟩ := countable_reference_exhaustion ν
  let B : ℝ := (|K|+|L|)/2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcross (x y : X) : |cylinderCross (b x) (a y)| ≤ B := by
    calc
      |cylinderCross (b x) (a y)| ≤ ((b x).sum (fun _ t => t^2)+(a y).sum (fun _ t => t^2))/2 :=
        abs_cylinderCross_le _ _
      _ ≤ B := by dsimp [B]; linarith [hb x,ha y,le_abs_self K,le_abs_self L]
  have hsum (σ : Fin (r+1) → X) : |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ (r+1 : ℕ)*B := by
    calc
      |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ ∑ i, |cylinderCross (b (σ 0)) (a (σ i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), B := Finset.sum_le_sum (fun i _ => hcross _ _)
      _ = (r+1 : ℕ)*B := by simp
  have hfirst (σ : Fin (r+1) → X) :
      |D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))| ≤ c*((r+1 : ℕ)*B) := by
    rw [abs_mul]
    exact mul_le_mul (hD σ) (hsum σ) (abs_nonneg _) hc
  have hfresh (τ : Fin (r+1+1) → X) :
      |D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))| ≤ c*B := by
    rw [abs_mul]
    exact mul_le_mul (hD _) (hcross _ _) (abs_nonneg _) hc
  have hleft := cylinder_replica_insertion_restriction_tendsto a b ha hb D hc hD hA hpos
  have hright₁ := cylinder_replica_restriction_tendsto a ha
    (fun σ : Fin (r+1) → X => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i))))
    (c := c*((r+1 : ℕ)*B)) (by positivity) hfirst hA hpos
  have hright₂ := cylinder_replica_restriction_tendsto a ha
    (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
    (c := c*B) (mul_nonneg hc hB) hfresh hA hpos
  apply tendsto_nhds_unique hleft
  exact (hright₁.sub (hright₂.const_mul ((r+1 : ℕ) : ℝ))).congr
    (fun n => (finite_restriction_cylinder_insertion (hfin n) (hpos n) a b D).symm)

lemma measurable_countable_measure_pi {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] (r : ℕ) :
    Measurable (fun ω => Measure.pi (fun _ : Fin r => ν ω)) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he (ω : Ω) : Measure.pi (fun _ : Fin r => ν ω) s =
      ∑' σ : Fin r → X, (∏ i : Fin r, ν ω {σ i}) * Measure.dirac σ s := by
    rw [← Measure.sum_smul_dirac (Measure.pi (fun _ : Fin r => ν ω)),Measure.sum_apply _ hs]
    simp only [Measure.smul_apply,smul_eq_mul,Measure.pi_singleton]
  simp_rw [he]
  apply Measurable.tsum
  intro σ
  exact (Finset.measurable_prod _ (fun i _ => (Measure.measurable_coe (measurableSet_singleton _)).comp hν)).mul_const _

lemma measurable_random_referenceReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H) {r : ℕ}
    {D : Ω × (Fin r → X) → ℝ} (hD : Measurable D) :
    Measurable (fun ω => referenceReplicaMean (ν ω) (fun x => H (ω,x)) (fun σ => D (ω,σ))) := by
  let κ : Kernel Ω (Fin r → X) := ⟨fun ω => Measure.pi (fun _ : Fin r => ν ω),
    measurable_countable_measure_pi hν r⟩
  have : IsMarkovKernel κ := ⟨fun ω => by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin r => ν ω))
    infer_instance⟩
  have hm : Measurable (fun z : Ω × (Fin r → X) => Real.exp (∑ i, H (z.1,z.2 i))*D z) := by
    apply Measurable.mul _ hD
    apply Measurable.exp
    exact Finset.measurable_sum _ (fun i _ => hH.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd)))
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.div
    ((measurable_random_referencePartition hν hH).pow_const r)

lemma referenceReplicaMean_abs_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    (hmD : Measurable D) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    |referenceReplicaMean ν H D| ≤ c := by
  rw [referenceReplicaMean_eq_ratio]
  by_cases he : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))) (Measure.pi (fun _ => ν))
  · exact abs_bounded_gibbs_test_le he hmD hc hD
  · rw [integral_undef he,div_zero,abs_zero]
    exact hc

lemma abs_integral_le_const_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : Measurable F)
    {c : ℝ} (hbound : ∀ ω, |F ω| ≤ c) : |∫ ω, F ω ∂μ| ≤ c := by
  calc
    _ ≤ ∫ ω, |F ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _, c ∂μ := integral_mono ((integrable_of_measurable_abs_le hF hbound).abs)
      (integrable_const _) hbound
    _ = c := by simp

lemma measurable_random_cylinder_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2) D) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  exact measurable_random_referenceReplicaMean (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst)
    ((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd))
    ((measurable_of_countable D).comp measurable_snd)

lemma integrable_random_cylinder_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun ω => ∫ g, referenceReplicaMean (ν ω)
      (fun x => cylinderField (a x) g) D ∂gaussianCoordinates) P := by
  apply integrable_of_measurable_abs_le
    (measurable_random_cylinder_mean hν a D |>.stronglyMeasurable.integral_prod_right'.measurable)
  intro ω
  apply abs_integral_le_const_of_bound
    ((measurable_random_cylinder_mean hν a D).comp measurable_prodMk_left)
  intro g
  exact referenceReplicaMean_abs_le (ν ω) (fun x => cylinderField (a x) g)
    D (measurable_of_countable _) hc hD

theorem random_countable_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    (∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ) ∂gaussianCoordinates ∂P) =
    (∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂gaussianCoordinates ∂P) -
    (r+1 : ℕ)*(∫ ω, ∫ g, referenceReplicaMean (ν ω) (fun x => cylinderField (a x) g)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂gaussianCoordinates ∂P) := by
  let B : ℝ := (|K|+|L|)/2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcross (x y : X) : |cylinderCross (b x) (a y)| ≤ B := by
    calc
      _ ≤ ((b x).sum (fun _ t => t^2)+(a y).sum (fun _ t => t^2))/2 := abs_cylinderCross_le _ _
      _ ≤ B := by dsimp [B]; linarith [hb x,ha y,le_abs_self K,le_abs_self L]
  have hsum (σ : Fin (r+1) → X) : |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ (r+1 : ℕ)*B := by
    calc
      _ ≤ ∑ i, |cylinderCross (b (σ 0)) (a (σ i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), B := Finset.sum_le_sum (fun _ _ => hcross _ _)
      _ = _ := by simp
  have hfirst (σ : Fin (r+1) → X) :
      |D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))| ≤ c*((r+1 : ℕ)*B) := by
    rw [abs_mul]; exact mul_le_mul (hD σ) (hsum σ) (abs_nonneg _) hc
  have hfresh (τ : Fin (r+1+1) → X) :
      |D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))| ≤ c*B := by
    rw [abs_mul]; exact mul_le_mul (hD _) (hcross _ _) (abs_nonneg _) hc
  simp_rw [countable_cylinder_reference_insertion _ a b ha hb D hc hD]
  rw [integral_sub (integrable_random_cylinder_mean hν a _ (by positivity) hfirst)
    ((integrable_random_cylinder_mean hν a _ (mul_nonneg hc hB) hfresh).const_mul _),integral_const_mul]

lemma joint_integrable_square_of_uniform_conditionals {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] {P : Measure Ω} {Q : Measure Γ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {F : Ω × Γ → ℝ}
    (hm : Measurable F) {C : ℝ}
    (hi : ∀ ω, Integrable (fun g => F (ω,g)^2) Q)
    (hb : ∀ ω, (∫ g, F (ω,g)^2 ∂Q) ≤ C) :
    Integrable (fun z => F z^2) (P.prod Q) := by
  apply (integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi,?_⟩
  simp only [Real.norm_eq_abs,abs_sq]
  apply integrable_of_measurable_abs_le
    ((hm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable)
  intro ω
  rw [abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  exact hb ω

lemma measurable_random_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin (r+1) → X) → ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2)
      (fun σ => cylinderField (b (σ 0)) z.2*D σ)) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  have hmD : Measurable (fun p : (Ω × (ℕ → ℝ)) × (Fin (r+1) → X) =>
      cylinderField (b (p.2 0)) p.1.2*D p.2) :=
    ((measurable_cylinderFields b).comp
      (measurable_fst.snd.prodMk ((measurable_pi_apply 0).comp measurable_snd))).mul
        ((measurable_of_countable D).comp measurable_snd)
  exact measurable_random_referenceReplicaMean (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst)
    ((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)) hmD

lemma cylinder_replica_insertion_second {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    let F := fun g => referenceReplicaMean ν (fun x => cylinderField (a x) g)
      (fun σ => cylinderField (b (σ 0)) g*D σ)
    Integrable (fun g => F g^2) gaussianCoordinates ∧
      (∫ g, F g^2 ∂gaussianCoordinates) ≤
        c^2*((Real.exp (32*((r+1:ℕ):ℝ)^2*K)+2*Real.exp (32*L)+Real.exp (8*((r+1:ℕ):ℝ)^2*K))/2) := by
  have hmH : Measurable (fun z : (ℕ → ℝ) × (Fin (r+1) → X) =>
      ∑ i, cylinderField (a (z.2 i)) z.1) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_cylinderFields a).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hmY : Measurable (fun z : (ℕ → ℝ) × (Fin (r+1) → X) => cylinderField (b (z.2 0)) z.1) :=
    (measurable_cylinderFields b).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have hv (σ : Fin (r+1) → X) : (((b (σ 0)).sum (fun _ c => c^2)).toNNReal : ℝ) ≤ L := by
    have hnonneg : 0 ≤ (b (σ 0)).sum (fun _ c => c^2) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    rw [Real.coe_toNNReal _ hnonneg]
    exact hb (σ 0)
  have ht := gaussian_bounded_insertion_second
    (ν := Measure.pi (fun _ : Fin (r+1) => ν)) hmH hmY
    (measurable_of_countable D |>.comp measurable_snd)
    hc (fun z => hD z.2) (cylinder_replica_law a) (fun σ => cylinderField_law (b (σ 0)))
    (cylinder_replica_variance_le a ha) hv
  simpa only [referenceReplicaMean_eq_ratio,mul_assoc,Function.comp_apply] using ht.2

theorem integrable_joint_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2)
      (fun σ => cylinderField (b (σ 0)) z.2*D σ)) (P.prod gaussianCoordinates) := by
  have hm := measurable_random_cylinder_insertion hν a b D
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_replica_insertion_second (ν ω) a b ha hb D hc hD).1)
    (fun ω => (cylinder_replica_insertion_second (ν ω) a b ha hb D hc hD).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

lemma integrable_exp_of_integer_exp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {Y : X → ℝ} (hm : Measurable Y)
    (he : ∀ n : ℤ, Integrable (fun x => Real.exp ((n:ℝ)*Y x)) ν) (t : ℝ) :
    Integrable (fun x => Real.exp (t*Y x)) ν := by
  obtain ⟨n,hn⟩ := exists_nat_gt |t|
  have hp := he (n:ℤ)
  have hm' := he (-(n:ℤ))
  apply (hp.add hm').mono' (hm.const_mul t |>.exp.aestronglyMeasurable)
  refine ae_of_all _ fun x => ?_
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Int.cast_natCast,Int.cast_neg]
  by_cases hy : 0 ≤ Y x
  · have h : t*Y x ≤ (n:ℝ)*Y x := mul_le_mul_of_nonneg_right ((le_abs_self t).trans hn.le) hy
    exact (Real.exp_le_exp.mpr h).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have h : t*Y x ≤ -(n:ℝ)*Y x := mul_le_mul_of_nonpos_right (by linarith [neg_abs_le t]) (le_of_not_ge hy)
    exact (Real.exp_le_exp.mpr h).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

lemma random_cylinder_all_exp_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) :
    ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ t : ℝ,
      Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1) := by
  let κ : Kernel (Ω × (ℕ → ℝ)) X := ⟨fun z => ν z.1,hν.comp measurable_fst⟩
  have : IsMarkovKernel κ := ⟨fun z => by
    change IsProbabilityMeasure (ν z.1)
    infer_instance⟩
  have hi (t : ℝ) : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates,
      Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1) := by
    have hm : Measurable (fun p : (Ω × (ℕ → ℝ)) × X =>
        Real.exp (t*cylinderField (a p.2) p.1.2)) :=
      ((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)).const_mul t |>.exp
    have hs : MeasurableSet {z : Ω × (ℕ → ℝ) |
        Integrable (fun x => Real.exp (t*cylinderField (a x) z.2)) (ν z.1)} :=
      ProbabilityTheory.measurableSet_kernel_integrable (κ := κ) hm.stronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae hs).mpr
    refine ae_of_all _ fun ω => ?_
    have hv (x : X) : (((a x).sum (fun _ c => c^2)).toNNReal : ℝ) ≤ K := by
      rw [Real.coe_toNNReal _ (show 0 ≤ (a x).sum (fun _ c => c^2) from
        Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
      exact ha x
    exact (gaussian_field_exp_integrable (ν := ν ω) (measurable_cylinderFields a)
      (fun x => cylinderField_law (a x)) hv t).1.prod_right_ae
  have hn : ∀ᵐ z : Ω × (ℕ → ℝ) ∂P.prod gaussianCoordinates, ∀ n : ℤ,
      Integrable (fun x => Real.exp ((n:ℝ)*cylinderField (a x) z.2)) (ν z.1) :=
    ae_all_iff.mpr (fun n => hi (n:ℝ))
  filter_upwards [hn] with z hz
  exact integrable_exp_of_integer_exp (measurable_of_countable _) hz

lemma measurable_random_cylinder_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) (t : ℝ) :
    Measurable (fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (a x) z.2) (ν z.1) t) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  exact (measurable_random_referencePartition (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst)
    (((measurable_cylinderFields a).comp (measurable_fst.snd.prodMk measurable_snd)).const_mul t)).log

lemma cylinder_scaled_law {X : Type*} (a : X → ℕ →₀ ℝ) (x : X) (t : ℝ) :
    gaussianCoordinates.map (fun g => t*cylinderField (a x) g) =
      gaussianReal 0 (⟨t^2,sq_nonneg t⟩*(((a x).sum (fun _ c => c^2)).toNNReal)) := by
  have hm := measurable_cylinderField (a x)
  rw [show (fun g => t*cylinderField (a x) g) = (fun y : ℝ => t*y) ∘ cylinderField (a x) from rfl,
    ← Measure.map_map (by fun_prop) hm,cylinderField_law,gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 2

lemma cylinder_cgf_second {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun g => (cgf (fun x => cylinderField (a x) g) ν t)^2) gaussianCoordinates ∧
      (∫ g, (cgf (fun x => cylinderField (a x) g) ν t)^2 ∂gaussianCoordinates) ≤
        4*Real.exp (2*(t^2*K)) := by
  have hm : Measurable (fun z : (ℕ → ℝ) × X => t*cylinderField (a z.2) z.1) :=
    (measurable_cylinderFields a).const_mul t
  have hv (x : X) : ((⟨t^2,sq_nonneg t⟩ : NNReal)*(((a x).sum (fun _ c => c^2)).toNNReal) : ℝ) ≤ t^2*K := by
    change t^2*((((a x).sum (fun _ c => c^2)).toNNReal : NNReal) : ℝ) ≤ t^2*K
    rw [Real.coe_toNNReal _ (show 0 ≤ (a x).sum (fun _ c => c^2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (ha x) (sq_nonneg _)
  exact gaussian_log_partition_second (ν := ν) hm (fun x => cylinder_scaled_law a x t) hv

lemma integrable_random_cylinder_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {K : ℝ} (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    Integrable (fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (a x) z.2) (ν z.1) t)
      (P.prod gaussianCoordinates) := by
  have hm := measurable_random_cylinder_cgf hν a t
  have hi := joint_integrable_square_of_uniform_conditionals (P := P) hm
    (fun ω => (cylinder_cgf_second (ν ω) a ha t).1)
    (fun ω => (cylinder_cgf_second (ν ω) a ha t).2)
  exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi).integrable (by norm_num)

lemma integrable_joint_cylinder_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a : X → ℕ →₀ ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => cylinderField (a x) z.2) D) (P.prod gaussianCoordinates) := by
  exact integrable_of_measurable_abs_le (measurable_random_cylinder_mean hν a D)
    (fun z => referenceReplicaMean_abs_le (ν z.1) _ D (measurable_of_countable _) hc hD)

theorem joint_countable_cylinder_insertion {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (a b : X → ℕ →₀ ℝ) {K L : ℝ}
    (ha : ∀ x, (a x).sum (fun _ c => c^2) ≤ K)
    (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ L)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (fun x => cylinderField (a x) z.2)
      (fun σ => cylinderField (b (σ 0)) z.2*D σ) ∂P.prod gaussianCoordinates) =
    (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (fun x => cylinderField (a x) z.2)
      (fun σ => D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))) ∂P.prod gaussianCoordinates) -
    (r+1 : ℕ)*(∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (fun x => cylinderField (a x) z.2)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0)))
      ∂P.prod gaussianCoordinates) := by
  let B : ℝ := (|K|+|L|)/2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcross (x y : X) : |cylinderCross (b x) (a y)| ≤ B := by
    calc
      _ ≤ ((b x).sum (fun _ t => t^2)+(a y).sum (fun _ t => t^2))/2 := abs_cylinderCross_le _ _
      _ ≤ B := by dsimp [B]; linarith [hb x,ha y,le_abs_self K,le_abs_self L]
  have hsum (σ : Fin (r+1) → X) : |∑ i, cylinderCross (b (σ 0)) (a (σ i))| ≤ (r+1 : ℕ)*B := by
    calc
      _ ≤ ∑ i, |cylinderCross (b (σ 0)) (a (σ i))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), B := Finset.sum_le_sum (fun _ _ => hcross _ _)
      _ = _ := by simp
  have hfirst (σ : Fin (r+1) → X) :
      |D σ*(∑ i, cylinderCross (b (σ 0)) (a (σ i)))| ≤ c*((r+1 : ℕ)*B) := by
    rw [abs_mul]; exact mul_le_mul (hD σ) (hsum σ) (abs_nonneg _) hc
  have hfresh (τ : Fin (r+1+1) → X) :
      |D (Fin.tail τ)*cylinderCross (b ((Fin.tail τ) 0)) (a (τ 0))| ≤ c*B := by
    rw [abs_mul]; exact mul_le_mul (hD _) (hcross _ _) (abs_nonneg _) hc
  rw [integral_prod _ (integrable_joint_cylinder_insertion hν a b ha hb D hc hD),
    integral_prod _ (integrable_joint_cylinder_mean hν a _ (by positivity) hfirst),
    integral_prod _ (integrable_joint_cylinder_mean hν a _ (mul_nonneg hc hB) hfresh)]
  exact random_countable_cylinder_insertion hν a b ha hb D hc hD

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ConvexDerivativeFluctuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Derivative Fluctuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma replica_tilted_pi {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (r : ℕ) :
    (Measure.pi (fun _ : Fin r => ν)).tilted (fun σ => ∑ i, H (σ i)) =
      Measure.pi (fun _ : Fin r => ν.tilted H) := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  have hz : 0 < referencePartition ν H := integral_exp_pos he
  apply Measure.ext_of_singleton
  intro σ
  rw [tilted_singleton,Measure.pi_singleton,Measure.pi_singleton]
  simp_rw [tilted_singleton]
  rw [show referencePartition (Measure.pi (fun _ : Fin r => ν)) (fun σ => ∑ i, H (σ i)) =
    (referencePartition ν H)^r from reference_replica_partition ν H r]
  rw [Real.exp_sum,ENNReal.ofReal_div_of_pos (pow_pos hz r),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),ENNReal.ofReal_pow hz.le]
  simp_rw [ENNReal.ofReal_div_of_pos hz]
  rw [Finset.prod_mul_distrib,ENNReal.prod_div_distrib_of_ne_top (fun _ _ => ENNReal.ofReal_ne_top)]
  simp

lemma referenceReplicaMean_eq_tilted {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) {r : ℕ} (D : (Fin r → X) → ℝ) :
    referenceReplicaMean ν H D = ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν.tilted H) := by
  rw [← replica_tilted_pi ν H he r,integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]
  rw [reference_replica_partition]; rfl

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ReplicaEnergyCovarianceBound
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica Energy Covariance Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma cylinderField_smul (a : ℕ →₀ ℝ) (t : ℝ) (g : ℕ → ℝ) :
    cylinderField (t • a) g = t*cylinderField a g := by
  simp only [cylinderField]
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma cylinder_norm_smul (a : ℕ →₀ ℝ) (t : ℝ) :
    (t • a).sum (fun _ c => c^2) = t^2*a.sum (fun _ c => c^2) := by
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [mul_pow,Finsupp.sum]
  rw [Finset.mul_sum]

lemma cylinderCross_smul_right (a b : ℕ →₀ ℝ) (t : ℝ) :
    cylinderCross a (t • b) = t*cylinderCross a b := by
  simp only [cylinderCross,Finsupp.smul_apply,smul_eq_mul,Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma referenceReplicaMean_const_mul {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) {r : ℕ} (D : (Fin r → X) → ℝ) (c : ℝ) :
    referenceReplicaMean ν H (fun σ => c*D σ) = c*referenceReplicaMean ν H D := by
  unfold referenceReplicaMean
  rw [show (fun σ : Fin r → X => Real.exp (∑ i, H (σ i))*(c*D σ)) =
    (fun σ => c*(Real.exp (∑ i, H (σ i))*D σ)) from by funext σ; ring,
    integral_const_mul]
  ring

lemma referenceReplicaMean_add_bounded {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (he : Integrable (fun x => Real.exp (H x)) ν)
    {r : ℕ} (D E : (Fin r → X) → ℝ) {c d : ℝ}
    (hD : ∀ σ, |D σ| ≤ c) (hE : ∀ σ, |E σ| ≤ d) :
    referenceReplicaMean ν H (fun σ => D σ+E σ) =
      referenceReplicaMean ν H D+referenceReplicaMean ν H E := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted he
  rw [referenceReplicaMean_eq_tilted ν H he,referenceReplicaMean_eq_tilted ν H he,
    referenceReplicaMean_eq_tilted ν H he]
  exact integral_add (integrable_of_measurable_abs_le (measurable_of_countable _) hD)
    (integrable_of_measurable_abs_le (measurable_of_countable _) hE)

lemma cylinderCross_self (a : ℕ →₀ ℝ) : cylinderCross a a = a.sum (fun _ c => c^2) := by
  simp only [cylinderCross,Finsupp.sum,pow_two]

lemma cylinderCross_bound {X : Type*} (A : X → ℕ →₀ ℝ) {B : ℝ}
    (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B) (x y : X) :
    |cylinderCross (A x) (A y)| ≤ |B| := by
  calc
    _ ≤ ((A x).sum (fun _ c => c^2)+(A y).sum (fun _ c => c^2))/2 := abs_cylinderCross_le _ _
    _ ≤ |B| := by linarith [hA x,hA y,le_abs_self B]

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

lemma integrable_random_scaled_mean [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) (t : ℝ) {r : ℕ} (D : (Fin r → X) → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    Integrable (fun z : Ω × (ℕ → ℝ) => referenceReplicaMean (ν z.1)
      (fun x => t*cylinderField (A x) z.2) D) (P.prod gaussianCoordinates) := by
  simpa only [cylinderField_smul] using
    integrable_joint_cylinder_mean (P := P) hν (fun x => t • A x) D hc hD

theorem randomReplicaEnergy_identity [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {B d : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ B)
    (hdiag : ∀ x, cylinderCross (A x) (A x) = d) (t : ℝ)
    {r : ℕ} (D : (Fin (r+1) → X) → ℝ) {c : ℝ} (hc : 0 ≤ c) (hD : ∀ σ, |D σ| ≤ c) :
    randomReplicaEnergy P ν A t D = t*(d*randomReplicaAverage P ν A t D +
      randomReplicaAverage P ν A t (fun σ => D σ*(∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ)))) -
      (r+1 : ℕ)*randomReplicaAverage P ν A t
        (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) := by
  let μ := P.prod gaussianCoordinates
  let H := fun z : Ω × (ℕ → ℝ) => fun x => t*cylinderField (A x) z.2
  let E := fun σ : Fin (r+1) → X => D σ*(∑ l : Fin r, cylinderCross (A (σ 0)) (A (σ l.succ)))
  have hE (σ : Fin (r+1) → X) : |E σ| ≤ c*((r:ℝ)*|B|) := by
    dsimp [E]
    rw [abs_mul]
    apply mul_le_mul (hD σ) _ (abs_nonneg _) hc
    calc
      _ ≤ ∑ l : Fin r, |cylinderCross (A (σ 0)) (A (σ l.succ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin r, |B| := Finset.sum_le_sum (fun _ _ => cylinderCross_bound A hA _ _)
      _ = _ := by simp
  have hV := integrable_random_scaled_mean (P := P) hν A t D hc hD
  have hW := integrable_random_scaled_mean (P := P) hν A t E (by positivity) hE
  have first : (∫ z : Ω × (ℕ → ℝ), referenceReplicaMean (ν z.1) (H z)
      (fun σ => D σ*(∑ i : Fin (r+1), t*cylinderCross (A (σ 0)) (A (σ i)))) ∂μ) =
      t*(d*randomReplicaAverage P ν A t D+randomReplicaAverage P ν A t E) := by
    calc
      _ = ∫ z : Ω × (ℕ → ℝ), t*(d*referenceReplicaMean (ν z.1) (H z) D+
          referenceReplicaMean (ν z.1) (H z) E) ∂μ := by
        apply integral_congr_ae
        filter_upwards [random_cylinder_all_exp_ae (P := P) hν A hA] with z hz
        have heq : (fun σ : Fin (r+1) → X => D σ*(∑ i, t*cylinderCross (A (σ 0)) (A (σ i)))) =
            (fun σ => t*(d*D σ+E σ)) := by
          funext σ
          rw [Fin.sum_univ_succ,hdiag,← Finset.mul_sum]
          dsimp [E]
          ring
        rw [heq,referenceReplicaMean_const_mul,
          referenceReplicaMean_add_bounded _ _ (hz t) _ _
            (fun σ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD σ) (abs_nonneg d)) hE,
          referenceReplicaMean_const_mul]
      _ = _ := by
        rw [integral_const_mul,integral_add (hV.const_mul d) hW,integral_const_mul]
        rfl
  have h := joint_countable_cylinder_insertion (P := P) hν (fun x => t • A x) A
    (fun x => by rw [cylinder_norm_smul]; exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg t)) hA D hc hD
  simp only [cylinderField_smul,cylinderCross_smul_right] at h
  have hfresh : (fun (z : Ω × (ℕ → ℝ)) => referenceReplicaMean (ν z.1) (H z)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*(t*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0))))) =
    (fun z : Ω × (ℕ → ℝ) => t*referenceReplicaMean (ν z.1) (H z)
      (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) := by
    funext z
    rw [show (fun τ : Fin (r+1+1) → X => D (Fin.tail τ)*(t*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) =
      (fun τ => t*(D (Fin.tail τ)*cylinderCross (A ((Fin.tail τ) 0)) (A (τ 0)))) from by funext τ; ring,
      referenceReplicaMean_const_mul]
  change randomReplicaEnergy P ν A t D = _ at h
  change (∫ z, referenceReplicaMean (ν z.1) (H z) _ ∂μ) = _ at first
  rw [first,hfresh,integral_const_mul] at h
  rw [h]
  dsimp [E,randomReplicaAverage,μ,H]
  ring

end IsingPerceptron

namespace IsingPerceptron

lemma cylinderCross_zero_left (b : ℕ →₀ ℝ) : cylinderCross 0 b = 0 := by
  simp [cylinderCross]
lemma cylinderCross_add_left (a b c : ℕ →₀ ℝ) :
    cylinderCross (a+b) c = cylinderCross a c+cylinderCross b c := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
lemma cylinderCross_single_left (i : ℕ) (c : ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (Finsupp.single i c) b = c*b i := by
  exact Finsupp.sum_single_index (zero_mul _)
lemma cylinderCross_finset_left {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ) (b : ℕ →₀ ℝ) :
    cylinderCross (∑ i ∈ s, a i) b = ∑ i ∈ s, cylinderCross (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cylinderCross_zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,cylinderCross_add_left,ih]

lemma featureCoefficients_apply {I : Type*} [Fintype I] (tag : I → ℕ) (c : I → ℝ) (j : ℕ) :
    featureCoefficients tag c j = ∑ i, if tag i = j then c i else 0 := by
  classical
  simp only [featureCoefficients,Finsupp.finsetSum_apply,Finsupp.single_apply]

lemma featureCoefficients_cross {I J : Type*} [Fintype I] [Fintype J]
    (t : I → ℕ) (u : J → ℕ) (a : I → ℝ) (b : J → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, ∑ j, if t i = u j then a i*b j else 0 := by
  classical
  rw [featureCoefficients,cylinderCross_finset_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [cylinderCross_single_left,featureCoefficients_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : t i = u j
  · simp [h]
  · simp only [Ne.symm h,h,ite_false,mul_zero]

lemma featureCoefficients_diagonal {I : Type*} [Fintype I]
    (t : I → ℕ) (u : I → ℕ)
    (hcross : ∀ i j, t i = u j → i = j) (a b : I → ℝ) :
    cylinderCross (featureCoefficients t a) (featureCoefficients u b) =
      ∑ i, if t i = u i then a i*b i else 0 := by
  classical
  rw [featureCoefficients_cross]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact ite_eq_right (fun h => hji (hcross i j h).symm)
  · simp

lemma labeledAddress_length (n : ℕ) (v : LabeledLeaf n) : (labeledAddress n v).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledAddress,List.length_cons,ih]

lemma labeledCommonDepth_le (n : ℕ) (v w : LabeledLeaf n) : labeledCommonDepth n v w ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    dsimp only [labeledCommonDepth]
    split_ifs
    · exact Nat.succ_le_succ (ih _ _)
    · exact Nat.zero_le _

lemma labeledCommonDepth_self (n : ℕ) (v : LabeledLeaf n) : labeledCommonDepth n v v = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [labeledCommonDepth,ite_true,ih]

lemma labeled_prefix_eq_iff (n : ℕ) (v w : LabeledLeaf n) {d : ℕ} (hd : d ≤ n) :
    (labeledAddress n v).take d = (labeledAddress n w).take d ↔ d ≤ labeledCommonDepth n v w := by
  induction n generalizing d with
  | zero =>
    have : d = 0 := by omega
    subst d
    simp [labeledAddress,labeledCommonDepth]
  | succ n ih =>
    cases d with
    | zero => simp
    | succ d =>
      simp only [labeledAddress,List.take_succ_cons,List.cons.injEq]
      rw [ih _ _ (by omega)]
      dsimp only [labeledCommonDepth]
      by_cases h : v.1 = w.1
      · simp only [h,ite_true,true_and,Nat.add_le_add_iff_right]
      · simp [h]

lemma treeFeatureTag_cross {J : Type*} [Encodable J] (n : ℕ) (v w : LabeledLeaf n)
    (i j : Fin (n+1) × J) :
    treeFeatureTag n v i = treeFeatureTag n w j ↔
      i = j ∧ i.1.1 ≤ labeledCommonDepth n v w := by
  unfold treeFeatureTag
  rw [Encodable.encode_inj]
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hi,haddr,hj⟩
    have he : i = j := Prod.ext (Fin.ext hi) hj
    subst j
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mp haddr⟩
  · rintro ⟨rfl,hd⟩
    exact ⟨rfl,(labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.1.isLt)).mpr hd,rfl⟩

lemma treeFieldCoefficients_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) (a b : Fin (n+1) → ℝ) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v a c) (treeFieldCoefficients n w b e) =
      (∑ i : Fin (n+1), if i.1 ≤ labeledCommonDepth n v w then a i*b i else 0) *
        (∑ j, c j*e j) := by
  classical
  rw [treeFieldCoefficients,treeFieldCoefficients,featureCoefficients_diagonal
    (treeFeatureTag n v) (treeFeatureTag n w)
    (fun i j h => ((treeFeatureTag_cross n v w i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.1 ≤ labeledCommonDepth n v w
  · simp only [h,ite_true]; ring
  · simp only [h,ite_false,zero_mul]

lemma pathIncrement_nonneg {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    0 ≤ pathIncrement q i := by
  cases i with
  | zero => exact h0
  | succ i => exact sub_nonneg.mpr (hq (Nat.le_succ i))

lemma pathAmplitude_sq {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    pathAmplitude q i ^ 2 = pathIncrement q i := Real.sq_sqrt (pathIncrement_nonneg hq h0 i)

lemma pathIncrement_sum (q : ℕ → ℝ) (r : ℕ) :
    ∑ i ∈ Finset.range (r+1), pathIncrement q i = q r := by
  induction r with
  | zero => simp [pathIncrement]
  | succ r ih => rw [Finset.sum_range_succ,ih,pathIncrement]; ring

lemma pathIncrement_prefix (q : ℕ → ℝ) (n r : ℕ) (hr : r ≤ n) :
    (∑ i : Fin (n+1), if (i : ℕ) ≤ r then pathIncrement q i else 0) = q r := by
  classical
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => if i ≤ r then pathIncrement q i else 0)]
  have he : (∑ i ∈ Finset.range (n+1), if i ≤ r then pathIncrement q i else 0) =
      ∑ i ∈ Finset.range (r+1), pathIncrement q i := by
    symm
    calc
      _ = ∑ i ∈ Finset.range (r+1), if i ≤ r then pathIncrement q i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).symm
      _ = _ := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hr)) (by
        intro i _ hi
        exact ite_eq_right (by simp only [Finset.mem_range,not_lt] at hi; omega))
  rw [he,pathIncrement_sum]

lemma treeField_path_cross {J : Type*} [Fintype J] [Encodable J] (n : ℕ)
    (v w : LabeledLeaf n) {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (c e : J → ℝ) :
    cylinderCross (treeFieldCoefficients n v (fun i => pathAmplitude q i) c)
      (treeFieldCoefficients n w (fun i => pathAmplitude q i) e) =
      q (labeledCommonDepth n v w) * (∑ j, c j*e j) := by
  rw [treeFieldCoefficients_cross]
  simp_rw [← pow_two,pathAmplitude_sq hq h0]
  rw [pathIncrement_prefix q n _ (labeledCommonDepth_le n v w)]

lemma tensorFeature_cross {J : Type*} [Fintype J] (p : ℕ) (x y : J → ℝ) :
    (∑ i : Fin p → J, tensorFeature p x i * tensorFeature p y i) =
      (∑ j, x j*y j)^p := by
  classical
  simp only [tensorFeature,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (j : J) => x j * y j)]
  simp

lemma spinValue_sq (x : Fin 2) : spinValue x ^ 2 = 1 := by
  simp only [spinValue]; split_ifs <;> norm_num

lemma spinCoordinate_cross {N : ℕ} (x y : Spin N) :
    (∑ i, spinCoordinate x i * spinCoordinate y i) = spinOverlap x y := by
  simp only [spinCoordinate,div_mul_div_comm,← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N),← Finset.sum_div,spinOverlap]

lemma spinOverlap_self {N : ℕ} (hN : 0 < N) (x : Spin N) : spinOverlap x x = 1 := by
  simp only [spinOverlap,← pow_two,spinValue_sq,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hN.ne')

lemma monomialPath_monotone (n d : ℕ) : Monotone (monomialPath n d) := by
  intro i j hij
  apply pow_le_pow_left₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)

lemma monomialPath_nonneg (n d i : ℕ) : 0 ≤ monomialPath n d i :=
  pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

lemma monomialPath_diag_le_one (n d : ℕ) : monomialPath n d n ≤ 1 := by
  apply pow_le_one₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    exact Nat.cast_le.mpr (Nat.le_succ n)

lemma monomialCoefficients_cross {N : ℕ} (n p d : ℕ)
    (s t : Spin N × LabeledLeaf n) :
    cylinderCross (monomialCoefficients n p d s) (monomialCoefficients n p d t) =
      spinOverlap s.1 t.1 ^ p * treeOverlap n s.2 t.2 ^ d := by
  unfold monomialCoefficients
  rw [treeField_path_cross n s.2 t.2 (monomialPath_monotone n d)
    (monomialPath_nonneg n d 0),tensorFeature_cross,spinCoordinate_cross]
  exact mul_comm _ _

lemma monomialCoefficients_variance {N : ℕ} (hN : 0 < N) (n p d : ℕ)
    (s : Spin N × LabeledLeaf n) :
    (monomialCoefficients n p d s).sum (fun _ c => c^2) = monomialPath n d n := by
  rw [← cylinderCross_self,monomialCoefficients_cross,spinOverlap_self hN,one_pow,one_mul]
  simp only [treeOverlap,labeledCommonDepth_self,monomialPath]

lemma monomialCoefficients_variance_le {N : ℕ} (hN : 0 < N) (n p d : ℕ)
    (s : Spin N × LabeledLeaf n) :
    (monomialCoefficients n p d s).sum (fun _ c => c^2) ≤ 1 := by
  rw [monomialCoefficients_variance hN]
  exact monomialPath_diag_le_one _ _

lemma gaussian_pullback_measurePreserving {ι : Type*} (tag : ι → ℕ)
    (ht : Function.Injective tag) :
    MeasurePreserving (fun g : ℕ → ℝ => fun i => g (tag i)) gaussianCoordinates
      (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) := by
  refine ⟨by fun_prop,?_⟩
  have hi : iIndepFun (fun i : ℕ => fun g : ℕ → ℝ => g i) gaussianCoordinates :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have he := (hi.precomp ht).map_fun_eq_infinitePi_map (fun _ => by fun_prop)
  simpa only [gaussianCoordinates,Measure.infinitePi_map_eval] using he

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_MonomialGgAtMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monomial Gg At Minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {A : Type*} [MeasurableSpace A]

lemma integral_exp_pos (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ)
    {b : ℝ} (hi : Integrable (fun a => Real.exp (b*F a)) μ) :
    0 < ∫ a, Real.exp (b*F a) ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun a => (Real.exp_pos _).le) hi).mpr
  simpa only [Function.support, ne_eq, Real.exp_ne_zero, not_false_eq_true, ofPred_true,
    measure_univ] using (zero_lt_one : (0 : ℝ≥0∞) < 1)

theorem logMean_normalized_moment (μ : Measure A) [IsProbabilityMeasure μ]
    (F : A → ℝ) {b : ℝ} (hb : b ≠ 0)
    (hi : Integrable (fun a => Real.exp (b*F a)) μ) :
    (∫⁻ a, ENNReal.ofReal ((Real.exp (F a-logMean b μ F))^b) ∂μ) = 1 := by
  let M := ∫ a, Real.exp (b*F a) ∂μ
  have hM : 0 < M := integral_exp_pos μ F hi
  have he a : (Real.exp (F a-logMean b μ F))^b = M⁻¹ * Real.exp (b*F a) := by
    rw [← Real.exp_mul]
    have he' : (F a-logMean b μ F)*b = -Real.log M+b*F a := by
      dsimp only [logMean, M]
      field_simp
      ring
    rw [he', Real.exp_add, Real.exp_neg, Real.exp_log hM]
  simp_rw [he, ENNReal.ofReal_mul (inv_nonneg.mpr hM.le)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun a => (Real.exp_pos _).le)]
  change ENNReal.ofReal M⁻¹ * ENNReal.ofReal M = 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hM.le), inv_mul_cancel₀ hM.ne', ENNReal.ofReal_one]

lemma logMean_bounds (μ : Measure A) [IsProbabilityMeasure μ]
    {F : A → ℝ} (hF : Measurable F) {b K : ℝ} (hb : 0 < b)
    (hbound : ∀ a, |F a| ≤ K) : |logMean b μ F| ≤ K := by
  have hi : Integrable (fun a => Real.exp (b*F a)) μ := by
    apply Integrable.of_bound ((measurable_const.mul hF).exp).aestronglyMeasurable (Real.exp (b*K))
    apply ae_of_all
    intro a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound a)) hb.le)
  have hlow : Real.exp (-b*K) ≤ ∫ a, Real.exp (b*F a) ∂μ := by
    calc
      _ = ∫ _, Real.exp (-b*K) ∂μ := by simp
      _ ≤ _ := by
        apply integral_mono (integrable_const _) hi
        intro a
        apply Real.exp_le_exp.mpr
        have := (abs_le.mp (hbound a)).1
        nlinarith
  have hhigh : (∫ a, Real.exp (b*F a) ∂μ) ≤ Real.exp (b*K) := by
    calc
      _ ≤ ∫ _, Real.exp (b*K) ∂μ := integral_mono hi (integrable_const _) (fun a =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound a)) hb.le))
      _ = _ := by simp
  have hM := integral_exp_pos μ F hi
  rw [abs_le, logMean]
  constructor
  · apply (le_div_iff₀ hb).mpr
    have := Real.log_le_log (Real.exp_pos _) hlow
    rw [Real.log_exp] at this
    nlinarith
  · apply (div_le_iff₀ hb).mpr
    have := Real.log_le_log hM hhigh
    rw [Real.log_exp] at this
    nlinarith

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]

lemma measurable_cascadeRecursion (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) :
    Measurable (cascadeRecursion n b μ u F) := by
  induction n generalizing b μ u with
  | zero => exact hF
  | succ n ih =>
    have hm : Measurable (fun p : S × A => Real.exp (b 0 *
        cascadeRecursion n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => u (j+1)) F (u 0 p))) :=
      (measurable_const.mul ((ih _ _ (fun j => hu (j+1))).comp (hu 0))).exp
    exact hm.stronglyMeasurable.integral_prod_right.measurable.log.div_const _

lemma cascadeRecursion_bound (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {u : ℕ → S × A → S} {F : S → ℝ} {K : ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F)
    (hb : ∀ i < n, 0 < b i) (hbound : ∀ s, |F s| ≤ K) :
    ∀ s, |cascadeRecursion n b μ u F s| ≤ K := by
  induction n generalizing b μ u with
  | zero => exact hbound
  | succ n ih =>
    intro s
    apply logMean_bounds (μ 0 : Measure A)
      ((measurable_cascadeRecursion n _ _ (fun j => hu (j+1)) hF).comp
        ((hu 0).comp (measurable_const.prodMk measurable_id))) (hb 0 (by omega))
    intro a
    exact ih _ _ (fun j => hu (j+1)) (fun i hi => hb (i+1) (by omega)) (u 0 (s,a))

lemma measurable_stoppedUpdate (n : ℕ) {u : ℕ → S × A → S}
    (hu : ∀ i, Measurable (u i)) (i : ℕ) : Measurable (stoppedUpdate n u i) := by
  unfold stoppedUpdate
  split_ifs
  · exact hu i
  · exact measurable_fst

lemma measurable_backwardValue (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (i : ℕ) :
    Measurable (backwardValue n b μ u F i) :=
  measurable_cascadeRecursion _ _ _ (fun j => hu (i+j)) hF

omit [MeasurableSpace S] in
lemma backwardValue_step (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (u : ℕ → S × A → S) (F : S → ℝ) {i : ℕ} (hi : i < n) (s : S) :
    backwardValue n b μ u F i s = logMean (b i) (μ i : Measure A)
      (fun a => backwardValue n b μ u F (i+1) (u i (s,a))) := by
  unfold backwardValue
  rw [show n-i = (n-(i+1))+1 by omega, cascadeRecursion]
  simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]

omit [MeasurableSpace S] in
lemma backwardValue_terminal (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (u : ℕ → S × A → S) (F : S → ℝ) {i : ℕ} (hi : n ≤ i) :
    backwardValue n b μ u F i = F := by
  simp [backwardValue, Nat.sub_eq_zero_of_le hi, cascadeRecursion]

theorem backwardValue_multiplier_moment (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {u : ℕ → S × A → S} {F : S → ℝ} {K : ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F)
    (hb : ∀ i < n, 0 < b i) (hbound : ∀ s, |F s| ≤ K) (i : ℕ) (s : S) :
    (∫⁻ a, ENNReal.ofReal ((Real.exp
      (backwardValue n b μ u F (i+1) (stoppedUpdate n u i (s,a)) -
        backwardValue n b μ u F i s)) ^ b i) ∂(μ i : Measure A)) = 1 := by
  by_cases hi : i < n
  · simp only [stoppedUpdate, ite_eq_left hi, backwardValue_step n b μ u F hi]
    apply logMean_normalized_moment _ _ (hb i hi).ne'
    apply Integrable.of_bound
      ((measurable_const.mul ((measurable_backwardValue n b μ hu hF (i+1)).comp
        ((hu i).comp (measurable_const.prodMk measurable_id)))).exp).aestronglyMeasurable
      (Real.exp (b i*K))
    apply ae_of_all
    intro a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (hb i hi).le
    apply le_trans (le_abs_self _)
    exact cascadeRecursion_bound _ _ _ (fun j => hu (i+1+j)) hF
      (fun j hj => hb (i+1+j) (by omega)) hbound _
  · have hni : n ≤ i := by omega
    simp only [stoppedUpdate, ite_eq_right hi,
      backwardValue_terminal n b μ u F hni,
      backwardValue_terminal n b μ u F (show n ≤ i+1 by omega), sub_self,
      Real.exp_zero, Real.one_rpow, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

omit [MeasurableSpace S] in
lemma noiseTreeFactor_terminal (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (X : ℕ → S → ℝ) (u : ℕ → S × A → S) (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ X u s ν = terminalTreeFactor n b μ u (X n) s ν := by
  induction n generalizing b μ X u s with
  | zero => rfl
  | succ n ih =>
    unfold noiseTreeFactor terminalTreeFactor
    apply lintegral_congr
    intro p
    congr 1
    exact ih _ _ _ _ _ _

omit [MeasurableSpace S] in
lemma terminalTreeFactor_update_congr (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (F : S → ℝ) {u v : ℕ → S × A → S} (huv : ∀ i < n, u i = v i)
    (s : S) (ν : NoiseTree A n) :
    terminalTreeFactor n b μ u F s ν = terminalTreeFactor n b μ v F s ν := by
  induction n generalizing b μ u v s with
  | zero => rfl
  | succ n ih =>
    unfold terminalTreeFactor
    rw [huv 0 (by omega)]
    apply lintegral_congr
    intro p
    congr 1
    exact ih _ _ (fun i hi => huv (i+1) (by omega)) _ _

omit [MeasurableSpace S] in
lemma backwardValue_treeFactor (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (F : S → ℝ) (u : ℕ → S × A → S) (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ (backwardValue n b μ u F) (stoppedUpdate n u) s ν =
      terminalTreeFactor n b μ u F s ν := by
  rw [noiseTreeFactor_terminal, backwardValue_terminal n b μ u F (le_refl n)]
  apply terminalTreeFactor_update_congr
  intro i hi
  funext p
  exact ite_eq_left hi

theorem bounded_noiseCascade_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {u : ℕ → S × A → S} {F : S → ℝ} {K : ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (hbound : ∀ s, |F s| ≤ K) (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal A n ν).toReal)
    (∀ᵐ ν ∂P, 0 < terminalTreeFactor n b μ u F s ν ∧ terminalTreeFactor n b μ u F s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  let X := backwardValue n b μ u F
  let v := stoppedUpdate n u
  let c : ℕ → S × A → ℝ := fun i p => Real.exp (X (i+1) (v i p)-X i p.1)
  have hX : ∀ i, Measurable (X i) := measurable_backwardValue n b μ hu hF
  have hv : ∀ i, Measurable (v i) := measurable_stoppedUpdate n hu
  have hc : ∀ i, Measurable (c i) := fun i =>
    (((hX (i+1)).comp (hv i)).sub ((hX i).comp measurable_fst)).exp
  have hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A)) = 1 :=
    backwardValue_multiplier_moment n b μ hu hF (fun i hi => (hb.1 i hi).1) hbound
  have h := noiseCascade_log_integral n b hb μ hc hv (X := X) (fun _ _ _ => rfl) hm s
  have hX0 : X 0 s = cascadeRecursion n b μ u F s := by simp [X, backwardValue]
  simpa only [X, v, backwardValue_treeFactor, hX0] using h

omit [MeasurableSpace S] [Nonempty A] in
lemma backwardValue_multiplier_moment_admissible (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure A) (u : ℕ → S × A → S) (F : S → ℝ)
    (hb : ∀ i < n, 0 < b i)
    (hadm : ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ u F (i+1) (u i (s,a)))) (μ i : Measure A))
    (i : ℕ) (s : S) :
    (∫⁻ a, ENNReal.ofReal ((Real.exp
      (backwardValue n b μ u F (i+1) (stoppedUpdate n u i (s,a)) -
        backwardValue n b μ u F i s)) ^ b i) ∂(μ i : Measure A)) = 1 := by
  by_cases hi : i < n
  · simp only [stoppedUpdate, ite_eq_left hi, backwardValue_step n b μ u F hi]
    exact logMean_normalized_moment _ _ (hb i hi).ne' (hadm i hi s)
  · have hni : n ≤ i := by omega
    simp only [stoppedUpdate, ite_eq_right hi,
      backwardValue_terminal n b μ u F hni,
      backwardValue_terminal n b μ u F (show n ≤ i+1 by omega), sub_self,
      Real.exp_zero, Real.one_rpow, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]

theorem admissible_noiseCascade_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (hadm : ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ u F (i+1) (u i (s,a)))) (μ i : Measure A)) (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal A n ν).toReal)
    (∀ᵐ ν ∂P, 0 < terminalTreeFactor n b μ u F s ν ∧ terminalTreeFactor n b μ u F s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  let X := backwardValue n b μ u F
  let v := stoppedUpdate n u
  let c : ℕ → S × A → ℝ := fun i p => Real.exp (X (i+1) (v i p)-X i p.1)
  have hX : ∀ i, Measurable (X i) := measurable_backwardValue n b μ hu hF
  have hv : ∀ i, Measurable (v i) := measurable_stoppedUpdate n hu
  have hc : ∀ i, Measurable (c i) := fun i =>
    (((hX (i+1)).comp (hv i)).sub ((hX i).comp measurable_fst)).exp
  have hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A)) = 1 :=
    backwardValue_multiplier_moment_admissible n b μ u F (fun i hi => (hb.1 i hi).1) hadm
  have h := noiseCascade_log_integral n b hb μ hc hv (X := X) (fun _ _ _ => rfl) hm s
  have hX0 : X 0 s = cascadeRecursion n b μ u F s := by simp [X, backwardValue]
  simpa only [X, v, backwardValue_treeFactor, hX0] using h

end IsingPerceptron

namespace IsingPerceptron
variable {A : Type*} [MeasurableSpace A]

lemma logMean_mono (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    {F G : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ)
    (hG : Integrable (fun a => Real.exp (b*G a)) μ) (hFG : ∀ a, F a ≤ G a) :
    logMean b μ F ≤ logMean b μ G := by
  apply div_le_div_of_nonneg_right _ hb.le
  apply Real.log_le_log (integral_exp_pos μ F hF)
  apply integral_mono hF hG
  intro a
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hFG a) hb.le)

lemma logMean_const_add (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : b ≠ 0)
    {F : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ) (c : ℝ) :
    logMean b μ (fun a => c+F a) = c+logMean b μ F := by
  have he a : Real.exp (b*(c+F a)) = Real.exp (b*c)*Real.exp (b*F a) := by
    rw [mul_add, Real.exp_add]
  simp_rw [logMean, he, integral_const_mul]
  rw [Real.log_mul (Real.exp_ne_zero _) (integral_exp_pos μ F hF).ne', Real.log_exp]
  field_simp

end IsingPerceptron

namespace IsingPerceptron
variable {S : Type*} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

omit [MeasurableAdd₂ S] in
lemma integrable_exp_of_linearGrowth (μ : Measure S) (hμ : ExponentialNormMoments μ)
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F) (b : ℝ) :
    Integrable (fun s => Real.exp (b*F s)) μ := by
  obtain ⟨C,L,_,_,hbound⟩ := hG
  apply ((hμ (|b| *L)).const_mul (Real.exp (|b| *C))).mono'
    ((hF.const_mul b).exp).aestronglyMeasurable
  apply ae_of_all
  intro s
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    b*F s ≤ |b*F s| := le_abs_self _
    _ = |b| *|F s| := abs_mul _ _
    _ ≤ |b| *(C+L*‖s‖) := mul_le_mul_of_nonneg_left (hbound s) (abs_nonneg _)
    _ = |b| *C+(|b| *L)*‖s‖ := by ring

omit [MeasurableSpace S] [MeasurableAdd₂ S] in
lemma HasLinearGrowth.add_left {F : S → ℝ} (h : HasLinearGrowth F) (x : S) :
    HasLinearGrowth (fun a => F (x+a)) := by
  obtain ⟨C,L,hC,hL,h⟩ := h
  refine ⟨C+L*‖x‖, L, by positivity, hL, fun a => ?_⟩
  calc
    _ ≤ C+L*‖x+a‖ := h _
    _ ≤ C+L*(‖x‖+‖a‖) := add_le_add_right (mul_le_mul_of_nonneg_left (norm_add_le _ _) hL) C
    _ = C+L*‖x‖+L*‖a‖ := by ring

lemma logMean_hasLinearGrowth (μ : Measure S) [IsProbabilityMeasure μ]
    (hμ : ExponentialNormMoments μ) {F : S → ℝ} (hF : Measurable F)
    (hG : HasLinearGrowth F) {b : ℝ} (hb : 0 < b) :
    HasLinearGrowth (fun x => logMean b μ (fun a => F (x+a))) := by
  obtain ⟨C,L,hC,hL,hbound⟩ := hG
  have hG : HasLinearGrowth F := ⟨C,L,hC,hL,hbound⟩
  let U := logMean b μ (fun a : S => L*‖a‖)
  let D := logMean b μ (fun a : S => -L*‖a‖)
  have hiU : Integrable (fun a : S => Real.exp (b*(L*‖a‖))) μ := by
    simpa only [mul_assoc] using hμ (b*L)
  have hiD : Integrable (fun a : S => Real.exp (b*(-L*‖a‖))) μ := by
    simpa only [mul_assoc] using hμ (b*(-L))
  have hi (x : S) : Integrable (fun a => Real.exp (b*F (x+a))) μ :=
    integrable_exp_of_linearGrowth μ hμ (hF.comp (measurable_const.add measurable_id))
      (hG.add_left x) b
  refine ⟨C+|U|+|D|, L, by positivity, hL, fun x => ?_⟩
  have hup : logMean b μ (fun a => F (x+a)) ≤ (C+L*‖x‖)+U := by
    rw [← logMean_const_add μ hb.ne' hiU]
    apply logMean_mono μ hb (hi x)
    · convert hiU.const_mul (Real.exp (b*(C+L*‖x‖))) using 1
      all_goals try with_reducible_and_instances rfl
      ext a
      rw [mul_add, Real.exp_add]
    · intro a
      calc
        F (x+a) ≤ |F (x+a)| := le_abs_self _
        _ ≤ C+L*‖x+a‖ := hbound _
        _ ≤ C+L*(‖x‖+‖a‖) := by gcongr; exact norm_add_le _ _
        _ = (C+L*‖x‖)+L*‖a‖ := by ring
  have hlo : (-C-L*‖x‖)+D ≤ logMean b μ (fun a => F (x+a)) := by
    rw [← logMean_const_add μ hb.ne' hiD]
    refine logMean_mono μ hb ?_ (hi x) ?_
    · convert hiD.const_mul (Real.exp (b*(-C-L*‖x‖))) using 1
      all_goals try with_reducible_and_instances rfl
      ext a
      rw [mul_add, Real.exp_add]
    · intro a
      have hh := (abs_le.mp (hbound (x+a))).1
      have hn := mul_le_mul_of_nonneg_left (norm_add_le x a) hL
      linarith
  rw [abs_le]
  constructor
  · have := neg_abs_le D
    linarith [abs_nonneg U]
  · have := le_abs_self U
    linarith [abs_nonneg D]

lemma cascadeRecursion_linearGrowth (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hb : ∀ i < n, 0 < b i) :
    HasLinearGrowth (cascadeRecursion n b μ (fun _ p => p.1+p.2) F) := by
  induction n generalizing b μ with
  | zero => exact hG
  | succ n ih =>
    exact logMean_hasLinearGrowth _ (hμ 0 (by omega))
      (measurable_cascadeRecursion n (fun i => b (i+1)) (fun i => μ (i+1))
        (fun _ => measurable_fst.add measurable_snd) hF)
      (ih _ _ (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)))
      (hb 0 (by omega))

lemma backwardValue_linearGrowth_moments (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hb : ∀ i < n, 0 < b i) :
    ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ (fun _ p => p.1+p.2) F (i+1) (s+a))) (μ i : Measure S) := by
  intro i hi s
  apply integrable_exp_of_linearGrowth _ (hμ i hi)
    ((measurable_backwardValue n b μ (fun _ => measurable_fst.add measurable_snd) hF (i+1)).comp
      (measurable_const.add measurable_id))
  apply HasLinearGrowth.add_left
  unfold backwardValue
  exact cascadeRecursion_linearGrowth _ _ _ (fun j hj => hμ (i+1+j) (by omega)) hF hG
    (fun j hj => hb (i+1+j) (by omega))

end IsingPerceptron

namespace IsingPerceptron
lemma gaussianReal_exponentialNormMoments (m : ℝ) (v : ℝ≥0) :
    ExponentialNormMoments (gaussianReal m v) := by
  intro a
  simpa only [Real.norm_eq_abs] using integrable_exp_mul_abs
    (integrable_exp_mul_gaussianReal (μ := m) (v := v) a)
    (integrable_exp_mul_gaussianReal (μ := m) (v := v) (-a))

variable {S : Type} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

theorem linearGrowth_noiseCascade_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure S) (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F) (s : S) :
    let u : ℕ → S × S → S := fun _ p => p.1+p.2
    let P := (noiseCascadeLaw S n b μ : Measure (NoiseTree S n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal S n ν).toReal)
    (∀ᵐ ν ∂P, 0 < terminalTreeFactor n b μ u F s ν ∧ terminalTreeFactor n b μ u F s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact admissible_noiseCascade_recursion n b hb μ (fun _ => measurable_fst.add measurable_snd) hF
    (backwardValue_linearGrowth_moments n b μ hμ hF hG (fun i hi => (hb.1 i hi).1)) s

end IsingPerceptron

namespace IsingPerceptron

lemma abs_log_cosh_le (x : ℝ) : |Real.log (Real.cosh x)| ≤ |x| := by
  have hp := Real.cosh_pos x
  rw [abs_of_nonneg (Real.log_nonneg (Real.one_le_cosh x))]
  calc
    _ ≤ Real.log (Real.exp |x|) := by
      apply Real.log_le_log hp
      rw [Real.cosh_eq]
      have h₁ := Real.exp_le_exp.mpr (le_abs_self x)
      have h₂ := Real.exp_le_exp.mpr (neg_le_abs x)
      linarith
    _ = |x| := Real.log_exp _

lemma logCosh_linearGrowth : HasLinearGrowth (fun x : ℝ => Real.log (Real.cosh x)) := by
  refine ⟨0, 1, le_rfl, zero_le_one, fun x => ?_⟩
  simpa only [zero_add, one_mul, Real.norm_eq_abs] using abs_log_cosh_le x

lemma measurable_logCosh : Measurable (fun x : ℝ => Real.log (Real.cosh x)) :=
  Real.measurable_log.comp Real.continuous_cosh.measurable

lemma logMean_const_add_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {b : ℝ} {F : A → ℝ}
    (hF : Integrable (fun a => Real.exp (b*F a)) μ) (c : ℝ) :
    Integrable (fun a => Real.exp (b*(c+F a))) μ := by
  simpa only [mul_add,Real.exp_add] using hF.const_mul (Real.exp (b*c))

lemma logMean_abs_sub_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    {F G : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ)
    (hG : Integrable (fun a => Real.exp (b*G a)) μ) {C : ℝ}
    (h : ∀ a, |F a-G a| ≤ C) : |logMean b μ F-logMean b μ G| ≤ C := by
  apply abs_le.mpr
  have hu : logMean b μ F ≤ C+logMean b μ G := by
    rw [← logMean_const_add μ hb.ne' hG C]
    exact logMean_mono μ hb hF (logMean_const_add_integrable hG C)
      (fun a => by linarith [(abs_le.mp (h a)).2])
  have hl : logMean b μ G ≤ C+logMean b μ F := by
    rw [← logMean_const_add μ hb.ne' hF C]
    exact logMean_mono μ hb hG (logMean_const_add_integrable hF C)
      (fun a => by linarith [(abs_le.mp (h a)).1])
  constructor <;> linarith

theorem cascadeRecursion_lipschitz {S : Type*} [SeminormedAddCommGroup S]
    [MeasurableSpace S] [MeasurableAdd₂ S]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    {L : ℝ} (hLip : ∀ x y, |F x-F y| ≤ L*‖x-y‖)
    (hb : ∀ i < n, 0 < b i) :
    ∀ x y, |cascadeRecursion n b μ (fun _ p => p.1+p.2) F x-
      cascadeRecursion n b μ (fun _ p => p.1+p.2) F y| ≤ L*‖x-y‖ := by
  induction n generalizing b μ with
  | zero => exact hLip
  | succ n ih =>
    let G := cascadeRecursion n (fun i => b (i+1)) (fun i => μ (i+1)) (fun _ p => p.1+p.2) F
    have hGm : Measurable G := measurable_cascadeRecursion n _ _
      (fun _ => measurable_fst.add measurable_snd) hF
    have hGG : HasLinearGrowth G := cascadeRecursion_linearGrowth n _ _
      (fun i hi => hμ (i+1) (by omega)) hF hG (fun i hi => hb (i+1) (by omega))
    have hGi (x : S) : Integrable (fun a => Real.exp (b 0*G (x+a))) (μ 0 : Measure S) :=
      integrable_exp_of_linearGrowth _ (hμ 0 (by omega))
        (hGm.comp (measurable_const.add measurable_id)) (hGG.add_left x) _
    intro x y
    apply logMean_abs_sub_le _ (hb 0 (by omega)) (hGi x) (hGi y)
    intro a
    simpa only [add_sub_add_right_eq_sub] using ih (fun i => b (i+1)) (fun i => μ (i+1))
      (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)) (x+a) (y+a)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_EnrichedFieldCap
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledSpinReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [Fintype I] [MeasurableSingletonClass I] in
lemma finiteLogIntegral_eq_logMean (ν : Measure I) (H : I → ℝ) :
    finiteLogIntegral ν H = logMean 1 ν H := by simp [finiteLogIntegral,logMean]

lemma measurable_finiteLogIntegral (ν : Measure I) : Measurable (finiteLogIntegral ν) := by
  unfold finiteLogIntegral
  have hm : Measurable (fun p : (I → ℝ) × I => Real.exp (p.1 p.2)) :=
    measurable_from_prod_countable_left (fun i => (measurable_pi_apply i).exp)
  exact hm.stronglyMeasurable.integral_prod_right.measurable.log

lemma finiteLogIntegral_lipschitz (ν : Measure I) [IsProbabilityMeasure ν] (H G : I → ℝ) :
    |finiteLogIntegral ν H-finiteLogIntegral ν G| ≤ ‖H-G‖ := by
  rw [finiteLogIntegral_eq_logMean,finiteLogIntegral_eq_logMean]
  apply logMean_abs_sub_le ν (by norm_num)
    (show Integrable (fun x => Real.exp (1*H x)) ν from Integrable.of_finite)
    (show Integrable (fun x => Real.exp (1*G x)) ν from Integrable.of_finite)
  intro x
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (H-G) x

lemma finiteLogIntegral_linearGrowth (ν : Measure I) [IsProbabilityMeasure ν] :
    HasLinearGrowth (finiteLogIntegral ν) := by
  refine ⟨0,1,le_rfl,zero_le_one,fun H => ?_⟩
  simpa only [finiteLogIntegral,Pi.zero_apply,Real.exp_zero,integral_const,probReal_univ,
    one_smul,Real.log_one,sub_zero,one_mul,zero_add] using finiteLogIntegral_lipschitz ν H 0

lemma measurable_energyRecursion (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) :
    Measurable (energyRecursion n b μ ν) :=
  measurable_cascadeRecursion n b μ (fun _ => measurable_fst.add measurable_snd)
    (measurable_finiteLogIntegral ν)

lemma energyRecursion_lipschitz (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    (hb : ∀ i < n, 0 < b i) (H G : I → ℝ) :
    |energyRecursion n b μ ν H-energyRecursion n b μ ν G| ≤ ‖H-G‖ := by
  simpa only [one_mul,energyRecursion] using cascadeRecursion_lipschitz n b μ hμ
    (measurable_finiteLogIntegral ν) (finiteLogIntegral_linearGrowth ν)
    (L := 1) (fun H G => by simpa only [one_mul] using finiteLogIntegral_lipschitz ν H G) hb H G

omit [MeasurableSpace I] [MeasurableSingletonClass I] in

lemma finite_gaussian_exponentialNormMoments [Nonempty I] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → I → ℝ}
    (hX : Measurable X) (m : I → ℝ) (v : I → ℝ≥0)
    (hlaw : ∀ i, P.map (fun ω => X ω i) = gaussianReal (m i) (v i)) :
    ExponentialNormMoments (P.map X) := by
  intro a
  have hi (i : I) : Integrable (fun ω => Real.exp (|a| * |X ω i|)) P := by
    have hh := gaussianReal_exponentialNormMoments (m i) (v i) (|a|)
    rw [← hlaw i] at hh
    have hm : Measurable (fun ω => X ω i) := (measurable_pi_apply i).comp hX
    simpa only [Function.comp_def,Real.norm_eq_abs] using
      (integrable_map_measure (by fun_prop) hm.aemeasurable).mp hh
  apply (integrable_map_measure (by fun_prop) hX.aemeasurable).mpr
  apply (integrable_finsetSum Finset.univ (fun i _ => hi i)).mono'
  · fun_prop
  · apply ae_of_all
    intro ω
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i : I => |X ω i|) Finset.univ_nonempty
    have hn : ‖X ω‖ ≤ |X ω i| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      (fun j => by simpa only [Real.norm_eq_abs] using hi j (Finset.mem_univ _))
    change |Real.exp (a * ‖X ω‖)| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (|a| * |X ω i|) := Real.exp_le_exp.mpr
        (le_trans (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hn (abs_nonneg a)))
      _ ≤ ∑ j : I, Real.exp (|a| * |X ω j|) :=
        Finset.single_le_sum (f := fun j : I => Real.exp (|a| * |X ω j|)) (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

end IsingPerceptron

namespace IsingPerceptron

theorem variance_of_conditional_center {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} {X : A → ℝ} (hF : Measurable F) (hX : MemLp X 2 μ)
    (hi : ∀ a, Integrable (fun b => (F (a,b)-X a)^2) ν)
    (hc : ∀ a, ∫ b, F (a,b) ∂ν = X a) {C : ℝ}
    (hb : ∀ a, (∫ b, (F (a,b)-X a)^2 ∂ν) ≤ C) :
    MemLp F 2 (μ.prod ν) ∧ Var[F; μ.prod ν] ≤ C+Var[X; μ] := by
  let D : A × B → ℝ := fun p => F p-X p.1
  have hd : AEStronglyMeasurable D (μ.prod ν) :=
    hF.aestronglyMeasurable.sub (hX.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_fst (μ := μ) (ν := ν)))
  have hdi : Integrable (fun p => (D p)^2) (μ.prod ν) := by
    apply (integrable_prod_iff (hd.pow 2)).mpr
    refine ⟨ae_of_all _ hi, ?_⟩
    have hnorm : (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) =
        fun a => ∫ b, (D (a,b))^2 ∂ν := by
      ext a
      apply integral_congr_ae
      apply ae_of_all
      intro b
      exact Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) μ
    rw [hnorm]
    apply Integrable.of_bound (hd.pow 2).integral_prod_right' C
    apply ae_of_all
    intro a
    change ‖∫ b, (D (a,b))^2 ∂ν‖ ≤ C
    rw [Real.norm_of_nonneg (integral_nonneg (fun b => sq_nonneg (D (a,b))))]
    exact hb a
  have hDLp : MemLp D 2 (μ.prod ν) := (memLp_two_iff_integrable_sq hd).mpr hdi
  have hfLp : MemLp F 2 (μ.prod ν) := by
    convert hDLp.add (hX.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp [D]
  refine ⟨hfLp, ?_⟩
  have hsecLp (a : A) : MemLp (fun b => F (a,b)) 2 ν := by
    have hdm : Measurable (fun b => F (a,b)-X a) :=
      (hF.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    have hL := (memLp_two_iff_integrable_sq hdm.aestronglyMeasurable).mpr (hi a)
    convert hL.add (memLp_const (X a)) using 1
    all_goals try with_reducible_and_instances rfl
    ext b
    simp
  have hsec (a : A) : (∫ b, F (a,b)^2 ∂ν) ≤ C+(X a)^2 := by
    have hv := hb a
    have he := variance_eq_integral (hsecLp a).aemeasurable
    rw [hc a] at he
    rw [← he, variance_eq_sub (hsecLp a)] at hv
    simp only [Pi.pow_apply,hc a] at hv
    linarith
  have hh := integral_mono hfLp.integrable_sq.integral_prod_left
    ((integrable_const C).add hX.integrable_sq) hsec
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hX.integrable_sq,integral_const,
    probReal_univ,one_smul] at hh
  rw [variance_eq_sub hfLp,variance_eq_sub hX]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hfLp.integrable_sq,
    integral_prod _ (hfLp.integrable (by norm_num))]
  simp_rw [hc]
  linarith

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma measurable_cascadeEnergyLog (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) : Measurable (fun p : (I → ℝ) × NoiseTree (I → ℝ) n =>
      cascadeEnergyLog n b μ ν p.1 p.2) := by
  have hm := measurable_noiseTreeFactor n b μ
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd)
  simp only [noiseTreeFactor_terminal] at hm
  exact hm.ennreal_toReal.div
    (((measurable_noiseTreeTotal (I → ℝ) n).comp measurable_snd).ennreal_toReal) |>.log

theorem cascadeEnergyLog_conditional (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    let P := (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))
    Integrable (cascadeEnergyLog n b μ ν H) P ∧
      (∫ T, cascadeEnergyLog n b μ ν H T ∂P) = energyRecursion n b μ ν H ∧
      Integrable (fun T => (cascadeEnergyLog n b μ ν H T-energyRecursion n b μ ν H)^2) P ∧
      (∫ T, (cascadeEnergyLog n b μ ν H T-energyRecursion n b μ ν H)^2 ∂P) ≤
        4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact (linearGrowth_noiseCascade_recursion n b hb μ hμ
    (measurable_finiteLogIntegral ν) (finiteLogIntegral_linearGrowth ν) H).2

theorem cascadeEnergyLog_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    {H : Ω → I → ℝ} (hH : Measurable H) (hL : MemLp (fun ω => energyRecursion n b μ ν (H ω)) 2 P) :
    MemLp (fun p : Ω × NoiseTree (I → ℝ) n => cascadeEnergyLog n b μ ν (H p.1) p.2) 2
      (P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))) ∧
    Var[(fun p : Ω × NoiseTree (I → ℝ) n => cascadeEnergyLog n b μ ν (H p.1) p.2);
      P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))] ≤
        4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
          +Var[(fun ω => energyRecursion n b μ ν (H ω)); P] := by
  exact variance_of_conditional_center P _
    ((measurable_cascadeEnergyLog n b μ ν).comp ((hH.comp measurable_fst).prodMk measurable_snd)) hL
    (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.2.1)
    (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.1)
    (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.2.2)

end IsingPerceptron

namespace IsingPerceptron

lemma pair_left_injective (j : ℕ) : Function.Injective (Nat.pair j) := by
  intro a b h
  have := congrArg Nat.unpair h
  simpa only [Nat.unpair_pair,Prod.mk.injEq,true_and] using this

lemma tagCoefficients_other {j k : ℕ} (hjk : j ≠ k) (a : ℕ →₀ ℝ) (i : ℕ) :
    tagCoefficients j a (Nat.pair k i) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨v,hv⟩
  have := congrArg Nat.unpair hv
  simp only [Nat.unpair_pair,Prod.mk.injEq] at this
  exact hjk this.1

lemma cylinderCross_tag (j k : ℕ) (a b : ℕ →₀ ℝ) :
    cylinderCross (tagCoefficients j a) (tagCoefficients k b) =
      if j = k then cylinderCross a b else 0 := by
  classical
  unfold cylinderCross tagCoefficients
  rw [Finsupp.sum_mapDomain_index_inj (pair_left_injective j)]
  by_cases h : j = k
  · subst k
    simp only [ite_true,Finsupp.mapDomain_apply (pair_left_injective j)]
  · simp only [h,ite_false]
    change a.sum (fun i c => c*tagCoefficients k b (Nat.pair j i)) = 0
    simp only [tagCoefficients_other (Ne.symm h),mul_zero]
    simp [Finsupp.sum]

lemma cylinderCross_smul (r t : ℝ) (a b : ℕ →₀ ℝ) :
    cylinderCross (r • a) (t • b) = r*t*cylinderCross a b := by
  unfold cylinderCross
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  simp only [Finsupp.smul_apply,smul_eq_mul,Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma cylinderCross_sum_right {ι : Type*} (s : Finset ι) (a : ℕ →₀ ℝ) (b : ι → ℕ →₀ ℝ) :
    cylinderCross a (∑ i ∈ s, b i) = ∑ i ∈ s, cylinderCross a (b i) := by
  classical
  simp only [cylinderCross,Finsupp.finsetSum_apply,Finsupp.sum,Finset.mul_sum]
  exact Finset.sum_comm

lemma cylinderCross_tagged_sum {m : ℕ} (a b : Fin m → ℕ →₀ ℝ) :
    cylinderCross (∑ i : Fin m, tagCoefficients i (a i)) (∑ i : Fin m, tagCoefficients i (b i)) =
      ∑ i, cylinderCross (a i) (b i) := by
  classical
  rw [cylinderCross_finset_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [cylinderCross_sum_right]
  simp only [cylinderCross_tag,Fin.val_inj]
  simp

lemma externalFieldCoefficients_variance {N : ℕ} (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (s : Spin N × LabeledLeaf n) :
    (externalFieldCoefficients n h s).sum (fun _ c => c^2) = N*h n := by
  rw [← cylinderCross_self,externalFieldCoefficients,treeField_path_cross n _ _ hh h0,
    labeledCommonDepth_self]
  simp only [← pow_two,spinValue_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  ring

lemma perturbationWeight_sum (N : ℕ) :
    (∑ j : Fin N, perturbationWeight j) = 1-(1/2 : ℝ)^N := by
  rw [Fin.sum_univ_eq_sum_range]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [perturbationWeight,pow_succ]
    ring

lemma perturbationWeight_nonneg (j : ℕ) : 0 ≤ perturbationWeight j := by
  exact pow_nonneg (by norm_num) _
lemma perturbationWeight_le_one (j : ℕ) : perturbationWeight j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma enrichedCoefficients_variance_le {N : ℕ} (hN : 0 < N) (n : ℕ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ)
    (hu : ∀ j, |u j| ≤ 2) (s : Spin N × LabeledLeaf n) :
    (enrichedCoefficients n h u s).sum (fun _ c => c^2) ≤
      N*h n+4*N*(perturbationScale N)^2 := by
  rw [← cylinderCross_self,enrichedCoefficients,cylinderCross_tagged_sum,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ]
  simp_rw [cylinderCross_smul]
  simp_rw [cylinderCross_self]
  rw [externalFieldCoefficients_variance n hh h0]
  apply add_le_add_right
  calc
    _ ≤ ∑ j : Fin N, (4*N*(perturbationScale N)^2)*perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hv := monomialCoefficients_variance_le hN n (monomialIndex j).1 (monomialIndex j).2 s
      have hw := perturbationWeight_nonneg j
      have hw1 := perturbationWeight_le_one j
      have hu2 : (u j)^2 ≤ 4 := by
        have hab := abs_le.mp (hu j)
        nlinarith
      have hs : (Real.sqrt N)^2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
      have ho : (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) *
          (Real.sqrt N*perturbationScale N*perturbationWeight j*u j) =
          N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 := by
        calc
          _ = (Real.sqrt N)^2*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 := by ring
          _ = _ := by rw [hs]
      rw [ho]
      calc
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 :=
          mul_le_of_le_one_right (by positivity) hv
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*4 :=
          mul_le_mul_of_nonneg_left hu2 (by positivity)
        _ ≤ (4*N*(perturbationScale N)^2)*perturbationWeight j := by
          have hww : (perturbationWeight j)^2 ≤ perturbationWeight j := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hww (show 0 ≤ 4*N*(perturbationScale N)^2 by positivity)]
    _ = (4*N*(perturbationScale N)^2)*(1-(1/2 : ℝ)^N) := by
      rw [← Finset.mul_sum,perturbationWeight_sum]
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (by linarith [pow_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num) N])

lemma spinValue_abs (x : Fin 2) : |spinValue x| = 1 := by
  simp only [spinValue]
  split_ifs <;> norm_num

lemma spinCoordinate_abs {N : ℕ} (x : Spin N) (i : Fin N) :
    |spinCoordinate x i| = 1/Real.sqrt N := by
  simp only [spinCoordinate,abs_div,spinValue_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

lemma tensorFeature_spin_abs {N p : ℕ} (x : Spin N) (i : Fin p → Fin N) :
    |tensorFeature p (spinCoordinate x) i| = (1/Real.sqrt N)^p := by
  simp only [tensorFeature,Finset.abs_prod,spinCoordinate_abs,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

lemma enrichedLevelCoefficient_abs {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (i : ℕ) (x y : Spin N) (j : EnrichedBlock N) :
    |enrichedLevelCoefficient n h u i x j| = |enrichedLevelCoefficient n h u i y j| := by
  rcases j with j | ⟨j,t⟩
  · simp only [enrichedLevelCoefficient,abs_mul,spinValue_abs]
  · simp only [enrichedLevelCoefficient,abs_mul,tensorFeature_spin_abs]

lemma sum_scaled_cross {J : Type*} [Fintype J] (c : ℝ) (v w : J → ℝ) :
    (∑ j, (c*v j)*(c*w j)) = c^2*(∑ j, v j*w j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma enrichedLevelCoefficient_cross {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (i : ℕ) (x y : Spin N) :
    (∑ j : EnrichedBlock N, enrichedLevelCoefficient n h u i x j * enrichedLevelCoefficient n h u i y j) =
      N*pathIncrement h i*spinOverlap x y +
      ∑ j : Fin N, (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 *
        pathIncrement (monomialPath n (monomialIndex j).2) i * (spinOverlap x y)^(monomialIndex j).1 := by
  classical
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [enrichedLevelCoefficient]
  rw [sum_scaled_cross,pathAmplitude_sq hh h0]
  have he : (∑ j : Fin N, spinValue (x j)*spinValue (y j)) = N*spinOverlap x y := by
    rw [spinOverlap,mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne')]
  rw [he]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [sum_scaled_cross,tensorFeature_cross,spinCoordinate_cross,mul_pow,
      pathAmplitude_sq (monomialPath_monotone n _) (monomialPath_nonneg n _ 0)]

lemma enrichedLevelCoefficient_variance {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (i : ℕ) (x : Spin N) :
    (∑ j : EnrichedBlock N, (enrichedLevelCoefficient n h u i x j)^2) =
      N*pathIncrement h i +
      ∑ j : Fin N, (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 *
        pathIncrement (monomialPath n (monomialIndex j).2) i := by
  simpa only [← pow_two,spinOverlap_self hN,one_pow,mul_one] using
    enrichedLevelCoefficient_cross hN n hh h0 u i x x

lemma enrichedRoot_envelope_sq {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (x : Spin N) :
    (∑ j : EnrichedBlock N, |enrichedLevelCoefficient n h u 0 x j|^2) ≤ N*h 0+4*N*(perturbationScale N)^2 := by
  simp only [sq_abs,enrichedLevelCoefficient_variance hN n hh h0 u 0 x,pathIncrement]
  apply add_le_add_right
  calc
    _ ≤ ∑ j : Fin N, (4*N*(perturbationScale N)^2)*perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hv : monomialPath n (monomialIndex j).2 0 ≤ 1 :=
        (monomialPath_monotone n (monomialIndex j).2 (Nat.zero_le n)).trans
          (monomialPath_diag_le_one n (monomialIndex j).2)
      have hw := perturbationWeight_nonneg j
      have hw1 := perturbationWeight_le_one j
      have hu2 : (u j)^2 ≤ 4 := by
        have hab := abs_le.mp (hu j)
        nlinarith
      have he : (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 =
          N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 := by
        simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
      rw [he]
      calc
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 :=
          mul_le_of_le_one_right (by positivity) hv
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*4 :=
          mul_le_mul_of_nonneg_left hu2 (by positivity)
        _ ≤ (4*N*(perturbationScale N)^2)*perturbationWeight j := by
          have hww : (perturbationWeight j)^2 ≤ perturbationWeight j := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hww (show 0 ≤ 4*N*(perturbationScale N)^2 by positivity)]
    _ = (4*N*(perturbationScale N)^2)*(1-(1/2 : ℝ)^N) := by
      rw [← Finset.mul_sum,perturbationWeight_sum]
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (by linarith [pow_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num) N])

lemma variance_le_square_about_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) (a : ℝ) :
    Var[F; μ] ≤ ∫ x, (F x-a)^2 ∂μ := by
  have hs := variance_eq_sub (hF.sub (memLp_const a))
  simp only [Pi.sub_apply, Pi.pow_apply] at hs
  change Var[fun x => F x-a; μ] = _ at hs
  rw [variance_sub_const hF.aestronglyMeasurable a] at hs
  linarith [sq_nonneg (∫ x, F x-a ∂μ)]

lemma gaussian_coord_memLp {n : ℕ} {F : (Fin n → ℝ) → ℝ} {c : Fin n → ℝ}
    (hm : Measurable F)
    (hl : ∀ x y, |F x-F y| ≤ ∑ i, c i*|x i-y i|) (p : ℝ≥0) :
    MemLp F p (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hcoord (i : Fin n) : MemLp (fun x : Fin n → ℝ => c i*|x i|) p
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    have h := (memLp_id_gaussianReal p).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)
    simpa only [Function.comp_def, id_eq, Pi.abs_apply] using h.abs.const_mul (c i)
  have hb := (memLp_const |F 0|).add (memLp_finsetSum Finset.univ (fun i _ => hcoord i))
  apply hb.mono' hm.aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  have hx := hl x 0
  simp only [Pi.zero_apply, sub_zero] at hx
  simp only [Pi.add_apply, Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]

lemma gaussian_variance_of_slope {F : ℝ → ℝ} (hm : Measurable F) {c : ℝ}
    (hl : ∀ x y, |F x-F y| ≤ c*|x-y|) : Var[F; gaussianReal 0 1] ≤ c^2 := by
  have hLp : MemLp F 2 (gaussianReal 0 1) := by
    apply ((memLp_const |F 0|).add ((memLp_id_gaussianReal 2).abs.const_mul c)).mono'
      hm.aestronglyMeasurable
    refine Eventually.of_forall fun x => ?_
    have hx := hl x 0
    simp only [sub_zero] at hx
    simp only [Real.norm_eq_abs, Pi.add_apply, Pi.abs_apply, id_eq]
    linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]
  have hsq : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
    simpa only [variance_id_gaussianReal, NNReal.coe_one, integral_id_gaussianReal,
      sq, mul_zero, sub_zero, Pi.pow_apply, id_eq] using h.symm
  calc
    _ ≤ ∫ x, (F x-F 0)^2 ∂gaussianReal 0 1 := variance_le_square_about_const hLp _
    _ ≤ ∫ x : ℝ, c^2*x^2 ∂gaussianReal 0 1 := by
      apply integral_mono (hLp.sub (memLp_const _)).integrable_sq
        ((memLp_id_gaussianReal 2).integrable_sq.const_mul _)
      intro x
      have hx := hl x 0
      simp only [sub_zero] at hx
      have hh := pow_le_pow_left₀ (abs_nonneg (F x-F 0)) hx 2
      simpa only [sq_abs, mul_pow, Pi.sub_apply, id_eq] using hh
    _ = c^2 := by rw [integral_const_mul, hsq, mul_one]

lemma gaussian_slope_memLp {F : ℝ → ℝ} (hm : Measurable F) {c : ℝ}
    (hl : ∀ x y, |F x-F y| ≤ c*|x-y|) (p : ℝ≥0) :
    MemLp F p (gaussianReal 0 1) := by
  apply ((memLp_const |F 0|).add ((memLp_id_gaussianReal p).abs.const_mul c)).mono'
    hm.aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  have hx := hl x 0
  simp only [sub_zero] at hx
  simp only [Real.norm_eq_abs, Pi.add_apply, Pi.abs_apply, id_eq]
  linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]

lemma variance_prod_le_fiber {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hLp : MemLp F 2 (μ.prod ν))
    (hsecLp : ∀ b, MemLp (fun a => F (a,b)) 2 μ)
    (hGLp : MemLp (fun b => ∫ a, F (a,b) ∂μ) 2 ν) {C : ℝ}
    (hvar : ∀ b, Var[fun a => F (a,b); μ] ≤ C) :
    Var[F; μ.prod ν] ≤ C + Var[fun b => ∫ a, F (a,b) ∂μ; ν] := by
  have hsec : ∀ b, (∫ a, F (a,b)^2 ∂μ) ≤ C + (∫ a, F (a,b) ∂μ)^2 := by
    intro b
    have h := hvar b
    rw [variance_eq_sub (hsecLp b)] at h
    simp only [Pi.pow_apply] at h
    linarith
  have hs := integral_mono hLp.integrable_sq.integral_prod_right
    ((integrable_const C).add hGLp.integrable_sq) hsec
  simp only [Pi.add_apply] at hs
  rw [integral_add (integrable_const _) hGLp.integrable_sq, integral_const,
    probReal_univ, one_smul] at hs
  rw [variance_eq_sub hLp, variance_eq_sub hGLp]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hLp.integrable_sq,
    integral_prod_symm _ (hLp.integrable (by norm_num))]
  linarith

theorem gaussian_variance_coordinate_bound (n : ℕ) {F : (Fin n → ℝ) → ℝ}
    (hm : Measurable F) {c : Fin n → ℝ}
    (hl : ∀ x y, |F x-F y| ≤ ∑ i, c i*|x i-y i|) :
    Var[F; Measure.pi (fun _ : Fin n => gaussianReal 0 1)] ≤ ∑ i, (c i)^2 := by
  induction n with
  | zero =>
    have hF : F = fun _ => F (fun i : Fin 0 => i.elim0) := by
      funext x
      congr 1
      funext i
      exact i.elim0
    rw [hF, variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let μ := gaussianReal (0 : ℝ) (1 : ℝ≥0)
    let ν := Measure.pi (fun _ : Fin n => μ)
    have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) => (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using
          (measurable_fst : Measurable (Prod.fst : ℝ × (Fin n → ℝ) → ℝ))
      · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_snd : Measurable (Prod.snd : ℝ × (Fin n → ℝ) → (Fin n → ℝ)))
    have hFm : Measurable (fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)) := hm.comp hcons
    have hsm (x : Fin n → ℝ) : Measurable (fun a => F (Fin.cons a x)) :=
      hFm.comp (measurable_id.prodMk measurable_const)
    have hsl (x : Fin n → ℝ) : ∀ a b,
        |F (Fin.cons a x)-F (Fin.cons b x)| ≤ c 0*|a-b| := by
      intro a b
      simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        sub_self, abs_zero, mul_zero, Finset.sum_const_zero, add_zero] using
        hl (Fin.cons a x) (Fin.cons b x)
    have hsi (x : Fin n → ℝ) : Integrable (fun a => F (Fin.cons a x)) μ :=
      (gaussian_slope_memLp (hsm x) (hsl x) 1).integrable (by norm_num)
    have hGm : Measurable (fun x => ∫ a, F (Fin.cons a x) ∂μ) :=
      hFm.stronglyMeasurable.integral_prod_left'.measurable
    have hGl : ∀ x y, |(∫ a, F (Fin.cons a x) ∂μ)-(∫ a, F (Fin.cons a y) ∂μ)| ≤
        ∑ i : Fin n, c i.succ*|x i-y i| := by
      intro x y
      rw [← integral_sub (hsi x) (hsi y)]
      have hB (a : ℝ) : |F (Fin.cons a x)-F (Fin.cons a y)| ≤
          ∑ i : Fin n, c i.succ*|x i-y i| := by
        simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
          sub_self, abs_zero, mul_zero, zero_add] using hl (Fin.cons a x) (Fin.cons a y)
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const (μ := μ)
          (f := fun a => F (Fin.cons a x)-F (Fin.cons a y))
          (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hB a)))
    have hGLp := gaussian_coord_memLp hGm hGl 2
    have hpres := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
    have hLp : MemLp (fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)) 2 (μ.prod ν) := by
      have h := (gaussian_coord_memLp hm hl 2).comp_measurePreserving hpres
      simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove,
        cast_eq, ENNReal.coe_ofNat, ν] using h
    have hprod := variance_prod_le_fiber hLp
      (fun x => gaussian_slope_memLp (hsm x) (hsl x) 2) hGLp
      (fun x => gaussian_variance_of_slope (hsm x) (hsl x))
    have heq : Var[fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2); μ.prod ν] =
        Var[F; Measure.pi (fun _ : Fin (n+1) => μ)] := by
      have h := hpres.variance_fun_comp hm.aemeasurable
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] using h
    rw [heq] at hprod
    have ht := ih hGm hGl
    rw [Fin.sum_univ_succ]
    change _ ≤ c 0 ^ 2 + Var[(fun b => ∫ a, F (Fin.cons a b) ∂μ); ν] at hprod
    dsimp only [ν, μ] at hprod ht ⊢
    linarith

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_MemLpOfAbsBound
attribute [-instance] _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedForestCoordinates_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mem Lp Of Abs Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
lemma memLp_of_abs_bound {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsFiniteMeasure μ] {F : A → ℝ} (hm : Measurable F) {K : ℝ}
    (hb : ∀ a, |F a| ≤ K) (p : ℝ≥0∞) : MemLp F p μ :=
  MemLp.of_bound hm.aestronglyMeasurable K
    (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hb a))

lemma integral_abs_le_bound {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsProbabilityMeasure μ] {F : A → ℝ} {K : ℝ}
    (hb : ∀ a, |F a| ≤ K) : |∫ a, F a ∂μ| ≤ K := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := K)
      (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hb a)))

lemma variance_le_of_oscillation {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsProbabilityMeasure μ] {F : A → ℝ} (hm : Measurable F) {K c : ℝ}
    (hb : ∀ a, |F a| ≤ K) (hc : 0 ≤ c) (ho : ∀ a b, |F a - F b| ≤ c) :
    variance F μ ≤ c ^ 2 := by
  have hLp := memLp_of_abs_bound hm hb 2 (μ := μ)
  have hi := hLp.integrable (by norm_num)
  have hcenter : ∀ a, |F a - ∫ b, F b ∂μ| ≤ c := by
    intro a
    have h := integral_abs_le_bound (μ := μ) (F := fun b => F a - F b) (ho a)
    simpa only [integral_sub (integrable_const _) hi, integral_const,
      probReal_univ, one_smul] using h
  rw [variance_eq_integral hm.aemeasurable]
  have hisq := (hLp.sub (memLp_const (∫ a, F a ∂μ))).integrable_sq
  have h := integral_mono hisq (integrable_const (c ^ 2)) (fun a =>
    sq_le_sq.mpr (by simpa only [abs_of_nonneg hc, Pi.sub_apply] using hcenter a))
  simpa using h

lemma variance_prod_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hm : Measurable F) {K c : ℝ} (hb : ∀ z, |F z| ≤ K)
    (hc : 0 ≤ c) (ho : ∀ b a a', |F (a, b) - F (a', b)| ≤ c) :
    variance F (μ.prod ν) ≤ c ^ 2 + variance (fun b => ∫ a, F (a, b) ∂μ) ν := by
  have hLp := memLp_of_abs_bound hm hb 2 (μ := μ.prod ν)
  have hGm : Measurable (fun b => ∫ a, F (a, b) ∂μ) :=
    hm.stronglyMeasurable.integral_prod_left'.measurable
  have hGb : ∀ b, |∫ a, F (a, b) ∂μ| ≤ K := fun b =>
    integral_abs_le_bound (fun a => hb (a, b))
  have hGLp := memLp_of_abs_bound hGm hGb 2 (μ := ν)
  have hsec : ∀ b, (∫ a, F (a, b) ^ 2 ∂μ) ≤ c ^ 2 + (∫ a, F (a, b) ∂μ) ^ 2 := by
    intro b
    have hm' : Measurable (fun a => F (a, b)) := hm.comp (measurable_id.prodMk measurable_const)
    have h := variance_le_of_oscillation (μ := μ) hm' (fun a => hb (a, b)) hc (ho b)
    rw [variance_eq_sub (memLp_of_abs_bound hm' (fun a => hb (a, b)) 2)] at h
    simp only [Pi.pow_apply] at h
    linarith
  have hs := integral_mono hLp.integrable_sq.integral_prod_right
    ((integrable_const (c ^ 2)).add hGLp.integrable_sq) hsec
  simp only [Pi.add_apply] at hs
  rw [integral_add (integrable_const _) hGLp.integrable_sq, integral_const,
    probReal_univ, one_smul] at hs
  rw [variance_eq_sub hLp, variance_eq_sub hGLp]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hLp.integrable_sq,
    integral_prod_symm _ (hLp.integrable (by norm_num))]
  linarith

lemma variance_pi_boundedDifferences {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ)
    {F : (Fin n → A) → ℝ} (hm : Measurable F) {K c : ℝ}
    (hb : ∀ x, |F x| ≤ K) (hc : 0 ≤ c)
    (ho : ∀ (i : Fin n) x y, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c) :
    variance F (Measure.pi (fun _ : Fin n => μ)) ≤ n * c ^ 2 := by
  induction n with
  | zero =>
    have hF : F = fun _ => F (fun i : Fin 0 => i.elim0) := by
      funext x
      congr 1
      funext i
      exact i.elim0
    rw [hF, variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let ν := Measure.pi (fun _ : Fin n => μ)
    have hcons : Measurable (fun z : A × (Fin n → A) => (Fin.cons z.1 z.2 : Fin (n + 1) → A)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : A × (Fin n → A) → A))
      · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_snd : Measurable (Prod.snd : A × (Fin n → A) → (Fin n → A)))
    have hFm : Measurable (fun z : A × (Fin n → A) => F (Fin.cons z.1 z.2)) := hm.comp hcons
    have hGb : ∀ x, |∫ a, F (Fin.cons a x) ∂μ| ≤ K := fun x =>
      integral_abs_le_bound (fun a => hb (Fin.cons a x))
    have hGm : Measurable (fun x => ∫ a, F (Fin.cons a x) ∂μ) :=
      hFm.stronglyMeasurable.integral_prod_left'.measurable
    have hGosc : ∀ (i : Fin n) x y, (∀ j, j ≠ i → x j = y j) →
        |(∫ a, F (Fin.cons a x) ∂μ) - ∫ a, F (Fin.cons a y) ∂μ| ≤ c := by
      intro i x y hxy
      have hmsec : ∀ x : Fin n → A, Measurable (fun a => F (Fin.cons a x)) :=
        fun x => hFm.comp (measurable_id.prodMk measurable_const)
      have hisec : ∀ x : Fin n → A, Integrable (fun a => F (Fin.cons a x)) μ :=
        fun x => (memLp_of_abs_bound (hmsec x) (fun a => hb (Fin.cons a x)) 1).integrable le_rfl
      have h := integral_abs_le_bound (μ := μ) (F := fun a => F (Fin.cons a x) - F (Fin.cons a y))
        (fun a => ho i.succ (Fin.cons a x) (Fin.cons a y) (fun j => by
          refine Fin.cases ?_ (fun l => ?_) j
          · intro _; simp
          · intro hl
            simp only [Fin.cons_succ]
            exact hxy l (fun h => hl (congrArg Fin.succ h))))
      simpa only [integral_sub (hisec x) (hisec y)] using h
    have hsec : ∀ (x : Fin n → A) a a', |F (Fin.cons a x) - F (Fin.cons a' x)| ≤ c := by
      intro x a a'
      apply ho 0
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · intro h; exact (h rfl).elim
      · intro _; simp
    have hprod := variance_prod_le (μ := μ) (ν := ν) hFm
      (fun z => hb (Fin.cons z.1 z.2)) hc hsec
    have htail := ih hGm hGb hGosc
    have heq : variance (fun z : A × (Fin n → A) => F (Fin.cons z.1 z.2)) (μ.prod ν) =
        variance F (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
      have h := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).variance_fun_comp hm.aemeasurable
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] using h
    rw [heq] at hprod
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp only [ν] at hprod
    nlinarith

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma finite_linear_vector_bound {m : ℕ} {a : I → Fin m → ℝ} {c : Fin m → ℝ}
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) (g g' : Fin m → ℝ) :
    ‖(fun x => ∑ j, a x j * g j) - (fun x => ∑ j, a x j * g' j)‖ ≤
      ∑ j, c j * |g j-g' j| := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hc j) (abs_nonneg _)))).mpr
  intro x
  simp only [Pi.sub_apply,Real.norm_eq_abs,← Finset.sum_sub_distrib,← mul_sub]
  exact (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum (fun j _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (ha x j) (abs_nonneg _))

lemma measurable_rootEnergy (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) :
    Measurable (rootEnergy n b μ ν H a) := by
  apply (measurable_energyRecursion n b μ ν).comp
  fun_prop

lemma rootEnergy_gaussian_slope (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) (g g' : Fin m → ℝ) :
    |rootEnergy n b μ ν H a g-rootEnergy n b μ ν H a g'| ≤ ∑ j, c j*|g j-g' j| := by
  refine (energyRecursion_lipschitz n b μ ν hμ hb _ _).trans ?_
  have heq : (fun x => H x+∑ j, a x j*g j) - (fun x => H x+∑ j, a x j*g' j) =
      (fun x => ∑ j, a x j*g j) - (fun x => ∑ j, a x j*g' j) := by
    ext x
    simp only [Pi.sub_apply,add_sub_add_left_eq_sub]
  rw [heq]
  exact finite_linear_vector_bound hc ha g g'

theorem rootEnergy_gaussian_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) :
    Var[rootEnergy n b μ ν H a; Measure.pi (fun _ : Fin m => gaussianReal 0 1)] ≤ ∑ j, (c j)^2 :=
  gaussian_variance_coordinate_bound m (measurable_rootEnergy n b μ ν H a)
    (rootEnergy_gaussian_slope n b μ ν hμ hb H a c hc ha)

lemma rootEnergy_base_lipschitz (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H G : I → ℝ) (a : I → Fin m → ℝ) (g : Fin m → ℝ) :
    |rootEnergy n b μ ν H a g-rootEnergy n b μ ν G a g| ≤ ‖H-G‖ := by
  have he := energyRecursion_lipschitz n b μ ν hμ hb
    (fun x => H x+∑ j, a x j*g j) (fun x => G x+∑ j, a x j*g j)
  have heq : (fun x => H x+∑ j, a x j*g j) - (fun x => G x+∑ j, a x j*g j) = H-G := by
    ext x
    simp only [Pi.sub_apply,add_sub_add_right_eq_sub]
  rw [heq] at he
  exact he

variable {A : Type*} [MeasurableSpace A]

omit [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A] in
lemma patternBase_bound {M : ℕ} {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (y : Fin M → A) : ‖patternBase φ y‖ ≤ M*K := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg M) hK)).mpr
  intro x
  simp only [patternBase,Real.norm_eq_abs]
  calc
    _ ≤ ∑ r : Fin M, |φ (y r) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin M, K := Finset.sum_le_sum (fun r _ => hφ (y r) x)
    _ = _ := by simp

omit [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A] in
lemma patternBase_one_change {M : ℕ} {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (i : Fin M) (y y' : Fin M → A)
    (he : ∀ j, j ≠ i → y j=y' j) : ‖patternBase φ y-patternBase φ y'‖ ≤ 2*K := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hK)).mpr
  intro x
  have hsum : (∑ r : Fin M, (φ (y r) x-φ (y' r) x)) = φ (y i) x-φ (y' i) x := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [he j hji,sub_self]
    · simp
  simp only [Pi.sub_apply,patternBase,Real.norm_eq_abs,← Finset.sum_sub_distrib,hsum]
  linarith [abs_sub (φ (y i) x) (φ (y' i) x),hφ (y i) x,hφ (y' i) x]

theorem pattern_root_energy_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m M : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j)
    (P : Measure A) [IsProbabilityMeasure P] {φ : A → I → ℝ}
    (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K) :
    Var[(fun p : (Fin m → ℝ) × (Fin M → A) => rootEnergy n b μ ν (patternBase φ p.2) a p.1);
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))]
      ≤ (∑ j, (c j)^2)+M*(2*K)^2 := by
  let γ := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let ρ := Measure.pi (fun _ : Fin M => P)
  let F : (Fin m → ℝ) × (Fin M → A) → ℝ :=
    fun p => rootEnergy n b μ ν (patternBase φ p.2) a p.1
  let F₀ : (Fin m → ℝ) → ℝ := rootEnergy n b μ ν 0 a
  have hFm : Measurable F := by
    apply (measurable_energyRecursion n b μ ν).comp
    apply Measurable.of_eval
    intro x
    apply Measurable.add
    · exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hm).comp
        ((measurable_pi_apply r).comp measurable_snd)))
    · fun_prop
  have hfl (y : Fin M → A) : MemLp (fun g => F (g,y)) 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν (patternBase φ y) a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb (patternBase φ y) a c hc ha) 2
  have h0l : MemLp F₀ 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν 0 a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb 0 a c hc ha) 2
  have hdiff (g : Fin m → ℝ) (y : Fin M → A) : |F (g,y)-F₀ g| ≤ M*K := by
    exact (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) 0 a g).trans
      (by simpa only [sub_zero] using patternBase_bound hK hφ y)
  have hLp : MemLp F 2 (γ.prod ρ) := by
    have hz : MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => F₀ p.1) 2 (γ.prod ρ) :=
      h0l.comp_measurePreserving (measurePreserving_fst (μ := γ) (ν := ρ))
    apply (hz.abs.add (memLp_const (M*K))).mono' hFm.aestronglyMeasurable
    apply ae_of_all
    intro p
    simp only [Pi.add_apply,Pi.abs_apply,Real.norm_eq_abs]
    linarith [hdiff p.1 p.2,abs_sub_abs_le_abs_sub (F p) (F₀ p.1)]
  let G : (Fin M → A) → ℝ := fun y => ∫ g, F (g,y) ∂γ
  have hGm : Measurable G := hFm.stronglyMeasurable.integral_prod_left'.measurable
  have hGb (y : Fin M → A) : |G y| ≤ |∫ g, F₀ g ∂γ|+M*K := by
    have hh := integral_abs_le_bound (μ := γ) (fun g => hdiff g y)
    rw [integral_sub ((hfl y).integrable (by norm_num)) (h0l.integrable (by norm_num))] at hh
    dsimp only [G]
    linarith [abs_sub_abs_le_abs_sub (∫ g, F (g,y) ∂γ) (∫ g, F₀ g ∂γ)]
  have hGLp : MemLp G 2 ρ := memLp_of_abs_bound hGm hGb 2
  have hosc (i : Fin M) (y y' : Fin M → A) (he : ∀ j, j ≠ i → y j=y' j) :
      |G y-G y'| ≤ 2*K := by
    have hd (g : Fin m → ℝ) : |F (g,y)-F (g,y')| ≤ 2*K :=
      (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) (patternBase φ y') a g).trans
        (patternBase_one_change hK hφ i y y' he)
    have hh := integral_abs_le_bound (μ := γ) hd
    simpa only [integral_sub ((hfl y).integrable (by norm_num))
      ((hfl y').integrable (by norm_num)),G] using hh
  have hv := variance_prod_le_fiber hLp hfl hGLp
    (fun y => rootEnergy_gaussian_variance n b μ ν hμ hb (patternBase φ y) a c hc ha)
  have hbvar := variance_pi_boundedDifferences P M hGm hGb (by positivity : 0 ≤ 2*K) hosc
  change Var[F; γ.prod ρ] ≤ _
  change Var[G; ρ] ≤ _ at hbvar
  linarith

end IsingPerceptron

namespace IsingPerceptron

lemma enrichedIncrementLaw_moments (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ) :
    ExponentialNormMoments (enrichedIncrementLaw N n h u i : Measure (Spin N → ℝ)) := by
  apply finite_gaussian_exponentialNormMoments (measurable_enrichedIncrement N n h u i)
    (fun _ => 0) (fun x => (∑ j, (enrichedCoefficientsFin N n h u i x j)^2).toNNReal)
  intro x
  exact (gaussian_weighted_sum_law (enrichedCoefficientsFin N n h u i x)).map_eq

variable {I A : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A]

lemma pattern_root_energy_memLp (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m M : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j)
    (P : Measure A) [IsProbabilityMeasure P] {φ : A → I → ℝ}
    (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K) :
    MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => rootEnergy n b μ ν (patternBase φ p.2) a p.1) 2
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))) := by
  let γ := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let ρ := Measure.pi (fun _ : Fin M => P)
  let F : (Fin m → ℝ) × (Fin M → A) → ℝ :=
    fun p => rootEnergy n b μ ν (patternBase φ p.2) a p.1
  let F₀ : (Fin m → ℝ) → ℝ := rootEnergy n b μ ν 0 a
  have hFm : Measurable F := by
    apply (measurable_energyRecursion n b μ ν).comp
    apply Measurable.of_eval
    intro x
    apply Measurable.add
    · exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hm).comp
        ((measurable_pi_apply r).comp measurable_snd)))
    · fun_prop
  have h0l : MemLp F₀ 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν 0 a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb 0 a c hc ha) 2
  have hdiff (g : Fin m → ℝ) (y : Fin M → A) : |F (g,y)-F₀ g| ≤ M*K := by
    exact (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) 0 a g).trans
      (by simpa only [sub_zero] using patternBase_bound hK hφ y)
  have hLp : MemLp F 2 (γ.prod ρ) := by
    have hz : MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => F₀ p.1) 2 (γ.prod ρ) :=
      h0l.comp_measurePreserving (measurePreserving_fst (μ := γ) (ν := ρ))
    apply (hz.abs.add (memLp_const (M*K))).mono' hFm.aestronglyMeasurable
    apply ae_of_all
    intro p
    simp only [Pi.add_apply,Pi.abs_apply,Real.norm_eq_abs]
    linarith [hdiff p.1 p.2,abs_sub_abs_le_abs_sub (F p) (F₀ p.1)]
  exact hLp

end IsingPerceptron

namespace IsingPerceptron

lemma measurable_enrichedBaseEnergy {N M : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) {φ : A → Spin N → ℝ} (hφ : Measurable φ) :
    Measurable (enrichedBaseEnergy (M := M) n h u φ) := by
  apply Measurable.of_eval
  intro x
  exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hφ).comp
    ((measurable_pi_apply r).comp measurable_snd))).add
    (((measurable_pi_apply x).comp (measurable_enrichedIncrement N n h u 0)).comp measurable_fst)

lemma memLp_variance_shift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} {C : ℝ}
    (h : MemLp X 2 P ∧ Var[X;P] ≤ C) (c : ℝ) :
    MemLp (fun ω => X ω-c) 2 P ∧ Var[(fun ω => X ω-c);P] ≤ C := by
  refine ⟨h.1.sub (memLp_const _), ?_⟩
  rw [variance_sub_const h.1.aestronglyMeasurable]
  exact h.2

lemma poissonMass_succ (r : ℝ≥0) (n : ℕ) :
    poissonMass r (n+1) * (n+1) = r * poissonMass r n := by
  unfold poissonMass
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma poisson_first_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonMass r n * n) (r : ℝ) := by
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have he : (fun n : ℕ => poissonMass r (n+1) * (n+1)) =
      fun n => (r : ℝ) * poissonMass r n := funext (poissonMass_succ r)
  have hs' : HasSum (fun n : ℕ => poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)) (r : ℝ) := by
    simp only [Nat.cast_add,Nat.cast_one]
    rw [he]
    simpa only [mul_one,poissonMass] using hs
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => poissonMass r n * n) 1).mp hs'
  simpa [poissonMass] using h

lemma poisson_second_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonMass r n * (n : ℝ)^2) ((r : ℝ)^2+r) := by
  have hs := ((poisson_first_hasSum r).add (hasSum_one_poissonMeasure r)).mul_left (r : ℝ)
  have he (n : ℕ) : poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)^2 =
      (r : ℝ) * (poissonMass r n * n + poissonMass r n) := by
    push_cast
    calc
      _ = (poissonMass r (n+1) * (n+1)) * (n+1) := by ring
      _ = _ := by rw [poissonMass_succ]; ring
  have hs' : HasSum (fun n : ℕ => poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)^2)
      ((r : ℝ) * (r+1)) := by
    simp_rw [he]
    exact hs
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => poissonMass r n * (n : ℝ)^2) 1).mp hs'
  simpa [poissonMass, pow_two, mul_add] using h

lemma poisson_cast_memLp (r : ℝ≥0) : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq (Measurable.of_discrete.aestronglyMeasurable)).mpr
  apply integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_eq_abs, abs_sq, poissonMass] using
    (poisson_second_hasSum r).summable

lemma poisson_cast_mean (r : ℝ≥0) : (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  exact (poisson_first_hasSum r).tsum_eq

lemma poisson_cast_second (r : ℝ≥0) : (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2+r := by
  rw [integral_poissonMeasure]
  exact (poisson_second_hasSum r).tsum_eq

lemma poisson_cast_variance (r : ℝ≥0) : Var[(fun n : ℕ => (n : ℝ)); poissonMeasure r] = r := by
  rw [variance_eq_sub (poisson_cast_memLp r)]
  simp only [Pi.pow_apply, poisson_cast_second, poisson_cast_mean]
  ring

lemma integral_prod_sub_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ p : Ω × Ω, (X p.1-X p.2)^2 ∂P.prod P) = 2*Var[X;P] := by
  have hi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hLp : MemLp (fun p : Ω × Ω => X p.1-X p.2) 2 (P.prod P) :=
    (hX.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hX.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  rw [integral_prod _ hLp.integrable_sq]
  have he (x : Ω) : (∫ y, (X x-X y)^2 ∂P) =
      (X x)^2-2*X x*(∫ y, X y ∂P)+(∫ y, (X y)^2 ∂P) := by
    simp_rw [sub_sq]
    rw [integral_add (f := fun y => (X x)^2-2*X x*X y) (g := fun y => (X y)^2)
      ((integrable_const _).sub (hi.const_mul _)) hX.integrable_sq,
      integral_sub (f := fun _ => (X x)^2) (g := fun y => 2*X x*X y)
      (integrable_const _) (hi.const_mul _), integral_const,
      integral_const_mul, probReal_univ, one_smul]
  simp_rw [he]
  rw [integral_add (f := fun x => (X x)^2-2*X x*(∫ y, X y ∂P))
    (g := fun _ => ∫ y, (X y)^2 ∂P)
    (hX.integrable_sq.sub ((hi.const_mul 2).mul_const _)) (integrable_const _),
    integral_sub (f := fun x => (X x)^2) (g := fun x => 2*X x*(∫ y, X y ∂P))
      hX.integrable_sq ((hi.const_mul 2).mul_const _),integral_const,
    integral_mul_const,integral_const_mul,probReal_univ,one_smul,
    variance_eq_sub hX]
  simp only [Pi.pow_apply]
  ring

lemma variance_of_distance_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    {K : ℝ} (_hK : 0 ≤ K) (h : ∀ x y, |X x-X y| ≤ K*|Y x-Y y|) :
    Var[X;P] ≤ K^2 * Var[Y;P] := by
  have hDX := (hX.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hX.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  have hDY := (hY.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hY.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  have he := integral_mono hDX.integrable_sq (hDY.integrable_sq.const_mul (K^2))
    (show ∀ p : Ω × Ω, (X p.1-X p.2)^2 ≤ K^2*(Y p.1-Y p.2)^2 from fun p => by
      simpa only [mul_pow,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h p.1 p.2) 2)
  simp only [Pi.sub_apply,Function.comp_apply] at he
  rw [integral_const_mul,integral_prod_sub_sq P hX,integral_prod_sub_sq P hY] at he
  linarith

lemma nat_abs_step_bound {F : ℕ → ℝ} {K : ℝ} (h : ∀ m, |F (m+1)-F m| ≤ K) :
    ∀ m n, |F m-F n| ≤ K*|(m : ℝ)-n| := by
  have hle (n d : ℕ) : |F (n+d)-F n| ≤ K*d := by
    induction d with
    | zero => simp
    | succ d ih =>
      calc
        _ ≤ |F (n+d+1)-F (n+d)|+|F (n+d)-F n| := by
          simpa only [Nat.add_assoc] using abs_sub_le (F (n+d+1)) (F (n+d)) (F n)
        _ ≤ K+K*d := add_le_add (h (n+d)) ih
        _ = K*(d+1 : ℕ) := by push_cast; ring
  intro m n
  rcases le_total n m with hnm | hmn
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hnm
    simpa only [Nat.cast_add,add_sub_cancel_left,abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)] using hle n d
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [abs_sub_comm (F m) (F (m+d)),show (m : ℝ)-(m+d : ℕ) = -(d : ℝ) by push_cast; ring]
    simp only [abs_neg,abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    exact hle m d

lemma nat_step_memLp {P : Measure ℕ} [IsProbabilityMeasure P]
    (hP : MemLp (fun n : ℕ => (n : ℝ)) 2 P) {F : ℕ → ℝ} {K : ℝ}
    (h : ∀ m, |F (m+1)-F m| ≤ K) : MemLp F 2 P := by
  apply ((hP.const_mul K).add (memLp_const |F 0|)).mono' Measurable.of_discrete.aestronglyMeasurable
  apply ae_of_all
  intro m
  have hh := nat_abs_step_bound h m 0
  simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)] at hh
  simp only [Pi.add_apply,Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (F m) (F 0)]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_VarianceOfConditionalCenterBound
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderBaseLaw_probability _root_.OAI.IsingPerceptron.enrichedCylinderLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.markedReplicaLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

theorem variance_of_conditional_center_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} {X : A → ℝ} (hF : Measurable F) (hX : MemLp X 2 μ)
    (hi : ∀ a, Integrable (fun b => (F (a,b)-X a)^2) ν)
    (hc : ∀ a, ∫ b, F (a,b) ∂ν = X a) {C : A → ℝ} (hC : Integrable C μ)
    (hb : ∀ a, (∫ b, (F (a,b)-X a)^2 ∂ν) ≤ C a) :
    MemLp F 2 (μ.prod ν) ∧ Var[F; μ.prod ν] ≤ (∫ a, C a ∂μ)+Var[X; μ] := by
  let D : A × B → ℝ := fun p => F p-X p.1
  have hd : AEStronglyMeasurable D (μ.prod ν) :=
    hF.aestronglyMeasurable.sub (hX.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_fst (μ := μ) (ν := ν)))
  have hdi : Integrable (fun p => (D p)^2) (μ.prod ν) := by
    apply (integrable_prod_iff (hd.pow 2)).mpr
    refine ⟨ae_of_all _ hi, ?_⟩
    have hnorm : (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) =
        fun a => ∫ b, (D (a,b))^2 ∂ν := by
      ext a
      apply integral_congr_ae
      apply ae_of_all
      intro b
      exact Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) μ
    rw [hnorm]
    apply hC.mono' (hd.pow 2).integral_prod_right'
    apply ae_of_all
    intro a
    change ‖∫ b, (D (a,b))^2 ∂ν‖ ≤ C a
    rw [Real.norm_of_nonneg (integral_nonneg (fun b => sq_nonneg (D (a,b))))]
    exact hb a
  have hDLp : MemLp D 2 (μ.prod ν) := (memLp_two_iff_integrable_sq hd).mpr hdi
  have hfLp : MemLp F 2 (μ.prod ν) := by
    convert hDLp.add (hX.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp [D]
  refine ⟨hfLp, ?_⟩
  have hsecLp (a : A) : MemLp (fun b => F (a,b)) 2 ν := by
    have hdm : Measurable (fun b => F (a,b)-X a) :=
      (hF.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    have hL := (memLp_two_iff_integrable_sq hdm.aestronglyMeasurable).mpr (hi a)
    convert hL.add (memLp_const (X a)) using 1
    all_goals try with_reducible_and_instances rfl
    ext b
    simp
  have hsec (a : A) : (∫ b, F (a,b)^2 ∂ν) ≤ C a+(X a)^2 := by
    have hv := hb a
    have he := variance_eq_integral (hsecLp a).aemeasurable
    rw [hc a] at he
    rw [← he, variance_eq_sub (hsecLp a)] at hv
    simp only [Pi.pow_apply,hc a] at hv
    linarith
  have hh := integral_mono hfLp.integrable_sq.integral_prod_left
    (hC.add hX.integrable_sq) hsec
  simp only [Pi.add_apply] at hh
  rw [integral_add hC hX.integrable_sq] at hh
  rw [variance_eq_sub hfLp,variance_eq_sub hX]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hfLp.integrable_sq,
    integral_prod _ (hfLp.integrable (by norm_num))]
  simp_rw [hc]
  linarith

theorem poisson_count_variance {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (r : ℝ≥0) {F : ℕ × Ω → ℝ} (hF : Measurable F)
    (hL : ∀ m, MemLp (fun ω => F (m,ω)) 2 Q) {C D K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ m, Var[(fun ω => F (m,ω)); Q] ≤ C+D*m)
    (hs : ∀ m, |(∫ ω, F (m+1,ω) ∂Q)-(∫ ω, F (m,ω) ∂Q)| ≤ K) :
    MemLp F 2 ((poissonMeasure r).prod Q) ∧
      Var[F; (poissonMeasure r).prod Q] ≤ C+D*r+K^2*r := by
  let X := fun m => ∫ ω, F (m,ω) ∂Q
  have hx : MemLp X 2 (poissonMeasure r) := nat_step_memLp (poisson_cast_memLp r) hs
  have hc : Integrable (fun m : ℕ => C+D*m) (poissonMeasure r) :=
    (integrable_const C).add (((poisson_cast_memLp r).integrable (by norm_num)).const_mul D)
  have hh := variance_of_conditional_center_bound (poissonMeasure r) Q hF hx
    (fun m => ((hL m).sub (memLp_const (X m))).integrable_sq) (fun _ => rfl) hc
    (fun m => by
      rw [← variance_eq_integral (hL m).aemeasurable]
      exact hv m)
  refine ⟨hh.1, ?_⟩
  have hhx := variance_of_distance_bound (poissonMeasure r) hx (poisson_cast_memLp r) hK
    (nat_abs_step_bound hs)
  rw [poisson_cast_variance] at hhx
  have hmean : (∫ m : ℕ, C+D*m ∂poissonMeasure r) = C+D*r := by
    rw [integral_add (integrable_const C)
      (((poisson_cast_memLp r).integrable (by norm_num)).const_mul D),
      integral_const,probReal_univ,one_smul,integral_const_mul,poisson_cast_mean]
  rw [hmean] at hh
  linarith [hh.2]

lemma infinite_prefix_preserving {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (M : ℕ) :
    MeasurePreserving (fun y : ℕ → A => fun i : Fin M => y i)
      (Measure.infinitePi (fun _ : ℕ => P)) (Measure.pi (fun _ : Fin M => P)) := by
  refine ⟨Measurable.of_eval (fun index => measurable_pi_apply (index : ℕ)), ?_⟩
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

lemma rootPrefix_preserving {m : ℕ} {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (M : ℕ) :
    MeasurePreserving (rootPrefix (m := m) (A := A) M)
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.infinitePi (fun _ : ℕ => P)))
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))) :=
  (MeasurePreserving.id _).prod (infinite_prefix_preserving P M)

lemma patternBase_prefix_succ {I A : Type*} [Fintype I] (φ : A → I → ℝ)
    (y : ℕ → A) (M : ℕ) :
    patternBase φ (fun i : Fin (M+1) => y i) = patternBase φ (fun i : Fin M => y i)+φ (y M) := by
  ext x
  simp only [patternBase,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,Pi.add_apply]

lemma rootEnergy_prefix_step {I A : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (p : InfiniteRootData m A) (M : ℕ) :
    |rootEnergy n b μ ν (patternBase φ (fun i : Fin (M+1) => p.2 i)) a p.1-
      rootEnergy n b μ ν (patternBase φ (fun i : Fin M => p.2 i)) a p.1| ≤ K := by
  apply (rootEnergy_base_lipschitz n b μ ν hμ hb _ _ a p.1).trans
  rw [patternBase_prefix_succ,add_sub_cancel_left]
  exact (pi_norm_le_iff_of_nonneg hK).mpr (fun x => by simpa only [Real.norm_eq_abs] using hφ (p.2 M) x)

lemma integral_difference_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)
    {K : ℝ} (h : ∀ ω, |X ω-Y ω| ≤ K) : |(∫ ω, X ω ∂P)-(∫ ω, Y ω ∂P)| ≤ K := by
  rw [← integral_sub hX hY,← Real.norm_eq_abs]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => X ω-Y ω) (C := K)
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using h ω))

lemma cascadeEnergyLog_total_mean {Ω : Type*} {I : Type} [MeasurableSpace Ω] [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    {H : Ω → I → ℝ} (hH : Measurable H) (hL : MemLp (fun ω => energyRecursion n b μ ν (H ω)) 2 P) :
    (∫ p : Ω × NoiseTree (I → ℝ) n, cascadeEnergyLog n b μ ν (H p.1) p.2
      ∂P.prod (noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n))) =
      ∫ ω, energyRecursion n b μ ν (H ω) ∂P := by
  have hi := (cascadeEnergyLog_variance P n b hb μ ν hμ hH hL).1.integrable (by norm_num)
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => (cascadeEnergyLog_conditional n b hb μ ν hμ (H ω)).2.1)

variable {I A : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable [MeasurableSpace A]

lemma measurable_infinitePatternRoot (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (a : I → Fin m → ℝ) {φ : A → I → ℝ} (hm : Measurable φ) :
    Measurable (infinitePatternRoot n b μ ν a φ) := by
  apply measurable_from_prod_countable_right
  intro M
  apply (measurable_energyRecursion n b μ ν).comp
  apply Measurable.of_eval
  intro x
  exact (Finset.measurable_sum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) =>
    ((measurable_pi_apply x).comp hm).comp
    ((measurable_pi_apply (i : ℕ)).comp measurable_snd))).add
    (by fun_prop : Measurable (fun p : InfiniteRootData m A => ∑ j, a x j*p.1 j))

lemma infinitePatternRoot_fixed_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (ha : ∀ x j, |a x j| ≤ c j) (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → I → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (M : ℕ) :
    let Q := (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.infinitePi (fun _ : ℕ => P))
    MemLp (fun p => infinitePatternRoot n b μ ν a φ (M,p)) 2 Q ∧
      Var[(fun p => infinitePatternRoot n b μ ν a φ (M,p));Q] ≤ (∑ j, (c j)^2)+M*(2*K)^2 := by
  have hL := pattern_root_energy_memLp n b μ ν hμ hb a c hc ha P hm hK hφ (M := M)
  have hv := pattern_root_energy_variance n b μ ν hμ hb a c hc ha P hm hK hφ (M := M)
  have hp := rootPrefix_preserving (m := m) P M
  constructor
  · simpa only [infinitePatternRoot, Function.comp_def, rootPrefix] using
      hL.comp_measurePreserving hp
  · simpa only [infinitePatternRoot, Function.comp_def, rootPrefix] using
      (hp.variance_fun_comp hL.aemeasurable).le.trans hv

theorem infinitePatternRoot_poisson_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (ha : ∀ x j, |a x j| ≤ c j) (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → I → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (r : ℝ≥0) :
    let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
    MemLp (infinitePatternRoot n b μ ν a φ) 2 Q ∧
      Var[infinitePatternRoot n b μ ν a φ;Q] ≤ (∑ j, (c j)^2)+(2*K)^2*r+K^2*r := by
  have hh := infinitePatternRoot_fixed_variance n b μ ν hμ hb a c hc ha P hm hK hφ
  apply poisson_count_variance _ r (measurable_infinitePatternRoot n b μ ν a hm)
    (fun M => (hh M).1) hK
  · intro M
    simpa only [mul_comm (M : ℝ)] using (hh M).2
  · intro M
    apply integral_difference_bound _ ((hh (M+1)).1.integrable (by norm_num))
      ((hh M).1.integrable (by norm_num))
    exact fun p => rootEnergy_prefix_step n b μ ν hμ hb a hK hφ p M

end IsingPerceptron

namespace IsingPerceptron

lemma enriched_poisson_root_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : ∀ i < n, 0 < b i) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
    let X := infinitePatternRoot n b μ ν (enrichedCoefficientsFin N n h u 0) φ
    MemLp X 2 Q ∧ Var[X;Q] ≤ N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  let x₀ : Spin N := fun _ => 0
  let c := fun j => |enrichedCoefficientsFin N n h u 0 x₀ j|
  have H := infinitePatternRoot_poisson_variance n b
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1)) hb
    (enrichedCoefficientsFin N n h u 0) c (fun _ => abs_nonneg _)
    (fun x j => (enrichedLevelCoefficient_abs n h u 0 x x₀ _).le) P hm hK hφ r
  have hc : (∑ j, (c j)^2) ≤ N*h 0+4*N*(perturbationScale N)^2 := by
    have he := (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
      (fun j => |enrichedLevelCoefficient n h u 0 x₀ j|^2)
    change (∑ j, |enrichedLevelCoefficient n h u 0 x₀ ((Fintype.equivFin _).symm j)|^2) ≤ _
    rw [he]
    exact enrichedRoot_envelope_sq hN n hh h0 u hu x₀
  refine ⟨H.1, ?_⟩
  linarith [H.2]

lemma measurable_enrichedPoissonBase {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (enrichedPoissonBase n h u φ) := by
  apply measurable_from_prod_countable_right
  intro M
  exact (measurable_enrichedBaseEnergy n h u hm).comp
    (measurable_fst.prodMk (Measurable.of_eval (fun index : Fin M =>
      (measurable_pi_apply (index : ℕ)).comp measurable_snd)))

lemma enriched_poisson_unshifted {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))).prod
        (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    let X := fun p : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n =>
      cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1) p.2
    MemLp X 2 Q ∧ Var[X;Q] ≤
      4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  have hr := enriched_poisson_root_variance hN n b (fun i hi => (hb.1 i hi).1) hh h0 u hu ν P hm hK hφ r
  have hv := cascadeEnergyLog_variance _ n b hb
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1))
    (measurable_enrichedPoissonBase n h u hm) hr.1
  refine ⟨hv.1, ?_⟩
  have hrv : Var[(fun p => energyRecursion n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (enrichedPoissonBase n h u φ p)); _] ≤ N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := hr.2
  linarith [hv.2,hrv]

theorem enriched_poisson_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))).prod
        (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    MemLp (enrichedPoissonLog n b h u ν φ) 2 Q ∧ Var[enrichedPoissonLog n b h u ν φ;Q] ≤
      4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  exact memLp_variance_shift _
    (enriched_poisson_unshifted hN n b hb hh h0 u hu ν P hm hK hφ r) (N*h n/2)

lemma perturbationScale_le_one {N : ℕ} (hN : 0 < N) : perturbationScale N ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast hN
  · norm_num

lemma perturbationScale_nonneg (N : ℕ) : 0 ≤ perturbationScale N :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma field_cap_arithmetic {N : ℕ} (hN : 0 < N) {C H h₀ e K r α : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e) (he1 : e ≤ 1) (hh : h₀ ≤ H)
    (hr : r ≤ α*N) :
    (C+N*h₀+4*N*e^2+5*K^2*r) / (N:ℝ)^2 ≤ (C+H+4+5*K^2*α)/N := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hc : C ≤ N*C := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hh hn.le
  have he' : 4*N*e^2 ≤ 4*N := by
    have : e^2 ≤ 1 := by nlinarith
    nlinarith
  have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ 5*K^2 by positivity)
  apply (div_le_iff₀ (sq_pos_of_pos hn)).2
  have hid : (C+H+4+5*K^2*α)/N*(N:ℝ)^2 = (C+H+4+5*K^2*α)*N := by
    field_simp
  rw [hid]
  nlinarith

theorem enriched_field_cap_variance {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := ((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))).prod
        (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    let X := fun p => enrichedPoissonLog n b h u ν φ p / N
    MemLp X 2 Q ∧ Var[X;Q] ≤ (C+H+4+5*K^2*α)/N := by
  have hv := enriched_poisson_variance hN n b hb hh h0 u hu ν P hm hK hφ r
  refine ⟨by simpa only [div_eq_mul_inv] using hv.1.mul_const ((N:ℝ)⁻¹), ?_⟩
  simp only [div_eq_mul_inv, variance_mul_const]
  have hh' : h 0 ≤ H := (hh (Nat.zero_le n)).trans hH
  have hc : 0 ≤ 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
    positivity
  have ha := field_cap_arithmetic hN hc (perturbationScale_nonneg N)
    (perturbationScale_le_one hN) hh' hr (K := K)
  have ha' : (4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +N*h 0+4*N*(perturbationScale N)^2+5*K^2*r)*(N:ℝ)⁻¹^2 ≤
      (4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
      +H+4+5*K^2*α)*(N:ℝ)⁻¹ := by
    simpa only [div_eq_mul_inv, inv_pow] using ha
  exact (mul_le_mul_of_nonneg_right hv.2 (sq_nonneg _)).trans ha'

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma labeled_terminal_integral (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z)))
    (ht : 0 < noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) ∧
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) < ∞)
    {X : ℕ → S → ℝ} {u : ℕ → S × A → S}
    (hX : ∀ i, Measurable (X i)) (hu : ∀ i, Measurable (u i)) (s : S) :
    (∫ γ, Real.exp (noiseLeafTerminal n X u s (labeledNoiseLeaf A n (ω,z) γ))
      ∂labeledLeafLaw n ω) =
    ∫ v, Real.exp (noiseLeafTerminal n X u s v)
      ∂noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  rw [← labeledLeafLaw_noiseMap A n ω z hgood ht]
  exact (integral_map (measurable_of_countable _).aemeasurable
    (((measurable_noiseLeafTerminal n hX hu).comp
      (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable)).symm

lemma cascadeEnergyLog_eq_leaf_integral (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) (H : I → ℝ) :
    ∀ᵐ T ∂(noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)),
      cascadeEnergyLog n b μ ν H T =
      Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
        (fun _ p => p.1 + p.2) H v) ∂noiseLeafKernel (I → ℝ) n T) := by
  have hfac := noiseTreeFactor_leafIntegral n b hb μ
    (X := fun _ => finiteLogIntegral ν) (u := fun _ p => p.1+p.2)
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd) H
  have htot : ∀ᵐ T ∂(noiseCascadeLaw (I → ℝ) n b μ : Measure (NoiseTree (I → ℝ) n)),
      0 < noiseTreeTotal (I → ℝ) n T ∧ noiseTreeTotal (I → ℝ) n T < ∞ := by
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget (I → ℝ) n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  filter_upwards [hfac,htot] with T hfac ht
  simp only [noiseTreeFactor_terminal] at hfac
  unfold cascadeEnergyLog
  rw [hfac, ENNReal.toReal_mul]
  have ht0 : (noiseTreeTotal (I → ℝ) n T).toReal ≠ 0 :=
    (ENNReal.toReal_pos ht.1.ne' ht.2.ne).ne'
  rw [mul_div_cancel_left₀ _ ht0]
  congr 1
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun v => (Real.exp_pos _).le))
    (((measurable_noiseLeafTerminal n (fun _ => measurable_finiteLogIntegral ν)
      (fun _ => measurable_fst.add measurable_snd)).comp
        (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable)).symm

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labeledEnergy_terminal (n : ℕ) (ω : LabeledTree n) (z : MarkForest (I → ℝ) n)
    (γ : LabeledLeaf n) (F : (I → ℝ) → ℝ) (H : I → ℝ) :
    noiseLeafTerminal n (fun _ => F) (fun _ p => p.1 + p.2) H
      (labeledNoiseLeaf (I → ℝ) n (ω,z) γ) = F (labeledEnergy n z γ H) := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih => exact ih _ _ _ _

lemma labeledEnergyLog_eq_leaf (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν]
    (H : I → ℝ) (p : LabeledTree n × MarkForest (I → ℝ) n) :
    labeledEnergyLog n ν H p = Real.log (∫ γ,
      Real.exp (finiteLogIntegral ν (labeledEnergy n p.2 γ H)) ∂labeledLeafLaw n p.1) := by
  have hE : Measurable (fun s : I × LabeledLeaf n => Real.exp (labeledEnergy n p.2 s.2 H s.1)) :=
    measurable_of_countable _
  have hF : Measurable (fun γ : LabeledLeaf n => Real.exp (finiteLogIntegral ν (labeledEnergy n p.2 γ H))) :=
    measurable_of_countable _
  unfold labeledEnergyLog labeledSpinReference
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hE.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hF.aestronglyMeasurable]
  congr 1
  rw [lintegral_prod _ hE.ennreal_ofReal.aemeasurable,
    lintegral_lintegral_swap hE.ennreal_ofReal.aemeasurable]
  apply lintegral_congr
  intro γ
  rw [finiteLogIntegral, Real.exp_log (MeasureTheory.integral_exp_pos Integrable.of_finite)]
  exact (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite (ae_of_all _ (fun _ => (Real.exp_pos _).le))).symm

theorem labeledEnergyLog_eq_cascade (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν] (H : I → ℝ) :
    ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (markForestLaw (I → ℝ) n μ)),
      labeledEnergyLog n ν H p =
        cascadeEnergyLog n b μ ν H (labeledNoiseJoin (I → ℝ) n p) := by
  have hgood : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)), GoodNoiseTree (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) := by
    apply ae_of_ae_map (measurable_labeledNoiseJoin (I → ℝ) n).aemeasurable
    rw [labeledNoiseJoin_law]
    exact noiseCascade_good (I → ℝ) n b hb μ
  have htot : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)),
      0 < noiseTreeTotal (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) ∧
      noiseTreeTotal (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p) < ∞ := by
    apply ae_of_ae_map (p := fun T : NoiseTree (I → ℝ) n =>
      0 < noiseTreeTotal (I → ℝ) n T ∧ noiseTreeTotal (I → ℝ) n T < ∞)
      (measurable_labeledNoiseJoin (I → ℝ) n).aemeasurable
    rw [labeledNoiseJoin_law]
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget (I → ℝ) n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  have he : ∀ᵐ p ∂((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)),
      cascadeEnergyLog n b μ ν H (labeledNoiseJoin (I → ℝ) n p) =
      Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => finiteLogIntegral ν)
        (fun _ p => p.1+p.2) H v) ∂noiseLeafKernel (I → ℝ) n (labeledNoiseJoin (I → ℝ) n p)) := by
    apply ae_of_ae_map (p := fun T : NoiseTree (I → ℝ) n =>
      cascadeEnergyLog n b μ ν H T = Real.log (∫ v, Real.exp (noiseLeafTerminal n
        (fun _ => finiteLogIntegral ν) (fun _ p => p.1+p.2) H v) ∂noiseLeafKernel (I → ℝ) n T))
      (measurable_labeledNoiseJoin (I → ℝ) n).aemeasurable
    rw [labeledNoiseJoin_law]
    exact cascadeEnergyLog_eq_leaf_integral n b hb μ ν H
  filter_upwards [hgood,htot,he] with p hg ht he
  rw [he,labeledEnergyLog_eq_leaf]
  congr 1
  have hm := labeled_terminal_integral n p.1 p.2 hg ht
    (X := fun _ => finiteLogIntegral ν) (u := fun _ p => p.1+p.2)
    (fun _ => measurable_finiteLogIntegral ν) (fun _ => measurable_fst.add measurable_snd) H
  simpa only [labeledEnergy_terminal] using hm

end IsingPerceptron

namespace IsingPerceptron

lemma measurable_enrichedForest (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) :
    Measurable (enrichedForest N n h u) := by
  apply (measurable_markForestOfCoords (Spin N → ℝ) n).comp
  exact Measurable.of_eval (fun vertex =>
    (measurable_enrichedIncrement N n h u (forestVertexDepth n vertex+1)).comp (measurable_pi_apply vertex))

theorem enrichedForest_law (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) :
    (enrichedForestCoordinates N n).map (enrichedForest N n h u) =
      markForestLaw (Spin N → ℝ) n (fun i => enrichedIncrementLaw N n h u (i+1)) := by
  change (enrichedForestCoordinates N n).map
    ((markForestOfCoords (Spin N → ℝ) n) ∘
      (fun g v => enrichedIncrement N n h u (forestVertexDepth n v+1) (g v))) = _
  have hm : Measurable (fun g : ForestVertex n → Fin (EnrichedRootSize N) → ℝ =>
      fun v => enrichedIncrement N n h u (forestVertexDepth n v+1) (g v)) := by
    exact Measurable.of_eval (fun vertex =>
      (measurable_enrichedIncrement N n h u (forestVertexDepth n vertex+1)).comp (measurable_pi_apply vertex))
  rw [← Measure.map_map (measurable_markForestOfCoords (Spin N → ℝ) n) hm]
  unfold enrichedForestCoordinates
  rw [Measure.infinitePi_map_pi _ (fun v => measurable_enrichedIncrement N n h u (forestVertexDepth n v+1))]
  exact markForestOfCoords_law (Spin N → ℝ) n (fun i => enrichedIncrementLaw N n h u (i+1))

theorem labeledEnrichedCoordinates_law (N n : ℕ) (b h : ℕ → ℝ) (u : Fin N → ℝ) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (enrichedForestCoordinates N n)).map
      (fun p => labeledNoiseJoin (Spin N → ℝ) n (p.1,enrichedForest N n h u p.2)) =
      noiseCascadeLaw (Spin N → ℝ) n b (fun i => enrichedIncrementLaw N n h u (i+1)) := by
  have hp := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
    (show MeasurePreserving (enrichedForest N n h u) (enrichedForestCoordinates N n)
      (markForestLaw (Spin N → ℝ) n (fun i => enrichedIncrementLaw N n h u (i+1))) from
        ⟨measurable_enrichedForest N n h u, enrichedForest_law N n h u⟩)
  change _ = _
  rw [show (fun p => labeledNoiseJoin (Spin N → ℝ) n (p.1,enrichedForest N n h u p.2)) =
    (labeledNoiseJoin (Spin N → ℝ) n) ∘ Prod.map id (enrichedForest N n h u) from rfl,
    ← Measure.map_map (measurable_labeledNoiseJoin (Spin N → ℝ) n) hp.measurable,
    hp.map_eq, labeledNoiseJoin_law]

variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_labeledEnergy (n : ℕ) (γ : LabeledLeaf n) :
    Measurable (fun p : MarkForest (I → ℝ) n × (I → ℝ) => labeledEnergy n p.1 γ p.2) := by
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
    exact (ih γ.2).comp (show Measurable (fun p : MarkForest (I → ℝ) (n+1) × (I → ℝ) =>
      ((p.1 γ.1.1 γ.1.2).2,p.2+(p.1 γ.1.1 γ.1.2).1)) from by fun_prop)

lemma measurable_labeledEnergyLog (n : ℕ) (ν : Measure I) [IsProbabilityMeasure ν] :
    Measurable (fun p : (I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n) =>
      labeledEnergyLog n ν p.1 p.2) := by
  let κ : Kernel ((I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n)) (LabeledLeaf n) :=
    ⟨fun p => labeledLeafLaw n p.2.1,(measurable_labeledLeafLaw n).comp (by fun_prop)⟩
  have : IsMarkovKernel κ := ⟨fun _ => labeledLeafLaw_probability _ _⟩
  have hm : Measurable (fun p : ((I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n)) × LabeledLeaf n =>
      Real.exp (finiteLogIntegral ν (labeledEnergy n p.1.2.2 p.2 p.1.1))) := by
    apply measurable_swap_iff.mp
    apply measurable_from_prod_countable_right
    intro γ
    exact ((measurable_finiteLogIntegral ν).comp
      ((measurable_labeledEnergy n γ).comp
        (show Measurable (fun p : (I → ℝ) × (LabeledTree n × MarkForest (I → ℝ) n) =>
          (p.2.2,p.1)) from by fun_prop))).exp
  simpa only [labeledEnergyLog_eq_leaf, κ, Kernel.coe_mk] using
    (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable.log

theorem labeledEnergyLog_eq_cascade_random {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    {H : Ω → I → ℝ} (hmH : Measurable H) :
    ∀ᵐ p ∂P.prod ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw (I → ℝ) n μ)),
      labeledEnergyLog n ν (H p.1) p.2 =
        cascadeEnergyLog n b μ ν (H p.1) (labeledNoiseJoin (I → ℝ) n p.2) := by
  have hbase : Measurable (fun p : Ω × (LabeledTree n × MarkForest (I → ℝ) n) =>
      (H p.1,p.2)) := (hmH.comp measurable_fst).prodMk measurable_snd
  have hjoin : Measurable (fun p : Ω × (LabeledTree n × MarkForest (I → ℝ) n) =>
      (H p.1,labeledNoiseJoin (I → ℝ) n p.2)) :=
    (hmH.comp measurable_fst).prodMk ((measurable_labeledNoiseJoin (I → ℝ) n).comp measurable_snd)
  have hl := (measurable_labeledEnergyLog n ν).comp hbase
  have hr := (measurable_cascadeEnergyLog n b μ ν).comp hjoin
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hl hr)).mpr
    (ae_of_all _ (fun ω => labeledEnergyLog_eq_cascade n b hb μ ν (H ω)))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_EnergyShift
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy Shift. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma enrichedToNoise_preserving {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) :
    MeasurePreserving (enrichedToNoise (A := A) n h u) (enrichedCoordinateLaw P r N n b)
      (((poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
        (Measure.infinitePi (fun _ : ℕ => P)))).prod
          (noiseCascadeLaw (Spin N → ℝ) n b (fun i => enrichedIncrementLaw N n h u (i+1)))) := by
  have hf : Measurable (fun p : LabeledTree n × (ForestVertex n → Fin (EnrichedRootSize N) → ℝ) =>
      (p.1,enrichedForest N n h u p.2)) :=
    measurable_fst.prodMk ((measurable_enrichedForest N n h u).comp measurable_snd)
  have hp : MeasurePreserving
      (fun p : LabeledTree n × (ForestVertex n → Fin (EnrichedRootSize N) → ℝ) =>
        labeledNoiseJoin (Spin N → ℝ) n (p.1,enrichedForest N n h u p.2))
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (enrichedForestCoordinates N n))
      (noiseCascadeLaw (Spin N → ℝ) n b (fun i => enrichedIncrementLaw N n h u (i+1))) :=
    ⟨(measurable_labeledNoiseJoin (Spin N → ℝ) n).comp hf,
      labeledEnrichedCoordinates_law N n b h u⟩
  exact (MeasurePreserving.id _).prod hp

 

theorem enrichedCoordinatePressure_eq_noise {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (hb : CascadeExponents n b) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    enrichedCoordinatePressure n h u ν φ =ᵐ[enrichedCoordinateLaw P r N n b]
      (fun p => enrichedPoissonLog n b h u ν φ (enrichedToNoise n h u p) / N) := by
  let Q := (poissonMeasure r).prod
    ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
  let μ := fun i => enrichedIncrementLaw N n h u (i+1)
  have hpF : MeasurePreserving (enrichedForest N n h u) (enrichedForestCoordinates N n)
      (markForestLaw (Spin N → ℝ) n μ) :=
    ⟨measurable_enrichedForest N n h u,enrichedForest_law N n h u⟩
  have hpT := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod hpF
  have hp := (MeasurePreserving.id Q).prod hpT
  have he := labeledEnergyLog_eq_cascade_random Q n b hb μ ν (measurable_enrichedPoissonBase n h u hm)
  have he' : ∀ᵐ p ∂enrichedCoordinateLaw P r N n b,
      labeledEnergyLog n ν (enrichedPoissonBase n h u φ p.1)
        (p.2.1,enrichedForest N n h u p.2.2) =
      cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1)
        (labeledNoiseJoin (Spin N → ℝ) n (p.2.1,enrichedForest N n h u p.2.2)) := by
    apply ae_of_ae_map (p := fun p : EnrichedPoissonRoot N A ×
        (LabeledTree n × MarkForest (Spin N → ℝ) n) =>
      labeledEnergyLog n ν (enrichedPoissonBase n h u φ p.1) p.2 =
        cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1)
          (labeledNoiseJoin (Spin N → ℝ) n p.2)) hp.measurable.aemeasurable
    rw [show enrichedCoordinateLaw P r N n b = Q.prod
      ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod (enrichedForestCoordinates N n)) from rfl,
      hp.map_eq]
    exact he
  filter_upwards [he'] with p he
  unfold enrichedCoordinatePressure enrichedPoissonLog enrichedToNoise
  dsimp only
  rw [he]

 

theorem enrichedCoordinatePressure_field_cap {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N) :
    let Q := enrichedCoordinateLaw P r N n b
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    let X := enrichedCoordinatePressure n h u ν φ
    MemLp X 2 Q ∧ Var[X;Q] ≤ (C+H+4+5*K^2*α)/N := by
  have hv := enriched_field_cap_variance hN n b hb hh h0 hH u hu ν P hm hK hφ r hr
  have hp := enrichedToNoise_preserving P r n b h u
  have he := enrichedCoordinatePressure_eq_noise P r n b h hb u ν hm
  have hL := hv.1.comp_measurePreserving hp
  refine ⟨MemLp.ae_eq he.symm hL, ?_⟩
  have ht := variance_map (X := fun p => enrichedPoissonLog n b h u ν φ p / N)
    (hp.map_eq.symm ▸ hv.1.aemeasurable) hp.measurable.aemeasurable
  rw [hp.map_eq] at ht
  simp only [Function.comp_def] at ht
  rw [variance_congr he, ← ht]
  exact hv.2

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma nodeAddress_injective (n : ℕ) : Function.Injective (nodeAddress n) := by
  induction n with
  | zero =>
    intro v w _
    cases v with
    | none => cases w with
      | none => rfl
      | some w => exact w.elim
    | some v => exact v.elim
  | succ n ih =>
    intro v w h
    cases v with
    | none => cases w with
      | none => rfl
      | some w => simp [nodeAddress] at h
    | some v => cases w with
      | none => simp [nodeAddress] at h
      | some w =>
        rcases v with ⟨m,i,v⟩
        rcases w with ⟨m',i',w⟩
        simp only [nodeAddress,List.cons.injEq,Prod.mk.injEq] at h
        rcases h with ⟨⟨rfl,rfl⟩,h⟩
        rw [ih h]


lemma nodeAddress_nodeAt (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    nodeAddress n (nodeAt n γ i) = (labeledAddress n γ).take i := by
  induction n with
  | zero => simp [nodeAt,nodeAddress,labeledAddress]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [nodeAt,nodeAddress]
    · simp [nodeAt,nodeAddress,labeledAddress,ih]

lemma nodeAddress_length_some (n : ℕ) (v : ForestVertex n) :
    (nodeAddress n (some v)).length = forestVertexDepth n v+1 := by
  induction n with
  | zero => exact v.elim
  | succ n ih =>
    rcases v with ⟨m,i,_ | v⟩
    · simp [nodeAddress,forestVertexDepth]
    · simp only [nodeAddress,List.length_cons,ih,forestVertexDepth,Nat.add_assoc]

lemma nodeAddress_nodeAt_length (n : ℕ) (γ : LabeledLeaf n) (i : Fin (n+1)) :
    (nodeAddress n (nodeAt n γ i)).length = i := by
  rw [nodeAddress_nodeAt,List.length_take,labeledAddress_length]
  exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)


lemma enrichedNodeTag_injective (N n : ℕ) :
    Function.Injective (fun p : Option (ForestVertex n) × EnrichedBlock N => enrichedNodeTag p.1 p.2) := by
  rintro ⟨v,a⟩ ⟨w,b⟩ h
  cases a with
  | inl a => cases b with
    | inl b =>
      have he := Encodable.encode_inj.mp (Nat.pair_eq_pair.mp h).2
      have hv : v = w := nodeAddress_injective n (congrArg (fun p => p.2.1) he)
      have hab : a = b := congrArg (fun p => p.2.2) he
      subst w; subst b; rfl
    | inr b =>
      have h' := (Nat.pair_eq_pair.mp h).1
      omega
  | inr a => cases b with
    | inl b =>
      have h' := (Nat.pair_eq_pair.mp h).1
      omega
    | inr b =>
      rcases a with ⟨j,t⟩
      rcases b with ⟨k,s⟩
      have hj : j = k := Fin.ext (by have h' := (Nat.pair_eq_pair.mp h).1; exact Nat.add_right_cancel h')
      subst k
      have he := Encodable.encode_inj.mp (Nat.pair_eq_pair.mp h).2
      have hv : v = w := nodeAddress_injective n (congrArg (fun p => p.2.1) he)
      have hts : t = s := congrArg (fun p => p.2.2) he
      subst w; subst s; rfl



lemma measurable_enrichedGaussianNodes (N n : ℕ) :
    Measurable (enrichedGaussianNodes N n) := by
  unfold enrichedGaussianNodes
  fun_prop

theorem enrichedGaussianNodes_law (N n : ℕ) :
    gaussianCoordinates.map (enrichedGaussianNodes N n) =
      Measure.infinitePi (fun _ : Option (ForestVertex n) =>
        Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)) := by
  let t : Option (ForestVertex n) × Fin (EnrichedRootSize N) → ℕ :=
    fun p => enrichedNodeTag p.1 ((Fintype.equivFin (EnrichedBlock N)).symm p.2)
  have ht : Function.Injective t := by
    intro p q h
    have he := @enrichedNodeTag_injective N n
      (p.1,(Fintype.equivFin (EnrichedBlock N)).symm p.2)
      (q.1,(Fintype.equivFin (EnrichedBlock N)).symm q.2) h
    have he' := Prod.mk.inj he
    exact Prod.ext he'.1 ((Fintype.equivFin (EnrichedBlock N)).symm.injective he'.2)
  have hp := gaussian_pullback_measurePreserving t ht
  change gaussianCoordinates.map
    ((MeasurableEquiv.curry (Option (ForestVertex n)) (Fin (EnrichedRootSize N)) ℝ) ∘
      (fun g => fun p => g (t p))) = _
  rw [← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hp.measurable,hp.map_eq,
    Measure.infinitePi_map_curry (fun (_ : Option (ForestVertex n)) (_ : Fin (EnrichedRootSize N)) => gaussianReal 0 1)]
  simp only [Measure.infinitePi_eq_pi]

 
theorem enrichedGaussianRootForest_law (N n : ℕ) :
    gaussianCoordinates.map (fun g =>
      (enrichedGaussianNodes N n g none, fun v => enrichedGaussianNodes N n g (some v))) =
      (Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
        (enrichedForestCoordinates N n) := by
  change gaussianCoordinates.map
    ((fun q : Option (ForestVertex n) → Fin (EnrichedRootSize N) → ℝ =>
      (q none,fun v => q (some v))) ∘ enrichedGaussianNodes N n) = _
  rw [← Measure.map_map (by fun_prop) (measurable_enrichedGaussianNodes N n),enrichedGaussianNodes_law]
  have he := infinitePi_option_split
    (Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))
    (fun _ : ForestVertex n => Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))
  have hc : (fun i : Option (ForestVertex n) => i.elim
      (Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))
      (fun _ => Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1))) =
      (fun _ => Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)) := by
    funext i; cases i <;> rfl
  simpa only [hc,enrichedForestCoordinates] using he

lemma cylinderField_tag (j : ℕ) (a : ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (tagCoefficients j a) g = cylinderField a (fun i => g (Nat.pair j i)) := by
  unfold cylinderField tagCoefficients
  rw [Finsupp.sum_mapDomain_index_inj (pair_left_injective j)]

lemma cylinderField_feature {J : Type*} [Fintype J] (t : J → ℕ) (a : J → ℝ) (g : ℕ → ℝ) :
    cylinderField (featureCoefficients t a) g = ∑ j, a j*g (t j) := by
  classical
  rw [featureCoefficients,cylinderField_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact Finsupp.sum_single_index (by simp)

lemma nodeAt_zero (n : ℕ) (γ : LabeledLeaf n) : nodeAt n γ 0 = none := by
  cases n <;> simp [nodeAt]

lemma nodeAt_succ (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    nodeAt n γ i.succ = some (edgeAt n γ i) := by
  cases n with
  | zero => exact i.elim0
  | succ n => simp [nodeAt,edgeAt]

lemma labeledEnergy_edge_sum {I : Type} (n : ℕ) (g : ForestVertex n → I → ℝ)
    (γ : LabeledLeaf n) (H : I → ℝ) (x : I) :
    labeledEnergy n (markForestOfCoords (I → ℝ) n g) γ H x =
      H x + ∑ i : Fin n, g (edgeAt n γ i) x := by
  induction n generalizing H with
  | zero => simp [labeledEnergy]
  | succ n ih =>
    rw [labeledEnergy,markForestOfCoords,ih,Fin.sum_univ_succ]
    simp only [edgeAt,nodeAt_zero,nodeAt_succ,Pi.add_apply]
    ring

lemma labeledEnergy_node_sum {I : Type} (n : ℕ) (g : Option (ForestVertex n) → I → ℝ)
    (γ : LabeledLeaf n) (H : I → ℝ) (x : I) :
    labeledEnergy n (markForestOfCoords (I → ℝ) n (fun v => g (some v))) γ (H+g none) x =
      H x + ∑ i : Fin (n+1), g (nodeAt n γ i) x := by
  rw [labeledEnergy_edge_sum,Fin.sum_univ_succ]
  simp only [nodeAt_zero,nodeAt_succ,Pi.add_apply]
  ring

lemma enrichedIncrement_nodes (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ)
    (g : ℕ → ℝ) (v : Option (ForestVertex n)) (x : Spin N) :
    enrichedIncrement N n h u i (enrichedGaussianNodes N n g v) x =
      ∑ a : EnrichedBlock N, enrichedLevelCoefficient n h u i x a * g (enrichedNodeTag v a) := by
  unfold enrichedIncrement enrichedCoefficientsFin enrichedGaussianNodes
  exact (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
    (fun a => enrichedLevelCoefficient n h u i x a * g (enrichedNodeTag v a))

lemma cylinderField_external_nodes {N : ℕ} (n : ℕ) (h : ℕ → ℝ)
    (x : Spin N) (γ : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tagCoefficients 0 (externalFieldCoefficients n h (x,γ))) g =
      ∑ i : Fin (n+1), ∑ a : Fin N,
        pathAmplitude h i * spinValue (x a) * g (enrichedNodeTag (nodeAt n γ i) (.inl a)) := by
  rw [cylinderField_tag,externalFieldCoefficients,treeFieldCoefficients,cylinderField_feature,
    Fintype.sum_prod_type]
  simp only [enrichedNodeTag]
  simp_rw [nodeAddress_nodeAt_length,nodeAddress_nodeAt]
  simp only [treeFeatureTag]

lemma cylinderField_monomial_nodes {N : ℕ} (n : ℕ) (j : Fin N) (c : ℝ)
    (x : Spin N) (γ : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (tagCoefficients (j+1) (c • monomialCoefficients n (monomialIndex j).1
      (monomialIndex j).2 (x,γ))) g =
      ∑ i : Fin (n+1), ∑ a : Fin (monomialIndex j).1 → Fin N,
        (c * pathAmplitude (monomialPath n (monomialIndex j).2) i *
          tensorFeature (monomialIndex j).1 (spinCoordinate x) a) *
            g (enrichedNodeTag (nodeAt n γ i) (.inr ⟨j,a⟩)) := by
  rw [cylinderField_tag,cylinderField_smul,monomialCoefficients,treeFieldCoefficients,
    cylinderField_feature,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [enrichedNodeTag]
  simp_rw [nodeAddress_nodeAt_length,nodeAddress_nodeAt]
  simp only [treeFeatureTag]
  ring

lemma cylinderField_enriched_nodes {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (x : Spin N) (γ : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (enrichedCoefficients n h u (x,γ)) g =
      ∑ i : Fin (n+1), ∑ a : EnrichedBlock N,
        enrichedLevelCoefficient n h u i x a * g (enrichedNodeTag (nodeAt n γ i) a) := by
  classical
  rw [enrichedCoefficients,cylinderField_finset_sum,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.val_zero,Fin.val_succ,
    cylinderField_external_nodes,cylinderField_monomial_nodes]
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,enrichedLevelCoefficient,
    Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

 

theorem enrichedEnergy_eq_cylinder {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (g : ℕ → ℝ) (H : Spin N → ℝ) (x : Spin N) (γ : LabeledLeaf n) :
    labeledEnergy n (enrichedForest N n h u
      (fun v => enrichedGaussianNodes N n g (some v))) γ
      (H+enrichedIncrement N n h u 0 (enrichedGaussianNodes N n g none)) x =
      H x + cylinderField (enrichedCoefficients n h u (x,γ)) g := by
  let F : Option (ForestVertex n) → Spin N → ℝ := fun v =>
    enrichedIncrement N n h u (nodeAddress n v).length (enrichedGaussianNodes N n g v)
  have he := labeledEnergy_node_sum n F γ H x
  have hf : (fun v => F (some v)) =
      (fun v => enrichedIncrement N n h u (forestVertexDepth n v+1)
        (enrichedGaussianNodes N n g (some v))) := by
    funext v
    simp only [F,nodeAddress_length_some]
  have h0 : F none = enrichedIncrement N n h u 0 (enrichedGaussianNodes N n g none) := by
    simp only [F,nodeAddress,List.length_nil]
  rw [hf,h0] at he
  rw [cylinderField_enriched_nodes]
  simpa only [F,nodeAddress_nodeAt_length,enrichedIncrement_nodes,enrichedForest] using he

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

private lemma preserving_three_rotate {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun p : (A × B) × C => (p.1.1,(p.2,p.1.2)))
      ((μ.prod ν).prod ρ) (μ.prod (ρ.prod ν)) :=
  ((MeasurePreserving.id μ).prod Measure.measurePreserving_swap).comp
    (measurePreserving_prodAssoc μ ν ρ)

private lemma preserving_four_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (τ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μ.prod ν).prod (ρ.prod τ)) ((μ.prod ρ).prod (ν.prod τ)) := by
  have h1 := (measurePreserving_prodAssoc (μ.prod ν) ρ τ).symm MeasurableEquiv.prodAssoc
  have h2 := ((measurePreserving_prodAssoc μ ρ ν).symm MeasurableEquiv.prodAssoc).comp
    (preserving_three_rotate μ ν ρ)
  exact (measurePreserving_prodAssoc (μ.prod ρ) ν τ).comp
    ((h2.prod (MeasurePreserving.id τ)).comp h1)

theorem enrichedCylinderToCoordinates_preserving {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (N n : ℕ) (b : ℕ → ℝ) :
    MeasurePreserving (enrichedCylinderToCoordinates (A := A) N n)
      (enrichedCylinderLaw P r n b) (enrichedCoordinateLaw P r N n b) := by
  let μ := poissonMeasure r
  let ν := Measure.infinitePi (fun _ : ℕ => P)
  let ρ := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let γ := Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)
  let τ := enrichedForestCoordinates N n
  have hn : MeasurePreserving (fun g =>
      (enrichedGaussianNodes N n g none,fun v => enrichedGaussianNodes N n g (some v)))
      gaussianCoordinates (γ.prod τ) :=
    ⟨(by unfold enrichedGaussianNodes; fun_prop),enrichedGaussianRootForest_law N n⟩
  have h1 := (MeasurePreserving.id ((μ.prod ν).prod ρ)).prod hn
  have h2 := preserving_four_shuffle (μ.prod ν) ρ γ τ
  have h3 := (preserving_three_rotate μ ν γ).prod (MeasurePreserving.id (ρ.prod τ))
  exact h3.comp (h2.comp h1)



theorem enrichedCylinderPressure_eq_coordinates {N : ℕ} {A : Type*}
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (ν : Measure (Spin N))
    (φ : A → Spin N → ℝ) (p : EnrichedCylinderData n A) :
    enrichedCylinderPressure n h u ν φ p =
      enrichedCoordinatePressure n h u ν φ (enrichedCylinderToCoordinates N n p) := by
  unfold enrichedCylinderPressure enrichedCoordinatePressure enrichedCylinderToCoordinates
    labeledEnergyLog enrichedPoissonBase enrichedBaseEnergy rootPrefix
  dsimp only
  congr 3
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  exact (enrichedEnergy_eq_cylinder n h u p.2
    (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i)) s.1 s.2).symm

 

theorem enrichedCylinderPressure_field_cap {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {H : ℝ} (hH : h n ≤ H) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {α : ℝ} (hr : (r:ℝ) ≤ α*N) :
    let Q := enrichedCylinderLaw P r n b
    let C := 4*∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n))
    let X := enrichedCylinderPressure n h u ν φ
    MemLp X 2 Q ∧ Var[X;Q] ≤ (C+H+4+5*K^2*α)/N := by
  have hv := enrichedCoordinatePressure_field_cap hN n b hb hh h0 hH u hu ν P hm hK hφ r hr
  have hp := enrichedCylinderToCoordinates_preserving P r N n b
  have he : enrichedCylinderPressure n h u ν φ =
      (enrichedCoordinatePressure n h u ν φ) ∘ enrichedCylinderToCoordinates N n := by
    funext p
    exact enrichedCylinderPressure_eq_coordinates n h u ν φ p
  have hL := hv.1.comp_measurePreserving hp
  refine ⟨he ▸ hL, ?_⟩
  have ht := variance_map (X := enrichedCoordinatePressure n h u ν φ)
    (hp.map_eq.symm ▸ hv.1.aemeasurable) hp.measurable.aemeasurable
  rw [hp.map_eq] at ht
  rw [he, ← ht]
  exact hv.2

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_NamespaceSplit
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Namespace Split. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_gaussianNamespaceSplit (j : ℕ) : Measurable (gaussianNamespaceSplit j) := by
  unfold gaussianNamespaceSplit
  fun_prop

lemma gaussianNamespaceSplit_law (j : ℕ) :
    gaussianCoordinates.map (gaussianNamespaceSplit j) =
      gaussianCoordinates.prod (otherNamespacesLaw j) := by
  let e := Equiv.optionSubtypeNe j
  let t : Option {k : ℕ // k ≠ j} × ℕ → ℕ := fun p => Nat.pair (e p.1) p.2
  have ht : Function.Injective t := by
    intro p q h
    have he := Nat.pair_eq_pair.mp h
    exact Prod.ext (e.injective he.1) he.2
  have hp := gaussian_pullback_measurePreserving t ht
  let F : (ℕ → ℝ) → Option {k : ℕ // k ≠ j} → ℕ → ℝ := fun g k i => g (t (k,i))
  have hmF : Measurable F := by unfold F; fun_prop
  have hF : gaussianCoordinates.map F = Measure.infinitePi
      (fun _ : Option {k : ℕ // k ≠ j} => gaussianCoordinates) := by
    change gaussianCoordinates.map
      ((MeasurableEquiv.curry (Option {k : ℕ // k ≠ j}) ℕ ℝ) ∘
        (fun g => fun p => g (t p))) = _
    rw [← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hp.measurable,hp.map_eq,
      Measure.infinitePi_map_curry (fun (_ : Option {k : ℕ // k ≠ j}) (_ : ℕ) => gaussianReal 0 1)]
    rfl
  have hs := infinitePi_option_split gaussianCoordinates
    (fun _ : {k : ℕ // k ≠ j} => gaussianCoordinates)
  have hc : (fun i : Option {k : ℕ // k ≠ j} =>
      i.elim gaussianCoordinates (fun _ => gaussianCoordinates)) = (fun _ => gaussianCoordinates) := by
    funext i; cases i <;> rfl
  rw [hc] at hs
  have he : gaussianNamespaceSplit j =
      (fun q : Option {k : ℕ // k ≠ j} → ℕ → ℝ => (q none,fun k => q (some k))) ∘ F := by
    rfl
  rw [he,← Measure.map_map (by fun_prop) hmF,hF]
  exact hs

end IsingPerceptron

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators
namespace IsingPerceptron

lemma gibbsProbability_eq_tilted {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) :
    gibbsProbability ν H = ν.tilted H := by
  exact ite_eq_right (ne_of_gt (_root_.MeasureTheory.integral_exp_pos he))

lemma integrable_exp_bounded_add {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {H B : X → ℝ} (he : Integrable (fun x => Real.exp (H x)) ν)
    (hB : Measurable B) {K : ℝ} (hbound : ∀ x, B x ≤ K) :
    Integrable (fun x => Real.exp (B x+H x)) ν := by
  have hm : AEStronglyMeasurable (fun x => Real.exp (H x)*Real.exp (B x)) ν :=
    he.aestronglyMeasurable.mul hB.exp.aestronglyMeasurable
  apply (he.const_mul (Real.exp K)).mono'
  · simpa only [Real.exp_add,mul_comm,Pi.mul_apply] using hm
  · exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_add]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbound x)) (Real.exp_pos _).le)

lemma cgf_fold {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H Y : X → ℝ) (t : ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν)
    (het : Integrable (fun x => Real.exp (H x+t*Y x)) ν) :
    cgf Y (gibbsProbability ν H) t =
      Real.log (referencePartition ν (fun x => H x+t*Y x)) - Real.log (referencePartition ν H) := by
  rw [gibbsProbability_eq_tilted _ _ he]
  unfold cgf mgf
  rw [integral_exp_tilted]
  simp only [Pi.add_apply]
  rw [Real.log_div (ne_of_gt (_root_.MeasureTheory.integral_exp_pos het))
    (ne_of_gt (_root_.MeasureTheory.integral_exp_pos he))]
  rfl

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_labeledSpinReference {N : ℕ} (n : ℕ) (ν : Measure (Spin N))
    [IsProbabilityMeasure ν] : Measurable (labeledSpinReference n ν) := by
  let κ : Kernel (LabeledTree n) (LabeledLeaf n) :=
    ⟨labeledLeafLaw n,measurable_labeledLeafLaw n⟩
  have : IsMarkovKernel κ := ⟨fun T => by
    change IsProbabilityMeasure (labeledLeafLaw n T)
    infer_instance⟩
  have he : (fun T => ((Kernel.const (LabeledTree n) ν).prod κ) T) =
      labeledSpinReference n ν := by
    funext T
    rw [Kernel.prod_apply,Kernel.const_apply]
    rfl
  rw [← he]
  exact ((Kernel.const (LabeledTree n) ν).prod κ).measurable

lemma measurable_patternBase_infinite {N : ℕ} {A : Type*} [MeasurableSpace A]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (fun p : (ℕ × (ℕ → A)) × Spin N =>
      patternBase φ (fun i : Fin p.1.1 => p.1.2 i) p.2) := by
  have hφm : Measurable (fun p : A × Spin N => φ p.1 p.2) :=
    measurable_from_prod_countable_left (fun x => (measurable_pi_apply x).comp hm)
  let F : ℕ × ((ℕ → A) × Spin N) → ℝ := fun p =>
    patternBase φ (fun i : Fin p.1 => p.2.1 i) p.2.2
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro M
    change Measurable (fun p : (ℕ → A) × Spin N => ∑ i : Fin M, φ (p.1 i) p.2)
    apply Finset.measurable_sum
    intro i _
    have hi : Measurable (fun p : (ℕ → A) × Spin N => (p.1 (i:ℕ),p.2)) := by fun_prop
    exact hφm.comp hi
  exact hF.comp (show Measurable (fun p : (ℕ × (ℕ → A)) × Spin N =>
    (p.1.1,(p.1.2,p.2))) from by fun_prop)

lemma enrichedCylinder_exp_ae {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (r : ℝ≥0) :
    ∀ᵐ p ∂enrichedCylinderLaw P r n b,
      Integrable (fun s => Real.exp
        (patternBase φ (fun i : Fin p.1.1.1 => p.1.1.2 i) s.1 +
        cylinderField (enrichedCoefficients n h u s) p.2)) (labeledSpinReference n ν p.1.2) := by
  have he := random_cylinder_all_exp_ae (P := enrichedCylinderBaseLaw P r n b)
    (ν := fun p : EnrichedCylinderBase n A => labeledSpinReference n ν p.2)
    ((measurable_labeledSpinReference n ν).comp measurable_snd)
    (enrichedCoefficients n h u) (enrichedCoefficients_variance_le hN n hh h0 u hu)
  filter_upwards [he] with p hp
  apply integrable_exp_bounded_add (by simpa using hp 1) (measurable_of_countable _)
    (K := (p.1.1.1:ℝ)*K)
  intro s
  let y : Fin p.1.1.1 → A := fun i => p.1.1.2 i
  have hb : |patternBase φ y s.1| ≤ ‖patternBase φ y‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (patternBase φ y) s.1
  exact (le_abs_self _).trans (hb.trans (patternBase_bound hK hφ y))

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_EnrichedCGF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched C G F. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma integral_comp_preserving_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    {F : B → ℝ} (hF : AEStronglyMeasurable F ν) :
    (∫ x, F (f x) ∂μ) = ∫ y, F y ∂ν := by
  have h := integral_map hf.measurable.aemeasurable (hf.map_eq.symm ▸ hF)
  rw [hf.map_eq] at h
  exact h.symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma cylinder_weighted_variant_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℝ) (hc : ∀ i j, cylinderCross (a i) (a j) = cylinderCross (b i) (b j))
    (c : ι → ℝ) :
    (∑ i, c i • a i).sum (fun _ v => v^2) = (∑ i, c i • b i).sum (fun _ v => v^2) := by
  classical
  simp only [← cylinderCross_self,cylinderCross_finset_left,cylinderCross_sum_right,cylinderCross_smul,hc]

lemma dual_cylinderField {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (a : ι → ℕ →₀ ℝ) (g : ℕ → ℝ) :
    L (fun i => cylinderField (a i) g) =
      cylinderField (∑ i, L (Pi.single i 1) • a i) g := by
  have hv : (fun i => cylinderField (a i) g) =
      ∑ i, cylinderField (a i) g • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hv,map_sum,cylinderField_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,cylinderField_smul,smul_eq_mul,mul_comm]

 

lemma cylinder_finite_law_eq {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℝ) (hc : ∀ i j, cylinderCross (a i) (a j) = cylinderCross (b i) (b j)) :
    gaussianCoordinates.map (fun g i => cylinderField (a i) g) =
      gaussianCoordinates.map (fun g i => cylinderField (b i) g) := by
  classical
  have ha : Measurable (fun g i => cylinderField (a i) g) :=
    Measurable.of_eval (fun coordinate => measurable_cylinderField (a coordinate))
  have hb : Measurable (fun g i => cylinderField (b i) g) :=
    Measurable.of_eval (fun coordinate => measurable_cylinderField (b coordinate))
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply,charFunDual_apply,integral_map ha.aemeasurable (by fun_prop),
    integral_map hb.aemeasurable (by fun_prop)]
  simp only [dual_cylinderField]
  rw [← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    ← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    cylinderField_law,cylinderField_law,cylinder_weighted_variant_eq a b hc]

 

theorem cylinder_fields_law_eq {X : Type*}
    (a b : X → ℕ →₀ ℝ) (hc : ∀ x y, cylinderCross (a x) (a y) = cylinderCross (b x) (b y)) :
    gaussianCoordinates.map (fun g x => cylinderField (a x) g) =
      gaussianCoordinates.map (fun g x => cylinderField (b x) g) := by
  classical
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (Measurable.of_eval (fun coordinate => measurable_cylinderField (a coordinate))).aemeasurable
    (Measurable.of_eval (fun coordinate => measurable_cylinderField (b coordinate))).aemeasurable).mpr
  intro I
  exact cylinder_finite_law_eq (fun i : I => a i) (fun i : I => b i) (fun i j => hc i j)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianPair_preserving : MeasurePreserving gaussianPair gaussianCoordinates
    (gaussianCoordinates.prod gaussianCoordinates) := by
  have hs : MeasurePreserving (gaussianNamespaceSplit 0) gaussianCoordinates
      (gaussianCoordinates.prod (otherNamespacesLaw 0)) :=
    ⟨measurable_gaussianNamespaceSplit 0,gaussianNamespaceSplit_law 0⟩
  have he := measurePreserving_eval_infinitePi
    (fun _ : {k : ℕ // k ≠ 0} => gaussianCoordinates) ⟨1,by decide⟩
  exact ((MeasurePreserving.id gaussianCoordinates).prod he).comp hs

lemma gaussianSumCoefficients_field {X : Type*} (a b : X → ℕ →₀ ℝ) (t : ℝ) (x : X) (g : ℕ → ℝ) :
    cylinderField (gaussianSumCoefficients a b t x) g =
      cylinderField (a x) (gaussianPair g).1 + t*cylinderField (b x) (gaussianPair g).2 := by
  unfold gaussianSumCoefficients
  rw [cylinderField_finset_sum,Fin.sum_univ_two]
  simp only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_succ,Fin.cases_zero]
  simp [cylinderField_tag,cylinderField_smul,gaussianPair]

lemma gaussianSumCoefficients_cross {X : Type*} (a b : X → ℕ →₀ ℝ) (t : ℝ) (x y : X) :
    cylinderCross (gaussianSumCoefficients a b t x) (gaussianSumCoefficients a b t y) =
      cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y) := by
  unfold gaussianSumCoefficients
  rw [cylinderCross_tagged_sum,Fin.sum_univ_two]
  simp only [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_succ,Fin.cases_zero]
  simp [cylinderCross_smul,pow_two]

 

theorem cylinder_independent_sum_law {X : Type*} (a b c : X → ℕ →₀ ℝ) (t : ℝ)
    (hc : ∀ x y, cylinderCross (c x) (c y) = cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y)) :
    (gaussianCoordinates.prod gaussianCoordinates).map
      (fun g x => cylinderField (a x) g.1+t*cylinderField (b x) g.2) =
      gaussianCoordinates.map (fun g x => cylinderField (c x) g) := by
  rw [← gaussianPair_preserving.map_eq,Measure.map_map (by
    apply Measurable.of_eval; intro x
    exact ((measurable_cylinderField (a x)).comp measurable_fst).add
      (((measurable_cylinderField (b x)).comp measurable_snd).const_mul t)) gaussianPair_preserving.measurable]
  have he : (fun g x => cylinderField (a x) (gaussianPair g).1+t*cylinderField (b x) (gaussianPair g).2) =
      (fun g x => cylinderField (gaussianSumCoefficients a b t x) g) := by
    funext g x; exact (gaussianSumCoefficients_field a b t x g).symm
  change gaussianCoordinates.map (fun g x => cylinderField (a x) (gaussianPair g).1+
    t*cylinderField (b x) (gaussianPair g).2) = _
  rw [he]
  exact cylinder_fields_law_eq _ _ (fun x y => (gaussianSumCoefficients_cross a b t x y).trans (hc x y).symm)

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_VarianceDerivative
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Derivative. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_sum_identDistrib {Ω X : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (a b c : X → ℕ →₀ ℝ) (t : ℝ)
    (hc : ∀ x y, cylinderCross (c x) (c y) = cylinderCross (a x) (a y)+t^2*cylinderCross (b x) (b y)) :
    IdentDistrib
      (fun z : (Ω × (ℕ → ℝ)) × (ℕ → ℝ) =>
        (z.1.1,fun x => cylinderField (a x) z.1.2+t*cylinderField (b x) z.2))
      (fun z : Ω × (ℕ → ℝ) => (z.1,fun x => cylinderField (c x) z.2))
      ((P.prod gaussianCoordinates).prod gaussianCoordinates) (P.prod gaussianCoordinates) := by
  let f : ((ℕ → ℝ) × (ℕ → ℝ)) → (X → ℝ) :=
    fun z x => cylinderField (a x) z.1+t*cylinderField (b x) z.2
  let g : (ℕ → ℝ) → (X → ℝ) := fun z x => cylinderField (c x) z
  have hf : Measurable f := by
    unfold f; apply Measurable.of_eval; intro x
    exact ((measurable_cylinderField (a x)).comp measurable_fst).add
      (((measurable_cylinderField (b x)).comp measurable_snd).const_mul t)
  have hg : Measurable g := by unfold g; apply Measurable.of_eval; intro x; exact measurable_cylinderField _
  have hp : MeasurePreserving (MeasurableEquiv.prodAssoc : ((Ω × (ℕ → ℝ)) × (ℕ → ℝ)) → Ω × ((ℕ → ℝ) × (ℕ → ℝ)))
      ((P.prod gaussianCoordinates).prod gaussianCoordinates) (P.prod (gaussianCoordinates.prod gaussianCoordinates)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod⟩
  refine ⟨((measurable_id.prodMap hf).comp hp.measurable).aemeasurable,
    (measurable_id.prodMap hg).aemeasurable,?_⟩
  change ((P.prod gaussianCoordinates).prod gaussianCoordinates).map
    ((Prod.map id f) ∘ MeasurableEquiv.prodAssoc) =
      (P.prod gaussianCoordinates).map (Prod.map id g)
  rw [← Measure.map_map (measurable_id.prodMap hf) hp.measurable,hp.map_eq,
    ← Measure.map_prod_map P (gaussianCoordinates.prod gaussianCoordinates) measurable_id hf,
    ← Measure.map_prod_map P gaussianCoordinates measurable_id hg]
  rw [show (gaussianCoordinates.prod gaussianCoordinates).map f = gaussianCoordinates.map g from
    cylinder_independent_sum_law a b c t hc]

lemma random_cgf_insertion_eq {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {H : Ω × X → ℝ} (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (b : X → ℕ →₀ ℝ) {K : ℝ} (hb : ∀ x, (b x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    ∀ᵐ z ∂P.prod gaussianCoordinates,
      cgf (fun x => cylinderField (b x) z.2) (gibbsProbability (ν z.1) (fun x => H (z.1,x))) t =
        Real.log (∫ x, Real.exp (H (z.1,x)+t*cylinderField (b x) z.2) ∂ν z.1)-
          Real.log (∫ x, Real.exp (H (z.1,x)) ∂ν z.1) := by
  have hη := measurable_gibbsProbability hν hH
  have ht := random_cylinder_all_exp_ae (P := P) hη b hb
  have he' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := gaussianCoordinates)).tendsto_ae.eventually he
  filter_upwards [ht,he'] with z ht he
  have hi := ht t
  rw [gibbsProbability_eq_tilted _ _ he,integrable_tilted_iff he] at hi
  have hisum : Integrable (fun x => Real.exp (H (z.1,x)+t*cylinderField (b x) z.2)) (ν z.1) := by
    simpa only [smul_eq_mul,← Real.exp_add] using hi
  exact cgf_fold _ _ _ _ he hisum

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma edgeGaussianTag_injective (n : ℕ) : Function.Injective (edgeGaussianTag n) := by
  intro v w h
  exact Option.some.inj (nodeAddress_injective n (Encodable.encode_inj.mp h))

lemma edgeGaussianCoordinates_preserving (n : ℕ) :
    MeasurePreserving (edgeGaussianCoordinates n) gaussianCoordinates
      (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)) :=
  gaussian_pullback_measurePreserving (edgeGaussianTag n) (edgeGaussianTag_injective n)



lemma forestVertexDepth_edgeAt (n : ℕ) (γ : LabeledLeaf n) (i : Fin n) :
    forestVertexDepth n (edgeAt n γ i) = i := by
  have h := nodeAddress_nodeAt_length n γ i.succ
  rw [nodeAt_succ,nodeAddress_length_some] at h
  exact Nat.add_right_cancel h

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma labelLevelCoefficients_cross (n : ℕ) (d : Fin n) (s t : I × LabeledLeaf n) :
    cylinderCross (labelLevelCoefficients n d s) (labelLevelCoefficients n d t) =
      if (labeledAddress n s.2).take (d+1) = (labeledAddress n t.2).take (d+1) then 1 else 0 := by
  classical
  have he : edgeGaussianTag n (edgeAt n t.2 d) = edgeGaussianTag n (edgeAt n s.2 d) ↔
      (labeledAddress n s.2).take (d+1) = (labeledAddress n t.2).take (d+1) := by
    rw [edgeGaussianTag,edgeGaussianTag,Encodable.encode_inj,← nodeAt_succ,← nodeAt_succ,
      nodeAddress_nodeAt,nodeAddress_nodeAt]
    exact eq_comm
  simp only [labelLevelCoefficients,cylinderCross_single_left,one_mul,Finsupp.single_apply,he]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma externalFieldCoefficients_cross {N : ℕ} (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (s t : Spin N × LabeledLeaf n) :
    cylinderCross (externalFieldCoefficients n h s) (externalFieldCoefficients n h t) =
      h (labeledCommonDepth n s.2 t.2) * ∑ i, spinValue (s.1 i)*spinValue (t.1 i) := by
  exact treeField_path_cross n s.2 t.2 hh h0 _ _

lemma monotone_field_add {h l : ℕ → ℝ} (hh : Monotone h) (hl : Monotone l)
    {a : ℝ} (ha : 0 ≤ a) : Monotone (fun i => h i+a*l i) := by
  intro i j hij
  exact add_le_add (hh hij) (mul_le_mul_of_nonneg_left (hl hij) ha)

lemma field_add_nonneg {h l : ℕ → ℝ} (h0 : 0 ≤ h 0) (l0 : 0 ≤ l 0)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ h 0+a*l 0 := add_nonneg h0 (mul_nonneg ha l0)

lemma enrichedCoefficients_field_add_cross {N : ℕ} (n : ℕ) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a) (s t : Spin N × LabeledLeaf n) :
    cylinderCross (enrichedCoefficients n (fun i => h i+a*l i) u s)
        (enrichedCoefficients n (fun i => h i+a*l i) u t) =
      cylinderCross (enrichedCoefficients n h u s) (enrichedCoefficients n h u t) +
        a*cylinderCross (externalFieldCoefficients n l s) (externalFieldCoefficients n l t) := by
  unfold enrichedCoefficients
  rw [cylinderCross_tagged_sum,cylinderCross_tagged_sum]
  simp only [Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ]
  rw [externalFieldCoefficients_cross n (monotone_field_add hh hl ha) (field_add_nonneg h0 l0 ha),
    externalFieldCoefficients_cross n hh h0,externalFieldCoefficients_cross n hl l0]
  ring

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_enrichedHamiltonian {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) {φ : A → Spin N → ℝ}
    (hm : Measurable φ) :
    Measurable (fun p : EnrichedCylinderData n A × (Spin N × LabeledLeaf n) =>
      enrichedHamiltonian n h u φ p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro s
  unfold enrichedHamiltonian
  have hg : Measurable (fun p : EnrichedCylinderData n A => (p.1.1,s.1)) :=
    measurable_fst.fst.prodMk measurable_const
  exact ((measurable_patternBase_infinite hm).comp hg).add
    ((measurable_cylinderField (enrichedCoefficients n h u s)).comp measurable_snd)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_enrichedFieldFunctional {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (d : ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    Measurable (enrichedFieldFunctional n d ν φ) := by
  have hH : Measurable (fun p : (EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ)) ×
      (Spin N × LabeledLeaf n) =>
      patternBase φ (fun i : Fin p.1.1.1.1 => p.1.1.1.2 i) p.2.1 + p.1.2 p.2) := by
    apply measurable_from_prod_countable_left
    intro s
    have hp : Measurable (fun p : EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ) => (p.1.1,s.1)) :=
      measurable_fst.fst.prodMk measurable_const
    exact ((measurable_patternBase_infinite hm).comp hp).add
      ((measurable_pi_apply s).comp measurable_snd)
  exact (((measurable_random_referencePartition
    (ν := fun p : EnrichedCylinderBase n A × ((Spin N × LabeledLeaf n) → ℝ) => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd) hH).log).sub_const _).div_const _

lemma measurable_enrichedGibbsReference {N : ℕ} {A : Type*} [MeasurableSpace A]
    (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) : Measurable (enrichedGibbsReference n h u ν φ) :=
  measurable_gibbsProbability
    (ν := fun p : EnrichedCylinderData n A => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd)
    (measurable_enrichedHamiltonian n h u hm)

lemma enrichedFieldInsertedPressure_law {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ)
    {h l : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν] {φ : A → Spin N → ℝ}
    (hm : Measurable φ) {a : ℝ} (ha : 0 ≤ a) :
    IdentDistrib (enrichedFieldInsertedPressure n h l u ν φ a)
      (enrichedCylinderPressure n (fun i => h i+a*l i) u ν φ)
      ((enrichedCylinderLaw P r n b).prod gaussianCoordinates) (enrichedCylinderLaw P r n b) := by
  have he := gaussian_sum_identDistrib (enrichedCylinderBaseLaw P r n b)
    (enrichedCoefficients n h u) (externalFieldCoefficients n l)
    (enrichedCoefficients n (fun i => h i+a*l i) u) (Real.sqrt a) (fun s t => by
      rw [Real.sq_sqrt ha]
      exact enrichedCoefficients_field_add_cross n hh h0 hl l0 u ha s t)
  exact he.comp (measurable_enrichedFieldFunctional n (h n+a*l n) ν hm)

lemma enrichedField_cgf_eq {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h l : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) (a : ℝ) :
    ∀ᵐ z ∂(enrichedCylinderLaw P r n b).prod gaussianCoordinates,
      enrichedFieldInsertedPressure n h l u ν φ a z =
        enrichedCylinderPressure n h u ν φ z.1 +
        (cgf (fun s => cylinderField (externalFieldCoefficients n l s) z.2)
          (enrichedGibbsReference n h u ν φ z.1) (Real.sqrt a))/N-a*l n/2 := by
  have he := random_cgf_insertion_eq
    (ν := fun p : EnrichedCylinderData n A => labeledSpinReference n ν p.1.2)
    ((measurable_labeledSpinReference n ν).comp measurable_fst.snd)
    (measurable_enrichedHamiltonian n h u hm)
    (enrichedCylinder_exp_ae hN n b hh h0 u hu ν P hK hφ r)
    (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le) (Real.sqrt a)
  filter_upwards [he] with z hz
  change cgf _ (enrichedGibbsReference n h u ν φ z.1) (Real.sqrt a) = _ at hz
  rw [hz]
  unfold enrichedFieldInsertedPressure enrichedFieldFunctional enrichedCylinderPressure enrichedHamiltonian
  simp only [add_assoc]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma enrichedMeanPressure_field_insert {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    enrichedMeanPressure P r n b (fun i => h i+a*l i) u ν φ =
      enrichedMeanPressure P r n b h u ν φ +
      (∫ z : EnrichedCylinderData n A × (ℕ → ℝ),
        cgf (fun s => cylinderField (externalFieldCoefficients n l s) z.2)
          (enrichedGibbsReference n h u ν φ z.1) (Real.sqrt a)
        ∂(enrichedCylinderLaw P r n b).prod gaussianCoordinates)/N-a*l n/2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hib := (enrichedCylinderPressure_field_cap hN n b hb hh h0 (le_refl (h n)) u hu ν P hm hK hφ r
    (α := (r:ℝ)/N) (by rw [div_mul_cancel₀ _ hn])).1.integrable (by norm_num)
  have hib' := hib.comp_fst gaussianCoordinates
  have hic := integrable_random_cylinder_cgf (P := enrichedCylinderLaw P r n b)
    (measurable_enrichedGibbsReference n h u ν hm) (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le) (Real.sqrt a)
  change Integrable (fun p : EnrichedCylinderData n A × (ℕ → ℝ) =>
    enrichedCylinderPressure n h u ν φ p.1) ((enrichedCylinderLaw P r n b).prod gaussianCoordinates) at hib'
  change (∫ z, enrichedCylinderPressure n (fun i => h i+a*l i) u ν φ z ∂enrichedCylinderLaw P r n b) = _
  rw [← (enrichedFieldInsertedPressure_law P r n b hh h0 hl l0 u ν hm ha).integral_eq,
    integral_congr_ae (enrichedField_cgf_eq hN n b hh h0 hl l0 u hu ν P hm hK hφ r a)]
  have hs := integral_sub (hib'.add (hic.div_const (N:ℝ))) (integrable_const (a*l n/2))
  simp only [Pi.add_apply] at hs
  rw [hs]
  have hadd := integral_add hib' (hic.div_const (N:ℝ))
  rw [hadd,integral_div]
  rw [integral_fun_fst (fun p : EnrichedCylinderData n A => enrichedCylinderPressure n h u ν φ p)]
  simp [enrichedMeanPressure]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_TiltedLabelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tilted Label Law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma replica_prefix_map {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (r : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun σ => fun i : Fin r => σ i) =
      Measure.pi (fun _ : Fin r => ν) := by
  have hi : iIndepFun (fun i : ℕ => fun σ : ℕ → X => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := iIndepFun_infinitePi (fun _ => measurable_id)
  have he := (hi.precomp (fun {i j : Fin r} h => Fin.val_injective h)).map_fun_eq_pi_map
    (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [Measure.infinitePi_map_eval] using he

lemma replicaLaw_integral_bounded {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {F : (ℕ → X) → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ σ, |F σ| ≤ C) :
    (∫ σ, F σ ∂replicaLaw P ν hν) =
      ∫ ω, ∫ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => ν ω) ∂P := by
  have hi : Integrable F (replicaLaw P ν hν) := (integrable_const C).mono'
    hF.aestronglyMeasurable (ae_of_all _ (fun σ => by simpa only [Real.norm_eq_abs] using hC σ))
  unfold replicaLaw at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  calc
    _ = ∫ ω, ∫ σ, F σ ∂(replicaKernel ν hν) ω ∂P := by
      simpa only [Kernel.const_apply] using Kernel.integral_comp hi
    _ = _ := rfl

lemma replicaLaw_integral_prefix {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {r : ℕ} (D : (Fin r → X) → ℝ) {C : ℝ} (hD : ∀ σ, |D σ| ≤ C) :
    (∫ σ, D (fun i : Fin r => σ i) ∂replicaLaw P ν hν) =
      ∫ ω, ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν ω) ∂P := by
  rw [replicaLaw_integral_bounded P ν hν (F := fun σ => D (fun i : Fin r => σ i))
    ((measurable_of_countable D).comp (by fun_prop)) (fun _ => hD _)]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => ((HasLaw.mk
    ((Measurable.of_eval (fun i : Fin r => measurable_pi_apply (i : ℕ))).aemeasurable)
    (replica_prefix_map (ν ω) r)).integral_comp (measurable_of_countable D).aestronglyMeasurable))

theorem jointArrayLaw_subsequence (L : ℕ → ProbabilityMeasure JointArray) :
    ∃ μ : ProbabilityMeasure JointArray, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (L ∘ φ) atTop (𝓝 μ) := by
  obtain ⟨μ,_,φ,hφ,ht⟩ := isSeqCompact_univ.subseq_of_frequently_in
    (x := L) (Filter.Frequently.of_forall (fun _ => Set.mem_univ _))
  exact ⟨μ,φ,hφ,ht⟩

lemma jointArray_tendsto_integral {L : ℕ → ProbabilityMeasure JointArray}
    {μ : ProbabilityMeasure JointArray} (hL : Tendsto L atTop (𝓝 μ))
    {F : JointArray → ℝ} (hF : Continuous F) :
    Tendsto (fun N => ∫ x, F x ∂(L N : Measure JointArray)) atTop
      (𝓝 (∫ x, F x ∂(μ : Measure JointArray))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
    (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩)

lemma continuous_entryCoordinate (b : Bool) : Continuous (entryCoordinate b) := by
  cases b
  · exact continuous_subtype_val.comp continuous_fst
  · exact continuous_subtype_val.comp continuous_snd

lemma entryCoordinate_ext (x y : JointEntry)
    (h : ∀ b, entryCoordinate b x = entryCoordinate b y) : x = y := by
  apply Prod.ext
  · exact Subtype.ext (h false)
  · exact Subtype.ext (h true)

lemma continuous_blockPairCoordinate (n : ℕ) (i : ((Fin n × Fin n) × Bool) ⊕ Bool) :
    Continuous (blockPairCoordinate n i) := by
  cases i with
  | inl ijb => exact (continuous_entryCoordinate ijb.2).comp (by fun_prop)
  | inr b => exact (continuous_entryCoordinate b).comp continuous_snd

lemma blockPairCoordinate_ext (n : ℕ) (x y : JointBlock n × JointEntry)
    (h : ∀ i, blockPairCoordinate n i x = blockPairCoordinate n i y) : x = y := by
  apply Prod.ext
  · funext i j
    apply entryCoordinate_ext
    intro b
    exact h (.inl ((i,j),b))
  · apply entryCoordinate_ext
    intro b
    exact h (.inr b)

theorem block_pair_monomials_unique (n : ℕ)
    (P Q : Measure (JointBlock n × JointEntry)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ (D : JointBlock n → ℝ), Continuous D → ∀ p d : ℕ,
      (∫ x, D x.1 * x.2.1.1 ^ p * x.2.2.1 ^ d ∂P) =
        ∫ x, D x.1 * x.2.1.1 ^ p * x.2.2.1 ^ d ∂Q) : P = Q := by
  classical
  have : TopologicalSpace.SeparableSpace (JointBlock n × JointEntry) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (JointBlock n × JointEntry) := inferInstance
  let I := ((Fin n × Fin n) × Bool) ⊕ Bool
  let g : I → ((JointBlock n × JointEntry) →ᵇ ℝ) := fun i =>
    BoundedContinuousFunction.mkOfCompact ⟨blockPairCoordinate n i,continuous_blockPairCoordinate n i⟩
  let ev : MvPolynomial I ℝ →ₐ[ℝ] ((JointBlock n × JointEntry) →ᵇ ℝ) := MvPolynomial.aeval g
  let A : StarSubalgebra ℝ ((JointBlock n × JointEntry) →ᵇ ℝ) :=
    { ev.range with
      star_mem' := by
        intro f hf
        have hs : star f = f := by ext x; simp
        rw [hs]
        exact hf }
  have hap (i : I) (x : JointBlock n × JointEntry) : g i x = blockPairCoordinate n i x := rfl
  have hsep : (A.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i,hi⟩ : ∃ i : I, blockPairCoordinate n i x ≠ blockPairCoordinate n i y := by
      by_contra! hno
      exact hxy (blockPairCoordinate_ext n x y hno)
    refine ⟨g i,?_,?_⟩
    · refine ⟨(g i).toContinuousMap,?_,rfl⟩
      exact ⟨g i,⟨MvPolynomial.X i,by simp [ev]⟩,rfl⟩
    · simpa only [hap] using hi
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish hsep
  intro f hf
  obtain ⟨p,rfl⟩ := hf
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add,BoundedContinuousFunction.coe_add,Pi.add_apply,
      integral_add (BoundedContinuousFunction.integrable _ _) (BoundedContinuousFunction.integrable _ _)]
      using congrArg₂ (· + ·) hp hq
  | monomial k c =>
    let D : JointBlock n → ℝ := fun b => ∏ i : (Fin n × Fin n) × Bool,
      entryCoordinate i.2 (b i.1.1 i.1.2) ^ k (.inl i)
    have hD : Continuous D := by
      apply continuous_finsetProd
      intro i _
      exact ((continuous_entryCoordinate i.2).comp (by fun_prop)).pow _
    have he (x : JointBlock n × JointEntry) : ev (MvPolynomial.monomial k c) x =
        c*(D x.1 * x.2.1.1 ^ k (.inr false) * x.2.2.1 ^ k (.inr true)) := by
      simp only [ev,MvPolynomial.aeval_monomial]
      rw [Finsupp.prod_pow]
      simp only [BoundedContinuousFunction.coe_mul,Pi.mul_apply,
        BoundedContinuousFunction.coe_prod,BoundedContinuousFunction.coe_pow,
        BoundedContinuousFunction.algebraMap_apply,Finset.prod_apply,Pi.pow_apply,smul_eq_mul,mul_one]
      change c*(∏ i : I,g i x ^ k i) = _
      rw [Fintype.prod_sum_type]
      simp only [Fintype.prod_bool,hap,blockPairCoordinate,entryCoordinate,Bool.false_eq_true,ite_false,ite_true]
      dsimp only [D,entryCoordinate]
      ring
    change (∫ x, ev (MvPolynomial.monomial k c) x ∂P) = ∫ x, ev (MvPolynomial.monomial k c) x ∂Q
    simp only [he,integral_const_mul]
    exact congrArg (c * ·) (h D hD _ _)

lemma continuous_jointBlockView (n : ℕ) : Continuous (jointBlockView n) := by
  unfold jointBlockView
  fun_prop

lemma continuous_jointBlockLink (n i j : ℕ) : Continuous (jointBlockLink n i j) := by
  unfold jointBlockLink
  exact (continuous_jointBlockView n).prodMk (continuous_apply _)

lemma compact_integrable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {P : Measure X} [IsFiniteMeasure P]
    {F : X → ℝ} (hF : Continuous F) : Integrable F P :=
  (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩).integrable P

theorem joint_monomial_measure_identity (μ : Measure JointArray) [IsProbabilityMeasure μ]
    (n : ℕ) (i : Fin n)
    (h : ∀ (D : JointBlock n → ℝ), Continuous D → ∀ p d : ℕ,
      (n : ℝ)*(∫ x, D (jointBlockView n x)*(x (i,n)).1.1^p*(x (i,n)).2.1^d ∂μ) =
        (∫ x, D (jointBlockView n x) ∂μ)*(∫ x, (x (0,1)).1.1^p*(x (0,1)).2.1^d ∂μ) +
        ∑ j ∈ Finset.univ.erase i,
          ∫ x, D (jointBlockView n x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d ∂μ) :
    (n : ℝ≥0∞) • μ.map (jointBlockLink n i n) =
      (μ.map (jointBlockView n)).prod (μ.map (fun x => x (0,1))) +
        ∑ j ∈ Finset.univ.erase i, μ.map (jointBlockLink n i j) := by
  classical
  let block := μ.map (jointBlockView n)
  let pair := μ.map (fun x => x (0,1))
  let link := fun j : ℕ => μ.map (jointBlockLink n i j)
  have : IsProbabilityMeasure block := (Measure.isProbabilityMeasure_map_iff
    (continuous_jointBlockView n).measurable.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure pair := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply (0,1)).aemeasurable).mpr inferInstance
  have (j : ℕ) : IsProbabilityMeasure (link j) := (Measure.isProbabilityMeasure_map_iff
    (continuous_jointBlockLink n i j).measurable.aemeasurable).mpr inferInstance
  change (n : ℝ≥0∞) • link n = block.prod pair+∑ j ∈ Finset.univ.erase i, link j
  have : IsFiniteMeasure ((n : ℝ≥0∞) • link n) := (link n).smul_finite (by simp)
  apply block_pair_monomials_unique n
  intro D hD p d
  let F : JointBlock n × JointEntry → ℝ := fun x => D x.1*x.2.1.1^p*x.2.2.1^d
  have hF : Continuous F := by fun_prop
  have hi (j : ℕ) : (∫ x, F x ∂link j) =
      ∫ x, D (jointBlockView n x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d ∂μ := by
    exact integral_map (continuous_jointBlockLink n i j).measurable.aemeasurable hF.aestronglyMeasurable
  change (∫ x, F x ∂(n : ℝ≥0∞) • link n) =
    ∫ x, F x ∂(block.prod pair+∑ j ∈ Finset.univ.erase i, link j)
  rw [integral_smul_measure,ENNReal.toReal_natCast,smul_eq_mul,
    integral_add_measure (compact_integrable hF) (compact_integrable hF),
    integral_finsetSum_measure (fun j _ => compact_integrable hF),hi]
  simp_rw [hi]
  rw [h D hD]
  congr 1
  have hp : Continuous (fun x : JointEntry => x.1.1^p*x.2.1^d) := by fun_prop
  have he : (∫ x, F x ∂block.prod pair) =
      (∫ b, D b ∂block)*(∫ x, x.1.1^p*x.2.1^d ∂pair) := by
    simpa only [F,mul_assoc] using
      (integral_prod_mul (μ := block) (ν := pair) D (fun x : JointEntry => x.1.1^p*x.2.1^d))
  rw [he,integral_map (continuous_jointBlockView n).measurable.aemeasurable hD.aestronglyMeasurable,
    integral_map (measurable_pi_apply (0,1)).aemeasurable hp.aestronglyMeasurable]

theorem joint_monomialGG_measurable (μ : Measure JointArray) [IsProbabilityMeasure μ]
    (h : ∀ n, 2 ≤ n → ∀ i : Fin n,
      ∀ (D : JointBlock n → ℝ), Continuous D → ∀ p d : ℕ,
      (n : ℝ)*(∫ x, D (jointBlockView n x)*(x (i,n)).1.1^p*(x (i,n)).2.1^d ∂μ) =
        (∫ x, D (jointBlockView n x) ∂μ)*(∫ x, (x (0,1)).1.1^p*(x (0,1)).2.1^d ∂μ) +
        ∑ j ∈ Finset.univ.erase i,
          ∫ x, D (jointBlockView n x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d ∂μ) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) μ := by
  classical
  intro n hn i A hA t ht
  have he := congrArg (fun ν : Measure (JointBlock n × JointEntry) => (ν (A ×ˢ t)).toReal)
    (joint_monomial_measure_identity μ n i (h n hn i))
  have hmap : ∀ j : ℕ, Measurable (jointBlockLink n i j) := fun j =>
    (continuous_jointBlockLink n i j).measurable
  have hblock := (continuous_jointBlockView n).measurable
  have hpair : Measurable (fun x : JointArray => x (0,1)) := by fun_prop
  simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast,
    Measure.add_apply,Measure.prod_prod,Measure.finsetSum_apply,
    Measure.map_apply (hmap _) (hA.prod ht),Measure.map_apply hblock hA,Measure.map_apply hpair ht] at he
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.sum_ne_top.mpr (fun j _ => measure_ne_top _ _)),ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)] at he
  change (n : ℝ)*μ.real ({x | jointBlockView n x ∈ A} ∩ {x | x (i,n) ∈ t}) =
    μ.real {x | jointBlockView n x ∈ A}*μ.real {x | x (0,1) ∈ t}+
    ∑ j ∈ Finset.univ.erase i, μ.real ({x | jointBlockView n x ∈ A} ∩ {x | x (i,j) ∈ t}) at he
  change μ.real ({x | jointBlockView n x ∈ A} ∩ {x | x (i,n) ∈ t}) =
    (μ.real {x | jointBlockView n x ∈ A}*μ.real {x | x (0,1) ∈ t})/n+
    (∑ j ∈ Finset.univ.erase i, μ.real ({x | jointBlockView n x ∈ A} ∩ {x | x (i,j) ∈ t}))/n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0]
  nlinarith [he]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ArraySynchronization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Synchronization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix

namespace IsingPerceptron


lemma measurable_arrayBlock {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} (hm : Measurable B) (n : ℕ) :
    Measurable (arrayBlock B n) := by
  unfold arrayBlock
  fun_prop

lemma isClosed_setOf_posSemidef (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  have he : {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} =
      {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j = A j i} ∩ {A | ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v)} := by
    ext A
    constructor
    · intro h
      refine ⟨?_, fun v => by simpa using h.dotProduct_mulVec_nonneg v⟩
      intro i j
      have he := congrFun (congrFun h.1 i) j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using he.symm
    · rintro ⟨hs, hq⟩
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · ext i j; exact hs j i
      · intro v; simpa using hq v
  rw [he]
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (by unfold dotProduct Matrix.mulVec; fun_prop)

lemma real_posSemidef_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : ∀ i j, A i j = A j i := by
  intro i j
  have h := congrFun (congrFun hA.1 i) j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm


lemma ultrametric_survival_rectangle {b : RealArray} (hs : ∀ i j, b i j = b j i)
    (hu : IsUltrametricArray b) {n : ℕ} (t : Fin n → ℝ) (k : Fin n)
    (hk : ∀ i, t i ≤ t k) :
    (∀ i : Fin n, t i ≤ b i n) ↔
      (∀ i : Fin n, t i ≤ b i k) ∧ t k ≤ b k n := by
  constructor
  · intro h
    exact ⟨fun i => (le_min (h i) ((hk i).trans (h k))).trans (hu i k n), h k⟩
  · rintro ⟨h, hkn⟩ i
    have hh := hu i n k
    rw [hs n k] at hh
    exact (le_min (h i) ((hk i).trans hkn)).trans hh

lemma measurableSet_survival_compatible {n : ℕ} (t : Fin n → ℝ) (k : Fin n) :
    MeasurableSet {b : Fin n → Fin n → ℝ | ∀ i, t i ≤ b i k} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (by fun_prop))

lemma gg_survival_extension {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hGG : HasGhirlandaGuerra B μ) (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω)) {n : ℕ} (hn : 2 ≤ n)
    {A : Set (Fin n → Fin n → ℝ)} (hA : MeasurableSet A)
    (t : Fin n → ℝ) (k : Fin n) (hk : ∀ i, t i ≤ t k) :
    let A' := A ∩ {b : Fin n → Fin n → ℝ | ∀ i, t i ≤ b i k}
    μ.real ((arrayBlock B n ⁻¹' A) ∩ {ω | ∀ i : Fin n, t i ≤ B ω i n}) =
      (μ.real (arrayBlock B n ⁻¹' A') * μ.real {ω | t k ≤ B ω 0 1}) / n +
      (∑ j ∈ Finset.univ.erase k,
        μ.real ((arrayBlock B n ⁻¹' A') ∩ {ω | t k ≤ B ω k j})) / n := by
  dsimp only
  have he := hGG n hn k _ (hA.inter (measurableSet_survival_compatible t k))
    (Set.Ici (t k)) measurableSet_Ici
  simp only [Set.mem_Ici] at he
  rw [← he]
  apply measureReal_congr
  filter_upwards [hs, hu] with ω hs hu
  apply propext
  change (arrayBlock B n ω ∈ A ∧ ∀ i : Fin n, t i ≤ B ω i n) ↔
    ((arrayBlock B n ω ∈ A ∧ ∀ i : Fin n, t i ≤ B ω i k) ∧ t k ≤ B ω k n)
  rw [ultrametric_survival_rectangle hs hu t k hk]
  tauto

lemma isCountablySpanning_real_Ici :
    IsCountablySpanning (Set.range (Set.Ici : ℝ → Set ℝ)) := by
  refine ⟨fun n => Set.Ici (-(n : ℝ)), fun n => ⟨_, rfl⟩, ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt (-x)
  exact Set.mem_iUnion.mpr ⟨n, by change -(n : ℝ) ≤ x; linarith⟩

lemma measure_eq_of_upper_orthants {ι : Type*} [Fintype ι]
    {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (h : ∀ t : ι → ℝ, μ {x | ∀ i, t i ≤ x i} = ν {x | ∀ i, t i ≤ x i})
    (hU : μ Set.univ = ν Set.univ) : μ = ν := by
  classical
  let C : Set (Set (ι → ℝ)) := Set.pi Set.univ '' Set.pi Set.univ
    (fun _ : ι => Set.range (Set.Ici : ℝ → Set ℝ))
  have hgen : (inferInstance : MeasurableSpace (ι → ℝ)) = MeasurableSpace.generateFrom C := by
    exact (generateFrom_eq_pi (fun _ => by
      rw [← borel_eq_generateFrom_Ici]; exact BorelSpace.measurable_eq.symm)
      (fun _ => isCountablySpanning_real_Ici)).symm
  apply ext_of_generate_finite C hgen (IsPiSystem.pi (fun _ => isPiSystem_Ici)) ?_ hU
  rintro _ ⟨s, hs, rfl⟩
  have hs' : ∀ i, ∃ t : ℝ, Set.Ici t = s i := fun i => hs i (Set.mem_univ i)
  choose t ht using hs'
  have he : Set.pi Set.univ s = {x | ∀ i, t i ≤ x i} := by
    ext x
    simp only [← ht, Set.mem_pi, Set.mem_univ, Set.mem_Ici, forall_true_left, Set.mem_ofPred_eq]
  rw [he]
  exact h t

lemma blockLaw_measureReal_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {μ : Measure Ω} {ν : Measure Ω'}
    (hm : Measurable B) (hm' : Measurable C) {n : ℕ}
    (h : blockLaw B μ n = blockLaw C ν n)
    {A : Set (Fin n → Fin n → ℝ)} (hA : MeasurableSet A) :
    μ.real (arrayBlock B n ⁻¹' A) = ν.real (arrayBlock C n ⁻¹' A) := by
  rw [← map_measureReal_apply (measurable_arrayBlock hm n) hA,
    ← map_measureReal_apply (measurable_arrayBlock hm' n) hA]
  exact congrArg (fun η => η.real A) h

lemma gg_survival_measure_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : Measurable B) (hm' : Measurable C)
    (hGG : HasGhirlandaGuerra B μ) (hGG' : HasGhirlandaGuerra C ν)
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hs' : ∀ᵐ ω ∂ν, ∀ i j, C ω i j = C ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω))
    (hu' : ∀ᵐ ω ∂ν, IsUltrametricArray (C ω)) {n : ℕ} (hn : 2 ≤ n)
    (h : blockLaw B μ n = blockLaw C ν n)
    {A : Set (Fin n → Fin n → ℝ)} (hA : MeasurableSet A) (t : Fin n → ℝ) :
    μ ((arrayBlock B n ⁻¹' A) ∩ {ω | ∀ i : Fin n, t i ≤ B ω i n}) =
    ν ((arrayBlock C n ⁻¹' A) ∩ {ω | ∀ i : Fin n, t i ≤ C ω i n}) := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ t
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hk' : ∀ i, t i ≤ t k := fun i => hk i (Finset.mem_univ _)
  apply (measureReal_eq_measureReal_iff).mp
  rw [gg_survival_extension hGG hs hu hn hA t k hk',
    gg_survival_extension hGG' hs' hu' hn hA t k hk']
  have hcomp := hA.inter (measurableSet_survival_compatible t k)
  have hp := blockLaw_measureReal_eq hm hm' h
    (A := {b | t k ≤ b ⟨0, by omega⟩ ⟨1, by omega⟩})
    (measurableSet_le measurable_const (by fun_prop))
  change μ.real {ω | t k ≤ B ω 0 1} = ν.real {ω | t k ≤ C ω 0 1} at hp
  rw [blockLaw_measureReal_eq hm hm' h hcomp, hp]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact blockLaw_measureReal_eq hm hm' h
    (hcomp.inter (measurableSet_le measurable_const (show Measurable (fun b : Fin n → Fin n → ℝ => b k j) by fun_prop)))

lemma gg_joint_extension_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : Measurable B) (hm' : Measurable C)
    (hGG : HasGhirlandaGuerra B μ) (hGG' : HasGhirlandaGuerra C ν)
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hs' : ∀ᵐ ω ∂ν, ∀ i j, C ω i j = C ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω))
    (hu' : ∀ᵐ ω ∂ν, IsUltrametricArray (C ω)) {n : ℕ} (hn : 2 ≤ n)
    (h : blockLaw B μ n = blockLaw C ν n) :
    μ.map (fun ω => (arrayBlock B n ω, fun i : Fin n => B ω i n)) =
    ν.map (fun ω => (arrayBlock C n ω, fun i : Fin n => C ω i n)) := by
  have hbm : Measurable (fun ω => (arrayBlock B n ω, fun i : Fin n => B ω i n)) :=
    (measurable_arrayBlock hm n).prodMk (by fun_prop)
  have hcm : Measurable (fun ω => (arrayBlock C n ω, fun i : Fin n => C ω i n)) :=
    (measurable_arrayBlock hm' n).prodMk (by fun_prop)
  apply Measure.ext_prod
  intro A T hA hT
  let μA := (μ.restrict (arrayBlock B n ⁻¹' A)).map (fun ω => fun i : Fin n => B ω i n)
  let νA := (ν.restrict (arrayBlock C n ⁻¹' A)).map (fun ω => fun i : Fin n => C ω i n)
  have hr : μA = νA := by
    apply measure_eq_of_upper_orthants
    · intro t
      have ht : MeasurableSet {x : Fin n → ℝ | ∀ i, t i ≤ x i} := by
        simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (by fun_prop))
      dsimp [μA, νA]
      rw [Measure.map_apply (by fun_prop) ht, Measure.map_apply (by fun_prop) ht,
        Measure.restrict_apply ((by fun_prop : Measurable (fun ω => fun i : Fin n => B ω i n)) ht),
        Measure.restrict_apply ((by fun_prop : Measurable (fun ω => fun i : Fin n => C ω i n)) ht)]
      rw [Set.inter_comm, Set.inter_comm _ (arrayBlock C n ⁻¹' A)]
      exact gg_survival_measure_eq hm hm' hGG hGG' hs hs' hu hu' hn h hA t
    · dsimp [μA, νA]
      simp only [Measure.map_apply (by fun_prop : Measurable (fun ω => fun i : Fin n => B ω i n)) MeasurableSet.univ,
        Measure.map_apply (by fun_prop : Measurable (fun ω => fun i : Fin n => C ω i n)) MeasurableSet.univ,
        Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact (measureReal_eq_measureReal_iff).mp (blockLaw_measureReal_eq hm hm' h hA)
  have he := congrArg (fun η => η T) hr
  dsimp [μA, νA] at he
  rw [Measure.map_apply (by fun_prop) hT, Measure.map_apply (by fun_prop) hT,
    Measure.restrict_apply ((by fun_prop : Measurable (fun ω => fun i : Fin n => B ω i n)) hT),
    Measure.restrict_apply ((by fun_prop : Measurable (fun ω => fun i : Fin n => C ω i n)) hT)] at he
  rw [Measure.map_apply hbm (hA.prod hT), Measure.map_apply hcm (hA.prod hT)]
  change μ ((arrayBlock B n ⁻¹' A) ∩ ((fun ω => fun i : Fin n => B ω i n) ⁻¹' T)) =
    ν ((arrayBlock C n ⁻¹' A) ∩ ((fun ω => fun i : Fin n => C ω i n) ⁻¹' T))
  simpa only [Set.inter_comm] using he

lemma measurable_augmentArrayBlock (D : ℝ) (n : ℕ) : Measurable (augmentArrayBlock D n) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold augmentArrayBlock
  split_ifs <;> fun_prop

lemma augmentArrayBlock_eq {b : RealArray} (hs : ∀ i j, b i j = b j i)
    {D : ℝ} (hd : ∀ i, b i i = D) (n : ℕ) :
    augmentArrayBlock D n ((fun i j : Fin n => b i j), fun i : Fin n => b i n) =
      fun i j : Fin (n+1) => b i j := by
  funext i j
  unfold augmentArrayBlock
  split_ifs with hi hj hj
  · rfl
  · have hj' : j.val = n := by omega
    simp only [hj']
  · have hi' : i.val = n := by omega
    simp only [hi', hs n j]
  · have hi' : i.val = n := by omega
    have hj' : j.val = n := by omega
    simp only [hi', hj', hd]

lemma gg_next_blockLaw_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : Measurable B) (hm' : Measurable C)
    (hGG : HasGhirlandaGuerra B μ) (hGG' : HasGhirlandaGuerra C ν)
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hs' : ∀ᵐ ω ∂ν, ∀ i j, C ω i j = C ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω))
    (hu' : ∀ᵐ ω ∂ν, IsUltrametricArray (C ω)) {D : ℝ}
    (hd : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) (hd' : ∀ᵐ ω ∂ν, ∀ i, C ω i i = D)
    {n : ℕ} (hn : 2 ≤ n) (h : blockLaw B μ n = blockLaw C ν n) :
    blockLaw B μ (n+1) = blockLaw C ν (n+1) := by
  have he := congrArg (Measure.map (augmentArrayBlock D n))
    (gg_joint_extension_law hm hm' hGG hGG' hs hs' hu hu' hn h)
  rw [Measure.map_map (measurable_augmentArrayBlock D n) (by
      exact (measurable_arrayBlock hm n).prodMk (by fun_prop)),
    Measure.map_map (measurable_augmentArrayBlock D n) (by
      exact (measurable_arrayBlock hm' n).prodMk (by fun_prop))] at he
  have hB : (fun ω => augmentArrayBlock D n (arrayBlock B n ω, fun i : Fin n => B ω i n)) =ᵐ[μ]
      arrayBlock B (n+1) := by
    filter_upwards [hs, hd] with ω hs hd
    exact augmentArrayBlock_eq hs hd n
  have hC : (fun ω => augmentArrayBlock D n (arrayBlock C n ω, fun i : Fin n => C ω i n)) =ᵐ[ν]
      arrayBlock C (n+1) := by
    filter_upwards [hs', hd'] with ω hs hd
    exact augmentArrayBlock_eq hs hd n
  exact (Measure.map_congr hB).symm.trans (he.trans (Measure.map_congr hC))

lemma blockLaw_two_eq_pair_map {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hm : Measurable B) {D : ℝ}
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hd : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) :
    blockLaw B μ 2 = (μ.map (fun ω => B ω 0 1)).map
      (fun r => fun i j : Fin 2 => if i = j then D else r) := by
  rw [Measure.map_map (by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    split_ifs <;> fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [hs, hd] with ω hs hd
  funext i j
  fin_cases i <;> fin_cases j <;> simp [arrayBlock, hs, hd]

lemma blockLaw_restrict {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hm : Measurable B) {m n : ℕ} (hmn : m ≤ n) :
    (blockLaw B μ n).map (fun b => fun i j : Fin m => b (Fin.castLE hmn i) (Fin.castLE hmn j)) =
      blockLaw B μ m := by
  unfold blockLaw
  rw [Measure.map_map (by fun_prop) (measurable_arrayBlock hm n)]
  rfl

 

theorem gg_blockLaw_unique {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : Measurable B) (hm' : Measurable C)
    (hGG : HasGhirlandaGuerra B μ) (hGG' : HasGhirlandaGuerra C ν)
    (hs : ∀ᵐ ω ∂μ, ∀ i j, B ω i j = B ω j i)
    (hs' : ∀ᵐ ω ∂ν, ∀ i j, C ω i j = C ω j i)
    (hu : ∀ᵐ ω ∂μ, IsUltrametricArray (B ω))
    (hu' : ∀ᵐ ω ∂ν, IsUltrametricArray (C ω)) {D : ℝ}
    (hd : ∀ᵐ ω ∂μ, ∀ i, B ω i i = D) (hd' : ∀ᵐ ω ∂ν, ∀ i, C ω i i = D)
    (hp : μ.map (fun ω => B ω 0 1) = ν.map (fun ω => C ω 0 1)) :
    ∀ n, blockLaw B μ n = blockLaw C ν n := by
  have h2 : blockLaw B μ 2 = blockLaw C ν 2 := by
    rw [blockLaw_two_eq_pair_map hm hs hd, blockLaw_two_eq_pair_map hm' hs' hd', hp]
  have hind : ∀ n, 2 ≤ n → blockLaw B μ n = blockLaw C ν n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact h2
    | succ n hn ih => exact gg_next_blockLaw_eq hm hm' hGG hGG' hs hs' hu hu' hd hd' hn ih
  intro n
  by_cases hn : 2 ≤ n
  · exact hind n hn
  · have hn' : n ≤ 2 := by omega
    rw [← blockLaw_restrict hm hn', ← blockLaw_restrict hm' hn', h2]

 
lemma HasEntryGhirlandaGuerra.map {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → F} (hf : Measurable f) :
    HasEntryGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := by
  intro n hn i A hA t ht
  exact h n hn i ((fun b j k => f (b j k)) ⁻¹' A)
    (hA.preimage (by fun_prop)) (f ⁻¹' t) (ht.preimage hf)

lemma HasEntryGhirlandaGuerra.real_map {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → ℝ} (hf : Measurable f) :
    HasGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := h.map hf

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_JointGGClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint G G Closure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron


lemma jointMonomialResidual_weak_limit {L : ℕ → ProbabilityMeasure JointArray}
    {μ : ProbabilityMeasure JointArray} (hL : Tendsto L atTop (𝓝 μ))
    (n : ℕ) (i : Fin n) (D : JointBlock n → ℝ) (hD : Continuous D) (p d : ℕ) :
    Tendsto (fun N => jointMonomialResidual (L N) n i D p d) atTop
      (𝓝 (jointMonomialResidual μ n i D p d)) := by
  have hI : ∀ F : JointArray → ℝ, Continuous F →
      Tendsto (fun N => ∫ x, F x ∂(L N : Measure JointArray)) atTop
        (𝓝 (∫ x, F x ∂(μ : Measure JointArray))) := by
    intro F hF
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hL)
      (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩)
  have hcD : Continuous (fun x => D (jointBlockView n x)) := hD.comp (continuous_jointBlockView n)
  have ht (j : ℕ) := hI (fun x => D (jointBlockView n x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d)
    (hcD.mul (by fun_prop) |>.mul (by fun_prop))
  exact (((ht n).const_mul (n : ℝ)).sub ((hI _ hcD).mul (hI _ (by fun_prop)))).sub
    (tendsto_finsetSum _ (fun j _ => ht j))

 

theorem jointGG_of_weak_monomial_residuals {L : ℕ → ProbabilityMeasure JointArray}
    {μ : ProbabilityMeasure JointArray} (hL : Tendsto L atTop (𝓝 μ))
    (hg : ∀ n, 2 ≤ n → ∀ i : Fin n, ∀ D : JointBlock n → ℝ, Continuous D → ∀ p d : ℕ,
      Tendsto (fun N => jointMonomialResidual (L N) n i D p d) atTop (𝓝 0)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (μ : Measure JointArray) := by
  apply joint_monomialGG_measurable
  intro n hn i D hD p d
  have he := tendsto_nhds_unique (jointMonomialResidual_weak_limit hL n i D hD p d)
    (hg n hn i D hD p d)
  dsimp only [jointMonomialResidual] at he
  linarith

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_log_partition_mean_bounds {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : Ω × X → ℝ} (hm : Measurable H) {v : X → NNReal} {K : ℝ}
    (hg : ∀ x, μ.map (fun ω => H (ω,x)) = gaussianReal 0 (v x))
    (hv : ∀ x, (v x : ℝ) ≤ K) :
    0 ≤ (∫ ω, Real.log (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ) ∧
      (∫ ω, Real.log (∫ x, Real.exp (H (ω,x)) ∂ν) ∂μ) ≤ K/2 := by
  let Z := fun ω => ∫ x, Real.exp (H (ω,x)) ∂ν
  have hmZ : Measurable Z := hm.exp.stronglyMeasurable.integral_prod_right'.measurable
  have hiH := gaussian_field_integrable (ν := ν) hm hg hv
  have hexp := gaussian_field_exp_integrable (ν := ν) hm hg hv 1
  simp only [one_mul,one_pow] at hexp
  have hZ : Integrable Z μ := hexp.1.integral_prod_left
  have hpos : ∀ᵐ ω ∂μ, 0 < Z ω := by
    filter_upwards [hexp.1.prod_right_ae] with ω hω
    exact MeasureTheory.integral_exp_pos hω
  have hiLog : Integrable (fun ω => Real.log (Z ω)) μ :=
    ((memLp_two_iff_integrable_sq hmZ.log.aestronglyMeasurable).2
      (gaussian_log_partition_second hm hg hv).1).integrable (by norm_num)
  have hexplog : Integrable (fun ω => Real.exp (Real.log (Z ω))) μ := by
    apply hZ.congr
    filter_upwards [hpos] with ω hω
    exact (Real.exp_log hω).symm
  have hmean : (∫ ω, ∫ x, H (ω,x) ∂ν ∂μ) = 0 := by
    rw [integral_integral_swap (f := fun ω x => H (ω,x)) hiH]
    have hz : ∀ x, (∫ ω, H (ω,x) ∂μ) = 0 := by
      intro x
      have hmx : Measurable (fun ω => H (ω,x)) := hm.comp (measurable_id.prodMk measurable_const)
      have he := integral_map hmx.aemeasurable (measurable_id.aestronglyMeasurable :
        AEStronglyMeasurable (fun y : ℝ => y) (μ.map (fun ω => H (ω,x))))
      simp only [hg x,id_eq,integral_id_gaussianReal] at he
      exact he.symm
    simp_rw [hz]
    simp
  refine ⟨?_, ?_⟩
  · rw [← hmean]
    apply integral_mono_ae hiH.integral_prod_left hiLog
    filter_upwards [hiH.prod_right_ae,hexp.1.prod_right_ae,hpos] with ω hω heω hpω
    exact Real.exp_le_exp.mp (by
      rw [Real.exp_log hpω]
      exact exp_integral_le_partition hω heω)
  · apply Real.exp_le_exp.mp
    calc
      _ ≤ ∫ ω, Real.exp (Real.log (Z ω)) ∂μ := exp_integral_le_partition hiLog hexplog
      _ = ∫ ω, Z ω ∂μ := integral_congr_ae (hpos.mono (fun _ h => Real.exp_log h))
      _ ≤ _ := hexp.2

lemma cylinder_cgf_mean_bounds {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {K : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    0 ≤ (∫ g, cgf (fun x => cylinderField (A x) g) ν t ∂gaussianCoordinates) ∧
      (∫ g, cgf (fun x => cylinderField (A x) g) ν t ∂gaussianCoordinates) ≤ t^2*K/2 := by
  have hm : Measurable (fun z : (ℕ → ℝ) × X => t*cylinderField (A z.2) z.1) :=
    (measurable_cylinderFields A).const_mul t
  have hv (x : X) : ((⟨t^2,sq_nonneg t⟩ : NNReal)*(((A x).sum (fun _ c => c^2)).toNNReal) : ℝ) ≤ t^2*K := by
    change t^2*((((A x).sum (fun _ c => c^2)).toNNReal : NNReal) : ℝ) ≤ t^2*K
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c^2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hA x) (sq_nonneg _)
  exact gaussian_log_partition_mean_bounds (ν := ν) hm (fun x => cylinder_scaled_law A x t) hv

lemma random_cylinder_cgf_mean_bounds {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Ω → Measure X}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {K : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c^2) ≤ K) (t : ℝ) :
    let F := fun z : Ω × (ℕ → ℝ) => cgf (fun x => cylinderField (A x) z.2) (ν z.1) t
    0 ≤ (∫ z, F z ∂P.prod gaussianCoordinates) ∧
      (∫ z, F z ∂P.prod gaussianCoordinates) ≤ t^2*K/2 := by
  have hi := integrable_random_cylinder_cgf (P := P) hν A hA t
  dsimp only
  rw [integral_prod _ hi]
  refine ⟨integral_nonneg (fun ω => (cylinder_cgf_mean_bounds (ν ω) A hA t).1), ?_⟩
  calc
    _ ≤ ∫ _ : Ω, t^2*K/2 ∂P := integral_mono hi.integral_prod_left
      (integrable_const _) (fun ω => (cylinder_cgf_mean_bounds (ν ω) A hA t).2)
    _ = _ := by simp



end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_EnrichedGGFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched G G Finite. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma newReplicaEmbedding_injective (k : ℕ) (e : Equiv.Perm (Fin k)) :
    Function.Injective (newReplicaEmbedding k e) := by
  intro a
  refine Fin.cases ?_ (fun a => ?_) a
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · exact fun _ => rfl
    · intro hab
      have hlt := (e b).isLt
      simp only [newReplicaEmbedding,Fin.cases_zero,Fin.cases_succ] at hab
      omega
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · intro hab
      have hlt := (e a).isLt
      simp only [newReplicaEmbedding,Fin.cases_zero,Fin.cases_succ] at hab
      omega
    · intro hab
      apply congrArg Fin.succ
      apply e.injective
      apply Fin.val_injective
      exact hab

lemma sum_nonzero_permutation {m : ℕ} (e : Equiv.Perm (Fin (m+1))) (f : Fin (m+1) → ℝ) :
    (∑ l : Fin m, f (e l.succ)) = ∑ j ∈ Finset.univ.erase (e 0), f j := by
  classical
  have he := Equiv.sum_comp e f
  rw [Fin.sum_univ_succ,← Finset.add_sum_erase _ _ (Finset.mem_univ (e 0))] at he
  exact add_left_cancel he

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_ArrayGeometry
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma labeledCommonDepth_symm (n : ℕ) (x y : LabeledLeaf n) :
    labeledCommonDepth n x y = labeledCommonDepth n y x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [labeledCommonDepth,eq_comm,ih]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma ae_closed_of_weak_limit {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X] {L : ℕ → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hL : Tendsto L atTop (𝓝 μ)) {S : Set X} (hS : IsClosed S)
    (hA : ∀ k, ∀ᵐ x ∂(L k : Measure X), x ∈ S) : ∀ᵐ x ∂(μ : Measure X), x ∈ S := by
  have he : ∀ k, (L k : Measure X) S = 1 := fun k => by
    simpa using (ae_iff_measure_eq (μ := (L k : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mp (hA k)
  have hh := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hL hS
  simp only [he,limsup_const] at hh
  apply (ae_iff_measure_eq (μ := (μ : Measure X)) (p := fun x => x ∈ S) hS.measurableSet.nullMeasurableSet).mpr
  rw [measure_univ]
  exact le_antisymm prob_le_one hh

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix
namespace IsingPerceptron

lemma isClosed_gramDiagonal (D : ℝ) : IsClosed {B | GramDiagonal D B} := by
  change IsClosed ({B : RealArray | ∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j)} ∩
    {B | ∀ i, B i i = D})
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    exact (isClosed_setOf_posSemidef n).preimage (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_eq (by fun_prop) continuous_const)

lemma GramDiagonal.symm {D : ℝ} {B : RealArray} (h : GramDiagonal D B) (i j : ℕ) : B i j = B j i := by
  let n := max i j+1
  let ii : Fin n := ⟨i,by omega⟩
  let jj : Fin n := ⟨j,by omega⟩
  exact real_posSemidef_symm (h.1 n) ii jj

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma continuous_spinArray : Continuous spinArray := by unfold spinArray; fun_prop

lemma isClosed_ultrametricArray : IsClosed {B : RealArray | IsUltrametricArray B} := by
  change IsClosed {B : RealArray | ∀ i j k, min (B i k) (B j k) ≤ B i j}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun k =>
    isClosed_le (by fun_prop) (by fun_prop))))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

lemma unitUniform_Iic {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    unitUniform (Iic a) = ENNReal.ofReal a := by
  rw [unitUniform,Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    Measure.restrict_apply measurableSet_Iic,inter_comm,Set.Ioc_inter_Iic]
  simp only [inf_eq_right.mpr ha.2,Real.volume_Ioc,sub_zero]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_VariationalDefs
attribute [-instance] _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Defs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma unitMonotoneExtension_eq {q : ℝ → ℝ} {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    unitMonotoneExtension q u = q u := by
  simp only [unitMonotoneExtension,not_le.mpr hu.1,not_le.mpr hu.2,ite_false]

lemma unitMonotoneExtension_mem {q : ℝ → ℝ}
    (hb : ∀ u ∈ Ioo (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1) (u : ℝ) :
    unitMonotoneExtension q u ∈ Icc (0:ℝ) 1 := by
  unfold unitMonotoneExtension
  split_ifs with h0 h1
  · exact ⟨le_rfl,zero_le_one⟩
  · exact ⟨zero_le_one,le_rfl⟩
  · exact hb u ⟨lt_of_not_ge h0,lt_of_not_ge h1⟩

lemma unitMonotoneExtension_monotone {q : ℝ → ℝ}
    (hq : MonotoneOn q (Ioo (0:ℝ) 1)) (hb : ∀ u ∈ Ioo (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1) :
    Monotone (unitMonotoneExtension q) := by
  intro u v huv
  by_cases hu0 : u ≤ 0
  · simpa only [unitMonotoneExtension,hu0,ite_true] using (unitMonotoneExtension_mem hb v).1
  by_cases hv1 : 1 ≤ v
  · simpa only [unitMonotoneExtension,hv1,ite_true,show ¬v ≤ 0 by linarith,ite_false] using (unitMonotoneExtension_mem hb u).2
  have hu : u ∈ Ioo (0:ℝ) 1 := ⟨lt_of_not_ge hu0,huv.trans_lt (lt_of_not_ge hv1)⟩
  have hv : v ∈ Ioo (0:ℝ) 1 := ⟨hu.1.trans_le huv,lt_of_not_ge hv1⟩
  rw [unitMonotoneExtension_eq hu,unitMonotoneExtension_eq hv]
  exact hq hu hv huv

lemma overlapPath_representative (q : OverlapPath) :
    ∃ p : ℝ → ℝ, (p =ᵐ[pathMeasure] q.val) ∧ Monotone p ∧ ∀ u, p u ∈ Icc (0:ℝ) 1 := by
  obtain ⟨p,hp,hm,hb⟩ := q.admissible
  refine ⟨unitMonotoneExtension p,?_,unitMonotoneExtension_monotone hm hb,unitMonotoneExtension_mem hb⟩
  filter_upwards [hp,ae_restrict_mem measurableSet_Ioo] with u hu huI
  exact (unitMonotoneExtension_eq huI).trans hu

lemma overlapPathOfMonotone_ae (p : ℝ → ℝ) (hp : Monotone p) (hb : ∀ u, p u ∈ Icc (0:ℝ) 1) :
    p =ᵐ[pathMeasure] (overlapPathOfMonotone p hp hb).val := (AEEqFun.coeFn_mk p _).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

theorem enrichedMeanPressure_recursion {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    enrichedMeanPressure P r n b h u ν φ =
      ((∫ p, energyRecursion n b (fun i => enrichedIncrementLaw N n h u (i+1)) ν
          (enrichedPoissonBase n h u φ p)
        ∂(poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
          (Measure.infinitePi (fun _ : ℕ => P)))) - N*h n/2)/N := by
  let μ := fun i => enrichedIncrementLaw N n h u (i+1)
  let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
    (Measure.infinitePi (fun _ : ℕ => P)))
  let R := Q.prod (noiseCascadeLaw (Spin N → ℝ) n b μ : Measure (NoiseTree (Spin N → ℝ) n))
  have hL := (enriched_poisson_variance hN n b hb hh h0 u hu ν P hm hK hφ r).1
  have hLd : MemLp (fun p => enrichedPoissonLog n b h u ν φ p / N) 2 R := by
    simpa only [div_eq_mul_inv] using hL.mul_const (N:ℝ)⁻¹
  have hco := hLd.comp_measurePreserving (enrichedToNoise_preserving P r n b h u)
  have hco' := MemLp.ae_eq (enrichedCoordinatePressure_eq_noise P r n b h hb u ν hm).symm hco
  unfold enrichedMeanPressure
  simp_rw [enrichedCylinderPressure_eq_coordinates]
  rw [integral_comp_preserving_ae (enrichedCylinderToCoordinates_preserving P r N n b)
    hco'.aestronglyMeasurable]
  rw [integral_congr_ae (enrichedCoordinatePressure_eq_noise P r n b h hb u ν hm)]
  rw [integral_comp_preserving_ae (enrichedToNoise_preserving P r n b h u) hLd.aestronglyMeasurable]
  rw [integral_div]
  change (∫ p : EnrichedPoissonRoot N A × NoiseTree (Spin N → ℝ) n,
    (cascadeEnergyLog n b μ ν (enrichedPoissonBase n h u φ p.1) p.2-(N:ℝ)*h n/2) ∂ R)/(N:ℝ) = _
  rw [integral_sub ((enriched_poisson_unshifted hN n b hb hh h0 u hu ν P hm hK hφ r).1.integrable (by norm_num))
    (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  congr 1
  congr 1
  exact cascadeEnergyLog_total_mean Q n b hb μ ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1))
    (measurable_enrichedPoissonBase n h u hm)
    (enriched_poisson_root_variance hN n b (fun i hi => (hb.1 i hi).1) hh h0 u hu ν P hm hK hφ r).1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron


lemma spinSign_integral (z : ℝ) :
    (∫ x : Fin 2, Real.exp (z*spinValue x) ∂(PMF.uniformOfFintype (Fin 2)).toMeasure) = Real.cosh z := by
  rw [integral_fintype (Integrable.of_finite),Fin.sum_univ_two]
  simp only [measureReal_def,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply,Fintype.card_fin,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    smul_eq_mul,spinValue]
  norm_num
  rw [Real.cosh_eq]
  ring

lemma finiteLogIntegral_magnetic {N : ℕ} (z : Fin N → ℝ) :
    finiteLogIntegral (spinLaw N) (magneticEnergy z) = ∑ i, Real.log (Real.cosh (z i)) := by
  unfold finiteLogIntegral magneticEnergy spinLaw
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (z i*spinValue x))]
  simp only [spinSign_integral]
  rw [Real.log_prod (fun i _ => (Real.cosh_pos _).ne')]

lemma logMean_independent_sum {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (F : ι → ℝ → ℝ)
    {b : ℝ} (_hb : b ≠ 0)
    (_hF : ∀ i, Measurable (F i)) (hi : ∀ i, Integrable (fun x => Real.exp (b*F i x)) (μ i)) :
    logMean b (Measure.pi μ) (fun z => ∑ i, F i (z i)) = ∑ i, logMean b (μ i) (F i) := by
  have hp (i : ι) : 0 < ∫ x, Real.exp (b*F i x) ∂μ i :=
    integral_exp_pos (μ i) (F i) (hi i)
  unfold logMean
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp (b*F i x)),Real.log_prod (fun i _ => (hp i).ne'),Finset.sum_div]

lemma HasLinearGrowth.scale_argument {F : ℝ → ℝ} (h : HasLinearGrowth F) (a : ℝ) :
    HasLinearGrowth (fun x => F (a*x)) := by
  obtain ⟨C,L,hC,hL,h⟩ := h
  refine ⟨C,L*|a|,hC,mul_nonneg hL (abs_nonneg a),fun x => ?_⟩
  simpa only [Real.norm_eq_abs,abs_mul,mul_assoc] using h (a*x)

lemma gaussianTransform_positive_linearGrowth {U : ℝ → ℝ} (hU : Measurable U)
    (hG : HasLinearGrowth U) (s : ℝ) {d : ℝ} (hd : 0 < d) :
    HasLinearGrowth (gaussianTransform s d U) := by
  let μ : Measure ℝ := gaussianReal 0 (NNReal.mk ((Real.sqrt s)^2) (sq_nonneg _))
  have hm : (gaussianReal 0 1).map (fun z => Real.sqrt s*z) = μ := by
    simpa only [zero_mul,NNReal.coe_mk,mul_zero,mul_one] using
      gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt s)
  have he (x : ℝ) : gaussianTransform s d U x=logMean d μ (fun z => U (x+z)) := by
    simp only [gaussianTransform,hd.ne',ite_false,logMean]
    rw [← hm]
    have hg : Measurable (fun a : ℝ => Real.exp (d*U (x+a))) :=
      ((hU.comp (measurable_const.add measurable_id)).const_mul d).exp
    rw [integral_map (show AEMeasurable (fun z : ℝ => Real.sqrt s*z) (gaussianReal 0 1) from
      (measurable_id.const_mul _).aemeasurable) hg.aestronglyMeasurable]
  change HasLinearGrowth (fun x => gaussianTransform s d U x)
  simp_rw [he]
  exact logMean_hasLinearGrowth μ (gaussianReal_exponentialNormMoments _ _) hU hG hd

lemma measurable_gaussianTransform {U : ℝ → ℝ} (hU : Measurable U) (s d : ℝ) :
    Measurable (gaussianTransform s d U) := by
  unfold gaussianTransform
  split
  · exact (hU.comp (measurable_fst.add (measurable_snd.const_mul _))).stronglyMeasurable.integral_prod_right'.measurable
  · exact Real.measurable_log.comp (((hU.comp
      (measurable_fst.add (measurable_snd.const_mul _))).const_mul d).exp.stronglyMeasurable.integral_prod_right'.measurable) |>.div_const d

lemma gaussianFold_linearGrowth (L : List (ℝ × ℝ))
    (hd : ∀ sd ∈ L, 0 < sd.2) {F : ℝ → ℝ} (hm : Measurable F) (hG : HasLinearGrowth F) :
    Measurable (L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) F) ∧
      HasLinearGrowth (L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) F) := by
  induction L with
  | nil => exact ⟨hm,hG⟩
  | cons sd L ih =>
    have hh := ih (fun sd h => hd sd (List.mem_cons_of_mem _ h))
    exact ⟨measurable_gaussianTransform hh.1 _ _,
      gaussianTransform_positive_linearGrowth hh.1 hh.2 _ (hd sd (List.mem_cons_self))⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma magneticEnergy_add {N : ℕ} (z w : Fin N → ℝ) :
    magneticEnergy (z+w) = magneticEnergy z+magneticEnergy w := by
  ext x
  simp [magneticEnergy,add_mul,Finset.sum_add_distrib]

lemma enrichedIncrement_zero {N n : ℕ} (h : ℕ → ℝ) (i : ℕ)
    (g : Fin (Fintype.card (EnrichedBlock N)) → ℝ) :
    enrichedIncrement N n h 0 i g =
      magneticEnergy (fun j => pathAmplitude h i*g ((Fintype.equivFin (EnrichedBlock N)) (.inl j))) := by
  ext x
  unfold enrichedIncrement enrichedCoefficientsFin
  have he := (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
    (fun j => enrichedLevelCoefficient n h 0 i x j*g ((Fintype.equivFin (EnrichedBlock N)) j))
  simp only [Equiv.apply_symm_apply] at he
  rw [he]
  simp only [Fintype.sum_sum_type,enrichedLevelCoefficient,Pi.zero_apply,mul_zero,
    zero_mul,Finset.sum_const_zero,add_zero, magneticEnergy]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma enrichedIncrementLaw_zero (N n : ℕ) (h : ℕ → ℝ) (i : ℕ) :
    enrichedIncrementLaw N n h 0 i = magneticIncrementLaw N (pathAmplitude h i) := by
  let e := Fintype.equivFin (EnrichedBlock N)
  let tag : Fin N → ℕ := fun j => (e (.inl j)).val
  have ht : Function.Injective tag := fun j k hjk => Sum.inl_injective (e.injective (Fin.ext hjk))
  have hf := gaussian_pullback_measurePreserving (fun j : Fin (Fintype.card (EnrichedBlock N)) => j.val)
    Fin.val_injective
  have hg := gaussian_pullback_measurePreserving tag ht
  rw [Measure.infinitePi_eq_pi] at hf hg
  apply Subtype.ext
  change (Measure.pi _).map (enrichedIncrement N n h 0 i) = (Measure.pi _).map _
  have hm : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun j => pathAmplitude h i*z j)) :=
    (measurable_magneticEnergy N).comp (by fun_prop)
  rw [← hf.map_eq,← hg.map_eq,Measure.map_map (measurable_enrichedIncrement N n h 0 i)
     hf.measurable,Measure.map_map hm hg.measurable]
  congr 1
  ext g x
  rw [Function.comp_apply,Function.comp_apply,enrichedIncrement_zero]

lemma logMean_magneticIncrement {N : ℕ} (a b : ℝ) (F : (Spin N → ℝ) → ℝ)
    (hF : Measurable F) :
    logMean b (magneticIncrementLaw N a : Measure (Spin N → ℝ)) F =
      logMean b (Measure.pi (fun _ : Fin N => gaussianReal 0 1))
        (fun z => F (magneticEnergy (fun i => a*z i))) := by
  unfold logMean
  change Real.log (∫ H, Real.exp (b*F H) ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
    (fun z => magneticEnergy (fun i => a*z i)))/b = _
  have hm : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun i => a*z i)) :=
    (measurable_magneticEnergy N).comp (by fun_prop)
  rw [integral_map hm.aemeasurable
    ((hF.const_mul b).exp.aestronglyMeasurable)]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma magneticRecursion_growth (n : ℕ) (a b : ℕ → ℝ) (hb : ∀ i < n, 0 < b i) :
    Measurable (magneticRecursion n a b) ∧ HasLinearGrowth (magneticRecursion n a b) := by
  induction n generalizing a b with
  | zero => exact ⟨measurable_logCosh,logCosh_linearGrowth⟩
  | succ n ih =>
    have H := ih (fun i => a (i+1)) (fun i => b (i+1)) (fun i hi => hb (i+1) (by omega))
    exact ⟨measurable_gaussianTransform H.1 _ _,gaussianTransform_positive_linearGrowth H.1 H.2 _ (hb 0 (by omega))⟩

lemma magneticRecursion_eq_fold (n : ℕ) (a b : ℕ → ℝ) :
    magneticRecursion n a b =
      (List.ofFn (fun i : Fin n => ((a i)^2,b i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U) (fun x => Real.log (Real.cosh x)) := by
  induction n generalizing a b with
  | zero => simp [magneticRecursion]
  | succ n ih =>
    rw [List.ofFn_succ,List.foldr_cons]
    simp only [magneticRecursion,ih,Fin.val_zero,Fin.val_succ]

lemma energyRecursion_magnetic (N n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i < n, 0 ≤ a i) (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    energyRecursion n b (fun i => magneticIncrementLaw N (a i)) (spinLaw N) (magneticEnergy z) =
      ∑ i, magneticRecursion n a b (z i) := by
  induction n generalizing a b z with
  | zero => exact finiteLogIntegral_magnetic z
  | succ n ih =>
    let U := magneticRecursion n (fun i => a (i+1)) (fun i => b (i+1))
    have hU := magneticRecursion_growth n (fun i => a (i+1)) (fun i => b (i+1))
      (fun i hi => hb (i+1) (by omega))
    change logMean (b 0) (magneticIncrementLaw N (a 0) : Measure (Spin N → ℝ))
      (fun H => energyRecursion n (fun i => b (i+1)) (fun i => magneticIncrementLaw N (a (i+1)))
        (spinLaw N) (magneticEnergy z+H)) = _
    have hm : Measurable (fun H : Spin N → ℝ => energyRecursion n (fun i => b (i+1))
        (fun i => magneticIncrementLaw N (a (i+1))) (spinLaw N) (magneticEnergy z+H)) :=
      (measurable_energyRecursion _ _ _ _).comp (measurable_const.add measurable_id)
    rw [logMean_magneticIncrement _ _ _ hm]
    have H (g : Fin N → ℝ) : energyRecursion n (fun i => b (i+1))
      (fun i => magneticIncrementLaw N (a (i+1))) (spinLaw N)
        (magneticEnergy z+magneticEnergy (fun i => a 0*g i)) = ∑ i, U (z i+a 0*g i) := by
      rw [← magneticEnergy_add]
      exact ih _ _ (fun i hi => ha (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)) _
    simp_rw [H]
    rw [logMean_independent_sum (fun _ : Fin N => gaussianReal 0 1)
      (fun i t => U (z i+a 0*t)) (hb 0 (by omega)).ne']
    · apply Finset.sum_congr rfl
      intro i _
      simp only [magneticRecursion,gaussianTransform,(hb 0 (by omega)).ne',ite_false,
        Real.sqrt_sq (ha 0 (by omega)),logMean,U]
    · intro i
      exact hU.1.comp (measurable_const.add (measurable_id.const_mul _))
    · intro i
      exact integrable_exp_of_linearGrowth (gaussianReal 0 1)
        (gaussianReal_exponentialNormMoments _ _)
        (hU.1.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hU.2.add_left (z i)).scale_argument (a 0)) _

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_linearGrowth_integrable {F : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (m : ℝ) (v : ℝ≥0) : Integrable F (gaussianReal m v) := by
  obtain ⟨C,L,hC,hL,h⟩ := hG
  have hi : Integrable (fun x : ℝ => C+L*‖x‖) (gaussianReal m v) :=
    (integrable_const _).add (((memLp_id_gaussianReal (μ := m) (v := v) 1).integrable le_rfl).norm.const_mul L)
  exact hi.mono' hF.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using h x))

lemma gaussianTransform_const_add {U : ℝ → ℝ} (hU : Measurable U) (hG : HasLinearGrowth U)
    (s d c : ℝ) :
    gaussianTransform s d (fun x => c+U x) = fun x => c+gaussianTransform s d U x := by
  ext x
  by_cases hd : d=0
  · simp only [gaussianTransform,hd,ite_true]
    have hi : Integrable (fun z : ℝ => U (x+Real.sqrt s*z)) (gaussianReal 0 1) :=
      gaussian_linearGrowth_integrable
        (hU.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) _ _
    rw [integral_add (integrable_const c) hi]
    simp only [integral_const,probReal_univ,one_smul]
  · simp only [gaussianTransform,hd,ite_false]
    exact logMean_const_add (gaussianReal 0 1) hd
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
        (hU.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) d) c

lemma gaussianFold_const_add (L : List (ℝ × ℝ)) (hd : ∀ sd ∈ L, 0 < sd.2)
    {F : ℝ → ℝ} (hm : Measurable F) (hG : HasLinearGrowth F) (c : ℝ) :
    L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) (fun x => c+F x) =
      fun x => c+L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) F x := by
  induction L with
  | nil => rfl
  | cons sd L ih =>
    simp only [List.foldr_cons]
    rw [ih (fun sd h => hd sd (List.mem_cons_of_mem _ h))]
    have hh := gaussianFold_linearGrowth L (fun sd h => hd sd (List.mem_cons_of_mem _ h)) hm hG
    exact gaussianTransform_const_add hh.1 hh.2 _ _ _

lemma poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n with
  | zero => simp
  | succ n => simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron



lemma integral_magnetic_energyRecursion (N n : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i < n, 0 ≤ a i) (hb : ∀ i < n, 0 < b i) (a₀ : ℝ) :
    (∫ z, energyRecursion n b (fun i => magneticIncrementLaw N (a i)) (spinLaw N)
       (magneticEnergy (fun i => a₀*z i)) ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      (N:ℝ)*(∫ z, magneticRecursion n a b (a₀*z) ∂gaussianReal 0 1) := by
  have hU := magneticRecursion_growth n a b hb
  have hm : Measurable (fun z : ℝ => magneticRecursion n a b (a₀*z)) :=
    hU.1.comp (measurable_id.const_mul _)
  have hi := gaussian_linearGrowth_integrable hm (hU.2.scale_argument a₀) 0 1
  have hpi (i : Fin N) : Integrable (fun z : Fin N → ℝ => magneticRecursion n a b (a₀*z i))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) :=
    ((measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).integrable_comp
      (g := fun z : ℝ => magneticRecursion n a b (a₀*z)) hm.aestronglyMeasurable).mpr hi
  simp_rw [energyRecursion_magnetic N n a b ha hb]
  rw [integral_finsetSum _ (fun i _ => hpi i)]
  have he (i : Fin N) :
    (∫ z : Fin N → ℝ, magneticRecursion n a b (a₀*z i) ∂Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      (∫ z, magneticRecursion n a b (a₀*z) ∂gaussianReal 0 1) :=
    integral_comp_preserving_ae (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i)
      (F := fun z : ℝ => magneticRecursion n a b (a₀*z)) hm.aestronglyMeasurable
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

 

theorem enrichedMeanPressure_initial_zero {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) :
    enrichedMeanPressure P 0 n b h 0 (spinLaw N) φ = magneticFieldValue n b h := by
  have hu : ∀ j : Fin N, |(0 : Fin N → ℝ) j| ≤ 2 := by intro j; norm_num
  let μ := fun i => enrichedIncrementLaw N n h 0 (i+1)
  let γ := Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)
  let ρ := Measure.infinitePi (fun _ : ℕ => P)
  have hL := (enriched_poisson_root_variance hN n b (fun i hi => (hb.1 i hi).1)
    hh h0 0 hu (spinLaw N) P hm hK hφ 0).1
  have hi : Integrable (fun p => energyRecursion n b μ (spinLaw N) (enrichedPoissonBase n h 0 φ p))
      ((poissonMeasure 0).prod (γ.prod ρ)) := hL.integrable (by norm_num)
  rw [enrichedMeanPressure_recursion hN n b hb hh h0 0 hu (spinLaw N) P hm hK hφ 0]
  change ((∫ p, energyRecursion n b μ (spinLaw N) (enrichedPoissonBase n h 0 φ p)
    ∂(poissonMeasure 0).prod (γ.prod ρ))-(N:ℝ)*h n/2)/(N:ℝ) = _
  rw [integral_prod _ hi,poissonMeasure_zero_eq_dirac,integral_dirac]
  have hbase (p : (Fin (EnrichedRootSize N) → ℝ) × (ℕ → A)) :
      enrichedPoissonBase n h 0 φ (0,p) = enrichedIncrement N n h 0 0 p.1 := by
    ext x
    simp [enrichedPoissonBase,enrichedBaseEnergy,rootPrefix,patternBase]
  simp_rw [hbase]
  rw [integral_fun_fst (fun z => energyRecursion n b μ (spinLaw N) (enrichedIncrement N n h 0 0 z))]
  simp only [probReal_univ,one_smul]
  have hmap : (∫ z, energyRecursion n b μ (spinLaw N) (enrichedIncrement N n h 0 0 z) ∂γ) =
      ∫ H, energyRecursion n b μ (spinLaw N) H ∂(enrichedIncrementLaw N n h 0 0 : Measure (Spin N → ℝ)) := by
    symm
    exact integral_map (measurable_enrichedIncrement N n h 0 0).aemeasurable
      (measurable_energyRecursion _ _ _ _).aestronglyMeasurable
  rw [hmap]
  dsimp only [μ]
  simp_rw [enrichedIncrementLaw_zero]
  have hmag : (∫ H, energyRecursion n b
        (fun i => magneticIncrementLaw N (pathAmplitude h (i+1))) (spinLaw N) H
      ∂(magneticIncrementLaw N (pathAmplitude h 0) : Measure (Spin N → ℝ))) =
      (N:ℝ)*(∫ z, magneticRecursion n (fun i => pathAmplitude h (i+1)) b (pathAmplitude h 0*z)
        ∂gaussianReal 0 1) := by
    change (∫ H, energyRecursion n b (fun i => magneticIncrementLaw N (pathAmplitude h (i+1)))
      (spinLaw N) H ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
        (fun z => magneticEnergy (fun i => pathAmplitude h 0*z i))) = _
    have hme : Measurable (fun z : Fin N → ℝ => magneticEnergy (fun i => pathAmplitude h 0*z i)) :=
      (measurable_magneticEnergy N).comp (by fun_prop)
    rw [integral_map hme.aemeasurable (measurable_energyRecursion _ _ _ _).aestronglyMeasurable]
    exact integral_magnetic_energyRecursion N n _ b (fun i _ => Real.sqrt_nonneg _)
      (fun i hi => (hb.1 i hi).1) _
  rw [hmag]
  unfold magneticFieldValue
  field_simp [Nat.cast_ne_zero.mpr hN.ne']

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_BoundedTiltAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded Tilt Average. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma exp_mul_integrable_of_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {U : Ω → ℝ} (hU : Measurable U)
    {K : ℝ} (hK : ∀ x, |U x| ≤ K) (d : ℝ) :
    Integrable (fun x => Real.exp (d*U x)) P := by
  apply Integrable.of_bound ((measurable_const.mul hU).exp).aestronglyMeasurable (Real.exp (|d| * K))
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
    change |d * U x| ≤ |d| * K
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK x) (abs_nonneg _)))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianTransform_abs_le {U : ℝ → ℝ} (hU : Measurable U)
    {K : ℝ} (hK : ∀ y, |U y| ≤ K) (s : ℝ) {d : ℝ} (hd : 0 ≤ d) (x : ℝ) :
    |gaussianTransform s d U x| ≤ K := by
  by_cases hz : d = 0
  · subst d
    simp only [gaussianTransform,ite_true]
    simpa [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
        (f := fun z => U (x+Real.sqrt s*z)) (C := K)
        (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hK (x+Real.sqrt s*z)))
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
    let Z := ∫ z, Real.exp (d*U (x+Real.sqrt s*z)) ∂gaussianReal 0 1
    have hi := exp_mul_integrable_of_bound (gaussianReal 0 1)
      (hU.comp (by fun_prop : Measurable (fun z => x+Real.sqrt s*z))) (fun z => hK _) d
    have hlo : Real.exp (-d*K) ≤ Z := by
      calc
        _ = ∫ _ : ℝ, Real.exp (-d*K) ∂gaussianReal 0 1 := by simp
        _ ≤ Z := integral_mono (integrable_const _) hi (fun z => Real.exp_le_exp.mpr (by
          have h := (abs_le.mp (hK (x+Real.sqrt s*z))).1
          nlinarith))
    have hhi : Z ≤ Real.exp (d*K) := by
      calc
        Z ≤ ∫ _ : ℝ, Real.exp (d*K) ∂gaussianReal 0 1 :=
          integral_mono hi (integrable_const _) (fun z => Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (abs_le.mp (hK _)).2 hd))
        _ = _ := by simp
    have hZ : 0 < Z := (Real.exp_pos _).trans_le hlo
    have hloglo := Real.log_le_log (Real.exp_pos _) hlo
    have hloghi := Real.log_le_log hZ hhi
    simp only [Real.log_exp] at hloglo hloghi
    simp only [gaussianTransform,hz,ite_false]
    change |Real.log Z/d| ≤ K
    apply abs_le.mpr
    exact ⟨(le_div_iff₀ hdpos).mpr (by nlinarith), (div_le_iff₀ hdpos).mpr (by nlinarith)⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_RetainedDisplacement
attribute [-instance] _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Displacement. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 
lemma map_powerIntensity_retained {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (b : ℝ)
    (μ : Measure A) (P : Measure B) (Q : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {c : A → ℝ} (hc : Measurable c) (hcpos : ∀ a, 0 < c a)
    {T : B → C} (hT : Measurable T) (hLaw : P.map T = Q) :
    ((powerIntensity b).prod (μ.prod P)).map
      (fun p : ℝ × (A × B) => (c p.2.1 * p.1,(p.2.1,T p.2.2))) =
      (powerIntensity b).prod ((μ.withDensity (fun a => ENNReal.ofReal (c a ^ b))).prod Q) := by
  have hF : Measurable (fun p : ℝ × (A × B) => (c p.2.1*p.1,(p.2.1,T p.2.2))) := by fun_prop
  have hw : Measurable (fun a => ENNReal.ofReal (c a ^ b)) := (hc.pow_const b).ennreal_ofReal
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hF,lintegral_prod
    (fun p : ℝ × (A × B) => f (c p.2.1*p.1,(p.2.1,T p.2.2))) (hf.comp hF).aemeasurable]
  have hv (x : ℝ) (a : A) :
      (∫⁻ v, f (c a*x,(a,T v)) ∂P) = ∫⁻ w, f (c a*x,(a,w)) ∂Q := by
    rw [← hLaw,lintegral_map]
    · fun_prop
    · exact hT
  have hp (x : ℝ) : (∫⁻ v : A × B, f (c v.1*x,(v.1,T v.2)) ∂μ.prod P) =
      ∫⁻ a, ∫⁻ w, f (c a*x,(a,w)) ∂Q ∂μ := by
    rw [lintegral_prod (fun v : A × B => f (c v.1*x,(v.1,T v.2)))
      ((hf.comp hF).comp (measurable_const.prodMk measurable_id)).aemeasurable]
    simp_rw [hv]
  simp_rw [hp]
  have hG : Measurable (fun p : ℝ × A => ∫⁻ w, f (c p.2*p.1,(p.2,w)) ∂Q) :=
    (hf.comp (by fun_prop : Measurable (fun p : (ℝ × A) × C => (c p.1.2*p.1.1,(p.1.2,p.2))))).lintegral_prod_right'
  rw [lintegral_lintegral_swap hG.aemeasurable]
  have hx (a : A) : (∫⁻ x, ∫⁻ w, f (c a*x,(a,w)) ∂Q ∂powerIntensity b) =
      ENNReal.ofReal (c a ^ b) * (∫⁻ x, ∫⁻ w, f (x,(a,w)) ∂Q ∂powerIntensity b) := by
    have hfa : Measurable (fun x : ℝ => ∫⁻ w, f (x,(a,w)) ∂Q) :=
      (hf.comp (by fun_prop : Measurable (fun z : ℝ × C => (z.1,(a,z.2))))).lintegral_prod_right'
    rw [← lintegral_map hfa (measurable_const_mul (c a)),map_powerIntensity_mul (hcpos a),lintegral_smul_measure]
    rfl
  simp_rw [hx]
  have hga : Measurable (fun a : A => ∫⁻ x, ∫⁻ w, f (x,(a,w)) ∂Q ∂powerIntensity b) :=
    ((hf.comp (by fun_prop : Measurable (fun z : (A × ℝ) × C => (z.1.2,(z.1.1,z.2))))).lintegral_prod_right').lintegral_prod_right'
  calc
    _ = ∫⁻ a, ∫⁻ x, ∫⁻ w, f (x,(a,w)) ∂Q ∂powerIntensity b
        ∂μ.withDensity (fun a => ENNReal.ofReal (c a ^ b)) :=
      (lintegral_withDensity_eq_lintegral_mul μ hw hga).symm
    _ = _ := by
      rw [lintegral_lintegral_swap]
      · rw [lintegral_prod _ hf.aemeasurable]
        congr 1; funext x
        exact (lintegral_prod _ (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
      · exact ((hf.comp (by fun_prop : Measurable (fun z : (A × ℝ) × C => (z.1.2,(z.1.1,z.2))))).lintegral_prod_right').aemeasurable

 

theorem noiseTreeKeep_independent_law {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ ν : ℕ → ProbabilityMeasure A) (c : ℕ → A → ℝ)
    (hc : ∀ i, Measurable (c i)) (hcpos : ∀ i a, 0 < c i a)
    (hν : ∀ i, (ν i : Measure A) = (μ i : Measure A).withDensity (fun a => ENNReal.ofReal (c i a ^ b i))) :
    (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)).map
      (noiseTreeKeep n b μ (fun i (p : PUnit × A) => c i p.2) (fun _ _ => PUnit.unit) PUnit.unit) =
      noiseCascadeLaw A n b ν := by
  induction n generalizing b μ ν c with
  | zero => exact Measure.map_dirac' measurable_const _
  | succ n ih =>
    let μ' := fun i => μ (i+1)
    let ν' := fun i => ν (i+1)
    let b' := fun i => b (i+1)
    let c' := fun i => c (i+1)
    let P : Measure (NoiseTree A n) := noiseCascadeLaw A n b' μ'
    let Q : Measure (NoiseTree A n) := noiseCascadeLaw A n b' ν'
    let T := noiseTreeKeep n b' μ' (fun i (p : PUnit × A) => c' i p.2) (fun _ _ => PUnit.unit) PUnit.unit
    have hT : Measurable T := (measurable_noiseTreeKeep n b' μ' (fun i => (hc (i+1)).comp measurable_snd)
      (fun _ => measurable_const)).comp (measurable_const.prodMk measurable_id)
    have hLaw : P.map T = Q := ih b' μ' ν' c' (fun i => hc (i+1)) (fun i => hcpos (i+1)) (fun i => hν (i+1))
    let I := (powerIntensity (b 0)).prod ((μ 0 : Measure A).prod P)
    let G : ℝ × (A × NoiseTree A n) → ℝ × (A × NoiseTree A n) := fun p => (c 0 p.2.1*p.1,(p.2.1,T p.2.2))
    have hG : Measurable G := by fun_prop
    have hI : I.map G = (powerIntensity (b 0)).prod ((ν 0 : Measure A).prod Q) := by
      rw [hν 0]
      exact map_powerIntensity_retained (b 0) (μ 0 : Measure A) P Q (hc 0) (hcpos 0) hT hLaw
    rw [noiseCascadeLaw_succ,noiseCascadeLaw_succ]
    change (poissonLaw I).map _ = poissonLaw ((powerIntensity (b 0)).prod ((ν 0 : Measure A).prod Q))
    calc
      _ = (poissonLaw I).map (fun V => V.map G) := by
        apply Measure.map_congr
        filter_upwards [sigmaPart_eq_ae I] with V hV
        change (sigmaPart I V).map G = V.map G
        rw [hV]
      _ = poissonLaw (I.map G) := poissonLaw_map I hG
      _ = _ := poissonLaw_congr hI

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

variable {A : Type} [MeasurableSpace A]

lemma measurable_noiseLeafMark (n : ℕ) (i : Fin n) : Measurable (fun v : NoiseLeaf A n => noiseLeafMark n v i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst.comp measurable_snd
    · exact (ih j).comp (measurable_snd.comp measurable_snd)

omit [MeasurableSpace A] in
lemma noiseLeafMark_keep {S : Type} (n : ℕ) (c : ℕ → S × A → ℝ) (u : ℕ → S × A → S)
    (s : S) (v : NoiseLeaf A n) (i : Fin n) :
    noiseLeafMark n (noiseLeafKeep n c u s v) i = noiseLeafMark n v i := by
  induction n generalizing c u s with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact ih _ _ _ _ j

lemma noiseLeafMark_labeled (n : ℕ) (ω : LabeledTree n) (g : ForestVertex n → A)
    (v : LabeledLeaf n) (i : Fin n) :
    noiseLeafMark n (labeledNoiseLeaf A n (ω,markForestOfCoords A n g) v) i = g (edgeAt n v i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [noiseLeafMark,labeledNoiseLeaf,markForestOfCoords,edgeAt,nodeAt_zero]
    · simpa only [noiseLeafMark,Fin.cases_succ,labeledNoiseLeaf,markForestOfCoords,edgeAt,nodeAt_succ] using
        ih (ω.2 v.1.1 v.1.2) (fun w => g (v.1.1,v.1.2,some w)) v.2 j

lemma edgeAt_eq_iff_prefix (n : ℕ) (v w : LabeledLeaf n) (d : Fin n) :
    edgeAt n v d = edgeAt n w d ↔ (labeledAddress n v).take (d+1) = (labeledAddress n w).take (d+1) := by
  rw [← Option.some_inj,← (nodeAddress_injective n).eq_iff,← nodeAt_succ,← nodeAt_succ,
    nodeAddress_nodeAt,nodeAddress_nodeAt]
  rfl

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma sampling_replica_morphism {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] [MeasurableSpace Y] (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω')
    {ν : Ω → Measure X} {κ : Ω' → Measure Y} (hν : Measurable ν) (hκ : Measurable κ)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (κ ω)]
    {T : Ω → Ω'} (hT : Measurable T) (hPQ : P.map T = Q)
    {ψ : Ω → X → Y} (hψ : Measurable (fun p : Ω × X => ψ p.1 p.2))
    (h : ∀ᵐ ω ∂P, (ν ω).map (ψ ω) = κ (T ω)) :
    (P ⊗ₘ probabilityReplicaKernel ν hν).map (fun p i => ψ p.1 (p.2 i)) =
      probabilityReplicaKernel κ hκ ∘ₘ Q := by
  have hΨ : Measurable (fun p : Ω × (ℕ → X) => fun i => ψ p.1 (p.2 i)) := by
    apply Measurable.of_eval
    intro i
    exact hψ.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hΨ,Measure.lintegral_compProd
    (show Measurable (fun p : Ω × (ℕ → X) => F (fun i => ψ p.1 (p.2 i))) from hF.comp hΨ)]
  have he : (∫⁻ ω, ∫⁻ σ, F (fun i => ψ ω (σ i)) ∂(probabilityReplicaKernel ν hν) ω ∂P) =
      ∫⁻ ω, ∫⁻ σ, F σ ∂(probabilityReplicaKernel κ hκ) (T ω) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [h] with ω hω
    change (∫⁻ σ, F (fun i => ψ ω (σ i)) ∂Measure.infinitePi (fun _ : ℕ => ν ω)) =
      ∫⁻ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => κ (T ω))
    have hψω : Measurable (ψ ω) := hψ.comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_map hF (by fun_prop : Measurable (fun σ : ℕ → X => fun i => ψ ω (σ i))),
      Measure.infinitePi_map_pi _ (fun _ => hψω)]
    simp only [hω]
  rw [he]
  have hI : Measurable (fun ω => ∫⁻ σ, F σ ∂(probabilityReplicaKernel κ hκ) ω) := hF.lintegral_kernel
  rw [← lintegral_map hI hT,hPQ]
  change _ = ∫⁻ σ, F σ ∂Q.bind (probabilityReplicaKernel κ hκ)
  exact (Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable).symm

 

theorem labeled_marked_replica_law {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure A) :
    let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))
    (P ⊗ₘ probabilityReplicaKernel (fun p => labeledLeafLaw n p.1)
      ((measurable_labeledLeafLaw n).comp measurable_fst)).map
      (fun p i => labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) (p.2 i)) =
      markedReplicaLaw n b μ := by
  intro P
  let T := fun p : LabeledTree n × (ForestVertex n → A) =>
    labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)
  have hT : Measurable T := by fun_prop
  have hPQ : P.map T = (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) :=
    labeledNoiseCoordinates_law A n b μ
  have hp : MeasurePreserving T P (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) := ⟨hT,hPQ⟩
  apply sampling_replica_morphism P _ (ν := fun p : LabeledTree n × (ForestVertex n → A) => labeledLeafLaw n p.1)
    (κ := noiseLeafKernel A n) ((measurable_labeledLeafLaw n).comp measurable_fst)
    (noiseLeafKernel A n).measurable hT hPQ
    (ψ := fun p v => labeledNoiseLeaf A n (p.1,markForestOfCoords A n p.2) v)
  · apply measurable_from_prod_countable_left
    intro v
    exact (measurable_labeledNoiseLeaf A n v).comp (by fun_prop)
  · filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseCascade_good A n b hb μ)] with p hp
    apply labeledLeafLaw_noiseMap A n p.1 (markForestOfCoords A n p.2) hp
    cases n with
    | zero => simp [noiseTreeTotal,rawTreeTotal]
    | succ n => exact hp.1

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma normalizeMass_exp {X : Type*} [MeasurableSpace X] [Nonempty X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) ν) :
    normalizeMass (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) = ν.tilted H := by
  have hZ : (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))) univ =
      ENNReal.ofReal (∫ x, Real.exp (H x) ∂ν) := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal he (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  have hpos := _root_.MeasureTheory.integral_exp_pos he
  rw [normalizeMass,ite_eq_left (by rw [hZ]; exact ⟨ENNReal.ofReal_pos.mpr hpos,ENNReal.ofReal_lt_top⟩),
    hZ,Measure.tilted,← withDensity_smul _ hH.exp.ennreal_ofReal]
  congr 1; funext x
  simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_inv_of_pos hpos,mul_comm]

lemma normalizeMass_weight_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y] (ν : Measure X) {ψ : X → Y} (hψ : Measurable ψ)
    {w : Y → ℝ≥0∞} (hw : Measurable w)
    (hm : 0 < ((ν.map ψ).withDensity w) univ ∧ ((ν.map ψ).withDensity w) univ < ∞) :
    (normalizeMass (ν.withDensity (fun x => w (ψ x)))).map ψ =
      normalizeMass ((ν.map ψ).withDensity w) := by
  have he := withDensity_map_pullback ν hψ hw
  have hmass : (ν.withDensity (fun x => w (ψ x))) univ = ((ν.map ψ).withDensity w) univ := by
    rw [← he,Measure.map_apply hψ MeasurableSet.univ]; rfl
  rw [normalizeMass_map _ hψ (by simpa only [hmass] using hm),he]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma kernel_comap_comp_measure {Ω Ω' X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] (P : Measure Ω) (K : Kernel Ω' X) {T : Ω → Ω'} (hT : Measurable T) :
    K.comap T hT ∘ₘ P = K ∘ₘ P.map T := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),Measure.bind_apply hs K.aemeasurable,
    lintegral_map (K.measurable_coe hs) hT]
  rfl

lemma replica_mark_transport {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] [MeasurableSpace Y] (P : Measure Ω) (Q : Measure Ω')
    {ν : Ω → Measure X} {κ : Ω' → Measure X} (hν : Measurable ν) (hκ : Measurable κ)
    [∀ ω, IsProbabilityMeasure (ν ω)] [∀ ω, IsProbabilityMeasure (κ ω)]
    {T : Ω → Ω'} (hT : Measurable T) (hPQ : P.map T = Q)
    {ψ : X → Y} (hψ : Measurable ψ)
    (h : ∀ᵐ ω ∂P, (ν ω).map ψ = (κ (T ω)).map ψ) :
    ((probabilityReplicaKernel ν hν) ∘ₘ P).map (fun σ i => ψ (σ i)) =
      ((probabilityReplicaKernel κ hκ) ∘ₘ Q).map (fun σ i => ψ (σ i)) := by
  let K := (probabilityReplicaKernel κ hκ).map (fun σ i => ψ (σ i))
  have hΨ : Measurable (fun σ : ℕ → X => fun i => ψ (σ i)) := by fun_prop
  rw [Measure.map_comp _ _ hΨ,Measure.map_comp _ _ hΨ]
  calc
    _ = K.comap T hT ∘ₘ P := by
      apply Measure.comp_congr
      filter_upwards [h] with ω hω
      simp only [Kernel.map_apply _ hΨ,Kernel.comap_apply,probabilityReplicaKernel,K]
      change (Measure.infinitePi (fun _ : ℕ => ν ω)).map (fun σ i => ψ (σ i)) =
        (Measure.infinitePi (fun _ : ℕ => κ (T ω))).map (fun σ i => ψ (σ i))
      rw [Measure.infinitePi_map_pi _ (fun _ => hψ),Measure.infinitePi_map_pi _ (fun _ => hψ)]
      simp only [hω]
    _ = K ∘ₘ Q := by rw [kernel_comap_comp_measure,hPQ]



theorem noise_mark_replica_transport {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ ν : ℕ → ProbabilityMeasure A)
    (c : ℕ → A → ℝ) (hc : ∀ i, Measurable (c i)) (hcpos : ∀ i a, 0 < c i a)
    (hν : ∀ i, (ν i : Measure A) = (μ i : Measure A).withDensity (fun a => ENNReal.ofReal (c i a ^ b i))) :
    ((probabilityReplicaKernel
      (noiseTiltedLeafLaw n (fun i (p : PUnit × A) => c i p.2) (fun _ _ => PUnit.unit) PUnit.unit)
      (measurable_noiseTiltedLeafLaw n (fun i => (hc i).comp measurable_snd) (fun _ => measurable_const) PUnit.unit)) ∘ₘ
      (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))).map
      (fun σ i => noiseLeafMark n (σ i)) =
      (markedReplicaLaw n b ν).map (fun σ i => noiseLeafMark n (σ i)) := by
  let c' := fun i (p : PUnit × A) => c i p.2
  let u := fun (_ : ℕ) (_ : PUnit × A) => PUnit.unit
  let T := noiseTreeKeep n b μ c' u PUnit.unit
  let ψ := noiseLeafMark (A := A) n
  have hc' : ∀ i, Measurable (c' i) := fun i => (hc i).comp measurable_snd
  have hu : ∀ i, Measurable (u i) := fun _ => measurable_const
  have hT : Measurable T := (measurable_noiseTreeKeep n b μ hc' hu).comp (measurable_const.prodMk measurable_id)
  have hψ : Measurable ψ := Measurable.of_eval (measurable_noiseLeafMark n)
  have hm (i : ℕ) (s : PUnit) : ∫⁻ a, ENNReal.ofReal (c' i (s,a)^b i) ∂(μ i : Measure A) = 1 := by
    have he := congrArg (fun P : Measure A => P univ) (hν i)
    simpa only [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,measure_univ] using he.symm
  apply replica_mark_transport _ _ (measurable_noiseTiltedLeafLaw n hc' hu PUnit.unit)
    (noiseLeafKernel A n).measurable hT (noiseTreeKeep_independent_law n b μ ν c hc hcpos hν) hψ
  filter_upwards [noiseGibbsRegular_ae n b hb μ hc' hu (fun i _ a => hcpos i a) hm PUnit.unit] with ω hω
  have he := noiseTiltedLeafLaw_keep n b μ hc' hu (fun i _ a => hcpos i a) PUnit.unit ω hω
  have hk : Measurable (noiseLeafKeep n c' u PUnit.unit) :=
    (measurable_noiseLeafKeep n hc' hu).comp (measurable_const.prodMk measurable_id)
  rw [← he,Measure.map_map hψ hk]
  congr 1
  funext v i
  exact (noiseLeafMark_keep n c' u PUnit.unit v i).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma regular_product_mass {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]
    {n : ℕ} {b : ℕ → ℝ} {μ : ℕ → ProbabilityMeasure A}
    {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a)) {s : S} {ν : NoiseTree A n}
    (hν : NoiseGibbsRegular n b μ c u s ν) :
    0 < ((noiseLeafKernel A n ν).withDensity (noiseLeafProduct n c u s)) univ ∧
      ((noiseLeafKernel A n ν).withDensity (noiseLeafProduct n c u s)) univ < ∞ := by
  let m := (noiseLeafKernel A n ν).withDensity (noiseLeafProduct n c u s)
  have hp : Measurable (noiseLeafProduct n c u s) :=
    (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id)
  have hk : Measurable (noiseLeafKeep n c u s) :=
    (measurable_noiseLeafKeep n hc hu).comp (measurable_const.prodMk measurable_id)
  have he : (noiseTreeTotal A n ν • m).map (noiseLeafKeep n c u s) =
      noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) •
        noiseLeafKernel A n (noiseTreeKeep n b μ c u s ν) := by
    have hh := noiseWeightedLeafMeasure_eq n b μ hc hu hcpos s ν hν
    unfold noiseWeightedLeafMeasure at hh
    change Measure.map (noiseLeafKeep n c u s)
      ((noiseLeafKernel A n ν).withDensity (noiseTreeTotal A n ν • noiseLeafProduct n c u s)) = _ at hh
    rwa [withDensity_smul _ hp] at hh
  have hm : noiseTreeTotal A n ν * m univ = noiseTreeTotal A n (noiseTreeKeep n b μ c u s ν) := by
    have hh := congrArg (fun η : Measure (NoiseLeaf A n) => η univ) he
    simpa only [Measure.map_apply hk MeasurableSet.univ, preimage_univ,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using hh
  have hm0 : 0 < m univ := by
    by_contra hh
    have hz : m univ = 0 := le_antisymm (le_of_not_gt hh) bot_le
    rw [hz,mul_zero] at hm
    exact hν.masses.2.1.ne' hm.symm
  refine ⟨hm0,?_⟩
  have hlt : noiseTreeTotal A n ν * m univ < ∞ := hm ▸ hν.masses.2.2
  rcases ENNReal.mul_lt_top_iff.mp hlt with h | h | h
  · exact h.2
  · exact (hν.masses.1.1.ne' h).elim
  · exact (hm0.ne' h).elim



theorem labeled_weighted_marked_replica_law {A S : Type} [MeasurableSpace A]
    [MeasurableSpace S] [Nonempty A] (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {c : ℕ → S × A → ℝ} {u : ℕ → S × A → S}
    (hc : ∀ i, Measurable (c i)) (hu : ∀ i, Measurable (u i))
    (hcpos : ∀ i s a, 0 < c i (s,a))
    (hm : ∀ i s, ∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A) = 1) (s : S) :
    let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))
    (P ⊗ₘ probabilityReplicaKernel (labeledWeightedLeafLaw n c u s)
      (measurable_labeledWeightedLeafLaw n hc hu s)).map
      (fun p i => labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) (p.2 i)) =
      probabilityReplicaKernel (noiseTiltedLeafLaw n c u s)
        (measurable_noiseTiltedLeafLaw n hc hu s) ∘ₘ (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) := by
  intro P
  let T := fun p : LabeledTree n × (ForestVertex n → A) =>
    labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)
  have hT : Measurable T := by fun_prop
  have hPQ : P.map T = (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) :=
    labeledNoiseCoordinates_law A n b μ
  have hp : MeasurePreserving T P (noiseCascadeLaw A n b μ : Measure (NoiseTree A n)) := ⟨hT,hPQ⟩
  apply sampling_replica_morphism P _ (measurable_labeledWeightedLeafLaw n hc hu s)
    (measurable_noiseTiltedLeafLaw n hc hu s) hT hPQ
    (ψ := fun p v => labeledNoiseLeaf A n (p.1,markForestOfCoords A n p.2) v)
  · apply measurable_from_prod_countable_left
    intro v
    exact (measurable_labeledNoiseLeaf A n v).comp (by fun_prop)
  · filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseCascade_good A n b hb μ),
      hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseGibbsRegular_ae n b hb μ hc hu hcpos hm s)] with p hg hr
    have hleaf := labeledLeafLaw_noiseMap A n p.1 (markForestOfCoords A n p.2) hg hr.masses.1
    have hw : Measurable (noiseLeafProduct n c u s) :=
      (measurable_noiseLeafProduct n hc hu).comp (measurable_const.prodMk measurable_id)
    have he := normalizeMass_weight_map (labeledLeafLaw n p.1)
      (measurable_of_countable (labeledNoiseLeaf A n (p.1,markForestOfCoords A n p.2))) hw
      (by rw [hleaf]; exact regular_product_mass hc hu hcpos hr)
    simpa only [hleaf,labeledWeightedLeafLaw,labeledWeightedMass,labeledWeight,noiseTiltedLeafLaw] using he

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianReal_shift_density (m : ℝ) :
    (gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (Real.exp (m*x-m^2/2))) =
      gaussianReal m 1 := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul volume (measurable_gaussianPDF _ _) (by fun_prop)]
  congr 1
  funext x
  dsimp only [Pi.mul_apply,gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,mul_assoc,← Real.exp_add]
  congr 2
  ring

lemma retainedGaussianScale_density (b a : ℝ) :
    (gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (retainedGaussianScale b a x ^ b)) =
      gaussianReal (b*a) 1 := by
  convert gaussianReal_shift_density (b*a) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1; funext x
  rw [retainedGaussianScale,← Real.exp_mul]
  congr 2
  ring

lemma retainedGaussianScale_normalized (b a : ℝ) :
    (∫⁻ x, ENNReal.ofReal (retainedGaussianScale b a x ^ b) ∂gaussianReal 0 1) = 1 := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) (retainedGaussianScale_density b a)
  simpa only [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,measure_univ] using h



end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma independent_atomless_injective {I : Type*} [Countable I]
    (μ : I → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, NullSingletonClass (μ i)] :
    ∀ᵐ g ∂Measure.infinitePi μ, Function.Injective g := by
  change ∀ᵐ g ∂Measure.infinitePi μ, ∀ i j, g i=g j → i=j
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i=j
  · subst j; exact ae_of_all _ (fun _ _ => rfl)
  have hp : MeasurePreserving (fun g : I → ℝ => (g i,g j)) (Measure.infinitePi μ) ((μ i).prod (μ j)) :=
    ⟨by fun_prop,Measure.infinitePi_map_eval_prod hij⟩
  have ha : ∀ᵐ p : ℝ × ℝ ∂(μ i).prod (μ j), p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact ae_of_all _ (fun x => by simp only [ae_iff]; simp)
  filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually ha] with g hg
  exact fun h => (hg h).elim

lemma gaussian_marks_injective (n : ℕ) (m : ℕ → ℝ) :
    ∀ᵐ g ∂Measure.infinitePi (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1),
      Function.Injective g := by
  let (v : ForestVertex n) : NullSingletonClass (gaussianReal (m (forestVertexDepth n v)) 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  exact independent_atomless_injective _

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_SamplingIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling Independent. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

lemma independent_marks_sampling {Ω G X : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace X] (P : Measure Ω) (Q : Measure G) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (K : Kernel Ω X) [IsMarkovKernel K] :
    ((P.prod Q) ⊗ₘ K.comap Prod.fst measurable_fst).map (fun p => (p.2,p.1.2)) =
      (K ∘ₘ P).prod Q := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  simp only [Kernel.comap_apply]
  have hI : Measurable (fun p : Ω × G => ∫⁻ x, F (x,p.2) ∂K p.1) :=
    (show Measurable (fun p : (Ω × G) × X => F (p.2,p.1.2)) from by fun_prop).lintegral_kernel_prod_right' (κ := K.comap Prod.fst measurable_fst)
  rw [lintegral_prod _ hI.aemeasurable]
  have he (ω : Ω) : (∫⁻ g, ∫⁻ x, F (x,g) ∂K ω ∂Q) = ∫⁻ x, ∫⁻ g, F (x,g) ∂Q ∂K ω :=
    lintegral_lintegral_swap (by fun_prop)
  simp_rw [he]
  rw [lintegral_prod _ hF.aemeasurable]
  exact (Measure.lintegral_bind (Kernel.aemeasurable K) (hF.lintegral_prod_right').aemeasurable).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma noiseLeafProduct_exp_marks (n : ℕ) (E : ℕ → ℝ → ℝ) (v : NoiseLeaf ℝ n) :
    noiseLeafProduct n (fun i (p : PUnit × ℝ) => Real.exp (E i p.2))
      (fun _ _ => PUnit.unit) PUnit.unit v =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, E i (noiseLeafMark n v i))) := by
  induction n generalizing E with
  | zero => simp [noiseLeafProduct]
  | succ n ih =>
    rw [noiseLeafProduct,ih,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,
      Fin.sum_univ_succ]
    rfl

lemma noiseLeafProduct_retained_labeled (n : ℕ) (b a : ℕ → ℝ) (ω : LabeledTree n)
    (g : ForestVertex n → ℝ) (v : LabeledLeaf n) :
    noiseLeafProduct n (fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (a i) p.2)
      (fun _ _ => PUnit.unit) PUnit.unit (labeledNoiseLeaf ℝ n (ω,markForestOfCoords ℝ n g) v) =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, (a i*g (edgeAt n v i)-b i*a i^2/2))) := by
  rw [show (fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (a i) p.2) =
    (fun i p => Real.exp (a i*p.2-b i*a i^2/2)) by rfl]
  rw [noiseLeafProduct_exp_marks n (fun i x => a i*x-b i*a i^2/2)]
  simp only [noiseLeafMark_labeled]

lemma noiseLeafProduct_single_level (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ)
    (ω : LabeledTree n) (g : ForestVertex n → ℝ) (v : LabeledLeaf n) :
    noiseLeafProduct n (fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (if i = d then t else 0) p.2)
      (fun _ _ => PUnit.unit) PUnit.unit (labeledNoiseLeaf ℝ n (ω,markForestOfCoords ℝ n g) v) =
      ENNReal.ofReal (Real.exp (t*g (edgeAt n v d)-b d*t^2/2)) := by
  rw [noiseLeafProduct_retained_labeled]
  congr 2
  rw [Finset.sum_eq_single d]
  · simp
  · intro i _ hi
    have hne : (i:ℕ) ≠ d := fun h => hi (Fin.ext h)
    simp [hne]
  · simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_selected_coordinate {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] {e : X → I} (he : Measurable e) :
    Measurable (fun p : X × (I → ℝ) => p.2 (e p.1)) := by
  have hv : Measurable (fun p : (I → ℝ) × I => p.1 p.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  exact hv.comp (measurable_snd.prodMk (he.comp measurable_fst))

lemma selected_coordinate_prod_law {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (P : Measure X) [IsProbabilityMeasure P] (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {e : X → I} (he : Measurable e) (v : Measure ℝ) [IsProbabilityMeasure v]
    (hm : ∀ x, μ (e x) = v) :
    (P.prod (Measure.infinitePi μ)).map (fun p => (p.1,p.2 (e p.1))) = P.prod v := by
  have hT : Measurable (fun p : X × (I → ℝ) => (p.1,p.2 (e p.1))) :=
    measurable_fst.prodMk (measurable_selected_coordinate he)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hT]
  have hFT : Measurable (fun p : X × (I → ℝ) => F (p.1,p.2 (e p.1))) := hF.comp hT
  rw [lintegral_prod _ hFT.aemeasurable]
  rw [lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro x
  have hFx : Measurable (fun y => F (x,y)) := hF.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_map hFx (measurable_pi_apply (e x))]
  change (∫⁻ a, F (x,a) ∂(Measure.infinitePi μ).map (fun g => g (e x))) = _
  rw [Measure.infinitePi_map_eval,hm]

lemma selected_gaussian_score {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (P : Measure X) [IsProbabilityMeasure P] (mean : I → ℝ)
    {e : X → I} (he : Measurable e) (m : ℝ) (hm : ∀ x, mean (e x) = m)
    {D : X → ℝ} (hD : Measurable D) :
    (∫ p : X × (I → ℝ), D p.1*p.2 (e p.1) ∂P.prod (Measure.infinitePi (fun i => gaussianReal (mean i) 1))) =
      (∫ x, D x ∂P)*m := by
  have hlaw := selected_coordinate_prod_law P (fun i => gaussianReal (mean i) 1) he
    (gaussianReal m 1) (fun x => by rw [hm x])
  have hT : Measurable (fun p : X × (I → ℝ) => (p.1,p.2 (e p.1))) :=
    measurable_fst.prodMk (measurable_selected_coordinate he)
  have hF : Measurable (fun p : X × ℝ => D p.1*p.2) := by fun_prop
  rw [← integral_map hT.aemeasurable hF.aestronglyMeasurable,hlaw,integral_prod_mul D (fun y : ℝ => y),integral_id_gaussianReal]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_replicaMarkPath {A : Type} [MeasurableSpace A] (n : ℕ) :
    Measurable (replicaMarkPath (A := A) n) := by
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro d
  exact (measurable_noiseLeafMark n d).comp (measurable_pi_apply i)

lemma measurable_coordinateMarkPath {A : Type} [MeasurableSpace A] (n : ℕ) :
    Measurable (coordinateMarkPath (A := A) n) := by
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro d
  have hv : Measurable (fun p : (ForestVertex n → A) × LabeledLeaf n => p.1 (edgeAt n p.2 d)) :=
    measurable_from_prod_countable_left (fun v => measurable_pi_apply (edgeAt n v d))
  exact hv.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))

 

theorem marked_path_law {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure A) :
    (markedReplicaLaw n b μ).map (replicaMarkPath n) =
      ((cascadeReplicaLaw n b).prod (Measure.infinitePi
        (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))).map (coordinateMarkPath n) := by
  let Q := Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A))
  let P := (labeledCascadeLaw n b : Measure (LabeledTree n)).prod Q
  let K := probabilityReplicaKernel (labeledLeafLaw n) (measurable_labeledLeafLaw n)
  have hΨ : Measurable (fun p : (LabeledTree n × (ForestVertex n → A)) × (ℕ → LabeledLeaf n) =>
      fun i => labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) (p.2 i)) := by
    apply Measurable.of_eval; intro i
    have hm : Measurable (fun p : (LabeledTree n × (ForestVertex n → A)) × LabeledLeaf n =>
        labeledNoiseLeaf A n (p.1.1,markForestOfCoords A n p.1.2) p.2) := by
      apply measurable_from_prod_countable_left; intro v
      exact (measurable_labeledNoiseLeaf A n v).comp (by fun_prop)
    exact hm.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  rw [← labeled_marked_replica_law n b hb μ,Measure.map_map (measurable_replicaMarkPath n) hΨ]
  have he := independent_marks_sampling (labeledCascadeLaw n b : Measure (LabeledTree n)) Q K
  change (P ⊗ₘ K.comap Prod.fst measurable_fst).map _ = _
  rw [show (cascadeReplicaLaw n b).prod Q =
    (P ⊗ₘ K.comap Prod.fst measurable_fst).map (fun p => (p.2,p.1.2)) from he.symm,
    Measure.map_map (measurable_coordinateMarkPath n) (by fun_prop)]
  congr 1
  funext p i d
  exact noiseLeafMark_labeled n p.1.1 p.1.2 (p.2 i) d

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_sampledMarkPath (n : ℕ) : Measurable (sampledMarkPath n) :=
  (measurable_coordinateMarkPath n).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))

 
theorem retained_joint_path_law (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (a : ℕ → ℝ) :
    (retainedLabelJoint n b a).map (sampledMarkPath n) =
      (markedReplicaLaw n b (fun i => ⟨gaussianReal (b i*a i) 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩)).map (replicaMarkPath n) := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun _ => ⟨gaussianReal 0 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  let ν : ℕ → ProbabilityMeasure ℝ := fun i => ⟨gaussianReal (b i*a i) 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  let c := fun i (p : PUnit × ℝ) => retainedGaussianScale (b i) (a i) p.2
  let u := fun (_ : ℕ) (_ : PUnit × ℝ) => PUnit.unit
  have hc : ∀ i, Measurable (c i) := fun i => by unfold c retainedGaussianScale; fun_prop
  have hu : ∀ i, Measurable (u i) := fun _ => measurable_const
  have hm : ∀ i s, ∫⁻ x, ENNReal.ofReal (c i (s,x)^b i) ∂(μ i : Measure ℝ) = 1 :=
    fun i _ => retainedGaussianScale_normalized _ _
  have hL := labeled_weighted_marked_replica_law n b hb μ hc hu
    (fun i s x => Real.exp_pos _) hm PUnit.unit
  have hM := noise_mark_replica_transport n b hb μ ν
    (fun i x => retainedGaussianScale (b i) (a i) x)
    (fun i => by unfold retainedGaussianScale; fun_prop) (fun i x => Real.exp_pos _)
    (fun i => (retainedGaussianScale_density _ _).symm)
  have hΨ : Measurable (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) =>
      fun i => labeledNoiseLeaf ℝ n (p.1.1,markForestOfCoords ℝ n p.1.2) (p.2 i)) := by
    apply Measurable.of_eval; intro i
    have hψ : Measurable (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × LabeledLeaf n =>
        labeledNoiseLeaf ℝ n (p.1.1,markForestOfCoords ℝ n p.1.2) p.2) := by
      apply measurable_from_prod_countable_left; intro v
      exact (measurable_labeledNoiseLeaf ℝ n v).comp (by fun_prop)
    exact hψ.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have he := congrArg (fun P : Measure (ℕ → NoiseLeaf ℝ n) => P.map (replicaMarkPath n)) hL
  rw [Measure.map_map (measurable_replicaMarkPath n) hΨ] at he
  have hpath : (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) =>
      replicaMarkPath n (fun i => labeledNoiseLeaf ℝ n (p.1.1,markForestOfCoords ℝ n p.1.2) (p.2 i))) =
      sampledMarkPath n := by
    funext p i d
    exact noiseLeafMark_labeled n p.1.1 p.1.2 (p.2 i) d
  change (retainedLabelJoint n b a).map _ = _ at he
  change (retainedLabelJoint n b a).map _ = _
  rw [show (replicaMarkPath n ∘ (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) =>
    fun i => labeledNoiseLeaf ℝ n (p.1.1,markForestOfCoords ℝ n p.1.2) (p.2 i))) = sampledMarkPath n from hpath] at he
  exact he.trans hM

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma tilted_sub_constant {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (he : Integrable (fun x => Real.exp (H x)) ν) (c : ℝ) :
    ν.tilted (fun x => H x-c) = ν.tilted H := by
  have := isProbabilityMeasure_tilted he
  have h := tilted_tilted he (fun _ => -c)
  simpa only [tilted_const,Pi.add_def,sub_eq_add_neg] using h.symm

lemma retainedLabelLeafLaw_single_tilted (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ)
    (p : LabeledTree n × (ForestVertex n → ℝ))
    (he : Integrable (fun v => Real.exp (t*p.2 (edgeAt n v d))) (labeledLeafLaw n p.1)) :
    retainedLabelLeafLaw n b (fun i => if i = d then t else 0) p =
      (labeledLeafLaw n p.1).tilted (fun v => t*p.2 (edgeAt n v d)) := by
  have hW : (fun v => labeledWeight n
      (fun i (q : PUnit × ℝ) => retainedGaussianScale (b i) (if i = d then t else 0) q.2)
      (fun _ _ => PUnit.unit) PUnit.unit (p,v)) =
      (fun v => ENNReal.ofReal (Real.exp (t*p.2 (edgeAt n v d)-b d*t^2/2))) := by
    funext v
    exact noiseLeafProduct_single_level n b d t p.1 p.2 v
  unfold retainedLabelLeafLaw labeledWeightedLeafLaw labeledWeightedMass
  rw [hW]
  have hei : Integrable (fun v => Real.exp (t*p.2 (edgeAt n v d)-b d*t^2/2)) (labeledLeafLaw n p.1) := by
    simpa only [Real.exp_sub] using he.div_const (Real.exp (b d*t^2/2))
  rw [normalizeMass_exp _ _ (measurable_of_countable _) hei,
    tilted_sub_constant _ _ he]

lemma leafLevelCoefficients_field (n : ℕ) (d : Fin n) (v : LabeledLeaf n) (g : ℕ → ℝ) :
    cylinderField (leafLevelCoefficients n d v) g = edgeGaussianCoordinates n g (edgeAt n v d) := by
  simp [leafLevelCoefficients,cylinderField,Finsupp.sum_single_index,edgeGaussianCoordinates]

lemma leafLevelCoefficients_bound (n : ℕ) (d : Fin n) (v : LabeledLeaf n) :
    (leafLevelCoefficients n d v).sum (fun _ c => c^2) ≤ 1 := by
  simp [leafLevelCoefficients,Finsupp.sum_single_index]

lemma leafLevelCoefficients_diag (n : ℕ) (d : Fin n) (v : LabeledLeaf n) :
    cylinderCross (leafLevelCoefficients n d v) (leafLevelCoefficients n d v) = 1 := by
  simp [leafLevelCoefficients,cylinderCross_single_left]

lemma leafLevelCoefficients_cross (n : ℕ) (d : Fin n) (v w : LabeledLeaf n) :
    cylinderCross (leafLevelCoefficients n d v) (leafLevelCoefficients n d w) =
      if (labeledAddress n v).take (d+1) = (labeledAddress n w).take (d+1) then 1 else 0 :=
  labelLevelCoefficients_cross n d (PUnit.unit,v) (PUnit.unit,w)

lemma rawLeafGibbs_retained (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ)
    (p : LabeledTree n × (ℕ → ℝ))
    (he : Integrable (fun v => Real.exp (t*cylinderField (leafLevelCoefficients n d v) p.2)) (labeledLeafLaw n p.1)) :
    rawLeafGibbs n d t p =
      retainedLabelLeafLaw n b (fun i => if i = d then t else 0) (p.1,edgeGaussianCoordinates n p.2) := by
  have heq : (fun v => t*cylinderField (leafLevelCoefficients n d v) p.2) =
      (fun v => t*edgeGaussianCoordinates n p.2 (edgeAt n v d)) := by
    funext v; rw [leafLevelCoefficients_field]
  have he' : Integrable (fun v => Real.exp (t*edgeGaussianCoordinates n p.2 (edgeAt n v d))) (labeledLeafLaw n p.1) := by
    simpa only [leafLevelCoefficients_field] using he
  have hR := retainedLabelLeafLaw_single_tilted n b d t (p.1,edgeGaussianCoordinates n p.2) he'
  have hG : rawLeafGibbs n d t p = (labeledLeafLaw n p.1).tilted
      (fun v => t*cylinderField (leafLevelCoefficients n d v) p.2) := gibbsProbability_eq_tilted _ _ he
  exact hG.trans ((congrArg (fun H => (labeledLeafLaw n p.1).tilted H) heq).trans hR.symm)

lemma rawLeafGibbs_retained_ae (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ) :
    ∀ᵐ p ∂rawLabelBase n b, rawLeafGibbs n d t p =
      retainedLabelLeafLaw n b (fun i => if i = d then t else 0) (p.1,edgeGaussianCoordinates n p.2) := by
  have ha := random_cylinder_all_exp_ae (P := (labeledCascadeLaw n b : Measure (LabeledTree n)))
      (measurable_labeledLeafLaw n) (leafLevelCoefficients n d) (leafLevelCoefficients_bound n d)
  exact ha.mono (fun p hp => rawLeafGibbs_retained n b d t p (hp t))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma compProd_base_map {Ω Ω' X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] (P : Measure Ω) [SFinite P] (Q : Measure Ω') [SFinite Q]
    (K : Kernel Ω X) [IsSFiniteKernel K] (L : Kernel Ω' X) [IsSFiniteKernel L]
    {T : Ω → Ω'} (hT : Measurable T) (hPQ : P.map T = Q)
    (hK : ∀ᵐ ω ∂P, K ω = L (T ω)) :
    (P ⊗ₘ K).map (fun p => (T p.1,p.2)) = Q ⊗ₘ L := by
  have hS : Measurable (fun p : Ω × X => (T p.1,p.2)) := (hT.comp measurable_fst).prodMk measurable_snd
  apply Measure.ext_of_lintegral
  intro F hF
  have hFS : Measurable (fun p : Ω × X => F (T p.1,p.2)) := hF.comp hS
  rw [lintegral_map hF hS,Measure.lintegral_compProd hFS,
    Measure.lintegral_compProd hF]
  calc
    _ = ∫⁻ ω, ∫⁻ x, F (T ω,x) ∂L (T ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hK] with ω hω
      rw [hω]
    _ = _ := by
      have hI : Measurable (fun ω' => ∫⁻ x, F (ω',x) ∂L ω') :=
        Measurable.lintegral_kernel_prod_right (f := fun ω' x => F (ω',x)) hF
      rw [← lintegral_map hI hT,hPQ]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_rawLabelToRetained (n : ℕ) : Measurable (rawLabelToRetained n) :=
  (measurable_fst.fst.prodMk ((edgeGaussianCoordinates_preserving n).measurable.comp measurable_fst.snd)).prodMk measurable_snd

lemma raw_retained_joint_preserving (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ) :
    MeasurePreserving (rawLabelToRetained n) (rawLabelJoint n b d t)
      (retainedLabelJoint n b (fun i => if i = d then t else 0)) := by
  have hp : MeasurePreserving (fun p : LabeledTree n × (ℕ → ℝ) => (p.1,edgeGaussianCoordinates n p.2))
      (rawLabelBase n b) (retainedLabelBase n b) :=
    (MeasurePreserving.id _).prod (edgeGaussianCoordinates_preserving n)
  refine ⟨measurable_rawLabelToRetained n,?_⟩
  apply compProd_base_map _ _ _ _ hp.measurable hp.map_eq
  filter_upwards [rawLeafGibbs_retained_ae n b d t] with p he
  change Measure.infinitePi (fun _ : ℕ => rawLeafGibbs n d t p) =
    Measure.infinitePi (fun _ : ℕ => retainedLabelLeafLaw n b (fun i => if i = d then t else 0)
      (p.1,edgeGaussianCoordinates n p.2))
  rw [he]

lemma rawJoint_integral_reference (n : ℕ) (b : ℕ → ℝ) (d : Fin n) (t : ℝ) (r : ℕ)
    (F : (LabeledTree n × (ℕ → ℝ)) → (Fin r → LabeledLeaf n) → ℝ)
    (hi : Integrable (fun p => F p.1 (fun i => p.2 i)) (rawLabelJoint n b d t)) :
    (∫ p, F p.1 (fun i => p.2 i) ∂rawLabelJoint n b d t) =
      ∫ p, referenceReplicaMean (labeledLeafLaw n p.1)
        (fun v => t*cylinderField (leafLevelCoefficients n d v) p.2) (F p) ∂rawLabelBase n b := by
  rw [show rawLabelJoint n b d t = rawLabelBase n b ⊗ₘ
    probabilityReplicaKernel (rawLeafGibbs n d t) (measurable_rawLeafGibbs n d t) from rfl,
    Measure.integral_compProd hi]
  have ha := random_cylinder_all_exp_ae (P := (labeledCascadeLaw n b : Measure (LabeledTree n)))
      (measurable_labeledLeafLaw n) (leafLevelCoefficients n d) (leafLevelCoefficients_bound n d)
  apply integral_congr_ae
  filter_upwards [ha] with p hp
  have he := hp t
  have hg : rawLeafGibbs n d t p = (labeledLeafLaw n p.1).tilted
      (fun v => t*cylinderField (leafLevelCoefficients n d v) p.2) := gibbsProbability_eq_tilted _ _ he
  rw [referenceReplicaMean_eq_tilted _ _ he,← hg]
  change (∫ σ, F p (fun i => σ i) ∂Measure.infinitePi (fun _ : ℕ => rawLeafGibbs n d t p)) = _
  have hh := (HasLaw.mk (P := Measure.infinitePi (fun _ : ℕ => rawLeafGibbs n d t p))
    (show AEMeasurable (fun σ : ℕ → LabeledLeaf n => fun i : Fin r => σ i) _ from (by fun_prop : Measurable _).aemeasurable)
    (replica_prefix_map (rawLeafGibbs n d t p) r)).integral_comp
    (measurable_of_countable (F p)).aestronglyMeasurable
  exact hh

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_pathPrefixPattern (n r : ℕ) : Measurable (pathPrefixPattern n r) := by
  unfold pathPrefixPattern
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  apply Measurable.of_eval; intro d
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_eq_fun ((measurable_pi_apply d).comp (measurable_pi_apply (i:ℕ)))
    ((measurable_pi_apply d).comp (measurable_pi_apply (j:ℕ)))

lemma pathPrefixPattern_coordinates (n r : ℕ) (σ : ℕ → LabeledLeaf n)
    (g : ForestVertex n → ℝ) (hg : Function.Injective g) :
    pathPrefixPattern n r (coordinateMarkPath n (σ,g)) =
      labelPrefixPattern n r (fun i => σ i) := by
  funext i j d
  unfold pathPrefixPattern coordinateMarkPath labelPrefixPattern
  simp only [hg.eq_iff,edgeAt_eq_iff_prefix]

lemma gaussianMarkedPathLaw_eq (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (m : ℕ → ℝ) :
    gaussianMarkedPathLaw n b m =
      ((cascadeReplicaLaw n b).prod (Measure.infinitePi
        (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1))).map (coordinateMarkPath n) :=
  marked_path_law n b hb _

lemma path_shape_ae_coordinates (n r : ℕ) (b m : ℕ → ℝ) :
    ∀ᵐ p ∂(cascadeReplicaLaw n b).prod (Measure.infinitePi
        (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1)),
      pathPrefixPattern n r (coordinateMarkPath n p) = labelPrefixPattern n r (fun i => p.1 i) := by
  have ha := gaussian_marks_injective n m
  have hp := measurePreserving_snd (μ := cascadeReplicaLaw n b)
    (ν := Measure.infinitePi (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1))
  filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually ha] with p hp
  exact pathPrefixPattern_coordinates n r p.1 p.2 hp

 
theorem gaussian_marked_shape (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (m : ℕ → ℝ) (D : PrefixPattern n r → ℝ) :
    (∫ z, D (pathPrefixPattern n r z) ∂gaussianMarkedPathLaw n b m) =
      ∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b := by
  have hD := measurable_of_countable D
  have hF : Measurable (fun z => D (pathPrefixPattern n r z)) := hD.comp (measurable_pathPrefixPattern n r)
  rw [gaussianMarkedPathLaw_eq n b hb m,
    integral_map (measurable_coordinateMarkPath n).aemeasurable hF.aestronglyMeasurable]
  calc
    _ = ∫ p, D (labelPrefixPattern n r (fun i => p.1 i))
        ∂(cascadeReplicaLaw n b).prod (Measure.infinitePi
          (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1)) :=
      integral_congr_ae ((path_shape_ae_coordinates n r b m).mono (fun _ h => congrArg D h))
    _ = _ := by
      simpa using integral_fun_fst (μ := cascadeReplicaLaw n b)
        (ν := Measure.infinitePi (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1))
        (fun σ => D (labelPrefixPattern n r (fun i => σ i)))

 

theorem gaussian_marked_shape_score (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (m : ℕ → ℝ) (d : Fin n) (D : PrefixPattern n r → ℝ) :
    (∫ z, D (pathPrefixPattern n r z)*z 0 d ∂gaussianMarkedPathLaw n b m) =
      (∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b)*m d := by
  have hD := measurable_of_countable D
  have hF : Measurable (fun z : ℕ → Fin n → ℝ => D (pathPrefixPattern n r z)*z 0 d) :=
    (hD.comp (measurable_pathPrefixPattern n r)).mul
      ((measurable_pi_apply d).comp (measurable_pi_apply 0))
  rw [gaussianMarkedPathLaw_eq n b hb m,
    integral_map (measurable_coordinateMarkPath n).aemeasurable hF.aestronglyMeasurable]
  calc
    _ = ∫ p, D (labelPrefixPattern n r (fun i => p.1 i))*p.2 (edgeAt n (p.1 0) d)
        ∂(cascadeReplicaLaw n b).prod (Measure.infinitePi
          (fun v : ForestVertex n => gaussianReal (m (forestVertexDepth n v)) 1)) := by
      apply integral_congr_ae
      filter_upwards [path_shape_ae_coordinates n r b m] with p hp
      rw [hp]; rfl
    _ = _ := by
      let : MeasurableSpace (ForestVertex n) := ⊤
      let : MeasurableSingletonClass (ForestVertex n) := ⟨fun _ => MeasurableSet.of_discrete⟩
      exact selected_gaussian_score (cascadeReplicaLaw n b) (fun v => m (forestVertexDepth n v))
        ((measurable_of_countable (fun v : LabeledLeaf n => edgeAt n v d)).comp (measurable_pi_apply 0))
        (m d) (fun σ => by simp only [Function.comp_apply,forestVertexDepth_edgeAt])
        (hD.comp (measurable_infiniteLabelPattern n r))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma selected_gaussian_score_integrable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I]
    (P : Measure X) [IsProbabilityMeasure P] (mean : I → ℝ)
    {e : X → I} (he : Measurable e) (m : ℝ) (hm : ∀ x, mean (e x) = m)
    {D : X → ℝ} (hD : Measurable D) (hi : Integrable D P) :
    Integrable (fun p : X × (I → ℝ) => D p.1*p.2 (e p.1))
      (P.prod (Measure.infinitePi (fun i => gaussianReal (mean i) 1))) := by
  have hlaw := selected_coordinate_prod_law P (fun i => gaussianReal (mean i) 1) he
    (gaussianReal m 1) (fun x => by rw [hm x])
  have hT : Measurable (fun p : X × (I → ℝ) => (p.1,p.2 (e p.1))) :=
    measurable_fst.prodMk (measurable_selected_coordinate he)
  have hF : Measurable (fun p : X × ℝ => D p.1*p.2) := by fun_prop
  have hG : Integrable (fun x : ℝ => x) (gaussianReal m 1) :=
    (memLp_id_gaussianReal (μ := m) (v := 1) 1).integrable (by norm_num)
  have hiF : Integrable (fun p : X × ℝ => D p.1*p.2) (P.prod (gaussianReal m 1)) := hi.mul_prod hG
  rw [← hlaw] at hiF
  exact (integrable_map_measure hF.aestronglyMeasurable hT.aemeasurable).mp hiF

lemma gaussian_marked_shape_score_integrable (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (m : ℕ → ℝ) (d : Fin n) (D : PrefixPattern n r → ℝ) {c : ℝ} (hD : ∀ x, |D x| ≤ c) :
    Integrable (fun z => D (pathPrefixPattern n r z)*z 0 d) (gaussianMarkedPathLaw n b m) := by
  have hDm := measurable_of_countable D
  have hF : Measurable (fun z : ℕ → Fin n → ℝ => D (pathPrefixPattern n r z)*z 0 d) :=
    (hDm.comp (measurable_pathPrefixPattern n r)).mul
      ((measurable_pi_apply d).comp (measurable_pi_apply 0))
  rw [gaussianMarkedPathLaw_eq n b hb m]
  apply (integrable_map_measure hF.aestronglyMeasurable (measurable_coordinateMarkPath n).aemeasurable).mpr
  let : MeasurableSpace (ForestVertex n) := ⊤
  let : MeasurableSingletonClass (ForestVertex n) := ⟨fun _ => MeasurableSet.of_discrete⟩
  have hiD : Integrable (fun σ : ℕ → LabeledLeaf n => D (labelPrefixPattern n r (fun i => σ i)))
      (cascadeReplicaLaw n b) :=
    integrable_of_measurable_abs_le (hDm.comp (measurable_infiniteLabelPattern n r)) (fun _ => hD _)
  have hi := selected_gaussian_score_integrable (cascadeReplicaLaw n b)
    (fun v => m (forestVertexDepth n v))
    ((measurable_of_countable (fun v : LabeledLeaf n => edgeAt n v d)).comp (measurable_pi_apply 0))
    (m d) (fun σ => by simp only [Function.comp_apply,forestVertexDepth_edgeAt])
    (hDm.comp (measurable_infiniteLabelPattern n r)) hiD
  apply hi.congr
  filter_upwards [path_shape_ae_coordinates n r b m] with p hp
  change D (labelPrefixPattern n r (fun i => p.1 i))*p.2 (edgeAt n (p.1 0) d) = _
  rw [← hp]; rfl

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_JointShapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint Shapes. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma retained_joint_shape_ae (n r : ℕ) (b a : ℕ → ℝ) :
    ∀ᵐ p ∂retainedLabelJoint n b a, pathPrefixPattern n r (sampledMarkPath n p) =
      labelPrefixPattern n r (fun i => p.2 i) := by
  have hg : ∀ᵐ p ∂retainedLabelBase n b, Function.Injective p.2 := by
    have hp := measurePreserving_snd (μ := (labeledCascadeLaw n b : Measure (LabeledTree n)))
      (ν := Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1))
    exact hp.quasiMeasurePreserving.tendsto_ae.eventually (gaussian_marks_injective n (fun _ => 0))
  have hf : MeasurePreserving Prod.fst (retainedLabelJoint n b a) (retainedLabelBase n b) :=
    ⟨measurable_fst,Measure.fst_compProd _ _⟩
  have hh := hf.quasiMeasurePreserving.tendsto_ae.eventually hg
  filter_upwards [hh] with p hp
  exact pathPrefixPattern_coordinates n r p.2 p.1.2 hp

lemma measurable_sampledLabelPattern (n r : ℕ) :
    Measurable (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) =>
      labelPrefixPattern n r (fun i => p.2 i)) :=
  (measurable_infiniteLabelPattern n r).comp measurable_snd

theorem retained_joint_shape (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (a : ℕ → ℝ) (D : PrefixPattern n r → ℝ) :
    (∫ p, D (labelPrefixPattern n r (fun i => p.2 i)) ∂retainedLabelJoint n b a) =
      ∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b := by
  have hF : Measurable (fun z => D (pathPrefixPattern n r z)) :=
    (measurable_of_countable D).comp (measurable_pathPrefixPattern n r)
  calc
    _ = ∫ p, D (pathPrefixPattern n r (sampledMarkPath n p)) ∂retainedLabelJoint n b a := by
      apply integral_congr_ae
      filter_upwards [retained_joint_shape_ae n r b a] with p hp
      rw [hp]
    _ = ∫ z, D (pathPrefixPattern n r z) ∂gaussianMarkedPathLaw n b (fun i => b i*a i) := by
      rw [← integral_map (measurable_sampledMarkPath n).aemeasurable hF.aestronglyMeasurable,
        retained_joint_path_law n b hb a]
      rfl
    _ = _ := gaussian_marked_shape n r b hb _ D

theorem retained_joint_shape_score (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (a : ℕ → ℝ) (d : Fin n) (D : PrefixPattern n r → ℝ) :
    (∫ p, D (labelPrefixPattern n r (fun i => p.2 i))*p.1.2 (edgeAt n (p.2 0) d)
      ∂retainedLabelJoint n b a) =
      (∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b)*(b d*a d) := by
  have hF : Measurable (fun z : ℕ → Fin n → ℝ => D (pathPrefixPattern n r z)*z 0 d) :=
    ((measurable_of_countable D).comp (measurable_pathPrefixPattern n r)).mul
      ((measurable_pi_apply d).comp (measurable_pi_apply 0))
  calc
    _ = ∫ p, D (pathPrefixPattern n r (sampledMarkPath n p))*sampledMarkPath n p 0 d
        ∂retainedLabelJoint n b a := by
      apply integral_congr_ae
      filter_upwards [retained_joint_shape_ae n r b a] with p hp
      rw [hp]; rfl
    _ = ∫ z, D (pathPrefixPattern n r z)*z 0 d ∂gaussianMarkedPathLaw n b (fun i => b i*a i) := by
      rw [← integral_map (measurable_sampledMarkPath n).aemeasurable hF.aestronglyMeasurable,
        retained_joint_path_law n b hb a]
      rfl
    _ = _ := gaussian_marked_shape_score n r b hb _ d D

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma retained_joint_shape_score_integrable (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (a : ℕ → ℝ) (d : Fin n) (D : PrefixPattern n r → ℝ) :
    Integrable (fun p => D (labelPrefixPattern n r (fun i => p.2 i))*p.1.2 (edgeAt n (p.2 0) d))
      (retainedLabelJoint n b a) := by
  obtain ⟨c,hc,hD⟩ := prefixPattern_bound n r D
  have hi := gaussian_marked_shape_score_integrable n r b hb (fun i => b i*a i) d D hD
  have hF : Measurable (fun z : ℕ → Fin n → ℝ => D (pathPrefixPattern n r z)*z 0 d) :=
    ((measurable_of_countable D).comp (measurable_pathPrefixPattern n r)).mul
      ((measurable_pi_apply d).comp (measurable_pi_apply 0))
  change Integrable _ ((markedReplicaLaw n b (fun i => ⟨gaussianReal (b i*a i) 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩)).map (replicaMarkPath n)) at hi
  rw [← retained_joint_path_law n b hb a] at hi
  have hj := (integrable_map_measure hF.aestronglyMeasurable (measurable_sampledMarkPath n).aemeasurable).mp hi
  apply hj.congr
  filter_upwards [retained_joint_shape_ae n r b a] with p hp
  change D (pathPrefixPattern n r (sampledMarkPath n p))*sampledMarkPath n p 0 d = _
  rw [hp]; rfl

lemma raw_joint_shape_score_integrable (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n r → ℝ) :
    Integrable (fun p => D (labelPrefixPattern n r (fun i => p.2 i))*
      cylinderField (leafLevelCoefficients n d (p.2 0)) p.1.2) (rawLabelJoint n b d t) := by
  have hi := retained_joint_shape_score_integrable n r b hb (fun i => if i = d then t else 0) d D
  have hp := raw_retained_joint_preserving n b d t
  have hi' : Integrable (fun p => D (labelPrefixPattern n r (fun i => p.2 i))*p.1.2 (edgeAt n (p.2 0) d))
      ((rawLabelJoint n b d t).map (rawLabelToRetained n)) := by rwa [hp.map_eq]
  have hj := (integrable_map_measure hi'.aestronglyMeasurable hp.measurable.aemeasurable).mp hi'
  change Integrable (fun p : (LabeledTree n × (ℕ → ℝ)) × (ℕ → LabeledLeaf n) => D (labelPrefixPattern n r (fun i => p.2 i))*edgeGaussianCoordinates n p.1.2 (edgeAt n (p.2 0) d)) _ at hj
  simpa only [leafLevelCoefficients_field] using hj

lemma raw_joint_shape (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n r → ℝ) :
    (∫ p, D (labelPrefixPattern n r (fun i => p.2 i)) ∂rawLabelJoint n b d t) =
      ∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b := by
  have hF : Measurable (fun p : (LabeledTree n × (ForestVertex n → ℝ)) × (ℕ → LabeledLeaf n) =>
      D (labelPrefixPattern n r (fun i => p.2 i))) :=
    (measurable_of_countable D).comp (measurable_sampledLabelPattern n r)
  have h := (HasLaw.mk (raw_retained_joint_preserving n b d t).measurable.aemeasurable (raw_retained_joint_preserving n b d t).map_eq).integral_comp hF.aestronglyMeasurable
  exact h.trans (retained_joint_shape n r b hb _ D)

lemma raw_joint_shape_score (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n r → ℝ) :
    (∫ p, D (labelPrefixPattern n r (fun i => p.2 i))*
      cylinderField (leafLevelCoefficients n d (p.2 0)) p.1.2 ∂rawLabelJoint n b d t) =
      (∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b)*(b d*t) := by
  have hi := retained_joint_shape_score_integrable n r b hb (fun i => if i = d then t else 0) d D
  have h := (HasLaw.mk (raw_retained_joint_preserving n b d t).measurable.aemeasurable (raw_retained_joint_preserving n b d t).map_eq).integral_comp hi.aestronglyMeasurable
  have hh := h.trans (retained_joint_shape_score n r b hb (fun i => if i = d then t else 0) d D)
  simpa only [Function.comp_apply,rawLabelToRetained,leafLevelCoefficients_field,ite_eq_left rfl,ite_true] using hh

lemma randomReplicaAverage_shape (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n r → ℝ) :
    randomReplicaAverage (labeledCascadeLaw n b) (labeledLeafLaw n) (leafLevelCoefficients n d) t
      (fun σ => D (labelPrefixPattern n r σ)) =
      ∫ σ, D (labelPrefixPattern n r (fun i => σ i)) ∂cascadeReplicaLaw n b := by
  obtain ⟨c,hc,hD⟩ := prefixPattern_bound n r D
  have hi : Integrable (fun p => D (labelPrefixPattern n r (fun i => p.2 i))) (rawLabelJoint n b d t) :=
    integrable_of_measurable_abs_le
      ((measurable_of_countable (fun σ : Fin r → LabeledLeaf n => D (labelPrefixPattern n r σ))).comp (by fun_prop))
      (fun _ => hD _)
  exact (rawJoint_integral_reference n b d t r (fun _ σ => D (labelPrefixPattern n r σ)) hi).symm.trans
    (raw_joint_shape n r b hb d t D)

lemma randomReplicaEnergy_shape (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n (r+1) → ℝ) :
    randomReplicaEnergy (labeledCascadeLaw n b) (labeledLeafLaw n) (leafLevelCoefficients n d) t
      (fun σ => D (labelPrefixPattern n (r+1) σ)) =
      (∫ σ, D (labelPrefixPattern n (r+1) (fun i => σ i)) ∂cascadeReplicaLaw n b)*(b d*t) := by
  have hi := raw_joint_shape_score_integrable n (r+1) b hb d t D
  have h := rawJoint_integral_reference n b d t (r+1)
    (fun p σ => D (labelPrefixPattern n (r+1) σ)*cylinderField (leafLevelCoefficients n d (σ 0)) p.2) hi
  simpa only [randomReplicaEnergy,rawLabelBase,mul_comm] using h.symm.trans (raw_joint_shape_score n (r+1) b hb d t D)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma patternReindex_label {n r s : ℕ} (σ : Fin r → LabeledLeaf n) (e : Fin s → Fin r) :
    patternReindex (labelPrefixPattern n r σ) e = labelPrefixPattern n s (σ ∘ e) := rfl

lemma leafLevelCoefficients_cross_bool (n r : ℕ) (d : Fin n) (σ : Fin r → LabeledLeaf n) (i j : Fin r) :
    cylinderCross (leafLevelCoefficients n d (σ i)) (leafLevelCoefficients n d (σ j)) =
      boolReal (labelPrefixPattern n r σ i j d) := by
  rw [leafLevelCoefficients_cross]
  simp only [labelPrefixPattern,boolReal]
  split <;> simp

lemma prefixPatternMean_const (n r : ℕ) (b : ℕ → ℝ) (c : ℝ) :
    prefixPatternMean n r b (fun _ => c) = c := by simp [prefixPatternMean]

 
theorem cascade_prefix_gg (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (D : PrefixPattern n (r+1) → ℝ) :
    (r+1 : ℕ)*prefixPatternMean n (r+1+1) b
      (fun Q => D (patternReindex Q Fin.succ)*boolReal (Q 1 0 d)) =
      (1-b d)*prefixPatternMean n (r+1) b D +
      prefixPatternMean n (r+1) b (fun Q => D Q*(∑ j : Fin r, boolReal (Q 0 j.succ d))) := by
  obtain ⟨c,hc,hD⟩ := prefixPattern_bound n (r+1) D
  have h := randomReplicaEnergy_identity (P := (labeledCascadeLaw n b : Measure (LabeledTree n)))
    (measurable_labeledLeafLaw n) (leafLevelCoefficients n d) (leafLevelCoefficients_bound n d)
    (leafLevelCoefficients_diag n d) 1 (fun σ => D (labelPrefixPattern n (r+1) σ)) hc (fun σ => hD _)
  have hE : (fun σ : Fin (r+1) → LabeledLeaf n => D (labelPrefixPattern n (r+1) σ)*
      (∑ l : Fin r, cylinderCross (leafLevelCoefficients n d (σ 0)) (leafLevelCoefficients n d (σ l.succ)))) =
      (fun σ => (fun Q : PrefixPattern n (r+1) => D Q*(∑ l : Fin r, boolReal (Q 0 l.succ d)))
        (labelPrefixPattern n (r+1) σ)) := by
    funext σ
    simp only [leafLevelCoefficients_cross_bool]
  have hF : (fun τ : Fin (r+1+1) → LabeledLeaf n => D (labelPrefixPattern n (r+1) (Fin.tail τ))*
      cylinderCross (leafLevelCoefficients n d ((Fin.tail τ) 0)) (leafLevelCoefficients n d (τ 0))) =
      (fun τ => (fun Q : PrefixPattern n (r+1+1) => D (patternReindex Q Fin.succ)*boolReal (Q 1 0 d))
        (labelPrefixPattern n (r+1+1) τ)) := by
    funext τ
    change D (labelPrefixPattern n (r+1) (Fin.tail τ))*cylinderCross (leafLevelCoefficients n d (τ 1)) (leafLevelCoefficients n d (τ 0)) = _
    rw [leafLevelCoefficients_cross_bool n (r+1+1) d τ 1 0]
    rfl
  rw [hE,hF,randomReplicaEnergy_shape n r b hb d 1 D,
    randomReplicaAverage_shape n (r+1) b hb d 1 D,
    randomReplicaAverage_shape n (r+1) b hb d 1 (fun Q => D Q*(∑ l : Fin r, boolReal (Q 0 l.succ d))),
    randomReplicaAverage_shape n (r+1+1) b hb d 1 (fun Q => D (patternReindex Q Fin.succ)*boolReal (Q 1 0 d))] at h
  change prefixPatternMean n (r+1) b D*(b d*1) = _ at h
  change _ = (1-b d)*prefixPatternMean n (r+1) b D+_ 
  dsimp only [prefixPatternMean] at *
  linarith

lemma prefix_pair_mean (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (d : Fin n) :
    prefixPatternMean n 2 b (fun Q => boolReal (Q 1 0 d)) = 1-b d := by
  have h := cascade_prefix_gg n 0 b hb d (fun _ => 1)
  simpa only [Nat.zero_add,Nat.cast_one,one_mul,Fin.sum_univ_zero,mul_zero,
    prefixPatternMean_const,mul_one,add_zero] using h

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma replica_injective_map_reindex {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {r : ℕ} {e : Fin r → ℕ} (he : Function.Injective e) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun σ => fun i : Fin r => σ (e i)) =
      Measure.pi (fun _ : Fin r => ν) := by
  have hi : iIndepFun (fun i : ℕ => fun σ : ℕ → X => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := iIndepFun_infinitePi (fun _ => measurable_id)
  have h := (hi.precomp (fun {_ _} h => he h)).map_fun_eq_pi_map
    (fun _ => (measurable_pi_apply _).aemeasurable)
  simpa only [Measure.infinitePi_map_eval] using h

lemma replicaLaw_integral_injective_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {r : ℕ} {e : Fin r → ℕ} (he : Function.Injective e)
    (F : (Fin r → X) → ℝ) {c : ℝ} (hF : ∀ σ, |F σ| ≤ c) :
    (∫ σ, F (fun i => σ (e i)) ∂replicaLaw P ν hν) =
      ∫ σ, F (fun i => σ i) ∂replicaLaw P ν hν := by
  have h1m : Measurable (fun σ : ℕ → X => F (fun i => σ (e i))) :=
    (measurable_of_countable F).comp (by fun_prop)
  have h2m : Measurable (fun σ : ℕ → X => F (fun i : Fin r => σ i)) :=
    (measurable_of_countable F).comp (by fun_prop)
  rw [replicaLaw_integral_bounded P ν hν h1m (fun σ => hF _),
    replicaLaw_integral_bounded P ν hν h2m (fun σ => hF _)]
  apply integral_congr_ae
  filter_upwards [] with ω
  have h1 : HasLaw (fun σ : ℕ → X => fun i : Fin r => σ (e i))
      (Measure.pi (fun _ : Fin r => ν ω)) (Measure.infinitePi (fun _ : ℕ => ν ω)) :=
    ⟨(by fun_prop : Measurable _).aemeasurable,replica_injective_map_reindex (ν ω) he⟩
  have h2 : HasLaw (fun σ : ℕ → X => fun i : Fin r => σ i)
      (Measure.pi (fun _ : Fin r => ν ω)) (Measure.infinitePi (fun _ : ℕ => ν ω)) :=
    ⟨(by fun_prop : Measurable _).aemeasurable,replica_prefix_map (ν ω) r⟩
  exact (h1.integral_comp (measurable_of_countable F).aestronglyMeasurable).trans
    (h2.integral_comp (measurable_of_countable F).aestronglyMeasurable).symm

lemma cascadeReplicaLaw_eq_replicaLaw (n : ℕ) (b : ℕ → ℝ) :
    cascadeReplicaLaw n b = replicaLaw (labeledCascadeLaw n b) (labeledLeafLaw n) (measurable_labeledLeafLaw n) := by
  unfold cascadeReplicaLaw replicaLaw
  congr 1

lemma cascade_integral_injective (n : ℕ) (b : ℕ → ℝ) {r : ℕ} {e : Fin r → ℕ}
    (he : Function.Injective e) (F : (Fin r → LabeledLeaf n) → ℝ) {c : ℝ} (hF : ∀ σ, |F σ| ≤ c) :
    (∫ σ, F (fun i => σ (e i)) ∂cascadeReplicaLaw n b) =
      ∫ σ, F (fun i => σ i) ∂cascadeReplicaLaw n b := by
  simp only [cascadeReplicaLaw_eq_replicaLaw]
  exact replicaLaw_integral_injective_eq (Ω := LabeledTree n) (X := LabeledLeaf n)
    (labeledCascadeLaw n b) (labeledLeafLaw n) (measurable_labeledLeafLaw n) (r := r) (e := e) he F hF

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma prefixPatternMean_injective (n r : ℕ) (b : ℕ → ℝ) {e : Fin r → ℕ}
    (he : Function.Injective e) (D : PrefixPattern n r → ℝ) :
    (∫ σ, D (labelPrefixPattern n r (fun i => σ (e i))) ∂cascadeReplicaLaw n b) =
      prefixPatternMean n r b D := by
  obtain ⟨c,hc,hD⟩ := prefixPattern_bound n r D
  exact cascade_integral_injective n b he (fun τ => D (labelPrefixPattern n r τ)) (fun σ => hD _)

lemma prefixPatternMean_congr (n r : ℕ) (b : ℕ → ℝ) {D E : PrefixPattern n r → ℝ}
    (h : ∀ σ : Fin r → LabeledLeaf n, D (labelPrefixPattern n r σ) = E (labelPrefixPattern n r σ)) :
    prefixPatternMean n r b D = prefixPatternMean n r b E :=
  integral_congr_ae (ae_of_all _ (fun σ => h (fun index => σ index)))

lemma prefixPatternMean_sum {I : Type*} (s : Finset I) (n r : ℕ) (b : ℕ → ℝ) (D : I → PrefixPattern n r → ℝ) :
    prefixPatternMean n r b (fun Q => ∑ i ∈ s, D i Q) = ∑ i ∈ s, prefixPatternMean n r b (D i) :=
  integral_finsetSum s (fun i _ => prefixPatternMean_integrable n r b (D i))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma prefixPatternMean_perm (n r : ℕ) (b : ℕ → ℝ) (e : Equiv.Perm (Fin r))
    (D : PrefixPattern n r → ℝ) :
    prefixPatternMean n r b (fun Q => D (patternReindex Q e)) = prefixPatternMean n r b D := by
  have h := prefixPatternMean_injective n r b (e := fun i => (e i).val)
    (fun _ _ h => e.injective (Fin.ext h)) D
  exact h

lemma patternReindex_perm_cancel {n r : ℕ} (Q : PrefixPattern n r) (e : Equiv.Perm (Fin r)) :
    patternReindex (patternReindex Q e) e.symm = Q := by
  funext i j d
  simp [patternReindex]

lemma prefix_fresh_permuted (n r : ℕ) (b : ℕ → ℝ) (d : Fin n)
    (e : Equiv.Perm (Fin (r+1))) (D : PrefixPattern n (r+1) → ℝ) :
    prefixPatternMean n (r+1+1) b (fun Q => D (patternReindex (patternReindex Q Fin.succ) e.symm)*boolReal (Q 1 0 d)) =
      prefixPatternMean n (r+1+1) b
        (fun Q => D (patternReindex Q Fin.castSucc)*boolReal (Q (e 0).castSucc (Fin.last (r+1)) d)) := by
  have h := prefixPatternMean_injective n (r+1+1) b (newReplicaEmbedding_injective (r+1) e)
    (fun Q => D (patternReindex (patternReindex Q Fin.succ) e.symm)*boolReal (Q 1 0 d))
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with σ
  congr 1
  · apply congrArg D
    funext i j d
    simp [patternReindex,labelPrefixPattern,newReplicaEmbedding]

lemma prefix_old_permuted (n r : ℕ) (b : ℕ → ℝ) (d : Fin n)
    (e : Equiv.Perm (Fin (r+1))) (D : PrefixPattern n (r+1) → ℝ) :
    prefixPatternMean n (r+1) b
      (fun Q => D (patternReindex Q e.symm)*(∑ j : Fin r, boolReal (Q 0 j.succ d))) =
      prefixPatternMean n (r+1) b
        (fun Q => D Q*(∑ j ∈ Finset.univ.erase (e 0), boolReal (Q (e 0) j d))) := by
  rw [← prefixPatternMean_perm n (r+1) b e]
  congr 1
  funext Q
  rw [patternReindex_perm_cancel]
  dsimp only [patternReindex]
  rw [sum_nonzero_permutation e (fun j => boolReal (Q (e 0) j d))]

lemma cascade_prefix_gg_all (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (i : Fin (r+1)) (d : Fin n) (D : PrefixPattern n (r+1) → ℝ) :
    (r+1 : ℕ)*prefixPatternMean n (r+1+1) b
      (fun Q => D (patternReindex Q Fin.castSucc)*boolReal (Q i.castSucc (Fin.last (r+1)) d)) =
      (1-b d)*prefixPatternMean n (r+1) b D +
      prefixPatternMean n (r+1) b
        (fun Q => D Q*(∑ j ∈ Finset.univ.erase i, boolReal (Q i j d))) := by
  have h := cascade_prefix_gg n r b hb d (fun Q => D (patternReindex Q (Equiv.swap 0 i).symm))
  rw [prefix_fresh_permuted,prefixPatternMean_perm,prefix_old_permuted,Equiv.swap_apply_left] at h
  exact h

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma sum_prefix_telescope (n k : ℕ) (hk : k ≤ n) (a : ℕ → ℝ) :
    a 0+(∑ d : Fin n, (a (d+1)-a d)*(if d.val+1 ≤ k then 1 else 0)) = a k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    by_cases h : k ≤ n
    · have he : (∑ d : Fin n, (a (d.castSucc+1)-a d.castSucc)*(if d.castSucc.val+1 ≤ k then 1 else 0)) =
          ∑ d : Fin n, (a (d+1)-a d)*(if d.val+1 ≤ k then 1 else 0) := rfl
      rw [he]
      simp only [Fin.val_last,show ¬ n+1 ≤ k by omega,ite_false,mul_zero,add_zero]
      exact ih k h
    · have hkn : k = n+1 := by omega
      subst k
      have hs : (∑ d : Fin n, (a (d.castSucc+1)-a d.castSucc)*(if d.castSucc.val+1 ≤ n+1 then 1 else 0)) =
          ∑ d : Fin n, (a (d+1)-a d)*(if d.val+1 ≤ n then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd := d.isLt
        simp only [Fin.val_castSucc,show d.val+1 ≤ n+1 by omega,show d.val+1 ≤ n by omega,ite_true]
      rw [hs]
      simp only [Fin.val_last,le_refl,ite_true,mul_one]
      have hi := ih n (le_refl n)
      linarith

lemma prefixVectorValue_label (n : ℕ) (a : ℕ → ℝ) (v w : LabeledLeaf n) :
    prefixVectorValue n a (fun d => if (labeledAddress n v).take (d+1) = (labeledAddress n w).take (d+1) then true else false) =
      a (labeledCommonDepth n v w) := by
  unfold prefixVectorValue
  have hf : (fun d : Fin n => boolReal (if (labeledAddress n v).take (d+1) = (labeledAddress n w).take (d+1) then true else false)) =
      (fun d => if d.val+1 ≤ labeledCommonDepth n v w then 1 else 0) := by
    funext d
    simp only [labeled_prefix_eq_iff n v w (d := d.val+1) (by omega), boolReal]
    split <;> simp
  simp_rw [congrFun hf]
  exact sum_prefix_telescope n _ (labeledCommonDepth_le n v w) a

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma prefixPatternMean_restrict (n r : ℕ) (b : ℕ → ℝ) (D : PrefixPattern n r → ℝ) :
    prefixPatternMean n (r+1) b (fun Q => D (patternReindex Q Fin.castSucc)) = prefixPatternMean n r b D := rfl

lemma prefixGGResidual_const (n r : ℕ) (b : ℕ → ℝ) (i : Fin (r+1)) (D : PrefixPattern n (r+1) → ℝ) :
    prefixGGResidual n r b i D (fun _ => 1) = 0 := by
  simp only [prefixGGResidual,LinearMap.coe_mk,AddHom.coe_mk,mul_one,
    prefixPatternMean_restrict,prefixPatternMean_const,Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,
    Nat.add_sub_cancel,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

lemma prefix_pair_mean_01 (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (d : Fin n) :
    prefixPatternMean n 2 b (fun Q => boolReal (Q 0 1 d)) = 1-b d := by
  rw [← prefix_pair_mean n b hb d]
  apply prefixPatternMean_congr
  intro σ
  simp [labelPrefixPattern,eq_comm]

lemma prefixGGResidual_level (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (i : Fin (r+1)) (d : Fin n) (D : PrefixPattern n (r+1) → ℝ) :
    prefixGGResidual n r b i D (fun v => boolReal (v d)) = 0 := by
  have h := cascade_prefix_gg_all n r b hb i d D
  have hs : prefixPatternMean n (r+1) b
      (fun Q => D Q*(∑ j ∈ Finset.univ.erase i, boolReal (Q i j d))) =
      ∑ j ∈ Finset.univ.erase i, prefixPatternMean n (r+1) b (fun Q => D Q*boolReal (Q i j d)) := by
    simp only [Finset.mul_sum,prefixPatternMean_sum]
  rw [hs] at h
  change (r+1 : ℕ)*prefixPatternMean n (r+1+1) b _ -
    prefixPatternMean n (r+1) b D*prefixPatternMean n 2 b (fun Q => boolReal (Q 0 1 d)) - _ = 0
  rw [prefix_pair_mean_01 n b hb d,h]
  ring

lemma prefixGGResidual_value (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (i : Fin (r+1)) (D : PrefixPattern n (r+1) → ℝ) (a : ℕ → ℝ) :
    prefixGGResidual n r b i D (prefixVectorValue n a) = 0 := by
  have he : prefixVectorValue n a = a 0 • (fun _ : Fin n → Bool => (1:ℝ))+
      ∑ d : Fin n, (a (d+1)-a d) • (fun v : Fin n → Bool => boolReal (v d)) := by
    funext v
    simp [prefixVectorValue,Finset.sum_apply]
  rw [he,map_add,map_smul,map_sum,prefixGGResidual_const]
  simp only [map_smul,prefixGGResidual_level n r b hb i,smul_zero,Finset.sum_const_zero,add_zero]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

lemma prefixVectorValue_pattern (n r : ℕ) (a : ℕ → ℝ) (σ : Fin r → LabeledLeaf n) (i j : Fin r) :
    prefixVectorValue n a (labelPrefixPattern n r σ i j) = a (labeledCommonDepth n (σ i) (σ j)) :=
  prefixVectorValue_label n a (σ i) (σ j)

lemma integral_ite_one_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω)
    (hA : MeasurableSet A) : (∫ ω, (if ω ∈ A then (1:ℝ) else 0) ∂μ) = μ.real A := by
  classical
  simpa only [Set.indicator,Pi.one_apply] using integral_indicator_one (μ := μ) hA

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_CascadePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Pair. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

lemma prefix_pair_value (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (a : ℕ → ℝ) :
    prefixPatternMean n 2 b (fun Q => prefixVectorValue n a (Q 0 1)) =
      a 0+∑ d : Fin n, (a (d+1)-a d)*(1-b d) := by
  unfold prefixVectorValue
  rw [prefixPatternMean_add,prefixPatternMean_const,prefixPatternMean_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [prefixPatternMean_mul,prefix_pair_mean_01 n b hb d]

lemma cascade_pair_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (a : ℕ → ℝ) :
    (∫ σ, cascadeScalarArray n a σ 0 1 ∂cascadeReplicaLaw n b) =
      a 0+∑ d : Fin n, (a (d+1)-a d)*(1-b d) := by
  rw [← prefix_pair_value n b hb a]
  apply integral_congr_ae
  filter_upwards [] with σ
  exact (prefixVectorValue_label n a (σ 0) (σ 1)).symm

lemma integral_depth_telescope {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} {L : Ω → ℕ} (hL : Measurable L) (hLn : ∀ᵐ ω ∂μ, L ω ≤ n) (a : ℕ → ℝ) :
    (∫ ω, a (L ω) ∂μ) = a 0+∑ d : Fin n, (a (d+1)-a d)*μ.real {ω | d.val+1 ≤ L ω} := by
  have hd (d : Fin n) : MeasurableSet {ω | d.val+1 ≤ L ω} :=
    measurableSet_le measurable_const hL
  have hi (d : Fin n) : Integrable (fun ω => (a (d+1)-a d)*(if d.val+1 ≤ L ω then (1:ℝ) else 0)) μ := by
    simpa only [Set.indicator,Set.mem_ofPred_eq] using ((integrable_const (μ := μ) (1:ℝ)).indicator (hd d)).const_mul (a (d+1)-a d)
  calc
    (∫ ω, a (L ω) ∂μ) = ∫ ω, a 0+∑ d : Fin n, (a (d+1)-a d)*(if d.val+1 ≤ L ω then (1:ℝ) else 0) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hLn] with ω hω
      exact (sum_prefix_telescope n (L ω) hω a).symm
    _ = _ := by
      rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun d _ => hi d)),integral_const,
        integral_finsetSum _ (fun d _ => hi d)]
      have he (d : Fin n) : (∫ ω, (if d.val+1 ≤ L ω then (1:ℝ) else 0) ∂μ) = μ.real {ω | d.val+1 ≤ L ω} := by
        refine Eq.trans ?_ (integral_ite_one_eq μ {ω | d.val+1 ≤ L ω} (hd d))
        apply integral_congr_ae
        filter_upwards [] with sample
        by_cases hle : d.val+1 ≤ L sample <;> simp [hle]
      simp only [integral_const_mul,he,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]

 

theorem cascade_pair_law_of_tails {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (a : ℕ → ℝ)
    {L : Ω → ℕ} (hL : Measurable L) (hLn : ∀ᵐ ω ∂μ, L ω ≤ n)
    (hT : ∀ d : Fin n, μ.real {ω | d.val+1 ≤ L ω} = 1-b d) :
    μ.map (fun ω => a (L ω)) = (cascadeReplicaLaw n b).map (fun σ => cascadeScalarArray n a σ 0 1) := by
  have hAm : Measurable (fun ω => a (L ω)) := (measurable_of_countable a).comp hL
  have hBm : Measurable (fun σ => cascadeScalarArray n a σ 0 1) := by
    exact (measurable_pi_apply 1).comp ((measurable_pi_apply 0).comp (measurable_cascadeScalarArray n a))
  apply Measure.ext
  intro t ht
  rw [Measure.map_apply hAm ht,Measure.map_apply hBm ht]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {ω | a (L ω) ∈ t} = (cascadeReplicaLaw n b).real {σ | cascadeScalarArray n a σ 0 1 ∈ t}
  rw [← integral_ite_one_eq μ {ω | a (L ω) ∈ t} (ht.preimage hAm),
    ← integral_ite_one_eq (cascadeReplicaLaw n b) {σ | cascadeScalarArray n a σ 0 1 ∈ t} (ht.preimage hBm)]
  have h := integral_depth_telescope μ hL hLn (fun k => if a k ∈ t then 1 else 0)
  simp only [hT] at h
  exact h.trans (cascade_pair_integral n b hb (fun k => if a k ∈ t then 1 else 0)).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformExponent_cascade (n : ℕ) : CascadeExponents n (uniformExponent n) := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  constructor
  · intro i hi
    constructor
    · exact div_pos (by positivity) hn
    · apply (div_lt_one hn).mpr
      exact_mod_cast Nat.succ_lt_succ hi
  · intro i j hij hj
    apply (div_lt_div_iff_of_pos_right hn).mpr
    have hh : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
    linarith

lemma measurable_uniformCellIndex (n : ℕ) : Measurable (uniformCellIndex n) := by
  unfold uniformCellIndex
  exact measurable_const.min (Nat.measurable_floor.comp (measurable_id.const_mul _))

lemma uniformCellIndex_le (n : ℕ) (u : ℝ) : uniformCellIndex n u ≤ n := min_le_left _ _

lemma uniformCellIndex_tail_iff (n : ℕ) (d : Fin n) (u : ℝ) :
    d.val+1 ≤ uniformCellIndex n u ↔ uniformExponent n d ≤ u := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  rw [uniformCellIndex,le_min_iff,and_iff_right (by omega : d.val+1 ≤ n),
    Nat.le_floor_iff' (by omega : d.val+1 ≠ 0)]
  simp only [uniformExponent,Nat.cast_add,Nat.cast_one]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < n+1),mul_comm]

lemma unitUniform_Ici_real {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    unitUniform.real (Ici a) = 1-a := by
  let : NullSingletonClass unitUniform := inferInstanceAs (NullSingletonClass (volume.restrict (Ioo (0:ℝ) 1)))
  have he : unitUniform (Iio a) = ENNReal.ofReal a := by
    rw [measure_congr (Iio_ae_eq_Iic (μ := unitUniform))]
    exact unitUniform_Iic ha
  rw [show Ici a = (Iio a)ᶜ from (compl_Iio).symm,
    measureReal_def,measure_compl measurableSet_Iio (measure_ne_top _ _),measure_univ,he,
    ENNReal.toReal_sub_of_le (by simp [ha.2] : ENNReal.ofReal a ≤ 1) (by simp)]
  simp [ENNReal.toReal_ofReal ha.1]

lemma uniformIndex_tail (n : ℕ) (d : Fin n) :
    unitUniform.real {u | d.val+1 ≤ uniformCellIndex n u} = 1-uniformExponent n d := by
  have h : {u : ℝ | d.val+1 ≤ uniformCellIndex n u} = Ici (uniformExponent n d) := by
    ext u; exact uniformCellIndex_tail_iff n d u
  rw [h]
  exact unitUniform_Ici_real ⟨(uniformExponent_cascade n).1 d d.isLt |>.1.le,
    (uniformExponent_cascade n).1 d d.isLt |>.2.le⟩

lemma cascade_pair_uniformIndex (n : ℕ) (a : ℕ → ℝ) :
    unitUniform.map (fun u => a (uniformCellIndex n u)) =
      (cascadeReplicaLaw n (uniformExponent n)).map (fun σ => cascadeScalarArray n a σ 0 1) :=
  cascade_pair_law_of_tails unitUniform n (uniformExponent n) (uniformExponent_cascade n) a
    (measurable_uniformCellIndex n) (ae_of_all _ (uniformCellIndex_le n)) (uniformIndex_tail n)

lemma uniformCellIndex_eq_floor (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    uniformCellIndex n u = ⌊((n+1:ℕ):ℝ)*u⌋₊ := by
  apply min_eq_right
  have h : ⌊((n+1:ℕ):ℝ)*u⌋₊ < n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) hu.1)]
    exact mul_lt_of_lt_one_right (by positivity) hu.2
  omega

lemma uniformCell_bounds (n : ℕ) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    (uniformCellIndex n u:ℝ)/(n+1:ℕ) ≤ u ∧
      u < ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ) := by
  rw [uniformCellIndex_eq_floor n hu]
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using (Nat.floor_le (mul_nonneg (by positivity) hu.1))
  · apply (lt_div_iff₀ (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    simpa only [mul_comm] using Nat.lt_floor_add_one (((n+1:ℕ):ℝ)*u)

lemma uniformCell_left_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => (uniformCellIndex n u:ℝ)/(n+1:ℕ)) atTop (𝓝 u) := by
  have hZ := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => u-1/((n:ℝ)+1))
    (h := fun _ : ℕ => u) (by simpa using tendsto_const_nhds.sub hZ) tendsto_const_nhds
  · intro n
    have h := (uniformCell_bounds n hu).2.le
    simp only [Nat.cast_add,Nat.cast_one,add_div] at h ⊢
    linarith
  · exact fun n => (uniformCell_bounds n hu).1

lemma uniformCell_right_tendsto {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => ((uniformCellIndex n u:ℝ)+1)/(n+1:ℕ)) atTop (𝓝 u) := by
  simpa only [add_div,Nat.cast_add,Nat.cast_one,add_zero] using
    (uniformCell_left_tendsto hu).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformCell_measure (n i : ℕ) :
    (volume.restrict (Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ)))).real univ = 1/(n+1:ℕ) := by
  rw [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioo]
  have he : (((i:ℝ)+1)/(n+1:ℕ))-(i:ℝ)/(n+1:ℕ) = 1/(n+1:ℕ) := by ring
  rw [he,ENNReal.toReal_ofReal (by positivity)]

lemma uniformCell_const (n i : ℕ) (c : ℝ) :
    ((n+1:ℕ):ℝ)*(∫ _ in Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ)), c) = c := by
  rw [integral_const,smul_eq_mul,uniformCell_measure]
  field_simp

lemma uniformCell_integrable {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n i : ℕ) :
    IntegrableOn q (Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ))) := by
  apply Integrable.of_bound hq.measurable.aestronglyMeasurable 1
  exact ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb u).1] using (hb u).2)

lemma uniformCellAverage_bounds {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n i : ℕ) :
    q ((i:ℝ)/(n+1:ℕ)) ≤ uniformCellAverage q n i ∧
      uniformCellAverage q n i ≤ q (((i:ℝ)+1)/(n+1:ℕ)) := by
  have hi := uniformCell_integrable hq hb n i
  have hn : (0:ℝ) ≤ (n+1:ℕ) := by positivity
  constructor
  · rw [← uniformCell_const n i (q ((i:ℝ)/(n+1:ℕ)))]
    apply mul_le_mul_of_nonneg_left _ hn
    apply integral_mono_ae (integrable_const _) hi
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hq hu.1.le
  · rw [← uniformCell_const n i (q (((i:ℝ)+1)/(n+1:ℕ)))]
    apply mul_le_mul_of_nonneg_left _ hn
    apply integral_mono_ae hi (integrable_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hq hu.2.le

lemma uniformCellAverage_mem {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n i : ℕ) : uniformCellAverage q n i ∈ Icc (0:ℝ) 1 :=
  ⟨(hb _).1.trans (uniformCellAverage_bounds hq hb n i).1,
    (uniformCellAverage_bounds hq hb n i).2.trans (hb _).2⟩

lemma uniformCellAverage_monotone {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (n : ℕ) : Monotone (uniformCellAverage q n) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl|hij
  · rfl
  · apply (uniformCellAverage_bounds hq hb n i).2.trans
    apply le_trans _ (uniformCellAverage_bounds hq hb n j).1
    apply hq
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.succ_le_of_lt hij

lemma uniformCellAverage_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ∈ Ico (0:ℝ) 1) (hc : ContinuousAt q u) :
    Tendsto (fun n => uniformCellAverage q n (uniformCellIndex n u)) atTop (𝓝 (q u)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (hc.tendsto.comp (uniformCell_left_tendsto hu)) (hc.tendsto.comp (uniformCell_right_tendsto hu))
    (fun n => (uniformCellAverage_bounds hq hb n _).1) (fun n => (uniformCellAverage_bounds hq hb n _).2)

lemma monotone_ae_continuous_unit {q : ℝ → ℝ} (hq : Monotone q) :
    ∀ᵐ u ∂unitUniform, ContinuousAt q u := by
  let : NullSingletonClass unitUniform := inferInstanceAs (NullSingletonClass (volume.restrict (Ioo (0:ℝ) 1)))
  exact (ae_iff).mpr (hq.countable_not_continuousAt.measure_zero unitUniform)

lemma uniformCellAverage_ae_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) :
    ∀ᵐ u ∂unitUniform, Tendsto (fun n => uniformCellAverage q n (uniformCellIndex n u)) atTop (𝓝 (q u)) := by
  filter_upwards [monotone_ae_continuous_unit hq,ae_restrict_mem measurableSet_Ioo] with u hc hu
  exact uniformCellAverage_tendsto hq hb ⟨hu.1.le,hu.2⟩ hc

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma scalarNodeTag_injective (n : ℕ) : Function.Injective (scalarNodeTag n) := by
  intro v w h
  exact nodeAddress_injective n (congrArg (fun p => p.2.1) (Encodable.encode_inj.mp h))

lemma scalarGaussianNodes_law (n : ℕ) :
    MeasurePreserving (scalarGaussianNodes n) gaussianCoordinates
      (Measure.infinitePi (fun _ : Option (ForestVertex n) => gaussianReal 0 1)) :=
  gaussian_pullback_measurePreserving (scalarNodeTag n) (scalarNodeTag_injective n)

lemma scalarGaussianRootForest_law (n : ℕ) :
    MeasurePreserving (fun g => ((scalarGaussianNodes n g none),fun v => scalarGaussianNodes n g (some v)))
      gaussianCoordinates ((gaussianReal 0 1).prod
        (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1))) := by
  refine ⟨by unfold scalarGaussianNodes; fun_prop,?_⟩
  change gaussianCoordinates.map ((fun q : Option (ForestVertex n) → ℝ =>
      (q none,fun v => q (some v))) ∘ scalarGaussianNodes n) = _
  rw [← Measure.map_map (by fun_prop) (scalarGaussianNodes_law n).measurable,(scalarGaussianNodes_law n).map_eq]
  have he := infinitePi_option_split (gaussianReal 0 1) (fun _ : ForestVertex n => gaussianReal 0 1)
  have hc : (fun i : Option (ForestVertex n) => i.elim (gaussianReal 0 1) (fun _ => gaussianReal 0 1)) =
      (fun _ => gaussianReal 0 1) := by funext i; cases i <;> rfl
  simpa only [hc] using he

lemma cylinderField_scalar_nodes (n : ℕ) (v : LabeledLeaf n) (q : ℕ → ℝ) (g : ℕ → ℝ) :
    cylinderField (treeFieldCoefficients n v (fun i => pathAmplitude q i) (fun _ : Unit => 1)) g =
      pathAmplitude q 0*scalarGaussianNodes n g none+
        ∑ i : Fin n, pathAmplitude q (i+1)*scalarGaussianNodes n g (some (edgeAt n v i)) := by
  rw [treeFieldCoefficients,cylinderField_feature,Fintype.sum_prod_type]
  simp only [Fintype.sum_unique,mul_one]
  have he (i : Fin (n+1)) : treeFeatureTag n v (i,(Unit.unit : Unit)) = scalarNodeTag n (nodeAt n v i) := by
    unfold treeFeatureTag scalarNodeTag
    rw [nodeAddress_nodeAt_length,nodeAddress_nodeAt]
  simp_rw [he]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,nodeAt_zero,nodeAt_succ,scalarGaussianNodes]

lemma noiseLeafTerminal_additive (n : ℕ) (s : ℕ → ℝ) (F : ℝ → ℝ) (x : ℝ) (v : NoiseLeaf ℝ n) :
    noiseLeafTerminal n (fun _ => F) (fun i p => p.1+s i*p.2) x v =
      F (x+∑ i : Fin n, s i*noiseLeafMark n v i) := by
  induction n generalizing s x with
  | zero => simp [noiseLeafTerminal]
  | succ n ih =>
    rw [noiseLeafTerminal,ih,Fin.sum_univ_succ]
    simp only [noiseLeafMark,Fin.cases_zero,Fin.cases_succ,Fin.val_zero,Fin.val_succ]
    congr 1
    ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

lemma noise_leaf_log_eq_ratio (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (s : S) :
    ∀ᵐ T ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)),
      Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => F) u s v)
        ∂noiseLeafKernel A n T) =
      Real.log ((terminalTreeFactor n b μ u F s T).toReal/(noiseTreeTotal A n T).toReal) := by
  have hfac := noiseTreeFactor_leafIntegral n b hb μ (fun _ => hF) hu s
  have htot : ∀ᵐ T ∂(noiseCascadeLaw A n b μ : Measure (NoiseTree A n)),
      0 < noiseTreeTotal A n T ∧ noiseTreeTotal A n T < ∞ := by
    apply ae_of_ae_map (p := fun T : RawTree n => 0 < rawTreeTotal n T ∧ rawTreeTotal n T < ∞)
      (measurable_noiseTreeForget A n).aemeasurable
    rw [noiseCascadeLaw_forget]
    exact (rawCascade_total_moments n b hb).1
  filter_upwards [hfac,htot] with T hfac ht
  simp only [noiseTreeFactor_terminal] at hfac
  rw [hfac,ENNReal.toReal_mul]
  have ht0 : (noiseTreeTotal A n T).toReal ≠ 0 :=
    (ENNReal.toReal_pos ht.1.ne' ht.2.ne).ne'
  rw [mul_div_cancel_left₀ _ ht0]
  congr 1
  exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun v => (Real.exp_pos _).le))
    (((measurable_noiseLeafTerminal n (fun _ => hF) hu).comp
      (measurable_const.prodMk measurable_id)).exp.aestronglyMeasurable)

 

theorem bounded_cascade_leaf_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {u : ℕ → S × A → S} {F : S → ℝ} {K : ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (hbound : ∀ s, |F s| ≤ K) (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun T => Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => F) u s v) ∂noiseLeafKernel A n T)
    Integrable L P ∧ (∫ T, L T ∂P) = cascadeRecursion n b μ u F s := by
  have he := noise_leaf_log_eq_ratio n b hb μ hu hF s
  have hi := bounded_noiseCascade_recursion n b hb μ hu hF hbound s
  exact ⟨hi.2.1.congr (Filter.EventuallyEq.symm he),(integral_congr_ae he).trans hi.2.2.1⟩

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma cascadeRecursion_gaussian (n : ℕ) (b s : ℕ → ℝ) (F : ℝ → ℝ)
    (hb : ∀ i < n, b i ≠ 0) :
    cascadeRecursion n b (fun _ => ⟨gaussianReal 0 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩)
      (fun i p => p.1+Real.sqrt (s i)*p.2) F =
    (List.ofFn (fun i : Fin n => (s i,b i))).foldr
      (fun sd U => gaussianTransform sd.1 sd.2 U) F := by
  induction n generalizing b s with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,List.foldr_cons]
    funext x
    change logMean (b 0) (gaussianReal 0 1)
      (fun z => cascadeRecursion n (fun j => b (j+1)) (fun _ => ⟨gaussianReal 0 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩)
        (fun i p => p.1+Real.sqrt (s (i+1))*p.2) F (x+Real.sqrt (s 0)*z)) = _
    rw [ih (fun j => b (j+1)) (fun j => s (j+1)) (fun i hi => hb (i+1) (by omega))]
    simp only [Fin.val_zero,Fin.val_succ,gaussianTransform,hb 0 (by omega),ite_false,logMean]



end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma continuous_covarianceGaussian (m : ℕ) : Continuous (covarianceGaussian m) := by
  let : FirstCountableTopology (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin m → Fin m → ℝ))
  apply continuous_iff_seqContinuous.mpr
  intro S Q hS
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro x
  have hc : Continuous (fun A : PositiveCovariance m =>
      Complex.exp (-(x.ofLp ⬝ᵥ A.1 *ᵥ x.ofLp : ℝ)/2)) := by
    have he (i j : Fin m) : Continuous (fun A : PositiveCovariance m => A.1 i j) := by
      have hc : Continuous (fun A : Matrix (Fin m) (Fin m) ℝ => A i j) :=
        (continuous_apply j).comp (continuous_apply i)
      exact hc.comp continuous_subtype_val
    have hr : Continuous (fun A : PositiveCovariance m => (x.ofLp ⬝ᵥ A.1 *ᵥ x.ofLp : ℝ)) := by
      simp only [dotProduct,Matrix.mulVec]
      exact continuous_finsetSum _ (fun i _ => continuous_const.mul
        (continuous_finsetSum _ (fun j _ => (he i j).mul continuous_const)))
    exact Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp hr).neg).div_const 2)
  have ht := hc.continuousAt.tendsto.comp hS
  simpa only [covarianceGaussian,ProbabilityMeasure.coe_mk,charFun_multivariateGaussian (S _).2,
    charFun_multivariateGaussian Q.2,Function.comp_def,inner_zero_right,Complex.ofReal_zero,zero_mul,zero_sub,neg_div] using ht

lemma continuous_gaussianMoment (m : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Continuous (fun S : PositiveCovariance m =>
      ∫ z : EuclideanSpace ℝ (Fin m), Real.exp (∑ i, f (z i)) ∂multivariateGaussian 0 S.1) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin m) => Real.exp (∑ i, f (z i))) := by
    apply Real.continuous_exp.comp
    exact continuous_finsetSum _ (fun i _ => hf.comp (PiLp.continuous_apply _ _ i))
  have hb (z : EuclideanSpace ℝ (Fin m)) : ‖Real.exp (∑ i, f (z i))‖ ≤ Real.exp (m*K) := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _ : Fin m, K := Finset.sum_le_sum (fun i _ => (le_abs_self _).trans (hK (z i)))
      _ = _ := by simp
  let F := BoundedContinuousFunction.ofNormedAddCommGroup _ hc _ hb
  exact ((ProbabilityMeasure.continuous_iff_forall_continuous_integral).mp
    (continuous_covarianceGaussian m)) F

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace
namespace IsingPerceptron

lemma cylinderCross_comm (a b : ℕ →₀ ℝ) : cylinderCross a b = cylinderCross b a := by
  classical
  let n := a.support.sup id + b.support.sup id + 1
  have ha : ∀ i ∈ a.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  have hb : ∀ i ∈ b.support, i < n := by
    intro i hi
    have := Finset.le_sup (f := id) hi
    dsimp only [id_eq] at this
    omega
  rw [cylinderCross_prefix a b ha,cylinderCross_prefix b a hb]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma cylinderCross_fin_covariance {m : ℕ} (A : Fin m → ℕ →₀ ℝ) (x : Fin m → ℝ) :
    (∑ i, x i • A i).sum (fun _ v => v^2) =
      x ⬝ᵥ (fun i j => cylinderCross (A i) (A j)) *ᵥ x := by
  simp only [← cylinderCross_self,cylinderCross_finset_left,cylinderCross_sum_right,cylinderCross_smul,
    Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cylinderCross_comm (A j) (A i)]
  ring

lemma cylinderCross_matrix_posSemidef {m : ℕ} (A : Fin m → ℕ →₀ ℝ) :
    Matrix.PosSemidef (fun i j => cylinderCross (A i) (A j)) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change cylinderCross (A j) (A i) = cylinderCross (A i) (A j)
    exact cylinderCross_comm _ _
  · intro x
    simp only [star_trivial]
    rw [← cylinderCross_fin_covariance]
    exact Finsupp.sum_nonneg (fun _ _ => sq_nonneg _)

lemma cylinder_vector_law {m : ℕ} (A : Fin m → ℕ →₀ ℝ) :
    gaussianCoordinates.map (fun g => (WithLp.toLp 2 (fun i => cylinderField (A i) g) : EuclideanSpace ℝ (Fin m))) =
      multivariateGaussian 0 (fun i j => cylinderCross (A i) (A j)) := by
  have hM : Measurable (fun g => (WithLp.toLp 2 (fun i => cylinderField (A i) g) : EuclideanSpace ℝ (Fin m))) :=
    (by fun_prop : Measurable (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m))).comp
      (Measurable.of_eval (fun i => measurable_cylinderField (A i)))
  let S : Matrix (Fin m) (Fin m) ℝ := fun i j => cylinderCross (A i) (A j)
  change gaussianCoordinates.map (fun g => (WithLp.toLp 2 (fun i => cylinderField (A i) g) : EuclideanSpace ℝ (Fin m))) = multivariateGaussian 0 S
  have : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S) := inferInstance
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_apply, integral_map hM.aemeasurable (by fun_prop)]
  have he (g : ℕ → ℝ) :
      ⟪(WithLp.toLp 2 (fun i => cylinderField (A i) g) : EuclideanSpace ℝ (Fin m)),x⟫_ℝ =
        cylinderField (∑ i, x i • A i) g := by
    rw [cylinderField_finset_sum]
    simp only [PiLp.inner_apply,cylinderField_smul,Real.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  simp_rw [he]
  rw [← integral_map (measurable_cylinderField _).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun z : ℝ => Complex.exp ((z:ℂ)*Complex.I)) (gaussianCoordinates.map _)),
    cylinderField_law]
  have hc : (∫ y : ℝ, Complex.exp ((y : ℂ) * Complex.I)
      ∂gaussianReal 0 ((∑ i, x i • A i).sum (fun _ v => v^2)).toNNReal) =
      charFun (gaussianReal 0 ((∑ i, x i • A i).sum (fun _ v => v^2)).toNNReal) 1 := by
    rw [charFun_apply]
    simp only [Real.inner_apply,mul_one]
  rw [hc]
  rw [charFun_gaussianReal,charFun_multivariateGaussian (show S.PosSemidef from cylinderCross_matrix_posSemidef A)]
  have hn : 0 ≤ (∑ i, x i • A i).sum (fun _ v => v^2) :=
    Finsupp.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : (↑((∑ i, x i • A i).sum (fun _ v => v^2)).toNNReal : ℝ) =
      x.ofLp ⬝ᵥ S *ᵥ x.ofLp := by
    rw [Real.coe_toNNReal _ hn]
    exact cylinderCross_fin_covariance A x.ofLp
  simp only [Complex.ofReal_zero,Complex.ofReal_one,mul_zero,zero_mul,zero_sub,one_pow,mul_one,inner_zero_right,hv]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_GaussianMomentTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian Moment Test. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix InnerProductSpace
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix BoundedContinuousFunction
namespace IsingPerceptron

lemma gaussianMoment_bound (m : ℕ) {f : ℝ → ℝ} {K : ℝ} (hf : ∀ x, |f x| ≤ K)
    (S : Matrix (Fin m) (Fin m) ℝ) : |gaussianMoment m f S| ≤ Real.exp (m*K) := by
  have h (z : EuclideanSpace ℝ (Fin m)) : ‖Real.exp (∑ i, f (z i))‖ ≤ Real.exp (m*K) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _ : Fin m, K := Finset.sum_le_sum (fun i _ => (le_abs_self _).trans (hf (z i)))
      _ = _ := by simp
  simpa only [gaussianMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S)
      (ae_of_all _ h)

lemma gaussianMoment_extension (m : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    ∃ F : Matrix (Fin m) (Fin m) ℝ →ᵇ ℝ,
      ∀ S, S.PosSemidef → F S = gaussianMoment m f S := by
  let : NormalSpace (Matrix (Fin m) (Fin m) ℝ) :=
    inferInstanceAs (NormalSpace (Fin m → Fin m → ℝ))
  let g : PositiveCovariance m →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun S => gaussianMoment m f S.val) (continuous_gaussianMoment m hf hK) (Real.exp (m*K))
    (fun S => by simpa only [Real.norm_eq_abs] using gaussianMoment_bound m hK S.val)
  obtain ⟨F,_,hF⟩ := g.exists_norm_eq_domRestrict_eq_of_closed (isClosed_setOf_posSemidef m)
  exact ⟨F,fun S hS => congrArg (fun g : PositiveCovariance m →ᵇ ℝ => g ⟨S,hS⟩) hF⟩

 

theorem jointArray_tendsto_gaussianMoment {L : ℕ → ProbabilityMeasure JointArray}
    {μ : ProbabilityMeasure JointArray} (hL : Tendsto L atTop (𝓝 μ))
    (hG : ∀ k, ∀ᵐ x ∂(L k : Measure JointArray), GramDiagonal 1 (spinArray x))
    (hGμ : ∀ᵐ x ∂(μ : Measure JointArray), GramDiagonal 1 (spinArray x))
    (m : ℕ) {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Tendsto (fun k => ∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(L k : Measure JointArray)) atTop
      (𝓝 (∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(μ : Measure JointArray))) := by
  obtain ⟨F,hF⟩ := gaussianMoment_extension m hf hK
  have he (P : ProbabilityMeasure JointArray) (hP : ∀ᵐ x ∂(P : Measure JointArray), GramDiagonal 1 (spinArray x)) :
      (∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(P : Measure JointArray)) =
      ∫ x, F (fun i j : Fin m => spinArray x i j) ∂(P : Measure JointArray) := by
    apply integral_congr_ae
    filter_upwards [hP] with x hx
    exact (hF _ (hx.1 m)).symm
  simp_rw [he _ (hGμ),he _ (hG _)]
  exact jointArray_tendsto_integral hL (F.continuous.comp (by unfold spinArray; fun_prop))

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma freshPatternFactor_bound {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) (f : ℝ → ℝ) {K : ℝ} (hK : ∀ x, |f x| ≤ K) (g : ℕ → ℝ) :
    freshPatternFactor ν A f g ∈ Icc (Real.exp (-K)) (Real.exp K) := by
  have hi : Integrable (fun x => Real.exp (f (cylinderField (A x) g))) ν :=
    Integrable.of_bound (.of_discrete) (Real.exp K) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hK _))))
  constructor
  · calc
      Real.exp (-K) = ∫ _ : X, Real.exp (-K) ∂ν := by simp
      _ ≤ _ := integral_mono (integrable_const _) hi (fun x =>
        Real.exp_le_exp.mpr (abs_le.mp (hK _)).1)
  · calc
      _ ≤ ∫ _ : X, Real.exp K ∂ν := integral_mono hi (integrable_const _) (fun x =>
        Real.exp_le_exp.mpr (abs_le.mp (hK _)).2)
      _ = _ := by simp

lemma gaussianMoment_cylinder_integral {m : ℕ} (A : Fin m → ℕ →₀ ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) :
    gaussianMoment m f (fun i j => cylinderCross (A i) (A j)) =
      ∫ g, Real.exp (∑ i, f (cylinderField (A i) g)) ∂gaussianCoordinates := by
  unfold gaussianMoment
  rw [← cylinder_vector_law A]
  have hint : Measurable (fun z : EuclideanSpace ℝ (Fin m) => Real.exp (∑ i, f (z i))) := by
    exact (Finset.measurable_sum _ (fun i _ => hf.comp (by fun_prop))).exp
  have hmap : Measurable (fun g =>
      (WithLp.toLp 2 (fun i => cylinderField (A i) g) : EuclideanSpace ℝ (Fin m))) :=
    (by fun_prop : Measurable (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m))).comp
      (Measurable.of_eval (fun i => measurable_cylinderField (A i)))
  rw [integral_map hmap.aemeasurable hint.aestronglyMeasurable]

lemma freshGaussianReplica_integrable {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) (m : ℕ) :
    Integrable (fun x : (Fin m → X) × (ℕ → ℝ) =>
      Real.exp (∑ i, f (cylinderField (A (x.1 i)) x.2)))
      ((Measure.pi (fun _ : Fin m => ν)).prod gaussianCoordinates) := by
  have hm : Measurable (fun x : (Fin m → X) × (ℕ → ℝ) =>
      Real.exp (∑ i, f (cylinderField (A (x.1 i)) x.2))) := by
    apply Measurable.exp
    apply Finset.measurable_sum
    intro i _
    exact hf.comp ((measurable_cylinderFields A).comp
      (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst)))
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (m*K))
  exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ∑ _ : Fin m, K := Finset.sum_le_sum (fun i _ => (le_abs_self _).trans (hK _))
        _ = _ := by simp)

lemma freshPatternFactor_pow {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (A : X → ℕ →₀ ℝ) (f : ℝ → ℝ) (m : ℕ) (g : ℕ → ℝ) : (freshPatternFactor ν A f g)^m =
      ∫ σ : Fin m → X, Real.exp (∑ i, f (cylinderField (A (σ i)) g)) ∂Measure.pi (fun _ => ν) := by
    simp only [Real.exp_sum]
    simpa only [Fintype.card_fin,freshPatternFactor] using
      (integral_fintype_prod_eq_pow (ι := Fin m) (μ := ν)
        (fun x => Real.exp (f (cylinderField (A x) g)))).symm

lemma freshPatternFactor_moment {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) (m : ℕ) :
    (∫ g, (freshPatternFactor ν A f g)^m ∂gaussianCoordinates) =
      ∫ σ : Fin m → X, gaussianMoment m f
        (fun i j => cylinderCross (A (σ i)) (A (σ j))) ∂Measure.pi (fun _ => ν) := by
  have he := freshPatternFactor_pow ν A f m
  calc
    _ = ∫ g, ∫ σ : Fin m → X, Real.exp (∑ i, f (cylinderField (A (σ i)) g))
        ∂Measure.pi (fun _ => ν) ∂gaussianCoordinates := integral_congr_ae (ae_of_all _ he)
    _ = ∫ σ : Fin m → X, ∫ g, Real.exp (∑ i, f (cylinderField (A (σ i)) g))
        ∂gaussianCoordinates ∂Measure.pi (fun _ => ν) := by
      have hi := freshGaussianReplica_integrable ν A hf hK m
      exact (integral_integral_swap hi).symm
    _ = _ := integral_congr_ae (ae_of_all _ (fun σ =>
      (gaussianMoment_cylinder_integral (fun i => A (σ i)) hf).symm))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma measurable_random_freshPatternFactor {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    {ν : Ω → Measure X} (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun z : Ω × (ℕ → ℝ) => freshPatternFactor (ν z.1) A f z.2) := by
  have : ∀ z : Ω × (ℕ → ℝ), IsProbabilityMeasure ((fun z => ν z.1) z) := fun _ => inferInstance
  exact measurable_random_referencePartition (ν := fun z : Ω × (ℕ → ℝ) => ν z.1)
    (hν.comp measurable_fst) (hf.comp ((measurable_cylinderFields A).comp
      (measurable_fst.snd.prodMk measurable_snd)))



end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_labeledScalarFactor (n : ℕ) (s : ℕ → ℝ) {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun p : ℝ × (LabeledTree n × (ForestVertex n → ℝ)) => labeledScalarFactor n s F p.1 p.2) := by
  change Measurable (fun p : ℝ × (LabeledTree n × (ForestVertex n → ℝ)) =>
    referencePartition (labeledLeafLaw n p.2.1) (fun v => F (p.1+∑ i : Fin n, s i*p.2.2 (edgeAt n v i))))
  apply measurable_random_referencePartition (ν := fun p : ℝ × (LabeledTree n × (ForestVertex n → ℝ)) => labeledLeafLaw n p.2.1)
    ((measurable_labeledLeafLaw n).comp (by fun_prop))
    (H := fun p : (ℝ × (LabeledTree n × (ForestVertex n → ℝ))) × LabeledLeaf n => F (p.1.1+∑ i : Fin n, s i*p.1.2.2 (edgeAt n p.2 i)))
  apply hF.comp
  apply Measurable.add (by fun_prop)
  apply Finset.measurable_sum
  intro i _
  apply Measurable.const_mul
  have hv : Measurable (fun p : (ForestVertex n → ℝ) × LabeledLeaf n => p.1 (edgeAt n p.2 i)) :=
    measurable_from_prod_countable_left (fun v => measurable_pi_apply (edgeAt n v i))
  exact hv.comp (by fun_prop : Measurable (fun p : (ℝ × (LabeledTree n × (ForestVertex n → ℝ))) × LabeledLeaf n => (p.1.2.2,p.2)))

lemma labeledScalar_log_bound (n : ℕ) (s : ℕ → ℝ) (F : ℝ → ℝ) {K : ℝ}
    (hF : ∀ y, |F y| ≤ K) (x : ℝ) (p : LabeledTree n × (ForestVertex n → ℝ)) :
    |Real.log (labeledScalarFactor n s F x p)| ≤ K := by
  simpa only [logMean,one_mul,div_one,labeledScalarFactor] using
    logMean_bounds (labeledLeafLaw n p.1) (measurable_of_countable (fun v => F (x+∑ i : Fin n, s i*p.2 (edgeAt n v i))))
      (b := 1) zero_lt_one (fun v => hF _)

lemma labeledScalarFactor_eq_noise (n : ℕ) (b s : ℕ → ℝ) (hb : CascadeExponents n b)
    {F : ℝ → ℝ} (hF : Measurable F) (x : ℝ) :
    ∀ᵐ p ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)),
      labeledScalarFactor n s F x p =
        ∫ v, Real.exp (noiseLeafTerminal n (fun _ => F) (fun i p => p.1+s i*p.2) x v)
          ∂noiseLeafKernel ℝ n (labeledNoiseJoin ℝ n (p.1,markForestOfCoords ℝ n p.2)) := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun _ => ⟨gaussianReal 0 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  let T := fun p : LabeledTree n × (ForestVertex n → ℝ) =>
    labeledNoiseJoin ℝ n (p.1,markForestOfCoords ℝ n p.2)
  have hp : MeasurePreserving T ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)))
      (noiseCascadeLaw ℝ n b μ : Measure (NoiseTree ℝ n)) :=
    ⟨by fun_prop,labeledNoiseCoordinates_law ℝ n b μ⟩
  filter_upwards [hp.quasiMeasurePreserving.tendsto_ae.eventually (noiseCascade_good ℝ n b hb μ)] with p hg
  have htot : 0 < noiseTreeTotal ℝ n (T p) ∧ noiseTreeTotal ℝ n (T p) < ∞ := by
    cases n with
    | zero => simp [noiseTreeTotal,rawTreeTotal]
    | succ n => exact hg.1
  have hmap := labeledLeafLaw_noiseMap ℝ n p.1 (markForestOfCoords ℝ n p.2) hg htot
  have hm : Measurable (fun v : NoiseLeaf ℝ n => Real.exp (noiseLeafTerminal n (fun _ => F) (fun i p => p.1+s i*p.2) x v)) :=
    ((measurable_noiseLeafTerminal n (fun _ => hF) (fun i => by fun_prop)).comp
      (measurable_const.prodMk measurable_id)).exp
  rw [← hmap,integral_map (measurable_of_countable _).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [noiseLeafTerminal_additive,noiseLeafMark_labeled]

 

theorem labeledScalar_log_recursion (n : ℕ) (b s : ℕ → ℝ) (hb : CascadeExponents n b)
    {F : ℝ → ℝ} (hF : Measurable F) {K : ℝ} (hbound : ∀ y, |F y| ≤ K) (x : ℝ) :
    (∫ p, Real.log (labeledScalarFactor n s F x p)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1))) =
      cascadeRecursion n b (fun _ => ⟨gaussianReal 0 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩)
        (fun i p => p.1+s i*p.2) F x := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun _ => ⟨gaussianReal 0 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  let T := fun p : LabeledTree n × (ForestVertex n → ℝ) =>
    labeledNoiseJoin ℝ n (p.1,markForestOfCoords ℝ n p.2)
  have hp : MeasurePreserving T ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)))
      (noiseCascadeLaw ℝ n b μ : Measure (NoiseTree ℝ n)) :=
    ⟨by fun_prop,labeledNoiseCoordinates_law ℝ n b μ⟩
  have hr := bounded_cascade_leaf_recursion n b hb μ
    (fun i => (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1+s i*p.2))) hF hbound x
  calc
    _ = ∫ p, Real.log (∫ v, Real.exp (noiseLeafTerminal n (fun _ => F) (fun i p => p.1+s i*p.2) x v)
        ∂noiseLeafKernel ℝ n (T p)) ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)) := by
      apply integral_congr_ae
      filter_upwards [labeledScalarFactor_eq_noise n b s hb hF x] with p hp
      rw [hp]
    _ = _ := by
      have he := (HasLaw.mk hp.measurable.aemeasurable hp.map_eq).integral_comp hr.1.aestronglyMeasurable
      exact he.trans hr.2

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron



lemma measurable_rowFactor (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f) : Measurable (rowFactor c f) := by
  exact (hf.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1+Real.sqrt c*p.2))).exp.stronglyMeasurable.integral_prod_right'.measurable

lemma rowFactor_bound (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K) (y : ℝ) :
    rowFactor c f y ∈ Icc (Real.exp (-K)) (Real.exp K) := by
  have hi : Integrable (fun z => Real.exp (f (y+Real.sqrt c*z))) (gaussianReal 0 1) := by
    apply Integrable.of_bound (hf.comp (by fun_prop)).exp.aestronglyMeasurable (Real.exp K)
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (abs_le.mp (hb _)).2
  constructor
  · calc
      Real.exp (-K) = ∫ _ : ℝ, Real.exp (-K) ∂gaussianReal 0 1 := by simp
      _ ≤ _ := integral_mono (integrable_const _) hi (fun z => Real.exp_le_exp.mpr (abs_le.mp (hb _)).1)
  · calc
      _ ≤ ∫ _ : ℝ, Real.exp K ∂gaussianReal 0 1 :=
        integral_mono hi (integrable_const _) (fun z => Real.exp_le_exp.mpr (abs_le.mp (hb _)).2)
      _ = _ := by simp

lemma gaussianTransform_one (c : ℝ) (f : ℝ → ℝ) : gaussianTransform c 1 f = fun y => Real.log (rowFactor c f y) := by
  funext y
  simp [gaussianTransform,rowFactor]

lemma exp_gaussianTransform_one (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K) (y : ℝ) :
    Real.exp (gaussianTransform c 1 f y) = rowFactor c f y := by
  rw [gaussianTransform_one,Real.exp_log ((Real.exp_pos (-K)).trans_le (rowFactor_bound c hf hb y).1)]

lemma gaussianTransform_one_bound (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K) (y : ℝ) : |gaussianTransform c 1 f y| ≤ K := by
  have h := rowFactor_bound c hf hb y
  rw [gaussianTransform_one]
  apply abs_le.mpr
  constructor
  · have hh := Real.log_le_log (Real.exp_pos (-K)) h.1
    simpa only [Real.log_exp] using hh
  · have hh := Real.log_le_log ((Real.exp_pos (-K)).trans_le h.1) h.2
    simpa only [Real.log_exp] using hh

lemma rowFactor_product {m : ℕ} (c : ℝ) (f : ℝ → ℝ) (y : Fin m → ℝ) :
    (∏ i, rowFactor c f (y i)) =
      ∫ z : Fin m → ℝ, Real.exp (∑ i, f (y i+Real.sqrt c*z i))
        ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  simp only [Real.exp_sum]
  exact (integral_fintype_prod_eq_prod (fun i z => Real.exp (f (y i+Real.sqrt c*z)))).symm

lemma gaussianCoordinates_prefix {m : ℕ} :
    MeasurePreserving (fun g : ℕ → ℝ => fun i : Fin m => g i) gaussianCoordinates
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := by
  refine ⟨by fun_prop,?_⟩
  exact replica_prefix_map (gaussianReal 0 1) m

lemma rowFactor_product_coordinates {m : ℕ} (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f) (y : Fin m → ℝ) :
    (∏ i, rowFactor c f (y i)) =
      ∫ z : ℕ → ℝ, Real.exp (∑ i, f (y i+Real.sqrt c*z i)) ∂gaussianCoordinates := by
  rw [rowFactor_product]
  exact (HasLaw.integral_comp ⟨gaussianCoordinates_prefix.measurable.aemeasurable,gaussianCoordinates_prefix.map_eq⟩
    (f := fun z : Fin m → ℝ => Real.exp (∑ i, f (y i+Real.sqrt c*z i))) ((Finset.measurable_sum _ (fun i _ => hf.comp (by fun_prop))).exp.aestronglyMeasurable)).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma residualGaussian_integrable {m : ℕ} (A : Fin m → ℕ →₀ ℝ) (c : ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hb : ∀ y, |f y| ≤ K) :
    Integrable (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      Real.exp (∑ i, f (cylinderField (A i) p.1+Real.sqrt c*p.2 i)))
      (gaussianCoordinates.prod gaussianCoordinates) := by
  have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      Real.exp (∑ i, f (cylinderField (A i) p.1+Real.sqrt c*p.2 i))) := by
    apply Measurable.exp
    apply Finset.measurable_sum
    intro i _
    exact hf.comp (((measurable_cylinderField (A i)).comp measurable_fst).add (by fun_prop))
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (m*K))
  filter_upwards [] with p
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ _ : Fin m, K := Finset.sum_le_sum (fun i _ => (abs_le.mp (hb _)).2)
    _ = _ := by simp

 

lemma gaussianMoment_residual {m : ℕ} (A : Fin m → ℕ →₀ ℝ) {c : ℝ} (hc : 0 ≤ c)
    {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hb : ∀ y, |f y| ≤ K) :
    gaussianMoment m (gaussianTransform c 1 f) (fun i j => cylinderCross (A i) (A j)) =
      gaussianMoment m f (fun i j => cylinderCross (A i) (A j)+(if i=j then c else 0)) := by
  classical
  let B : Fin m → ℕ →₀ ℝ := fun i => Finsupp.single i.val 1
  let C := gaussianSumCoefficients A B (Real.sqrt c)
  have hC (i j : Fin m) : cylinderCross (C i) (C j) =
      cylinderCross (A i) (A j)+(if i=j then c else 0) := by
    rw [gaussianSumCoefficients_cross,Real.sq_sqrt hc]
    simp only [B,cylinderCross_single_left,one_mul,Finsupp.single_apply,Fin.val_inj]
    by_cases h : i=j
    · simp [h]
    · simp [h,Ne.symm h]
  have hfield (i : Fin m) (g : ℕ → ℝ) : cylinderField (C i) g =
      cylinderField (A i) (gaussianPair g).1+Real.sqrt c*(gaussianPair g).2 i := by
    rw [gaussianSumCoefficients_field]
    simp [B,cylinderField]
  rw [gaussianMoment_cylinder_integral A (by rw [gaussianTransform_one]; exact (measurable_rowFactor c hf).log)]
  have hR : (fun i j => cylinderCross (A i) (A j)+(if i=j then c else 0)) =
      (fun i j => cylinderCross (C i) (C j)) := funext (fun i => funext (fun j => (hC i j).symm))
  rw [hR,gaussianMoment_cylinder_integral C hf]
  calc
    _ = ∫ g, ∫ z : ℕ → ℝ, Real.exp (∑ i, f (cylinderField (A i) g+Real.sqrt c*z i)) ∂gaussianCoordinates ∂gaussianCoordinates := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [Real.exp_sum]
      simp_rw [exp_gaussianTransform_one c hf hb]
      exact rowFactor_product_coordinates c hf (fun i => cylinderField (A i) g)
    _ = ∫ p : (ℕ → ℝ) × (ℕ → ℝ), Real.exp (∑ i, f (cylinderField (A i) p.1+Real.sqrt c*p.2 i))
        ∂gaussianCoordinates.prod gaussianCoordinates := (integral_prod _ (residualGaussian_integrable A c hf hb)).symm
    _ = _ := by
      have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
          Real.exp (∑ i, f (cylinderField (A i) p.1+Real.sqrt c*p.2 i))) := by
        apply Measurable.exp
        apply Finset.measurable_sum
        intro i _
        exact hf.comp (((measurable_cylinderField (A i)).comp measurable_fst).add (by fun_prop))
      have he := (HasLaw.mk gaussianPair_preserving.measurable.aemeasurable gaussianPair_preserving.map_eq).integral_comp hm.aestronglyMeasurable
      rw [← he]
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [Function.comp_apply,hfield]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma labeledCommonDepth_ultrametric (n : ℕ) (v w z : LabeledLeaf n) :
    min (labeledCommonDepth n v z) (labeledCommonDepth n w z) ≤ labeledCommonDepth n v w := by
  let d := min (labeledCommonDepth n v z) (labeledCommonDepth n w z)
  have hd : d ≤ n := (min_le_left _ _).trans (labeledCommonDepth_le n v z)
  apply (labeled_prefix_eq_iff n v w hd).mp
  exact ((labeled_prefix_eq_iff n v z hd).mpr (min_le_left _ _)).trans
    ((labeled_prefix_eq_iff n w z hd).mpr (min_le_right _ _)).symm

lemma monotone_labeledCommonDepth_ultrametric (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a)
    (v w z : LabeledLeaf n) :
    min (a (labeledCommonDepth n v z)) (a (labeledCommonDepth n w z)) ≤ a (labeledCommonDepth n v w) := by
  have h := ha (labeledCommonDepth_ultrametric n v w z)
  rcases le_total (labeledCommonDepth n v z) (labeledCommonDepth n w z) with he|he
  · simpa only [min_eq_left he,min_eq_left (ha he)] using h
  · simpa only [min_eq_right he,min_eq_right (ha he)] using h

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Classical
namespace IsingPerceptron

lemma diagonalPatch_arrayBlock (D : ℝ) {Ω : Type*} (B : Ω → RealArray) (n : ℕ) (ω : Ω) :
    arrayBlock (fun ω => diagonalPatch D (B ω)) n ω = diagonalPatch D (arrayBlock B n ω) := by
  funext i j
  simp only [arrayBlock,diagonalPatch,Fin.val_inj]

lemma diagonalPatch_ultrametric {B : RealArray} (D : ℝ) (hs : ∀ i j, B i j = B j i)
    (hB : IsUltrametricArray B) (hb : ∀ i j, B i j ≤ D) :
    IsUltrametricArray (diagonalPatch D B) := by
  intro i j k
  by_cases hij : i=j
  · subst j
    by_cases hik : i=k
    · subst k; simp [diagonalPatch]
    · simp [diagonalPatch,hik,hb]
  · by_cases hik : i=k
    · subst k
      simpa only [diagonalPatch,ite_true,hij,ite_false,Ne.symm hij,hs j i] using (min_le_right D (B i j))
    · by_cases hjk : j=k
      · subst k
        simpa only [diagonalPatch,ite_true,hij,ite_false] using (min_le_left (B i j) D)
      · simpa only [diagonalPatch,hij,hik,hjk,ite_false] using hB i j k

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_CascadeFreshMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Fresh Moments. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma freshPatternFactor_replica_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) (m : ℕ) :
    (∫ z : Ω × (ℕ → ℝ), (freshPatternFactor (ν z.1) A f z.2)^m ∂P.prod gaussianCoordinates) =
      ∫ σ, gaussianMoment m f (fun i j : Fin m => cylinderCross (A (σ i)) (A (σ j)))
        ∂replicaLaw P ν hν := by
  rw [replicaLaw_integral_prefix P ν hν
    (fun σ : Fin m → X => gaussianMoment m f (fun i j : Fin m => cylinderCross (A (σ i)) (A (σ j))))
    (fun σ => gaussianMoment_bound m hK _)]
  have hi : Integrable (fun z : Ω × (ℕ → ℝ) => (freshPatternFactor (ν z.1) A f z.2)^m)
      (P.prod gaussianCoordinates) := by
    apply Integrable.of_bound ((measurable_random_freshPatternFactor hν A hf).pow_const m).aestronglyMeasurable
      ((Real.exp K)^m)
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_pow,abs_of_nonneg ((Real.exp_pos _).le.trans (freshPatternFactor_bound (ν z.1) A f hK z.2).1)]
      exact pow_le_pow_left₀ ((Real.exp_pos _).le.trans (freshPatternFactor_bound (ν z.1) A f hK z.2).1)
        (freshPatternFactor_bound (ν z.1) A f hK z.2).2 _)
  rw [integral_prod _ hi]
  exact integral_congr_ae (ae_of_all _ (fun ω => freshPatternFactor_moment (ν ω) A hf hK m))



lemma measurable_cascadeFreshFactor (n : ℕ) (a : ℕ → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (cascadeFreshFactor n a f) := by
  apply measurable_random_freshPatternFactor (measurable_labeledLeafLaw n)
  rw [gaussianTransform_one]
  exact (measurable_rowFactor _ hf).log

lemma cascadeFreshFactor_bound (n : ℕ) (a : ℕ → ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hb : ∀ x, |f x| ≤ K) (p : LabeledTree n × (ℕ → ℝ)) :
    cascadeFreshFactor n a f p ∈ Icc (Real.exp (-K)) (Real.exp K) :=
  freshPatternFactor_bound _ _ _ (gaussianTransform_one_bound _ hf hb) _

 

theorem cascadeFreshFactor_moment (n : ℕ) (b a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0)
    (ha1 : a n ≤ 1) {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hb : ∀ x, |f x| ≤ K) (m : ℕ) :
    (∫ p, (cascadeFreshFactor n a f p)^m
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) =
      ∫ σ, gaussianMoment m f (fun i j : Fin m => diagonalPatch 1 (cascadeScalarArray n a σ) i j)
        ∂cascadeReplicaLaw n b := by
  rw [cascadeReplicaLaw_eq_replicaLaw]
  change (∫ p, (freshPatternFactor _ _ _ _ : ℝ)^m ∂_) = _
  rw [freshPatternFactor_replica_moment _ _ (measurable_labeledLeafLaw n) _
    (by rw [gaussianTransform_one]; exact (measurable_rowFactor _ hf).log)
    (gaussianTransform_one_bound _ hf hb)]
  apply integral_congr_ae
  filter_upwards [] with σ
  rw [gaussianMoment_residual _ (sub_nonneg.mpr ha1) hf hb]
  congr 1
  funext i j
  rw [treeField_path_cross n (σ i) (σ j) ha ha0]
  simp only [Fintype.sum_unique,mul_one,diagonalPatch,cascadeScalarArray]
  by_cases hij : i=j
  · subst j
    simp only [ite_true,labeledCommonDepth_self]
    ring
  · simp [hij,show (i:ℕ) ≠ (j:ℕ) from fun h => hij (Fin.ext h)]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_scalar_root_factor (n : ℕ) (s : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) (c : ℝ) :
    Measurable (fun p : (LabeledTree n × ℝ) × (ForestVertex n → ℝ) =>
      Real.log (labeledScalarFactor n s F (c*p.1.2) (p.1.1,p.2))) := by
  let j : (LabeledTree n × ℝ) × (ForestVertex n → ℝ) → ℝ × (LabeledTree n × (ForestVertex n → ℝ)) :=
    fun p => (c*p.1.2,(p.1.1,p.2))
  have hj : Measurable j :=
    (measurable_fst.snd.const_mul c).prodMk (measurable_fst.fst.prodMk measurable_snd)
  exact ((measurable_labeledScalarFactor n s hF).comp hj).log

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma scalarFreshFactor_nodes (n : ℕ) (a : ℕ → ℝ) (F : ℝ → ℝ) (T : LabeledTree n) (g : ℕ → ℝ) :
    freshPatternFactor (labeledLeafLaw n T)
      (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1)) F g =
    labeledScalarFactor n (fun i => pathAmplitude a (i+1)) F (pathAmplitude a 0*scalarGaussianNodes n g none)
      (T,fun v => scalarGaussianNodes n g (some v)) := by
  unfold freshPatternFactor labeledScalarFactor
  apply integral_congr_ae
  filter_upwards [] with v
  rw [cylinderField_scalar_nodes]

lemma scalarFresh_log_bound (n : ℕ) (a : ℕ → ℝ) (F : ℝ → ℝ) {K : ℝ}
    (hF : ∀ y, |F y| ≤ K) (T : LabeledTree n) (g : ℕ → ℝ) :
    |Real.log (freshPatternFactor (labeledLeafLaw n T)
      (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1)) F g)| ≤ K := by
  rw [scalarFreshFactor_nodes]
  exact labeledScalar_log_bound _ _ _ hF _ _

 

theorem scalarFresh_log_recursion (n : ℕ) (b a : ℕ → ℝ) (hb : CascadeExponents n b)
    {F : ℝ → ℝ} (hF : Measurable F) {K : ℝ} (hbound : ∀ y, |F y| ≤ K) :
    (∫ p, Real.log (freshPatternFactor (labeledLeafLaw n p.1)
      (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1)) F p.2)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) =
    ∫ z, cascadeRecursion n b (fun _ => ⟨gaussianReal 0 1,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩)
      (fun i p => p.1+pathAmplitude a (i+1)*p.2) F (pathAmplitude a 0*z) ∂gaussianReal 0 1 := by
  let P := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let Q := Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)
  let s := fun i => pathAmplitude a (i+1)
  let J : (LabeledTree n × ℝ) × (ForestVertex n → ℝ) → ℝ :=
    fun p => Real.log (labeledScalarFactor n s F (pathAmplitude a 0*p.1.2) (p.1.1,p.2))
  have hJ : Measurable J := measurable_scalar_root_factor n s hF (pathAmplitude a 0)
  have hJB (p) : |J p| ≤ K := labeledScalar_log_bound n s F hbound _ _
  have hi : Integrable (fun p : LabeledTree n × (ℕ → ℝ) => Real.log (freshPatternFactor (labeledLeafLaw n p.1)
      (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1)) F p.2))
      (P.prod gaussianCoordinates) := by
    apply Integrable.of_bound ((measurable_random_freshPatternFactor (measurable_labeledLeafLaw n) _ hF).log).aestronglyMeasurable K
    exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using scalarFresh_log_bound n a F hbound p.1 p.2)
  rw [integral_prod _ hi]
  have heT (T : LabeledTree n) :
      (∫ g, Real.log (freshPatternFactor (labeledLeafLaw n T)
        (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1)) F g) ∂gaussianCoordinates) =
      ∫ z, ∫ w, J ((T,z),w) ∂Q ∂gaussianReal 0 1 := by
    have hm : Measurable (fun p : ℝ × (ForestVertex n → ℝ) => J ((T,p.1),p.2)) := hJ.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hI : Integrable (fun p : ℝ × (ForestVertex n → ℝ) => J ((T,p.1),p.2)) ((gaussianReal 0 1).prod Q) := by
      apply Integrable.of_bound hm.aestronglyMeasurable K
      exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hJB ((T,p.1),p.2))
    have he := (HasLaw.mk (scalarGaussianRootForest_law n).measurable.aemeasurable
      (scalarGaussianRootForest_law n).map_eq).integral_comp hm.aestronglyMeasurable
    rw [integral_prod _ hI] at he
    simpa only [Function.comp_apply,scalarFreshFactor_nodes,J,s] using he
  simp_rw [heT]
  have hI : Integrable (fun p : LabeledTree n × ℝ => ∫ w, J (p,w) ∂Q) (P.prod (gaussianReal 0 1)) := by
    apply Integrable.of_bound hJ.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable K
    filter_upwards [] with p
    have hh : ‖∫ w, J (p,w) ∂Q‖ ≤ K*Q.real univ :=
      norm_integral_le_of_norm_le_const (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hJB (p,w)))
    simpa using hh
  rw [integral_integral_swap hI]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : Integrable (fun p : LabeledTree n × (ForestVertex n → ℝ) => J ((p.1,z),p.2)) (P.prod Q) := by
    apply Integrable.of_bound (hJ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).aestronglyMeasurable K
    exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hJB ((p.1,z),p.2))
  rw [← integral_prod _ hz]
  exact labeledScalar_log_recursion n b s hb hF hbound (pathAmplitude a 0*z)

 
theorem cascadeFresh_log_value (n : ℕ) (b a : ℕ → ℝ) (hb : CascadeExponents n b)
    {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hbound : ∀ y, |f y| ≤ K) :
    (∫ p, Real.log (cascadeFreshFactor n a f p)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) =
    gaussianTransform (a 0) 0
      ((List.ofFn (fun i : Fin n => (pathIncrement a (i+1),b i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U) (gaussianTransform (1-a n) 1 f)) 0 := by
  rw [show cascadeFreshFactor n a f = fun p => freshPatternFactor (labeledLeafLaw n p.1)
      (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1))
      (gaussianTransform (1-a n) 1 f) p.2 from rfl]
  rw [scalarFresh_log_recursion n b a hb
    (by rw [gaussianTransform_one]; exact (measurable_rowFactor _ hf).log)
    (gaussianTransform_one_bound _ hf hbound)]
  change (∫ z, cascadeRecursion n b _ (fun i p => p.1+Real.sqrt (pathIncrement a (i+1))*p.2)
    (gaussianTransform (1-a n) 1 f) (pathAmplitude a 0*z) ∂gaussianReal 0 1) = _
  rw [cascadeRecursion_gaussian n b (fun i => pathIncrement a (i+1)) _ (fun i hi => (hb.1 i hi).1.ne')]
  simp only [gaussianTransform,ite_true,pathAmplitude,pathIncrement,zero_add]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma cell_subset_unit (n i : ℕ) (hi : i ≤ n) :
    Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ)) ⊆ Ioo (0:ℝ) 1 := by
  intro u hu
  constructor
  · exact lt_of_le_of_lt (by positivity) hu.1
  · apply hu.2.trans_le
    apply (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    exact_mod_cast Nat.succ_le_succ hi

lemma uniformCellAverage_eq_cellAverage (q : OverlapPath) (p : ℝ → ℝ)
    (hp : p =ᵐ[pathMeasure] q.val) (n i : ℕ) (hi : i ≤ n) :
    uniformCellAverage p n i = cellAverage q (n+1) i := by
  unfold uniformCellAverage cellAverage
  congr 1
  have hm : pathMeasure.restrict (Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ))) =
      volume.restrict (Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ))) := by
    rw [pathMeasure,Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr (cell_subset_unit n i hi)]
  rw [← hm]
  exact integral_congr_ae hp.restrict

lemma uniformPattern_root_tail (f : ℝ → ℝ) (q : OverlapPath) (n : ℕ) :
    uniformPattern f q n =
    gaussianTransform (cellAverage q (n+1) 0) 0
      ((List.ofFn (fun i : Fin n => (cellAverage q (n+1) (i+1)-cellAverage q (n+1) i,
        uniformExponent n i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U)
        (gaussianTransform (1-cellAverage q (n+1) n) 1 f)) 0 := by
  dsimp only [uniformPattern]
  rw [List.ofFn_succ]
  simp only [Fin.val_zero,Nat.cast_zero,Nat.zero_lt_succ,ite_true,sub_zero,zero_div,List.foldr_cons]
  apply congrArg (fun U : ℝ → ℝ => gaussianTransform (cellAverage q (n+1) 0) 0 U 0)
  rw [List.ofFn_succ']
  rw [List.concat_eq_append]
  simp only [List.foldr_append,List.foldr_cons,List.foldr_nil]
  congr 1
  · simp only [Fin.val_last,Fin.val_succ,Nat.lt_irrefl,ite_false,Nat.succ_ne_zero,
      Nat.add_sub_cancel,Nat.lt_succ_self,ite_true,Nat.cast_add,Nat.cast_one]
    rw [div_self (by positivity : (n:ℝ)+1 ≠ 0)]
  · apply congrArg List.ofFn
    funext i
    simp only [Fin.val_castSucc,Fin.val_succ,Nat.add_sub_cancel,Nat.succ_ne_zero,ite_false,
      show i.val+1 < n+1 by omega,show i.val < n+1 by omega,ite_true,uniformExponent,Nat.cast_add,Nat.cast_one]

lemma cascadeFresh_uniformPattern (q : OverlapPath) (p : ℝ → ℝ)
    (hp : p =ᵐ[pathMeasure] q.val) (n : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hbound : ∀ y, |f y| ≤ K) :
    (∫ x, Real.log (cascadeFreshFactor n (uniformCellAverage p n) f x)
      ∂(labeledCascadeLaw n (uniformExponent n) : Measure (LabeledTree n)).prod gaussianCoordinates) =
    uniformPattern f q n := by
  rw [cascadeFresh_log_value n _ _ (uniformExponent_cascade n) hf hbound,uniformPattern_root_tail]
  congr 2
  · exact uniformCellAverage_eq_cellAverage q p hp n 0 (Nat.zero_le _)
  congr 2
  · exact uniformCellAverage_eq_cellAverage q p hp n n le_rfl
  · apply congrArg List.ofFn
    funext i
    simp only [pathIncrement]
    rw [uniformCellAverage_eq_cellAverage q p hp n (i+1) (by omega),
      uniformCellAverage_eq_cellAverage q p hp n i (by omega)]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

lemma unitClip_eq {x : ℝ} (h : x ∈ Icc (0:ℝ) 1) : unitClip x = x := by
  simp only [unitClip,min_eq_right h.2,max_eq_right h.1]

lemma spinArray_compactScalarArray {B : RealArray} (hB : ∀ i j, B i j ∈ Icc (0:ℝ) 1) :
    spinArray (compactScalarArray B) = B := by
  funext i j
  exact unitClip_eq (hB i j)

lemma cascade_patch_mem (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) (i j : ℕ) :
    diagonalPatch 1 (cascadeScalarArray n a σ) i j ∈ Icc (0:ℝ) 1 := by
  unfold diagonalPatch cascadeScalarArray
  split_ifs
  · exact ⟨zero_le_one,le_rfl⟩
  · exact ⟨h0.trans (ha (Nat.zero_le _)),(ha (labeledCommonDepth_le n _ _)).trans h1⟩

lemma cascadeCompact_spin (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) :
    spinArray (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) =
      diagonalPatch 1 (cascadeScalarArray n a σ) :=
  spinArray_compactScalarArray (cascade_patch_mem n ha h0 h1 σ)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

 

lemma cascade_integral_GG (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (a : ℕ → ℝ) (i : Fin (r+1)) (D : (Fin (r+1) → Fin (r+1) → ℝ) → ℝ)
    (c : ℝ → ℝ) :
    ((r+1:ℕ):ℝ)*(∫ σ, D (arrayBlock (cascadeScalarArray n a) (r+1) σ)*c (cascadeScalarArray n a σ i (r+1)) ∂cascadeReplicaLaw n b) -
      (∫ σ, D (arrayBlock (cascadeScalarArray n a) (r+1) σ) ∂cascadeReplicaLaw n b)*
      (∫ σ, c (cascadeScalarArray n a σ 0 1) ∂cascadeReplicaLaw n b) -
      ∑ j ∈ Finset.univ.erase i,
        ∫ σ, D (arrayBlock (cascadeScalarArray n a) (r+1) σ)*c (cascadeScalarArray n a σ i j) ∂cascadeReplicaLaw n b = 0 := by
  let E : PrefixPattern n (r+1) → ℝ := fun Q => D (fun i j => prefixVectorValue n a (Q i j))
  let e : ℕ → ℝ := fun k => c (a k)
  have h := prefixGGResidual_value n r b hb i E e
  change ((r+1:ℕ):ℝ)*prefixPatternMean n (r+1+1) b
      (fun Q => E (patternReindex Q Fin.castSucc)*prefixVectorValue n e (Q i.castSucc (Fin.last (r+1)))) -
    prefixPatternMean n (r+1) b E*prefixPatternMean n 2 b (fun Q => prefixVectorValue n e (Q 0 1)) -
    (∑ j ∈ Finset.univ.erase i, prefixPatternMean n (r+1) b (fun Q => E Q*prefixVectorValue n e (Q i j))) = 0 at h
  unfold arrayBlock
  simpa only [prefixPatternMean,E,e,patternReindex_label,prefixVectorValue_pattern,
    Function.comp_apply,Fin.val_castSucc,Fin.val_last,Fin.val_zero,Fin.val_one,cascadeScalarArray] using h

lemma cascade_patch_integral_GG (n m : ℕ) (hm : 0 < m) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (a : ℕ → ℝ) (i : Fin m) (v : ℝ)
    (D : (Fin m → Fin m → ℝ) → ℝ) (c : ℝ → ℝ) :
    (m:ℝ)*(∫ σ, D (arrayBlock (fun σ => diagonalPatch v (cascadeScalarArray n a σ)) m σ)*
        c (diagonalPatch v (cascadeScalarArray n a σ) i m) ∂cascadeReplicaLaw n b) -
      (∫ σ, D (arrayBlock (fun σ => diagonalPatch v (cascadeScalarArray n a σ)) m σ) ∂cascadeReplicaLaw n b)*
      (∫ σ, c (diagonalPatch v (cascadeScalarArray n a σ) 0 1) ∂cascadeReplicaLaw n b) -
      ∑ j ∈ Finset.univ.erase i,
        ∫ σ, D (arrayBlock (fun σ => diagonalPatch v (cascadeScalarArray n a σ)) m σ)*
          c (diagonalPatch v (cascadeScalarArray n a σ) i j) ∂cascadeReplicaLaw n b = 0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have h := cascade_integral_GG n r b hb a i (fun B => D (diagonalPatch v B)) c
  simp_rw [diagonalPatch_arrayBlock]
  have hin : (i:ℕ) ≠ r+1 := Nat.ne_of_lt i.isLt
  simp only [diagonalPatch,hin,show (0:ℕ) ≠ 1 by omega,ite_false]
  have hs : (∑ j ∈ Finset.univ.erase i, ∫ σ, D (diagonalPatch v (arrayBlock (cascadeScalarArray n a) (r+1) σ))*
        c (if (i:ℕ) = (j:ℕ) then v else cascadeScalarArray n a σ i j) ∂cascadeReplicaLaw n b) =
      ∑ j ∈ Finset.univ.erase i, ∫ σ, D (diagonalPatch v (arrayBlock (cascadeScalarArray n a) (r+1) σ))*
        c (cascadeScalarArray n a σ i j) ∂cascadeReplicaLaw n b := by
    apply Finset.sum_congr rfl
    intro j hj
    have hij : (i:ℕ) ≠ (j:ℕ) := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h).symm
    simp only [hij,ite_false]
  rw [hs]
  exact h

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

lemma cascadeCompact_integral (n : ℕ) (b a : ℕ → ℝ) {F : JointArray → ℝ}
    (hF : Measurable F) :
    (∫ x, F x ∂(cascadeCompactLaw n b a : Measure JointArray)) =
      ∫ σ, F (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) ∂cascadeReplicaLaw n b := by
  exact integral_map
    (continuous_compactScalarArray.measurable.comp ((measurable_diagonalPatch 1).comp (measurable_cascadeScalarArray n a))).aemeasurable
    hF.aestronglyMeasurable

lemma cascadeCompact_residual (n : ℕ) (b a : ℕ → ℝ) (hb : CascadeExponents n b)
    (m : ℕ) (hm : 0 < m) (i : Fin m) (D : JointBlock m → ℝ) (hD : Continuous D) (p d : ℕ) :
    jointMonomialResidual (cascadeCompactLaw n b a) m i D p d = 0 := by
  have hDm : Measurable (fun x : JointArray => D (jointBlockView m x)) := hD.measurable.comp (continuous_jointBlockView m).measurable
  have htest (j : ℕ) : Measurable (fun x : JointArray => D (jointBlockView m x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d) :=
    (hDm.mul (by fun_prop)).mul (by fun_prop)
  unfold jointMonomialResidual
  rw [cascadeCompact_integral n b a (htest m),cascadeCompact_integral n b a hDm,
    cascadeCompact_integral n b a (by fun_prop)]
  simp_rw [cascadeCompact_integral n b a (htest _)]
  have h := cascade_patch_integral_GG n m hm b hb a i 1
    (fun B => D (fun i j => scalarJointEntry (B i j))) (fun x => unitClip x^p*(0:ℝ)^d)
  unfold jointBlockView compactScalarArray
  simpa only [scalarJointEntry,arrayBlock,mul_assoc] using h

lemma cascadeCompact_limit_GG {n : ℕ → ℕ} {b a : ℕ → ℕ → ℝ}
    (hb : ∀ k, CascadeExponents (n k) (b k)) {μ : ProbabilityMeasure JointArray}
    (hL : Tendsto (fun k => cascadeCompactLaw (n k) (b k) (a k)) atTop (𝓝 μ)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (μ : Measure JointArray) := by
  apply jointGG_of_weak_monomial_residuals hL
  intro r hr i D hD p d
  simpa only [cascadeCompact_residual _ _ _ (hb _) r (by omega) i D hD p d] using
    (tendsto_const_nhds (x := (0:ℝ)) : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix Classical
namespace IsingPerceptron

lemma cascade_patch_gram (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) : GramDiagonal 1 (diagonalPatch 1 (cascadeScalarArray n a σ)) := by
  constructor
  · intro m
    let A : Fin m → ℕ →₀ ℝ := fun i => treeFieldCoefficients n (σ i) (fun j => pathAmplitude a j) (fun _ : Unit => 1)
    have hA (i j : Fin m) : cylinderCross (A i) (A j) = cascadeScalarArray n a σ i j := by
      rw [treeField_path_cross n (σ i) (σ j) ha h0]
      simp only [Fintype.sum_unique,mul_one,cascadeScalarArray]
    have hM : (fun i j : Fin m => diagonalPatch 1 (cascadeScalarArray n a σ) i j) =
        (show Matrix (Fin m) (Fin m) ℝ from fun i j => cylinderCross (A i) (A j))+Matrix.diagonal (fun _ => 1-a n) := by
      funext i j
      change (if (i:ℕ)=(j:ℕ) then 1 else cascadeScalarArray n a σ i j) =
        cylinderCross (A i) (A j)+(if i=j then 1-a n else 0)
      simp only [hA,Fin.val_inj]
      by_cases hij : i=j
      · subst j
        simp only [ite_true,cascadeScalarArray,labeledCommonDepth_self]
        ring
      · simp only [hij,ite_false,add_zero]
    rw [hM]
    exact (cylinderCross_matrix_posSemidef A).add (Matrix.PosSemidef.diagonal (fun _ => sub_nonneg.mpr h1))
  · intro i
    simp only [diagonalPatch,ite_true]

lemma cascade_patch_ultra (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) : IsUltrametricArray (diagonalPatch 1 (cascadeScalarArray n a σ)) := by
  apply diagonalPatch_ultrametric
  · exact fun i j => congrArg a (labeledCommonDepth_symm n (σ i) (σ j))
  · exact fun i j k => monotone_labeledCommonDepth_ultrametric n ha (σ i) (σ j) (σ k)
  · exact fun i j => (ha (labeledCommonDepth_le n (σ i) (σ j))).trans h1

lemma cascadeCompact_geometry (n : ℕ) (b : ℕ → ℝ) {a : ℕ → ℝ}
    (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1) :
    (∀ᵐ x ∂(cascadeCompactLaw n b a : Measure JointArray), GramDiagonal 1 (spinArray x)) ∧
      ∀ᵐ x ∂(cascadeCompactLaw n b a : Measure JointArray), IsUltrametricArray (spinArray x) := by
  have hm := (continuous_compactScalarArray.measurable.comp ((measurable_diagonalPatch 1).comp (measurable_cascadeScalarArray n a))).aemeasurable (μ := cascadeReplicaLaw n b)
  constructor
  · apply (ae_map_iff hm ((isClosed_gramDiagonal 1).preimage continuous_spinArray).measurableSet).mpr
    filter_upwards [] with σ
    simp only [Function.comp_apply]
    rw [cascadeCompact_spin n ha h0 h1]
    exact cascade_patch_gram n ha h0 h1 σ
  · apply (ae_map_iff hm (isClosed_ultrametricArray.preimage continuous_spinArray).measurableSet).mpr
    filter_upwards [] with σ
    simp only [Function.comp_apply]
    rw [cascadeCompact_spin n ha h0 h1]
    exact cascade_patch_ultra n ha h1 σ

lemma cascadeCompact_limit_geometry {n : ℕ → ℕ} {b a : ℕ → ℕ → ℝ}
    (ha : ∀ k, Monotone (a k)) (h0 : ∀ k, 0 ≤ a k 0) (h1 : ∀ k, a k (n k) ≤ 1)
    {μ : ProbabilityMeasure JointArray}
    (hL : Tendsto (fun k => cascadeCompactLaw (n k) (b k) (a k)) atTop (𝓝 μ)) :
    (∀ᵐ x ∂(μ : Measure JointArray), GramDiagonal 1 (spinArray x)) ∧
      ∀ᵐ x ∂(μ : Measure JointArray), IsUltrametricArray (spinArray x) := by
  constructor
  · exact ae_closed_of_weak_limit hL ((isClosed_gramDiagonal 1).preimage continuous_spinArray)
      (fun k => (cascadeCompact_geometry _ _ (ha k) (h0 k) (h1 k)).1)
  · exact ae_closed_of_weak_limit hL (isClosed_ultrametricArray.preimage continuous_spinArray)
      (fun k => (cascadeCompact_geometry _ _ (ha k) (h0 k) (h1 k)).2)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma cellAverage_integral_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (F : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ u, F (uniformCellAverage q n (uniformCellIndex n u)) ∂unitUniform)
      atTop (𝓝 (∫ u, F (q u) ∂unitUniform)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.continuous.measurable.comp ((measurable_of_countable (uniformCellAverage q n)).comp
      (measurable_uniformCellIndex n))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun u => F.norm_coe_le_norm _)
  · filter_upwards [uniformCellAverage_ae_tendsto hq hb] with u hu
    exact F.continuous.continuousAt.tendsto.comp hu

lemma cascadeCompact_pair_integral (n : ℕ) {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (F : ℝ →ᵇ ℝ) :
    (∫ x, F (spinArray x 0 1) ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage q n) : Measure JointArray)) =
      ∫ u, F (uniformCellAverage q n (uniformCellIndex n u)) ∂unitUniform := by
  rw [cascadeCompact_integral n (uniformExponent n) (uniformCellAverage q n)
    (F := fun x => F (spinArray x 0 1)) ((F.continuous.comp (by unfold spinArray; fun_prop)).measurable)]
  simp_rw [cascadeCompact_spin n (uniformCellAverage_monotone hq hb n) (uniformCellAverage_mem hq hb n 0).1
    (uniformCellAverage_mem hq hb n n).2]
  simp only [diagonalPatch,show (0:ℕ) ≠ 1 by omega,ite_false]
  have he := congrArg (fun μ : Measure ℝ => ∫ x, F x ∂μ) (cascade_pair_uniformIndex n (uniformCellAverage q n))
  have hmap : Measurable (fun u => uniformCellAverage q n (uniformCellIndex n u)) :=
    (measurable_of_countable (uniformCellAverage q n)).comp (measurable_uniformCellIndex n)
  have hmap2 : Measurable (fun σ => cascadeScalarArray n (uniformCellAverage q n) σ 0 1) :=
    (measurable_pi_apply 1).comp ((measurable_pi_apply 0).comp (measurable_cascadeScalarArray n (uniformCellAverage q n)))
  rw [integral_map hmap.aemeasurable
      F.continuous.aestronglyMeasurable,
    integral_map hmap2.aemeasurable
      F.continuous.aestronglyMeasurable] at he
  exact he.symm

lemma cascadeCompact_limit_pairLaw {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {μ : ProbabilityMeasure JointArray}
    (hL : Tendsto (fun k => cascadeCompactLaw (ns k) (uniformExponent (ns k)) (uniformCellAverage q (ns k))) atTop (𝓝 μ)) :
    (μ : Measure JointArray).map (fun x => spinArray x 0 1) = unitUniform.map q := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map (by unfold spinArray; fun_prop : Measurable (fun x : JointArray => spinArray x 0 1)).aemeasurable
      F.continuous.aestronglyMeasurable,
    integral_map hq.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  apply tendsto_nhds_unique (jointArray_tendsto_integral hL (F.continuous.comp (by unfold spinArray; fun_prop)))
  simpa only [Function.comp_def,cascadeCompact_pair_integral _ hq hb F] using (cellAverage_integral_tendsto hq hb F).comp hns

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix BoundedContinuousFunction
namespace IsingPerceptron

lemma gaussianMoment_blockLaw {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {P : Measure Ω} (hB : Measurable B)
    (hG : ∀ᵐ x ∂P, GramDiagonal 1 (B x))
    (m : ℕ) {f : ℝ → ℝ} (_hf : Continuous f) {K : ℝ} (_hK : ∀ x, |f x| ≤ K)
    (F : Matrix (Fin m) (Fin m) ℝ →ᵇ ℝ) (hF : ∀ S, S.PosSemidef → F S = gaussianMoment m f S) :
    (∫ x, gaussianMoment m f (fun i j => B x i j) ∂P) = ∫ S, F S ∂blockLaw B P m := by
  let : MeasurableSpace (Matrix (Fin m) (Fin m) ℝ) := inferInstanceAs (MeasurableSpace (Fin m → Fin m → ℝ))
  let : BorelSpace (Matrix (Fin m) (Fin m) ℝ) := inferInstanceAs (BorelSpace (Fin m → Fin m → ℝ))
  rw [blockLaw,integral_map (measurable_arrayBlock hB m).aemeasurable F.continuous.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hG] with x hx
  exact (hF _ (hx.1 m)).symm

lemma gaussianMoment_blockLaw_congr {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {P : Measure Ω} {Q : Measure Ω'}
    (hB : Measurable B) (hC : Measurable C)
    (hG : ∀ᵐ x ∂P, GramDiagonal 1 (B x)) (hH : ∀ᵐ x ∂Q, GramDiagonal 1 (C x))
    (m : ℕ) (hL : blockLaw B P m = blockLaw C Q m)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    (∫ x, gaussianMoment m f (fun i j => B x i j) ∂P) =
      ∫ x, gaussianMoment m f (fun i j => C x i j) ∂Q := by
  obtain ⟨F,hF⟩ := gaussianMoment_extension m hf hK
  rw [gaussianMoment_blockLaw hB hG m hf hK F hF,gaussianMoment_blockLaw hC hH m hf hK F hF,hL]

lemma cascadeFreshFactor_compact_moment (n : ℕ) (b a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0)
    (ha1 : a n ≤ 1) {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hb : ∀ x, |f x| ≤ K) (m : ℕ) :
    (∫ p, (cascadeFreshFactor n a f p)^m
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) =
      ∫ x, gaussianMoment m f (fun i j : Fin m => spinArray x i j)
        ∂(cascadeCompactLaw n b a : Measure JointArray) := by
  rw [cascadeFreshFactor_moment n b a ha ha0 ha1 hf.measurable hb m]
  obtain ⟨F,hF⟩ := gaussianMoment_extension m hf hb
  have he : (∫ x, gaussianMoment m f (fun i j : Fin m => spinArray x i j)
      ∂(cascadeCompactLaw n b a : Measure JointArray)) =
      ∫ x, F (fun i j : Fin m => spinArray x i j) ∂(cascadeCompactLaw n b a : Measure JointArray) := by
    apply integral_congr_ae
    filter_upwards [(cascadeCompact_geometry n b ha ha0 ha1).1] with x hx
    exact (hF _ (hx.1 m)).symm
  rw [he,cascadeCompact_integral n b a (F := fun x => F (fun i j : Fin m => spinArray x i j))
    (F.continuous.comp (by unfold spinArray; fun_prop)).measurable]
  apply integral_congr_ae
  filter_upwards [] with σ
  rw [cascadeCompact_spin n ha ha0 ha1]
  exact (hF _ ((cascade_patch_gram n ha ha0 ha1 σ).1 m)).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

 

theorem cascadeFresh_moments_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (μ : ProbabilityMeasure JointArray)
    (hGG : HasGhirlandaGuerra spinArray (μ : Measure JointArray))
    (hG : ∀ᵐ x ∂(μ : Measure JointArray), GramDiagonal 1 (spinArray x))
    (hU : ∀ᵐ x ∂(μ : Measure JointArray), IsUltrametricArray (spinArray x))
    (hp : (μ : Measure JointArray).map (fun x => spinArray x 0 1) = unitUniform.map q)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) (m : ℕ) :
    Tendsto (fun n => ∫ x, (cascadeFreshFactor n (uniformCellAverage q n) f x)^m
      ∂(labeledCascadeLaw n (uniformExponent n) : Measure (LabeledTree n)).prod gaussianCoordinates)
      atTop (𝓝 (∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(μ : Measure JointArray))) := by
  simp_rw [cascadeFreshFactor_compact_moment _ _ _ (uniformCellAverage_monotone hq hb _)
    (uniformCellAverage_mem hq hb _ 0).1 (uniformCellAverage_mem hq hb _ _).2 hf hK m]
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν,ms,hms,hν⟩ := jointArrayLaw_subsequence
    (fun k => cascadeCompactLaw (ns k) (uniformExponent (ns k)) (uniformCellAverage q (ns k)))
  have hν' : Tendsto (fun k => cascadeCompactLaw (ns (ms k)) (uniformExponent (ns (ms k)))
      (uniformCellAverage q (ns (ms k)))) atTop (𝓝 ν) := hν
  have hgeom := cascadeCompact_limit_geometry
    (fun k => uniformCellAverage_monotone hq hb (ns (ms k)))
    (fun k => (uniformCellAverage_mem hq hb (ns (ms k)) 0).1)
    (fun k => (uniformCellAverage_mem hq hb (ns (ms k)) (ns (ms k))).2) hν'
  have hGGν : HasGhirlandaGuerra spinArray (ν : Measure JointArray) :=
    (cascadeCompact_limit_GG (fun k => uniformExponent_cascade (ns (ms k))) hν').real_map
      (f := fun x => x.1.1) (by fun_prop)
  have hpair := cascadeCompact_limit_pairLaw hq hb (hns.comp hms.tendsto_atTop) hν'
  have hblock := gg_blockLaw_unique continuous_spinArray.measurable continuous_spinArray.measurable
    hGGν hGG (hgeom.1.mono (fun _ h => h.symm)) (hG.mono (fun _ h => h.symm))
    hgeom.2 hU (hgeom.1.mono (fun _ h => h.2)) (hG.mono (fun _ h => h.2)) (hpair.trans hp.symm)
  have he := gaussianMoment_blockLaw_congr continuous_spinArray.measurable continuous_spinArray.measurable
    hgeom.1 hG m (hblock m) hf hK
  refine ⟨ms,?_⟩
  rw [← he]
  exact jointArray_tendsto_gaussianMoment hν'
    (fun k => (cascadeCompact_geometry _ _ (uniformCellAverage_monotone hq hb _)
      (uniformCellAverage_mem hq hb _ 0).1 (uniformCellAverage_mem hq hb _ _).2).1)
    hgeom.1 m hf hK

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_FieldChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Field Chain. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma chainExponent_apply {n : ℕ} (ζ : Fin (n+2) → ℝ) {i : ℕ} (hi : i<n) :
    chainExponent ζ i = ζ ⟨i+1,by omega⟩ := by simp [chainExponent,min_eq_left (by omega : i+1 ≤ n+1)]

lemma chainExponent_admissible {n : ℕ} {ζ : Fin (n+2) → ℝ} (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1) : CascadeExponents n (chainExponent ζ) := by
  constructor
  · intro i hi
    rw [chainExponent_apply ζ hi]
    constructor
    · rw [← hfirst]
      exact hz (by change (0 : ℕ) < i+1; omega)
    · rw [← hlast]
      exact hz (by change i+1 < n+1; omega)
  · intro i j hij hj
    rw [chainExponent_apply ζ (by omega),chainExponent_apply ζ hj]
    exact hz (by simpa using (show i+1<j+1 by omega))

lemma stepAt_chain {n : ℕ} (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) {i : ℕ} (hi : i≤n) :
    stepAt (chainFieldStep n ζ hz hfirst hlast h hh h0) i = h i := by
  simp [stepAt,chainFieldStep,chainPartition,show i<n+1 by omega]

lemma fieldRecursion_chain (n : ℕ) (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    fieldRecursion (chainFieldStep n ζ hz hfirst hlast h hh h0) =
      magneticFieldValue n (chainExponent ζ) h := by
  let F := chainFieldStep n ζ hz hfirst hlast h hh h0
  have hat (i : ℕ) (hi : i≤n) : stepAt F i=h i := stepAt_chain ζ hz hfirst hlast h hh h0 hi
  let T := List.ofFn (fun i : Fin n => ((pathAmplitude h (i+1))^2,chainExponent ζ i))
  have ht : (List.ofFn (fun i : Fin n =>
      (stepAt F (i.val+1)-(if i.val+1=0 then 0 else stepAt F (i.val+1-1)),
        ζ i.succ.castSucc))) = T := by
    apply congrArg List.ofFn
    funext i
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,hat _ (by omega : i.val+1≤n),hat _ (by omega : i.val≤n),
      pathAmplitude_sq hh h0,pathIncrement,chainExponent_apply ζ i.isLt]
    rfl
  have hd : ∀ sd ∈ T, 0 < sd.2 := by
    intro sd hs
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
    exact ((chainExponent_admissible hz hfirst hlast).1 i i.isLt).1
  have hg := magneticRecursion_growth n (fun i => pathAmplitude h (i+1)) (chainExponent ζ)
    (fun i hi => ((chainExponent_admissible hz hfirst hlast).1 i hi).1)
  have hf : T.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) (fun x => Real.log (Real.cosh x)) =
      magneticRecursion n (fun i => pathAmplitude h (i+1)) (chainExponent ζ) :=
    (magneticRecursion_eq_fold n (fun i => pathAmplitude h (i+1)) (chainExponent ζ)).symm
  change (List.ofFn (fun i : Fin (n+1) =>
    (stepAt F i-(if i.val=0 then 0 else stepAt F (i.val-1)), ζ i.castSucc))).foldr
      (fun sd U => gaussianTransform sd.1 sd.2 U)
      (fun x => Real.log (Real.cosh x)-stepAt F n/2) 0 = _
  rw [List.ofFn_succ,List.foldr_cons]
  simp only [Fin.val_zero,ite_true,Fin.castSucc_zero,hfirst,hat 0 (Nat.zero_le _),sub_zero,
    Fin.val_succ,hat n le_rfl]
  rw [ht]
  have hc : (fun x => Real.log (Real.cosh x)-h n/2) = (fun x => -h n/2+Real.log (Real.cosh x)) := by
    ext x; ring
  rw [hc,gaussianFold_const_add T hd measurable_logCosh logCosh_linearGrowth, hf,
    gaussianTransform_const_add hg.1 hg.2]
  simp only [gaussianTransform,ite_true,zero_add,magneticFieldValue,pathAmplitude,pathIncrement]
  ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open scoped BigOperators





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_MomentLogLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moment Log Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Polynomial
namespace IsingPerceptron

lemma integrable_pow_of_pos_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    {a b : ℝ} (ha : 0 < a) (hb : ∀ ω, Z ω ∈ Icc a b) (k : ℕ) :
    Integrable (fun ω => Z ω ^ k) P := by
  apply Integrable.of_bound (hZ.pow_const k).aestronglyMeasurable (b^k)
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs,abs_pow,abs_of_nonneg (ha.le.trans (hb ω).1)]
    exact pow_le_pow_left₀ (ha.le.trans (hb ω).1) (hb ω).2 _)

lemma integral_polynomial_of_pos_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    {a b : ℝ} (ha : 0 < a) (hb : ∀ ω, Z ω ∈ Icc a b) (p : ℝ[X]) :
    (∫ ω, p.eval (Z ω) ∂P) = ∑ k ∈ p.support, p.coeff k * ∫ ω, Z ω ^ k ∂P := by
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  rw [integral_finsetSum _ (fun k _ => (integrable_pow_of_pos_bounds hZ ha hb k).const_mul _)]
  simp only [integral_const_mul]

lemma integral_log_polynomial_error {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Z' : Ω' → ℝ) (hZ' : Measurable Z')
      {a b : ℝ} (hc : ContinuousOn Real.log (Icc a b))
    (hb' : ∀ ω, Z' ω ∈ Icc a b) (p : ℝ[X]) {ε : ℝ} (_hε : 0 < ε)
      (hp : ∀ x ∈ Icc a b, |p.eval x - Real.log x| < ε) :
      |(∫ ω, p.eval (Z' ω) ∂P') - ∫ ω, Real.log (Z' ω) ∂P'| ≤ ε := by
    have hip : Integrable (fun ω => p.eval (Z' ω)) P' := by
      have hpc : ContinuousOn (fun x => p.eval x) (Icc a b) := p.continuous.continuousOn
      obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hpc
      exact Integrable.of_bound (p.continuous.measurable.comp hZ').aestronglyMeasurable C
        (ae_of_all _ (fun ω => hC _ (hb' ω)))
    have hil : Integrable (fun ω => Real.log (Z' ω)) P' := by
      obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
      exact Integrable.of_bound (hZ'.log).aestronglyMeasurable C
        (ae_of_all _ (fun ω => hC _ (hb' ω)))
    rw [← integral_sub hip hil,← Real.norm_eq_abs]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := P') (C := ε) (ae_of_all _ (fun ω => by
        simpa only [Real.norm_eq_abs] using (hp _ (hb' ω)).le))

 

theorem tendsto_integral_log_of_moments
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ωlim : Type*} [MeasurableSpace Ωlim]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ωlim) [IsProbabilityMeasure Q]
    (Z : ∀ n, Ω n → ℝ) (W : Ωlim → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : Measurable W)
    {a b : ℝ} (ha : 0 < a) (_hb : a ≤ b)
    (hbound : ∀ n ω, Z n ω ∈ Icc a b) (hwbound : ∀ ω, W ω ∈ Icc a b)
    (hmoment : ∀ k : ℕ, Tendsto (fun n => ∫ ω, Z n ω ^ k ∂P n) atTop
      (𝓝 (∫ ω, W ω ^ k ∂Q))) :
    Tendsto (fun n => ∫ ω, Real.log (Z n ω) ∂P n) atTop
      (𝓝 (∫ ω, Real.log (W ω) ∂Q)) := by
  have hc : ContinuousOn Real.log (Icc a b) := Real.continuousOn_log.mono
    (fun x hx => ne_of_gt (ha.trans_le hx.1))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn a b Real.log hc (ε/3) (by positivity)
  have ht : Tendsto (fun n => ∫ ω, p.eval (Z n ω) ∂P n) atTop
      (𝓝 (∫ ω, p.eval (W ω) ∂Q)) := by
    simp_rw [integral_polynomial_of_pos_bounds (hZ _) ha (hbound _) p,
      integral_polynomial_of_pos_bounds hW ha hwbound p]
    exact tendsto_finsetSum _ (fun k _ => tendsto_const_nhds.mul (hmoment k))
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε/3) (by positivity)
  use N
  intro n hn
  rw [Real.dist_eq]
  have h1 := integral_log_polynomial_error (P n) (Z n) (hZ n) hc (hbound n) p (by positivity : 0 < ε/3) hp
  have h2 := integral_log_polynomial_error Q W hW hc hwbound p (by positivity : 0 < ε/3) hp
  have h3 := hN n hn
  rw [Real.dist_eq] at h3
  have htri := abs_add_three
    ((∫ ω, Real.log (Z n ω) ∂P n) - ∫ ω, p.eval (Z n ω) ∂P n)
    ((∫ ω, p.eval (Z n ω) ∂P n) - ∫ ω, p.eval (W ω) ∂Q)
    ((∫ ω, p.eval (W ω) ∂Q) - ∫ ω, Real.log (W ω) ∂Q)
  rw [abs_sub_comm] at h1
  have he : ((∫ ω, Real.log (Z n ω) ∂P n) - ∫ ω, p.eval (Z n ω) ∂P n) +
      ((∫ ω, p.eval (Z n ω) ∂P n) - ∫ ω, p.eval (W ω) ∂Q) +
      ((∫ ω, p.eval (W ω) ∂Q) - ∫ ω, Real.log (W ω) ∂Q) =
      (∫ ω, Real.log (Z n ω) ∂P n) - ∫ ω, Real.log (W ω) ∂Q := by ring
  rw [he] at htri
  linarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

 

theorem exists_positive_factor_of_moments
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z : ∀ n, Ω n → ℝ) (hZ : ∀ n, Measurable (Z n))
    {a b : ℝ} (hab : a ≤ b) (hb : ∀ n ω, Z n ω ∈ Icc a b)
    (L : ℕ → ℝ) (hL : ∀ k, Tendsto (fun n => ∫ ω, Z n ω^k ∂P n) atTop (𝓝 (L k))) :
    ∃ Q : ProbabilityMeasure (Icc a b), ∀ k, (∫ x, (x:ℝ)^k ∂(Q : Measure (Icc a b))) = L k := by
  let : Nonempty (Icc a b) := ⟨⟨a,le_rfl,hab⟩⟩
  let F (n : ℕ) : Ω n → Icc a b := fun ω => ⟨Z n ω,hb n ω⟩
  have hF (n) : Measurable (F n) := (hZ n).subtype_mk
  let M (n : ℕ) : ProbabilityMeasure (Icc a b) := ⟨(P n).map (F n),by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  obtain ⟨Q,_,ns,hns,hQ⟩ := isSeqCompact_univ.subseq_of_frequently_in
    (x := M) (Filter.Frequently.of_forall (fun _ => Set.mem_univ _))
  refine ⟨Q,?_⟩
  intro k
  have hT := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ)
    (BoundedContinuousFunction.mkOfCompact ⟨fun x : Icc a b => (x:ℝ)^k,by fun_prop⟩)
  have he (n) : (∫ x : Icc a b, (x:ℝ)^k ∂(M n : Measure (Icc a b))) = ∫ ω, Z n ω^k ∂P n := by
    exact integral_map (hF n).aemeasurable (by fun_prop : Continuous (fun x : Icc a b => (x:ℝ)^k)).aestronglyMeasurable
  change Tendsto (fun n => ∫ x : Icc a b, (x:ℝ)^k ∂(M (ns n) : Measure (Icc a b))) atTop
    (𝓝 (∫ x : Icc a b, (x:ℝ)^k ∂(Q : Measure (Icc a b)))) at hT
  simp only [he] at hT
  exact tendsto_nhds_unique hT ((hL k).comp hns.tendsto_atTop)

lemma factor_log_converges_of_moments
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z : ∀ n, Ω n → ℝ) (hZ : ∀ n, Measurable (Z n))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : ∀ n ω, Z n ω ∈ Icc a b)
    (L : ℕ → ℝ) (hL : ∀ k, Tendsto (fun n => ∫ ω, Z n ω^k ∂P n) atTop (𝓝 (L k))) :
    ∃ Q : ProbabilityMeasure (Icc a b),
      (∀ k, (∫ x, (x:ℝ)^k ∂(Q : Measure (Icc a b))) = L k) ∧
      Tendsto (fun n => ∫ ω, Real.log (Z n ω) ∂P n) atTop
        (𝓝 (∫ x, Real.log (x:ℝ) ∂(Q : Measure (Icc a b)))) := by
  obtain ⟨Q,hQ⟩ := exists_positive_factor_of_moments P Z hZ hab hb L hL
  refine ⟨Q,hQ,?_⟩
  exact tendsto_integral_log_of_moments P (Q : Measure (Icc a b)) Z (fun x => (x:ℝ)) hZ
    measurable_subtype_coe ha hab hb (fun x => x.property) (fun k => by rw [hQ k]; exact hL k)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

 

theorem patternFunctional_factor_law (q : OverlapPath) (p : ℝ → ℝ)
    (hpq : p =ᵐ[pathMeasure] q.val) (hp : Monotone p) (hb : ∀ u, p u ∈ Icc (0:ℝ) 1)
    (μ : ProbabilityMeasure JointArray) (hGG : HasGhirlandaGuerra spinArray (μ : Measure JointArray))
    (hG : ∀ᵐ x ∂(μ : Measure JointArray), GramDiagonal 1 (spinArray x))
    (hU : ∀ᵐ x ∂(μ : Measure JointArray), IsUltrametricArray (spinArray x))
    (hpair : (μ : Measure JointArray).map (fun x => spinArray x 0 1) = unitUniform.map p)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    ∃ Q : ProbabilityMeasure (Icc (Real.exp (-K)) (Real.exp K)),
      (∀ m, (∫ x, (x:ℝ)^m ∂(Q : Measure (Icc (Real.exp (-K)) (Real.exp K)))) =
        ∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(μ : Measure JointArray)) ∧
      (∫ x, Real.log (x:ℝ) ∂(Q : Measure (Icc (Real.exp (-K)) (Real.exp K)))) = patternFunctional f q ∧
      Tendsto (uniformPattern f q) atTop (𝓝 (patternFunctional f q)) := by
  have hK0 : 0 ≤ K := (abs_nonneg (f 0)).trans (hK 0)
  have he : Real.exp (-K) ≤ Real.exp K := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨Q,hQ,hT⟩ := factor_log_converges_of_moments
    (fun n => (labeledCascadeLaw n (uniformExponent n) : Measure (LabeledTree n)).prod gaussianCoordinates)
    (fun n => cascadeFreshFactor n (uniformCellAverage p n) f)
    (fun n => measurable_cascadeFreshFactor n _ hf.measurable) (Real.exp_pos _) he
    (fun n x => cascadeFreshFactor_bound n _ hf.measurable hK x)
    (fun m => ∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(μ : Measure JointArray))
    (cascadeFresh_moments_tendsto hp hb μ hGG hG hU hpair hf hK)
  have hv : Tendsto (uniformPattern f q) atTop (𝓝 (∫ x, Real.log (x:ℝ) ∂(Q : Measure (Icc (Real.exp (-K)) (Real.exp K))))) := by
    simpa only [cascadeFresh_uniformPattern q p hpq _ hf.measurable hK] using hT
  have heq : patternFunctional f q = ∫ x, Real.log (x:ℝ) ∂(Q : Measure (Icc (Real.exp (-K)) (Real.exp K))) := hv.limUnder_eq
  exact ⟨Q,hQ,heq.symm,by simpa only [heq] using hv⟩



end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

 

theorem uniformPattern_tendsto (q : OverlapPath) {f : ℝ → ℝ}
    (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Tendsto (uniformPattern f q) atTop (𝓝 (patternFunctional f q)) := by
  obtain ⟨p,hpq,hp,hb⟩ := overlapPath_representative q
  obtain ⟨μ,ns,hns,hL⟩ := jointArrayLaw_subsequence
    (fun k => cascadeCompactLaw k (uniformExponent k) (uniformCellAverage p k))
  have hL' : Tendsto (fun k => cascadeCompactLaw (ns k) (uniformExponent (ns k))
      (uniformCellAverage p (ns k))) atTop (𝓝 μ) := hL
  have hgeom := cascadeCompact_limit_geometry
    (fun k => uniformCellAverage_monotone hp hb (ns k))
    (fun k => (uniformCellAverage_mem hp hb (ns k) 0).1)
    (fun k => (uniformCellAverage_mem hp hb (ns k) (ns k)).2) hL'
  have hGG : HasGhirlandaGuerra spinArray (μ : Measure JointArray) :=
    (cascadeCompact_limit_GG (fun k => uniformExponent_cascade (ns k)) hL').real_map
      (f := fun x => x.1.1) (by fun_prop)
  have hpair := cascadeCompact_limit_pairLaw hp hb hns.tendsto_atTop hL'
  obtain ⟨Q,hQ,hlog,hlim⟩ := patternFunctional_factor_law q p hpq hp hb μ hGG
    hgeom.1 hgeom.2 hpair hf hK
  exact hlim

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Ip.IsingPerceptron_VariationalFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Finiteness. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussianTransform_zero_variance (d : ℝ) (U : ℝ → ℝ) :
    gaussianTransform 0 d U = U := by
  ext x
  by_cases hd : d = 0
  · simp [gaussianTransform, hd]
  · simp [gaussianTransform, hd]

lemma magneticRecursion_zero (n : ℕ) (b : ℕ → ℝ) :
    magneticRecursion n (fun _ => 0) b = fun x => Real.log (Real.cosh x) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [magneticRecursion, ih, zero_pow (by decide : 2 ≠ 0),
      gaussianTransform_zero_variance]

lemma magneticFieldValue_zero (n : ℕ) (b : ℕ → ℝ) :
    magneticFieldValue n b (fun _ => 0) = 0 := by
  simp [magneticFieldValue, pathAmplitude, pathIncrement, magneticRecursion_zero]

 
lemma enrichedMeanPressure_field_add_le {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    enrichedMeanPressure P r n b (fun i => h i + l i) u ν φ ≤
      enrichedMeanPressure P r n b h u ν φ := by
  have he := enrichedMeanPressure_field_insert hN n b hb hh h0 hl l0 u hu ν P hm hK hφ r
    (a := 1) zero_le_one
  simp only [one_mul, Real.sqrt_one] at he
  have hc := (random_cylinder_cgf_mean_bounds (P := enrichedCylinderLaw P r n b)
    (measurable_enrichedGibbsReference n h u ν hm) (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le) 1).2
  simp only [one_pow, one_mul] at hc
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hc' : (∫ z : EnrichedCylinderData n A × (ℕ → ℝ),
      cgf (fun s => cylinderField (externalFieldCoefficients n l s) z.2)
        (enrichedGibbsReference n h u ν φ z.1) 1
        ∂(enrichedCylinderLaw P r n b).prod gaussianCoordinates) / (N : ℝ) ≤ l n / 2 :=
    (div_le_iff₀ hn).mpr (hc.trans_eq (by ring))
  rw [he]
  linarith

lemma magneticFieldValue_nonpos (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0) :
    magneticFieldValue n b h ≤ 0 := by
  let P : Measure Unit := Measure.dirac ()
  let φ : Unit → Spin 1 → ℝ := fun _ _ => 0
  have hm : Measurable φ := measurable_const
  have hφ : ∀ y x, |φ y x| ≤ (0 : ℝ) := by intros; simp [φ]
  have hu : ∀ j : Fin 1, |(0 : Fin 1 → ℝ) j| ≤ 2 := by simp
  have he := enrichedMeanPressure_field_add_le (N := 1) (by decide) n b hb
    (h := fun _ => 0) monotone_const le_rfl hh h0 0 hu (spinLaw 1) P hm le_rfl hφ 0
  simp only [zero_add] at he
  rw [enrichedMeanPressure_initial_zero (by decide) n b hb hh h0 P hm le_rfl hφ,
    enrichedMeanPressure_initial_zero (by decide) n b hb monotone_const le_rfl P hm le_rfl hφ,
    magneticFieldValue_zero] at he
  exact he

lemma fieldRecursion_nonpos (h : FieldStep) : fieldRecursion h ≤ 0 := by
  rcases h with ⟨⟨k, hk, ζ, hz, hz0, hz1⟩, v, hv0, hv⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  change Fin (n + 1) → ℝ at v
  have hζ0 : ζ 0 = 0 := by
    convert hz0 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  have hζ1 : ζ (Fin.last (n+1)) = 1 := hz1
  let w : ℕ → ℝ := fun i => v ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hw : Monotone w := by
    intro i j hij
    apply hv
    exact min_le_min_right n hij
  have hw0 : 0 ≤ w 0 := hv0 _
  have he : (⟨⟨n+1, hk, ζ, hz, hz0, hz1⟩, v, hv0, hv⟩ : FieldStep) =
      chainFieldStep n ζ hz hζ0 hζ1 w hw hw0 := by
    congr 1
    funext i
    apply congrArg v
    apply Fin.ext
    have hi : i.val < n+1 := i.isLt
    exact (min_eq_left (by omega : i.val ≤ n)).symm
  rw [he, fieldRecursion_chain]
  exact magneticFieldValue_nonpos _ _ (chainExponent_admissible hz hζ0 hζ1) hw hw0


lemma fieldRecursion_zeroFieldStep : fieldRecursion zeroFieldStep = 0 := by
  rw [zeroFieldStep, fieldRecursion_chain, magneticFieldValue_zero]

lemma stepFunction_zeroFieldStep : stepFunction zeroFieldStep = fun _ => 0 := by
  funext u
  dsimp only [stepFunction, zeroFieldStep, chainFieldStep]
  simp only [ite_self, Finset.sum_const_zero]

 
lemma isingEntropy_nonneg (q : OverlapPath) : 0 ≤ isingEntropy q := by
  have h := le_iSup (fun h : FieldStep =>
    ((fieldRecursion h + (∫ u, stepFunction h u*q.val u ∂pathMeasure)/2 : ℝ) : EReal))
      zeroFieldStep
  simpa only [isingEntropy, fieldRecursion_zeroFieldStep, stepFunction_zeroFieldStep, zero_mul,
    integral_zero, zero_div, add_zero, EReal.coe_zero] using h


lemma zeroOverlapPath_ae : (fun _ => (0 : ℝ)) =ᵐ[pathMeasure] zeroOverlapPath.val :=
  overlapPathOfMonotone_ae _ _ _

lemma isingEntropy_zero : isingEntropy zeroOverlapPath = 0 := by
  apply le_antisymm _ (isingEntropy_nonneg _)
  apply iSup_le
  intro h
  have hi : (∫ u, stepFunction h u * zeroOverlapPath.val u ∂pathMeasure) = 0 := by
    calc
      _ = ∫ _u : ℝ, (0 : ℝ) ∂pathMeasure := integral_congr_ae (by
        filter_upwards [zeroOverlapPath_ae] with u hu
        rw [← hu, mul_zero])
      _ = 0 := integral_zero _ _
  simpa only [hi, zero_div, add_zero, EReal.coe_zero] using
    EReal.coe_le_coe (fieldRecursion_nonpos h)

lemma gaussianFold_measurable_bounded (L : List (ℝ × ℝ))
    (hd : ∀ sd ∈ L, 0 ≤ sd.2) {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Measurable (L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) f) ∧
      ∀ x, |L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) f x| ≤ K := by
  induction L with
  | nil => exact ⟨hf, hK⟩
  | cons sd L ih =>
    have hi := ih (fun sd hs => hd sd (List.mem_cons_of_mem _ hs))
    exact ⟨measurable_gaussianTransform hi.1 _ _,
      gaussianTransform_abs_le hi.1 hi.2 sd.1 (hd sd (List.mem_cons_self))⟩

lemma uniformPattern_abs_bound {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) (q : OverlapPath) (n : ℕ) :
    |uniformPattern f q n| ≤ K := by
  apply (gaussianFold_measurable_bounded _ ?_ hf hK).2 0
  intro sd hs
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  simp only
  positivity

 

lemma patternFunctional_abs_bound {f : ℝ → ℝ} (hf : Continuous f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) (q : OverlapPath) :
    |patternFunctional f q| ≤ K := by
  exact le_of_tendsto (uniformPattern_tendsto q hf hK).abs
    (Eventually.of_forall (uniformPattern_abs_bound hf.measurable hK q))

 

theorem variationalValue_finite_of_continuous {α : ℝ} (hα : 0 ≤ α)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    (-(α*K) : EReal) ≤ variationalValue α f ∧
      variationalValue α f ≤ (α*K : ℝ) := by
  constructor
  · apply le_iInf
    intro q
    have hv : -(α*K) ≤ α*patternFunctional f q := by
      have hi := mul_le_mul_of_nonneg_left (abs_le.mp (patternFunctional_abs_bound hf hK q)).1 hα
      nlinarith
    calc
      (-(α*K) : EReal) ≤ (α*patternFunctional f q : ℝ) := by exact_mod_cast hv
      _ ≤ (α*patternFunctional f q : ℝ)+isingEntropy q := le_add_of_nonneg_right (isingEntropy_nonneg q)
  · calc
      variationalValue α f ≤ (α*patternFunctional f zeroOverlapPath : ℝ) + isingEntropy zeroOverlapPath :=
        iInf_le _ zeroOverlapPath
      _ = (α*patternFunctional f zeroOverlapPath : ℝ) := by rw [isingEntropy_zero, add_zero]
      _ ≤ (α*K : ℝ) := by
        exact_mod_cast mul_le_mul_of_nonneg_left (abs_le.mp (patternFunctional_abs_bound hf hK _)).2 hα

 

theorem variationalValue_real_of_continuous_oai {α : ℝ} (hα : 0 ≤ α)
    {f : ℝ → ℝ} (hf : Continuous f) (hbounded : ∃ K : ℝ, ∀ x, |f x| ≤ K) :
    ∃ p : ℝ, variationalValue α f = (p : EReal) := by
  obtain ⟨K, hK⟩ := hbounded
  have hb := variationalValue_finite_of_continuous hα hf hK
  have hl : ⊥ < variationalValue α f := lt_of_lt_of_le (EReal.bot_lt_coe _) hb.1
  have hu : variationalValue α f < ⊤ := lt_of_le_of_lt hb.2 (EReal.coe_lt_top _)
  exact ⟨(variationalValue α f).toReal, (EReal.coe_toReal hu.ne hl.ne').symm⟩

end IsingPerceptron

end

end OAI
end

theorem solution : type_of% @OAI.IsingPerceptron.variationalValue_real_of_continuous_oai := @OAI.IsingPerceptron.variationalValue_real_of_continuous_oai
