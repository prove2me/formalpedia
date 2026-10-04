-- Prove2me | solution 1 for MDPFinance.POMDP.lemma_5_2_2
-- status  : ACCEPTED   (disprove)
-- author  : @Gabewhigham
-- created : 2026-10-02T15:27:46.719886+00:00
-- url     : https://prove2.me/submissions/a15afe8a-801e-4340-9cd7-ec6c50c00919

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model
import Definitions.Def_MDPFinance_POMDP_FilterData

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Cex_lemma_5_2_2

open MDPFinance.POMDP

/-- Prior weights `ρ_y = 2^{-(y+1)}`. -/
noncomputable def w (y : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ (y + 1)

lemma w_ne_top (y : ℕ) : w y ≠ ∞ := by
  unfold w; exact ENNReal.pow_ne_top (by simp)

lemma w_ne_zero (y : ℕ) : w y ≠ 0 := by
  unfold w; exact pow_ne_zero _ (by simp)

lemma w_toReal (y : ℕ) : (w y).toReal = (1 / 2 : ℝ) ^ (y + 1) := by
  unfold w; simp [ENNReal.toReal_pow, ENNReal.toReal_inv]

/-- The prior `Q_0 = Σ_y 2^{-(y+1)} δ_y`. -/
noncomputable def Q0 : Measure ℕ := Measure.sum fun y => w y • Measure.dirac y

lemma Q0_singleton (y : ℕ) : Q0 {y} = w y := by
  unfold Q0
  rw [Measure.sum_apply _ (measurableSet_singleton y)]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton y),
    smul_eq_mul]
  rw [tsum_eq_single y]
  · simp
  · intro b hb
    simp [Set.indicator, hb]

lemma Q0_univ : Q0 Set.univ = 1 := by
  unfold Q0
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, w]
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

instance : IsProbabilityMeasure Q0 := ⟨Q0_univ⟩

/-- The transition: from hidden state `y`, the hidden state stays `y` and the observation is
`y` or `y + 1` with probability `1/2` each. -/
noncomputable def Qfun (p : (ℕ × ℕ) × Unit) : Measure (ℕ × ℕ) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (p.1.2, p.1.2) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (p.1.2 + 1, p.1.2)

noncomputable def Qk : Kernel ((ℕ × ℕ) × Unit) (ℕ × ℕ) := Kernel.ofFunOfCountable Qfun

lemma Qk_apply (p : (ℕ × ℕ) × Unit) : Qk p = Qfun p := rfl

instance : IsMarkovKernel Qk := by
  constructor
  intro p
  constructor
  rw [Qk_apply]
  simp only [Qfun, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- The transition density with respect to counting measure. -/
noncomputable def qd (_x y : ℕ) (_a : Unit) (x' y' : ℕ) : ℝ :=
  if y' = y ∧ (x' = y ∨ x' = y + 1) then 1 / 2 else 0

/-- The support of the posterior after observing `x'`. -/
def S (x' : ℕ) : Finset ℕ := {x', x' - 1}

lemma mem_S (x' y' : ℕ) : y' ∈ S x' ↔ (x' = y' ∨ x' = y' + 1) := by
  simp only [S, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- The Bayes operator: conditioning on the support `S x'`. -/
noncomputable def PhiM (ρ : Measure ℕ) (x' : ℕ) : Measure ℕ :=
  (ρ (S x' : Set ℕ))⁻¹ • ρ.restrict (S x' : Set ℕ) +
    (if ρ (S x' : Set ℕ) = 0 then (1 : ℝ≥0∞) else 0) • Measure.dirac 0

lemma PhiM_prob (ρ : ProbabilityMeasure ℕ) (x' : ℕ) : IsProbabilityMeasure (PhiM ρ x') := by
  constructor
  unfold PhiM
  by_cases h : (ρ : Measure ℕ) (S x' : Set ℕ) = 0
  · have : (ρ : Measure ℕ).restrict (S x' : Set ℕ) = 0 := Measure.restrict_eq_zero.mpr h
    simp [h, this]
  · simp only [h, if_false, zero_smul, add_zero, Measure.smul_apply, Measure.restrict_apply_univ,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel h (measure_ne_top _ _)

noncomputable def Phi (_x : ℕ) (ρ : ProbabilityMeasure ℕ) (_a : Unit) (x' : ℕ) :
    ProbabilityMeasure ℕ :=
  ⟨PhiM ρ x', PhiM_prob ρ x'⟩

lemma measurable_PhiM (x' : ℕ) : Measurable fun ρ : ProbabilityMeasure ℕ => PhiM ρ x' := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hS : MeasurableSet (S x' : Set ℕ) := (S x').measurableSet
  have h1 : Measurable fun ρ : ProbabilityMeasure ℕ => (ρ : Measure ℕ) (S x' : Set ℕ) :=
    (Measure.measurable_coe hS).comp measurable_subtype_coe
  have h2 : Measurable fun ρ : ProbabilityMeasure ℕ => (ρ : Measure ℕ) (s ∩ (S x' : Set ℕ)) :=
    (Measure.measurable_coe (hs.inter hS)).comp measurable_subtype_coe
  simp only [PhiM, Measure.add_apply, Measure.smul_apply, Measure.restrict_apply hs,
    smul_eq_mul]
  refine (h1.inv.mul h2).add ?_
  refine Measurable.mul_const ?_ _
  exact Measurable.ite (measurableSet_eq_fun h1 measurable_const) measurable_const
    measurable_const

lemma lintegral_qd (ρ : Measure ℕ) (x' y' : ℕ) :
    ∫⁻ y, ENNReal.ofReal (qd 0 y () x' y') ∂ρ =
      (S x' : Set ℕ).indicator (fun y' => (2 : ℝ≥0∞)⁻¹ * ρ {y'}) y' := by
  have : (fun y => ENNReal.ofReal (qd 0 y () x' y')) =
      ({y'} : Set ℕ).indicator (fun _ =>
        (S x' : Set ℕ).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) y') := by
    funext y
    simp only [qd, Set.indicator, Set.mem_singleton_iff, Finset.mem_coe, mem_S]
    by_cases hy : y = y'
    · subst hy; by_cases h : x' = y ∨ x' = y + 1 <;> simp [h, ENNReal.ofReal_div_of_pos]
    · have : ¬ y' = y := fun h => hy h.symm
      simp [hy, this]
  rw [this, lintegral_indicator (measurableSet_singleton _), setLIntegral_const]
  simp only [Set.indicator]
  split_ifs <;> simp [mul_comm]


lemma lintegral_qd' (ρ : Measure ℕ) (x y0 : ℕ) (a : Unit) (x' y' : ℕ) :
    ∫⁻ y, ENNReal.ofReal (qd x y a x' y') ∂ρ =
      (S x' : Set ℕ).indicator (fun y' => (2 : ℝ≥0∞)⁻¹ * ρ {y'}) y' :=
  lintegral_qd ρ x' y'

lemma num_eq (ρ : Measure ℕ) (x : ℕ) (a : Unit) (x' : ℕ) (C : Set ℕ) (hC : MeasurableSet C) :
    ∫⁻ y' in C, (∫⁻ y, ENNReal.ofReal (qd x y a x' y') ∂ρ) ∂Measure.count =
      (2 : ℝ≥0∞)⁻¹ * ρ (C ∩ (S x' : Set ℕ)) := by
  simp_rw [lintegral_qd' ρ x 0 a x']
  rw [← lintegral_indicator hC, lintegral_count]
  have : (fun y' => C.indicator (fun y' => (S x' : Set ℕ).indicator
      (fun y' => (2 : ℝ≥0∞)⁻¹ * ρ {y'}) y') y') =
      fun y' => (2 : ℝ≥0∞)⁻¹ * (C ∩ (S x' : Set ℕ)).indicator (fun y' => ρ {y'}) y' := by
    funext y'
    simp only [Set.indicator, Set.mem_inter_iff]
    split_ifs <;> simp_all
  rw [this, ENNReal.tsum_mul_left, Measure.tsum_indicator_apply_singleton _ _
    (hC.inter (S x').measurableSet)]

/-- The bad test function. -/
noncomputable def vv (x' y' : ℕ) : ℝ :=
  if x' = y' then (2 : ℝ) ^ (y' + 2) else if x' = y' + 1 then -(2 : ℝ) ^ (y' + 2) else 0

lemma vv_bound (x' y' : ℕ) : |vv x' y'| ≤ (2 : ℝ) ^ (x' + 2) := by
  unfold vv
  split_ifs with h1 h2
  · subst h1; simp [abs_of_pos]
  · subst h2
    rw [abs_neg, abs_of_pos (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · simp only [abs_zero]; positivity

noncomputable def M : PartiallyObservableMDM ℕ ℕ Unit where
  D := Set.univ
  hD_meas := MeasurableSet.univ
  hD_graph := ⟨fun _ => (), measurable_const, fun _ => trivial⟩
  Q := Qk
  isMarkovQ := inferInstance
  Q0 := Q0
  isProbQ0 := inferInstance
  r := fun _ => 0
  hr_meas := measurable_const
  g := fun _ => 0
  hg_meas := measurable_const
  β := 1
  hβ0 := one_pos
  hβ1 := le_rfl

lemma Q_density (x y : ℕ) (a : Unit) : M.Q ((x, y), a) =
    (Measure.count.prod Measure.count).withDensity fun p => ENNReal.ofReal (qd x y a p.1 p.2) := by
  apply Measure.ext_of_singleton
  rintro ⟨x', y'⟩
  have hp : (Measure.count.prod Measure.count : Measure (ℕ × ℕ)) {(x', y')} = 1 := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod, Measure.count_singleton,
      Measure.count_singleton, mul_one]
  rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton, hp, mul_one]
  show Qfun ((x, y), a) {(x', y')} = _
  simp only [Qfun, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator, Set.mem_singleton_iff,
    Prod.mk.injEq, qd, Pi.one_apply]
  by_cases h1 : y' = y
  · subst h1
    by_cases h2 : x' = y'
    · subst h2; simp [ENNReal.ofReal_div_of_pos]
    · by_cases h3 : x' = y' + 1
      · subst h3; simp [ENNReal.ofReal_div_of_pos]
      · simp [h2, h3, Ne.symm h2, Ne.symm h3]
  · simp [h1, Ne.symm h1]

noncomputable def Fd : FilterData M where
  lam := Measure.count
  nu := Measure.count
  hlam_sigmaFinite := inferInstance
  hnu_sigmaFinite := inferInstance
  q := qd
  hq_meas := measurable_of_countable _
  hq_nonneg := by intro x y a x' y'; unfold qd; split_ifs <;> norm_num
  hQ_density := Q_density
  Phi := Phi
  hPhi_meas := by
    have : (fun p : (ℕ × ProbabilityMeasure ℕ) × Unit × ℕ => Phi p.1.1 p.1.2 p.2.1 p.2.2) =
        (fun q : ProbabilityMeasure ℕ × ℕ => Phi 0 q.1 () q.2) ∘
          (fun p : (ℕ × ProbabilityMeasure ℕ) × Unit × ℕ => (p.1.2, p.2.2)) := rfl
    rw [this]
    refine Measurable.comp ?_ (measurable_fst.snd.prodMk measurable_snd.snd)
    apply measurable_from_prod_countable_left
    intro x'
    exact (measurable_PhiM x').subtype_mk
  hPhi := by
    intro x ρ a x' hpos _ C hC
    have hN := num_eq (ρ : Measure ℕ) x a x' Set.univ MeasurableSet.univ
    rw [Measure.restrict_univ, Set.univ_inter] at hN
    rw [num_eq (ρ : Measure ℕ) x a x' C hC, hN]
    rw [hN] at hpos
    have hS : (ρ : Measure ℕ) (S x' : Set ℕ) ≠ 0 := by
      intro h; rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
    show PhiM ρ x' C = _
    simp only [PhiM, hS, if_false, zero_smul, add_zero, Measure.smul_apply, Measure.restrict_apply hC,
      smul_eq_mul]
    rw [ENNReal.mul_div_mul_left _ _ (by simp) (by simp), div_eq_mul_inv, mul_comm]


lemma integral_Qfun (f : ℕ × ℕ → ℝ) (x y : ℕ) (a : Unit) :
    ∫ p, f p ∂(Qfun ((x, y), a)) = (1 / 2 : ℝ) * f (y, y) + (1 / 2 : ℝ) * f (y + 1, y) := by
  have hi : ∀ p : ℕ × ℕ, Integrable f ((2 : ℝ≥0∞)⁻¹ • Measure.dirac p) := fun p =>
    (integrable_dirac (by simp)).smul_measure (by simp)
  simp only [Qfun]
  rw [integral_add_measure (hi _) (hi _), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp [ENNReal.toReal_inv]

lemma integrable_Qfun (f : ℕ × ℕ → ℝ) (x y : ℕ) (a : Unit) : Integrable f (Qfun ((x, y), a)) := by
  have hi : ∀ p : ℕ × ℕ, Integrable f ((2 : ℝ≥0∞)⁻¹ • Measure.dirac p) := fun p =>
    (integrable_dirac (by simp)).smul_measure (by simp)
  exact (hi _).add_measure (hi _)

lemma integral_map_Qfun (F : ℕ → ℝ) (x y : ℕ) (a : Unit) :
    ∫ x', F x' ∂((Qfun ((x, y), a)).map Prod.fst) = (1 / 2 : ℝ) * F y + (1 / 2 : ℝ) * F (y + 1) := by
  rw [integral_map measurable_fst.aemeasurable
    (measurable_of_countable F).aestronglyMeasurable, integral_Qfun]

lemma Q0_real (y : ℕ) : Q0.real {y} = (1 / 2 : ℝ) ^ (y + 1) := by
  rw [measureReal_def, Q0_singleton, w_toReal]

lemma Q0_S_ne_zero (x' : ℕ) : Q0 (S x' : Set ℕ) ≠ 0 := by
  intro h
  have : Q0 {x'} ≤ Q0 (S x' : Set ℕ) :=
    measure_mono (by intro y hy; simp only [Set.mem_singleton_iff] at hy; subst hy; simp [S])
  rw [h, Q0_singleton] at this
  exact w_ne_zero x' (le_antisymm this bot_le)

lemma F_eq (x : ℕ) (a : Unit) (x' : ℕ) :
    ∫ y', vv x' y' ∂(Phi x ⟨Q0, inferInstance⟩ a x').toMeasure = if x' = 0 then 4 else 0 := by
  show ∫ y', vv x' y' ∂(PhiM Q0 x') = _
  simp only [PhiM, Q0_S_ne_zero x', if_false, zero_smul, add_zero]
  rw [integral_smul_measure]
  have hint : IntegrableOn (vv x') (S x' : Set ℕ) Q0 :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable ((2 : ℝ) ^ (x' + 2))
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact vv_bound x' y)
  rw [setIntegral_finset _ hint]
  rcases x' with _ | k
  · have hS0 : S 0 = {0} := by decide
    simp only [hS0, Finset.sum_singleton, Q0_real, smul_eq_mul, if_true]
    have : Q0 ((({0} : Finset ℕ)) : Set ℕ) = w 0 := by
      rw [Finset.coe_singleton, Q0_singleton]
    rw [this]
    simp [vv, w, ENNReal.toReal_inv]
    norm_num
  · have hSk : S (k + 1) = {k + 1, k} := by simp [S]
    rw [hSk, Finset.sum_pair (by omega)]
    simp only [Q0_real, smul_eq_mul, vv, if_true, show k + 1 ≠ 0 by omega, if_false,
      show k + 1 ≠ k by omega, ↓reduceIte]
    refine mul_eq_zero_of_right _ ?_
    ring

end Cex_lemma_5_2_2

open MDPFinance.POMDP Cex_lemma_5_2_2 in
theorem solution : ¬ (∀ {EX EY A : Type} [MeasurableSpace EX] [MeasurableSpace EY]
    [MeasurableSpace A] (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M) (n : ℕ)
    (xs : ℕ → EX) (as : ℕ → A) (han : as n ∈ M.Dx (xs n))
    (v : (ℕ → EX) → (ℕ → A) → EX → EY → ℝ)
    (hv_meas : Measurable fun p : (ℕ → EX) × (ℕ → A) × EX × EY => v p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hv_int0 : ∀ yn, Integrable (fun p : EX × EY => v xs as p.1 p.2) (M.Q ((xs n, yn), as n)))
    (hv_int1 : Integrable
      (fun yn => ∫ p : EX × EY, v xs as p.1 p.2 ∂(M.Q ((xs n, yn), as n)))
      (Fd.mu M n xs as).toMeasure)
    (hv_int2a : ∀ x', Integrable (fun y' => v xs as x' y')
      (Fd.Phi (xs n) (Fd.mu M n xs as) (as n) x').toMeasure)
    (hv_int2b : ∀ yn, Integrable
      (fun x' : EX => ∫ y', v xs as x' y' ∂(Fd.Phi (xs n) (Fd.mu M n xs as) (as n) x').toMeasure)
      ((M.Q ((xs n, yn), as n)).map Prod.fst))
    (hv_int2 : Integrable
      (fun yn => ∫ x' : EX, ∫ y', v xs as x' y'
          ∂(Fd.Phi (xs n) (Fd.mu M n xs as) (as n) x').toMeasure
        ∂(M.Q ((xs n, yn), as n)).map Prod.fst)
      (Fd.mu M n xs as).toMeasure),
    ∫ yn, (∫ p : EX × EY, v xs as p.1 p.2 ∂(M.Q ((xs n, yn), as n))) ∂(Fd.mu M n xs as).toMeasure =
      ∫ yn, (∫ x' : EX, ∫ y', v xs as x' y'
          ∂(Fd.Phi (xs n) (Fd.mu M n xs as) (as n) x').toMeasure
        ∂(M.Q ((xs n, yn), as n)).map Prod.fst) ∂(Fd.mu M n xs as).toMeasure) := by
  intro h
  have hG : ∀ yn : ℕ, ∫ p : ℕ × ℕ, vv p.1 p.2 ∂(M.Q ((0, yn), ())) = 0 := by
    intro yn
    show ∫ p : ℕ × ℕ, vv p.1 p.2 ∂(Qfun ((0, yn), ())) = 0
    rw [integral_Qfun]
    simp only [vv, if_true, show yn + 1 ≠ yn by omega, if_false]
    ring
  have hH : ∀ yn : ℕ, ∫ x' : ℕ, ∫ y', vv x' y' ∂(Fd.Phi 0 ⟨Q0, inferInstance⟩ () x').toMeasure
      ∂(M.Q ((0, yn), ())).map Prod.fst = ({0} : Set ℕ).indicator (fun _ => (2 : ℝ)) yn := by
    intro yn
    show ∫ x' : ℕ, ∫ y', vv x' y' ∂(Phi 0 ⟨Q0, inferInstance⟩ () x').toMeasure
      ∂(Qfun ((0, yn), ())).map Prod.fst = _
    rw [integral_map_Qfun]
    simp only [F_eq, show yn + 1 ≠ 0 by omega, if_false, Set.indicator, Set.mem_singleton_iff]
    split_ifs <;> norm_num
  have hbd : ∀ (μ : Measure ℕ) [IsFiniteMeasure μ] (f : ℕ → ℝ) (C : ℝ), (∀ x, |f x| ≤ C) →
      Integrable f μ := fun μ _ f C hC =>
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC y)
  have key := @h ℕ ℕ Unit _ _ _ M Fd 0 (fun _ => 0) (fun _ => ()) trivial
    (fun _ _ x' y' => vv x' y')
    ((measurable_of_countable (fun q : ℕ × ℕ => vv q.1 q.2)).comp measurable_snd.snd)
    (fun yn => integrable_Qfun _ 0 yn ())
    (by
      show Integrable (fun yn : ℕ => ∫ p : ℕ × ℕ, vv p.1 p.2 ∂(M.Q ((0, yn), ()))) Q0
      simp only [hG]; exact integrable_zero _ _ _)
    (fun x' => hbd _ _ ((2 : ℝ) ^ (x' + 2)) (vv_bound x'))
    (fun yn => by
      haveI := M.isMarkovQ
      haveI : IsFiniteMeasure ((M.Q ((0, yn), ())).map Prod.fst) := inferInstance
      refine hbd _ _ 4 fun x' => ?_
      show |∫ y', vv x' y' ∂(Phi 0 ⟨Q0, inferInstance⟩ () x').toMeasure| ≤ 4
      rw [F_eq]; split_ifs <;> norm_num)
    (by
      show Integrable (fun yn : ℕ => ∫ x' : ℕ, ∫ y', vv x' y'
        ∂(Fd.Phi 0 ⟨Q0, inferInstance⟩ () x').toMeasure ∂(M.Q ((0, yn), ())).map Prod.fst) Q0
      simp only [hH]
      refine hbd _ _ 2 fun y => ?_
      simp only [Set.indicator]; split_ifs <;> norm_num)
  change ∫ yn : ℕ, (∫ p : ℕ × ℕ, vv p.1 p.2 ∂(M.Q ((0, yn), ()))) ∂Q0 =
    ∫ yn : ℕ, (∫ x' : ℕ, ∫ y', vv x' y' ∂(Fd.Phi 0 ⟨Q0, inferInstance⟩ () x').toMeasure
      ∂(M.Q ((0, yn), ())).map Prod.fst) ∂Q0 at key
  simp only [hG, hH, integral_zero] at key
  rw [integral_indicator_const _ (measurableSet_singleton 0), Q0_real] at key
  norm_num at key
