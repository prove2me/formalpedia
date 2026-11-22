-- Prove2me | solution 1 for LCAGroup.euclidean_schwartz_withSeminorms_eLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:21:41.20519+00:00
-- url     : https://prove2.me/submissions/73f85489-5204-4cfa-bcd1-33a9c72c1ed1

import Mathlib

open MeasureTheory
open scoped SchwartzMap ENNReal

set_option autoImplicit false

namespace Sol_LCAGroup_euclidean_schwartz_withSeminorms_eLpNorm

open LineDeriv SchwartzMap Function Set

abbrev Idx (m : ℕ) := (Fin m → ℕ) × (Σ n : ℕ, Fin n → Fin m)

noncomputable def mono {m : ℕ} (α : Fin m → ℕ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∏ i, x i ^ α i

noncomputable def dirs {m n : ℕ} (σ : Fin n → Fin m) : Fin n → EuclideanSpace ℝ (Fin m) :=
  fun j => EuclideanSpace.single (σ j) (1 : ℝ)

theorem mono_hasTemperateGrowth {m : ℕ} (α : Fin m → ℕ) :
    (fun x : EuclideanSpace ℝ (Fin m) => ((mono α x : ℝ) : ℂ)).HasTemperateGrowth := by
  unfold mono
  push_cast
  generalize Finset.univ (α := Fin m) = s
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact Function.HasTemperateGrowth.const _
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    have h := (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).hasTemperateGrowth
    exact Function.HasTemperateGrowth.fun_mul (Function.HasTemperateGrowth.fun_pow h (α i)) ih

noncomputable def T {m : ℕ} (j : Idx m) :
    𝓢(EuclideanSpace ℝ (Fin m), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin m), ℂ) :=
  smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin m) => ((mono j.1 x : ℝ) : ℂ)) ∘L
    iteratedLineDerivOpCLM ℂ 𝓢(EuclideanSpace ℝ (Fin m), ℂ) (dirs j.2.2)

theorem T_apply {m : ℕ} (j : Idx m) (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ))
    (x : EuclideanSpace ℝ (Fin m)) :
    T j f x = mono j.1 x • iteratedFDeriv ℝ j.2.1 (⇑f) x (dirs j.2.2) := by
  simp only [T, ContinuousLinearMap.comp_apply, iteratedLineDerivOpCLM_apply,
    smulLeftCLM_apply_apply (mono_hasTemperateGrowth j.1), iteratedLineDerivOp_eq_iteratedFDeriv]
  rw [Complex.coe_smul]

theorem dirs_cons {m n : ℕ} (i : Fin m) (σ : Fin n → Fin m) :
    (Fin.cons (EuclideanSpace.single i (1 : ℝ)) (dirs σ) : Fin (n + 1) → EuclideanSpace ℝ (Fin m)) =
      dirs (Fin.cons i σ) := by
  funext l
  refine Fin.cases ?_ (fun l => ?_) l
  · simp [dirs]
  · simp [dirs]

theorem hasDerivAt_path {m : ℕ} (w : Fin m → ℝ) (i : Fin m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (WithLp.toLp 2 (update w i s) : EuclideanSpace ℝ (Fin m)))
      (EuclideanSpace.single i 1) t := by
  let path : ℝ → EuclideanSpace ℝ (Fin m) := fun s => WithLp.toLp 2 (update w i s)
  have heq : path = fun s : ℝ => path 0 + s • EuclideanSpace.single i 1 := by
    funext s
    ext j
    by_cases hj : j = i
    · subst j
      simp [path]
    · simp [path, EuclideanSpace.single, hj]
  change HasDerivAt path _ t
  rw [heq]
  simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add (path 0)

theorem mono_update {m : ℕ} (β : Fin m → ℕ) (w : Fin m → ℝ) (i : Fin m) (t : ℝ) :
    mono β (WithLp.toLp 2 (update w i t) : EuclideanSpace ℝ (Fin m)) =
      t ^ β i * ∏ l ∈ Finset.univ.erase i, w l ^ β l := by
  classical
  unfold mono
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun l hl => ?_
    rw [PiLp.toLp_apply, update_of_ne (Finset.ne_of_mem_erase hl)]

theorem hasDerivAt_mono {m : ℕ} (α : Fin m → ℕ) (w : Fin m → ℝ) (i : Fin m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => mono α (WithLp.toLp 2 (update w i s) : EuclideanSpace ℝ (Fin m)))
      ((α i : ℝ) * mono (update α i (α i - 1)) (WithLp.toLp 2 (update w i t))) t := by
  classical
  have h1 : (fun s : ℝ => mono α (WithLp.toLp 2 (update w i s) : EuclideanSpace ℝ (Fin m))) =
      fun s => s ^ α i * ∏ l ∈ Finset.univ.erase i, w l ^ α l := by
    funext s; exact mono_update α w i s
  have h2 : mono (update α i (α i - 1)) (WithLp.toLp 2 (update w i t) : EuclideanSpace ℝ (Fin m))
      = t ^ (α i - 1) * ∏ l ∈ Finset.univ.erase i, w l ^ α l := by
    rw [mono_update]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun l hl => ?_
      rw [update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [h1, h2, ← mul_assoc]
  exact (hasDerivAt_pow (α i) t).mul_const _

theorem hasDerivAt_iter {m n : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (σ : Fin n → Fin m)
    (w : Fin m → ℝ) (i : Fin m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n (⇑f)
        (WithLp.toLp 2 (update w i s) : EuclideanSpace ℝ (Fin m)) (dirs σ))
      (iteratedFDeriv ℝ (n + 1) (⇑f) (WithLp.toLp 2 (update w i t)) (dirs (Fin.cons i σ))) t := by
  let F : 𝓢(EuclideanSpace ℝ (Fin m), ℂ) := ∂^{dirs σ} f
  have hF : (fun s : ℝ => iteratedFDeriv ℝ n (⇑f)
        (WithLp.toLp 2 (update w i s) : EuclideanSpace ℝ (Fin m)) (dirs σ)) =
      fun s => F (WithLp.toLp 2 (update w i s)) := by
    funext s
    simp only [F, iteratedLineDerivOp_eq_iteratedFDeriv]
  rw [hF]
  have h := (F.hasFDerivAt (WithLp.toLp 2 (update w i t))).comp_hasDerivAt t (hasDerivAt_path w i t)
  refine h.congr_deriv ?_
  rw [← lineDerivOp_apply_eq_fderiv, ← iteratedLineDerivOp_eq_iteratedFDeriv,
    iteratedLineDerivOp_succ_left]
  simp only [F, ← dirs_cons, Fin.cons_zero, Fin.tail_cons]

/-- The index obtained by differentiating the monomial in direction `i`. -/
def idxMono {m : ℕ} (j : Idx m) (i : Fin m) : Idx m := (update j.1 i (j.1 i - 1), j.2)

/-- The index obtained by differentiating the derivative factor in direction `i`. -/
def idxDer {m : ℕ} (j : Idx m) (i : Fin m) : Idx m := (j.1, ⟨j.2.1 + 1, Fin.cons i j.2.2⟩)

theorem hasDerivAt_T {m : ℕ} (j : Idx m) (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ))
    (w : Fin m → ℝ) (i : Fin m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => T j f (WithLp.toLp 2 (update w i s)))
      (T (idxDer j i) f (WithLp.toLp 2 (update w i t)) +
        (j.1 i : ℝ) • T (idxMono j i) f (WithLp.toLp 2 (update w i t))) t := by
  obtain ⟨α, n, σ⟩ := j
  simp only [T_apply, idxDer, idxMono]
  have h := (hasDerivAt_mono α w i t).smul (hasDerivAt_iter f σ w i t)
  refine h.congr_deriv ?_
  rw [smul_smul]

/-- The fundamental theorem of calculus, averaged over a unit interval. -/
theorem enorm_le_unitInterval {U V : ℝ → ℂ} (h : ∀ t, HasDerivAt U (V t) t)
    (hV : Continuous V) (a : ℝ) :
    ‖U a‖ₑ ≤ (∫⁻ t in Icc a (a+1), ‖U t‖ₑ) + ∫⁻ t in Icc a (a+1), ‖V t‖ₑ := by
  let μ := (volume : Measure ℝ).restrict (Icc a (a+1))
  have hvol : μ univ = 1 := by simp [μ, Real.volume_Icc]
  have : IsProbabilityMeasure μ := ⟨hvol⟩
  have hU : Continuous U := continuous_iff_continuousAt.mpr fun t ↦ (h t).continuousAt
  have hUi : Integrable U μ := hU.continuousOn.integrableOn_Icc
  have hVi : Integrable V μ := hV.continuousOn.integrableOn_Icc
  have hpoint (t : ℝ) (ht : t ∈ Icc a (a+1)) : ‖U a‖ ≤ ‖U t‖ + ∫ v, ‖V v‖ ∂μ := by
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := t)
      (fun v _ ↦ h v) (hV.intervalIntegrable _ _)
    have hd : ‖U t - U a‖ ≤ ∫ v, ‖V v‖ ∂μ := calc
      _ ≤ ∫ v in a..t, ‖V v‖ := heq ▸ intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ _ := by
        rw [intervalIntegral.integral_of_le ht.1]
        exact setIntegral_mono_set hVi.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
          (Filter.Eventually.of_forall (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2)))
    exact (norm_le_insert' (U a) (U t)).trans (by rw [norm_sub_rev]; linarith)
  have hreal := integral_mono_ae (integrable_const (μ := μ) ‖U a‖)
    (hUi.norm.add (integrable_const (∫ v, ‖V v‖ ∂μ)))
    ((ae_restrict_mem measurableSet_Icc).mono hpoint)
  simp only [Pi.add_apply] at hreal
  rw [integral_add hUi.norm (integrable_const _)] at hreal
  simp only [integral_const, probReal_univ, one_smul] at hreal
  rw [← ofReal_integral_norm_eq_lintegral_enorm hUi, ← ofReal_integral_norm_eq_lintegral_enorm hVi,
    ← ENNReal.ofReal_add (integral_nonneg fun _ ↦ norm_nonneg _)
      (integral_nonneg fun _ ↦ norm_nonneg _),
    ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The finite box of indices with monomial exponents `≤ A` and derivative order `≤ N`. -/
def box {m : ℕ} (A N : ℕ) : Finset (Idx m) :=
  (Fintype.piFinset fun _ => Finset.range (A + 1)) ×ˢ
    ((Finset.range (N + 1)).sigma fun _ => Finset.univ)

theorem mem_box {m : ℕ} {A N : ℕ} {j : Idx m} : j ∈ box A N ↔ (∀ i, j.1 i ≤ A) ∧ j.2.1 ≤ N := by
  simp [box, Finset.mem_sigma]

theorem box_mono {m : ℕ} {A N N' : ℕ} (h : N ≤ N') {j : Idx m} (hj : j ∈ box A N) :
    j ∈ box A N' := by
  rw [mem_box] at hj ⊢
  exact ⟨hj.1, hj.2.trans h⟩

theorem idxMono_mem {m : ℕ} {A N : ℕ} {j : Idx m} (hj : j ∈ box A N) (i : Fin m) :
    idxMono j i ∈ box A (N + 1) := by
  rw [mem_box] at hj ⊢
  refine ⟨fun l => ?_, by simp [idxMono]; omega⟩
  by_cases hl : l = i
  · subst hl; simp [idxMono]; have := hj.1 l; omega
  · simp [idxMono, update_of_ne hl, hj.1 l]

theorem idxDer_mem {m : ℕ} {A N : ℕ} {j : Idx m} (hj : j ∈ box A N) (i : Fin m) :
    idxDer j i ∈ box A (N + 1) := by
  rw [mem_box] at hj ⊢
  exact ⟨hj.1, by simp [idxDer]; omega⟩

/-- Sum of the pointwise moduli over the box, in cartesian coordinates. -/
noncomputable def W {m : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (A N : ℕ) (w : Fin m → ℝ) :
    ℝ≥0∞ :=
  ∑ j ∈ box A N, ‖T j f (WithLp.toLp 2 w)‖ₑ

theorem measurable_W {m : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (A N : ℕ) :
    Measurable (W f A N) := by
  unfold W
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((T j f).continuous.comp (PiLp.continuous_toLp 2 _)).enorm.measurable

theorem le_W {m : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) {A N : ℕ} {j : Idx m}
    (hj : j ∈ box A N) (w : Fin m → ℝ) : ‖T j f (WithLp.toLp 2 w)‖ₑ ≤ W f A N w :=
  Finset.single_le_sum (f := fun j => ‖T j f (WithLp.toLp 2 w)‖ₑ) (fun _ _ => zero_le) hj

/-- One-variable step: the box sum at a point is controlled by the integral of the next box
sum over a unit segment in one coordinate direction. -/
theorem W_le_slice {m : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (A N : ℕ) (i : Fin m)
    (w : Fin m → ℝ) :
    W f A N w ≤ (((box (m := m) A N).card : ℝ≥0∞) * (A + 2)) *
      ∫⁻ t in Icc (w i) (w i + 1), W f A (N + 1) (update w i t) := by
  have hterm : ∀ j ∈ box (m := m) A N, ‖T j f (WithLp.toLp 2 w)‖ₑ ≤
      (A + 2) * ∫⁻ t in Icc (w i) (w i + 1), W f A (N + 1) (update w i t) := by
    intro j hj
    let U : ℝ → ℂ := fun s => T j f (WithLp.toLp 2 (update w i s))
    let V : ℝ → ℂ := fun s => T (idxDer j i) f (WithLp.toLp 2 (update w i s)) +
        (j.1 i : ℝ) • T (idxMono j i) f (WithLp.toLp 2 (update w i s))
    have hpath : Continuous fun s : ℝ => (WithLp.toLp 2 (update w i s) : EuclideanSpace ℝ (Fin m)) :=
      continuous_iff_continuousAt.mpr fun t => (hasDerivAt_path w i t).continuousAt
    have hV : Continuous V :=
      ((T _ f).continuous.comp hpath).add
        (((T (idxMono j i) f).continuous.comp hpath).const_smul (j.1 i : ℝ))
    have h1 := enorm_le_unitInterval (U := U) (V := V) (fun t => hasDerivAt_T j f w i t) hV (w i)
    have hUa : U (w i) = T j f (WithLp.toLp 2 w) := by simp [U]
    rw [hUa] at h1
    refine h1.trans ?_
    have hA : (j.1 i : ℝ≥0∞) ≤ A := by
      have := (mem_box.mp hj).1 i
      exact_mod_cast this
    have hU' : ∀ s, ‖U s‖ₑ ≤ W f A (N + 1) (update w i s) := fun s =>
      le_W f (box_mono (Nat.le_succ N) hj) _
    have hV' : ∀ s, ‖V s‖ₑ ≤ (A + 1) * W f A (N + 1) (update w i s) := by
      intro s
      refine (enorm_add_le _ _).trans ?_
      rw [enorm_smul, Real.enorm_natCast, add_mul, one_mul, add_comm (_ * _)]
      exact add_le_add (le_W f (idxDer_mem hj i) _) (mul_le_mul' hA (le_W f (idxMono_mem hj i) _))
    calc (∫⁻ t in Icc (w i) (w i + 1), ‖U t‖ₑ) + ∫⁻ t in Icc (w i) (w i + 1), ‖V t‖ₑ
        ≤ (∫⁻ t in Icc (w i) (w i + 1), W f A (N + 1) (update w i t)) +
          ∫⁻ t in Icc (w i) (w i + 1), (A + 1) * W f A (N + 1) (update w i t) :=
          add_le_add (lintegral_mono hU') (lintegral_mono hV')
      _ = (A + 2) * ∫⁻ t in Icc (w i) (w i + 1), W f A (N + 1) (update w i t) := by
          rw [lintegral_const_mul' _ _ (by simp)]
          ring
  calc W f A N w ≤ ∑ j ∈ box (m := m) A N,
        (A + 2) * ∫⁻ t in Icc (w i) (w i + 1), W f A (N + 1) (update w i t) :=
        Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- The unit-segment measures in each coordinate, with lower corner `x`. -/
noncomputable def segMeas {m : ℕ} (x : Fin m → ℝ) (i : Fin m) : Measure ℝ :=
  (volume : Measure ℝ).restrict (Icc (x i) (x i + 1))

instance {m : ℕ} (x : Fin m → ℝ) (i : Fin m) : SigmaFinite (segMeas x i) := by
  unfold segMeas; infer_instance

/-- Iteration of the one-variable step over a set of coordinates (Fubini–Tonelli via
`lmarginal`). -/
theorem W_le_lmarginal {m : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (A : ℕ) (x : Fin m → ℝ)
    (s : Finset (Fin m)) : ∀ (N : ℕ) (w : Fin m → ℝ), (∀ i ∈ s, w i = x i) →
      W f A N w ≤ (∏ l ∈ Finset.range s.card,
          (((box (m := m) A (N + l)).card : ℝ≥0∞) * (A + 2))) *
        lmarginal (segMeas x) s (W f A (N + s.card)) w := by
  classical
  induction s using Finset.induction_on with
  | empty => intro N w _; simp
  | @insert i s hi ih =>
    intro N w hw
    have hwi : w i = x i := hw i (Finset.mem_insert_self i s)
    have hcard : (insert i s).card = s.card + 1 := Finset.card_insert_of_notMem hi
    have hN : N + (insert i s).card = N + 1 + s.card := by rw [hcard]; ring
    rw [hN, lmarginal_insert _ (measurable_W f A _) hi w]
    refine (W_le_slice f A N i w).trans ?_
    rw [hwi]
    have hmeas : Measurable fun t : ℝ =>
        lmarginal (segMeas x) s (W f A (N + 1 + s.card)) (update w i t) :=
      ((measurable_W f A _).lmarginal (segMeas x)).comp
        (continuous_const.update i continuous_id).measurable
    set P := ∏ l ∈ Finset.range s.card, (((box (m := m) A (N + 1 + l)).card : ℝ≥0∞) * (A + 2))
    have hstep : ∀ t, W f A (N + 1) (update w i t) ≤
        P * lmarginal (segMeas x) s (W f A (N + 1 + s.card)) (update w i t) := by
      intro t
      refine ih (N + 1) _ fun l hl => ?_
      rw [update_of_ne (ne_of_mem_of_not_mem hl hi)]
      exact hw l (Finset.mem_insert_of_mem hl)
    calc (((box (m := m) A N).card : ℝ≥0∞) * (A + 2)) *
          ∫⁻ t in Icc (x i) (x i + 1), W f A (N + 1) (update w i t)
        ≤ (((box (m := m) A N).card : ℝ≥0∞) * (A + 2)) *
          ∫⁻ t in Icc (x i) (x i + 1),
            P * lmarginal (segMeas x) s (W f A (N + 1 + s.card)) (update w i t) := by
          gcongr with t
          exact hstep t
      _ = ((((box (m := m) A N).card : ℝ≥0∞) * (A + 2)) * P) *
          ∫⁻ t, lmarginal (segMeas x) s (W f A (N + 1 + s.card)) (update w i t) ∂(segMeas x i) := by
          rw [lintegral_const_mul _ hmeas, ← mul_assoc]
          rfl
      _ = _ := by
          congr 1
          rw [hcard, Finset.prod_range_succ', mul_comm]
          congr 1
          · refine Finset.prod_congr rfl fun l _ => ?_
            rw [show N + (l + 1) = N + 1 + l by omega]

theorem lintegral_cube_le {m : ℕ} (g : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : Fin m → ℝ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ∫⁻ w, ‖g (WithLp.toLp 2 w)‖ₑ ∂(Measure.pi (segMeas x)) ≤ eLpNorm (⇑g) p volume := by
  have hν : Measure.pi (segMeas x) =
      (volume : Measure (Fin m → ℝ)).restrict (Set.univ.pi fun i => Icc (x i) (x i + 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
    rfl
  have hprob : IsProbabilityMeasure (Measure.pi (segMeas x)) := by
    constructor
    rw [Measure.pi_univ]
    simp [segMeas, Real.volume_Icc]
  have hG : AEStronglyMeasurable (fun w : Fin m → ℝ => g (WithLp.toLp 2 w))
      (Measure.pi (segMeas x)) :=
    (g.continuous.comp (PiLp.continuous_toLp 2 _)).aestronglyMeasurable
  rw [← eLpNorm_one_eq_lintegral_enorm]
  refine (eLpNorm_le_eLpNorm_of_exponent_le hp hG).trans ?_
  rw [hν]
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_eq ?_
  exact eLpNorm_comp_measurePreserving g.continuous.aestronglyMeasurable
    (PiLp.volume_preserving_toLp (Fin m))

theorem W_le_eLpNorm {m : ℕ} (A N : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : Fin m → ℝ),
      W f A N x ≤ C * ∑ j ∈ box (m := m) A (N + m), eLpNorm (⇑(T j f)) p volume := by
  refine ⟨∏ l ∈ Finset.range m, (((box (m := m) A (N + l)).card : ℝ≥0∞) * (A + 2)), ?_,
    fun f x => ?_⟩
  · exact ENNReal.prod_ne_top fun _ _ => ENNReal.mul_ne_top (by simp) (by simp)
  · have h := W_le_lmarginal f A x Finset.univ N x (fun _ _ => rfl)
    simp only [Finset.card_univ, Fintype.card_fin, lmarginal_univ] at h
    refine h.trans (mul_le_mul' le_rfl ?_)
    unfold W
    rw [lintegral_finsetSum]
    · exact Finset.sum_le_sum fun j _ => lintegral_cube_le (T j f) x p hp
    · intro j _
      exact ((T j f).continuous.comp (PiLp.continuous_toLp 2 _)).enorm.measurable

theorem eucl_eq_sum {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
  classical
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]

theorem norm_multilinear_le {m n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ (Fin m)) ℂ) :
    ‖A‖ ≤ ∑ σ : Fin n → Fin m, ‖A (dirs σ)‖ := by
  classical
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun v => ?_
  have hv : v = fun j => ∑ i, v j i • EuclideanSpace.single i (1 : ℝ) := by
    funext j; exact eucl_eq_sum (v j)
  have hAv : A v = ∑ σ : Fin n → Fin m, (∏ j, v j (σ j)) • A (dirs σ) := by
    conv_lhs => rw [hv]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
    rfl
  rw [hAv]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [norm_smul, norm_prod, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => PiLp.norm_apply_le (v j) (σ j)

/-- Exponent vector counting the fibres of `τ`. -/
def cnt {m k : ℕ} (τ : Fin k → Fin m) : Fin m → ℕ :=
  fun i => (Finset.univ.filter fun l => τ l = i).card

theorem prod_eq_mono {m k : ℕ} (τ : Fin k → Fin m) (y : EuclideanSpace ℝ (Fin m)) :
    ∏ l, y (τ l) = mono (cnt τ) y := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ τ (fun l => y (τ l))]
  unfold mono cnt
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_congr rfl (fun l hl => by rw [(Finset.mem_filter.mp hl).2]), Finset.prod_const]

theorem norm_pow_le {m k : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ‖y‖ ^ k ≤ ∑ τ : Fin k → Fin m, ‖mono (cnt τ) y‖ := by
  classical
  have h1 : ‖y‖ ≤ ∑ i, ‖y i‖ := by
    conv_lhs => rw [eucl_eq_sum y]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_smul]
    simp
  calc ‖y‖ ^ k ≤ (∑ i, ‖y i‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) h1 k
    _ = ∑ τ : Fin k → Fin m, ∏ l, ‖y (τ l)‖ := by
      rw [Finset.sum_pow', Fintype.piFinset_univ]
    _ = _ := by
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← norm_prod, prod_eq_mono]

theorem cnt_le {m k : ℕ} (τ : Fin k → Fin m) (i : Fin m) : cnt τ i ≤ k := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem ofReal_le_W {m : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (k n : ℕ)
    (y : EuclideanSpace ℝ (Fin m)) :
    ENNReal.ofReal (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) y‖) ≤
      ((m : ℝ≥0∞) ^ k * (m : ℝ≥0∞) ^ n) * W f k n (WithLp.ofLp y) := by
  have hreal : ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) y‖ ≤
      ∑ τ : Fin k → Fin m, ∑ σ : Fin n → Fin m, ‖T (cnt τ, ⟨n, σ⟩) f y‖ := by
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) y‖
        ≤ (∑ τ : Fin k → Fin m, ‖mono (cnt τ) y‖) *
            ∑ σ : Fin n → Fin m, ‖iteratedFDeriv ℝ n (⇑f) y (dirs σ)‖ :=
          mul_le_mul (norm_pow_le y) (norm_multilinear_le _) (norm_nonneg _)
            (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [T_apply, norm_smul]
  have hW : ∀ (τ : Fin k → Fin m) (σ : Fin n → Fin m),
      ‖T (cnt τ, ⟨n, σ⟩) f y‖ₑ ≤ W f k n (WithLp.ofLp y) := by
    intro τ σ
    have h := le_W f (A := k) (N := n) (j := (cnt τ, ⟨n, σ⟩))
      (mem_box.mpr ⟨cnt_le τ, le_rfl⟩) (WithLp.ofLp y)
    simpa using h
  calc ENNReal.ofReal (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) y‖)
      ≤ ENNReal.ofReal (∑ τ : Fin k → Fin m, ∑ σ : Fin n → Fin m, ‖T (cnt τ, ⟨n, σ⟩) f y‖) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ∑ τ : Fin k → Fin m, ∑ σ : Fin n → Fin m, ‖T (cnt τ, ⟨n, σ⟩) f y‖ₑ := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
        refine Finset.sum_congr rfl fun σ _ => ?_
        exact ofReal_norm _
    _ ≤ ∑ τ : Fin k → Fin m, ∑ σ : Fin n → Fin m, W f k n (WithLp.ofLp y) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun σ _ => hW τ σ
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

end Sol_LCAGroup_euclidean_schwartz_withSeminorms_eLpNorm

open Sol_LCAGroup_euclidean_schwartz_withSeminorms_eLpNorm in
theorem solution (m : ℕ) (p : ℝ≥0∞) (hp₁ : 1 ≤ p) (hp : p ≠ ⊤) :
    ∃ q : (Fin m → ℕ) × (Σ n : ℕ, Fin n → Fin m) →
        Seminorm ℂ 𝓢(EuclideanSpace ℝ (Fin m), ℂ),
      (∀ (α : Fin m → ℕ) (n : ℕ) (σ : Fin n → Fin m) (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)),
        ENNReal.ofReal (q (α, ⟨n, σ⟩) f) =
          eLpNorm (fun x : EuclideanSpace ℝ (Fin m) =>
            (∏ i, x i ^ α i) •
              iteratedFDeriv ℝ n (⇑f) x (fun j => EuclideanSpace.single (σ j) (1 : ℝ)))
            p volume) ∧
      WithSeminorms q := by
  have : Fact (1 ≤ p) := ⟨hp₁⟩
  let L : Idx m → 𝓢(EuclideanSpace ℝ (Fin m), ℂ) →L[ℂ]
      Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin m))) := fun j =>
    (SchwartzMap.toLpCLM ℂ ℂ p (volume : Measure (EuclideanSpace ℝ (Fin m)))) ∘L T j
  let q : Idx m → Seminorm ℂ 𝓢(EuclideanSpace ℝ (Fin m), ℂ) := fun j =>
    (normSeminorm ℂ (Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin m))))).comp
      (L j).toLinearMap
  have hq : ∀ j f, q j f = (eLpNorm (⇑(T j f)) p volume).toReal := by
    intro j f
    change ‖(T j f).toLp p volume‖ = _
    exact SchwartzMap.norm_toLp
  have hq' : ∀ j f, ENNReal.ofReal (q j f) = eLpNorm (⇑(T j f)) p volume := by
    intro j f
    rw [hq, ENNReal.ofReal_toReal ((T j f).eLpNorm_lt_top p volume).ne]
  refine ⟨q, fun α n σ f => ?_, ?_⟩
  · rw [hq']
    congr 1
    funext x
    exact T_apply (α, ⟨n, σ⟩) f x
  · refine (schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin m)) ℂ).congr ?_ ?_
    · intro j
      have hcont : Continuous (q j) := by
        change Continuous fun f => ‖L j f‖
        exact (L j).continuous.norm
      obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous
        (schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin m)) ℂ) (q j) hcont
      exact ⟨s, C, hC⟩
    · refine Seminorm.IsBounded.of_real fun kn => ?_
      obtain ⟨k, n⟩ := kn
      obtain ⟨C, hCtop, hC⟩ := W_le_eLpNorm (m := m) k n p hp₁
      let J := box (m := m) k (n + m)
      let K : ℝ≥0∞ := ((m : ℝ≥0∞) ^ k * (m : ℝ≥0∞) ^ n) * C
      have hK : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top m))
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top m))) hCtop
      refine ⟨J, K.toReal * J.card, fun f => ?_⟩
      change SchwartzMap.seminorm ℂ k n f ≤ _
      refine SchwartzMap.seminorm_le_bound ℂ k n f (by positivity) fun y => ?_
      have hsum : ∑ j ∈ J, eLpNorm (⇑(T j f)) p volume ≤
          J.card * ENNReal.ofReal (J.sup q f) := by
        calc ∑ j ∈ J, eLpNorm (⇑(T j f)) p volume = ∑ j ∈ J, ENNReal.ofReal (q j f) := by
              simp_rw [hq']
          _ ≤ ∑ j ∈ J, ENNReal.ofReal (J.sup q f) :=
              Finset.sum_le_sum fun j hj =>
                ENNReal.ofReal_le_ofReal (Seminorm.le_finset_sup_apply hj)
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      have h := (ofReal_le_W f k n y).trans (mul_le_mul' le_rfl (hC f (WithLp.ofLp y)))
      rw [← mul_assoc] at h
      have h2 := h.trans (mul_le_mul' le_rfl hsum)
      rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
      refine h2.trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_toReal hK, ENNReal.ofReal_natCast]
      simp only [K]
      ring
