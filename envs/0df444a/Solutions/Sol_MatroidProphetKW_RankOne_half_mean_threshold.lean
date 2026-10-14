-- Prove2me | solution 1 for MatroidProphetKW.RankOne.half_mean_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:45:56.819994+00:00
-- url     : https://prove2.me/submissions/88f1d4ad-44bc-4f3e-b3fe-c2f31f3673cf

import Mathlib
import Definitions.Def_MatroidProphetKW_RankOne_Setting

set_option autoImplicit false

open MatroidProphetKW.RankOne MeasureTheory ProbabilityTheory in
lemma pv19b_reward_eq {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (T : ℝ) (ω : Ω) :
    thresholdReward X T ω = (if T ≤ maxX X ω then T else 0) +
      ∑ i, max (X i ω - T) 0 * (if ∀ j < i, X j ω < T then (1:ℝ) else 0) := by
  classical
  unfold thresholdReward
  by_cases h : (Finset.univ.filter (fun i : Fin n => T ≤ X i ω)).Nonempty
  · rw [dif_pos h]
    set k := (Finset.univ.filter (fun i : Fin n => T ≤ X i ω)).min' h with hk
    have hkmem : k ∈ Finset.univ.filter (fun i : Fin n => T ≤ X i ω) := Finset.min'_mem _ h
    have hkT : T ≤ X k ω := by simpa using hkmem
    have hbefore : ∀ j < k, X j ω < T := by
      intro j hj
      by_contra hcon
      push Not at hcon
      have : j ∈ Finset.univ.filter (fun i : Fin n => T ≤ X i ω) := by simpa using hcon
      have := Finset.min'_le _ _ this
      omega
    have hmax : T ≤ maxX X ω := by
      unfold maxX
      exact le_trans hkT (Finset.le_sup' (fun i => X i ω) (Finset.mem_univ k))
    rw [if_pos hmax, Finset.sum_eq_single k]
    · rw [if_pos hbefore, max_eq_left (by linarith)]
      ring
    · intro i _ hik
      rcases lt_or_gt_of_ne hik with hlt | hgt
      · rw [max_eq_right (by linarith [hbefore i hlt])]
        simp
      · rw [if_neg (by push Not; exact ⟨k, hgt, hkT⟩)]
        simp
    · simp
  · rw [dif_neg h]
    have hall : ∀ i, X i ω < T := by
      intro i
      by_contra hcon
      push Not at hcon
      exact h ⟨i, by simpa using hcon⟩
    have hmax : ¬ T ≤ maxX X ω := by
      unfold maxX
      rw [not_le, Finset.sup'_lt_iff]
      intro i _; exact hall i
    rw [if_neg hmax]
    simp [fun i => max_eq_right (by linarith [hall i] : X i ω - T ≤ 0)]

open MatroidProphetKW.RankOne MeasureTheory ProbabilityTheory in
lemma pv19b_max_le {Ω : Type*} {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ) (T : ℝ) (ω : Ω) :
    maxX X ω ≤ T + ∑ i, max (X i ω - T) 0 := by
  classical
  unfold maxX
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin n)) (fun i => X i ω)
  rw [hk]
  have h1 : max (X k ω - T) 0 ≤ ∑ i, max (X i ω - T) 0 :=
    Finset.single_le_sum (f := fun i => max (X i ω - T) 0) (fun i _ => le_max_right _ _)
      (Finset.mem_univ k)
  have h2 : X k ω - T ≤ max (X k ω - T) 0 := le_max_left _ _
  linarith

open MatroidProphetKW.RankOne MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} [NeZero n] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hnonneg : ∀ i ω, 0 ≤ X i ω) (hint : Integrable (maxX X) P) :
    (∫ ω, maxX X ω ∂P) / 2 ≤ ∫ ω, reward P X ω ∂P := by
  classical
  set T : ℝ := (∫ ω, maxX X ω ∂P) / 2 with hT
  have hrew : ∀ ω, reward P X ω = thresholdReward X T ω := fun ω => rfl
  have hXle : ∀ i ω, X i ω ≤ maxX X ω := fun i ω =>
    Finset.le_sup' (fun i => X i ω) (Finset.mem_univ i)
  have hmaxnn : ∀ ω, 0 ≤ maxX X ω := fun ω => le_trans (hnonneg 0 ω) (hXle 0 ω)
  have hT0 : 0 ≤ T := by
    have := integral_nonneg (f := maxX X) (μ := P) hmaxnn
    rw [hT]; linarith
  have hmaxmeas : Measurable (maxX X) := by
    have h := Finset.measurable_sup' (s := Finset.univ) (f := X) Finset.univ_nonempty
      (fun i _ => hmeas i)
    convert h using 1
    ext ω
    simp [maxX, Finset.sup'_apply]
  let g : Fin n → Ω → ℝ := fun i ω => max (X i ω - T) 0
  have hgmeas : ∀ i, Measurable (g i) := fun i => ((hmeas i).sub_const T).max measurable_const
  have hgle : ∀ i ω, g i ω ≤ maxX X ω := by
    intro i ω
    refine max_le ?_ (hmaxnn ω)
    linarith [hXle i ω]
  have hgnn : ∀ i ω, 0 ≤ g i ω := fun i ω => le_max_right _ _
  have hgint : ∀ i, Integrable (g i) P := by
    intro i
    refine Integrable.mono' hint (hgmeas i).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hgnn i ω)]
    exact hgle i ω
  let E : Fin n → Set Ω := fun i => {ω | ∀ j < i, X j ω < T}
  have hEmeas : ∀ i, MeasurableSet (E i) := by
    intro i
    have : E i = ⋂ j ∈ Finset.Iio i, {ω | X j ω < T} := by
      ext ω; simp [E]
    rw [this]
    exact Finset.measurableSet_biInter _ (fun j _ => measurableSet_lt (hmeas j) measurable_const)
  let h : Fin n → Ω → ℝ := fun i => (E i).indicator (fun _ => (1:ℝ))
  have hhmeas : ∀ i, Measurable (h i) := fun i => measurable_const.indicator (hEmeas i)
  have hhite : ∀ i ω, h i ω = if ∀ j < i, X j ω < T then (1:ℝ) else 0 := by
    intro i ω
    simp [h, Set.indicator_apply, E]
  let A : Set Ω := {ω | T ≤ maxX X ω}
  have hAmeas : MeasurableSet A := measurableSet_le measurable_const hmaxmeas
  have hAcE : ∀ i, Aᶜ ⊆ E i := by
    intro i ω hω j _
    have : ¬ T ≤ maxX X ω := hω
    exact lt_of_le_of_lt (hXle j ω) (not_le.mp this)
  have hPA : ∀ i, P.real Aᶜ ≤ P.real (E i) := fun i => measureReal_mono (hAcE i)
  have hPAc : P.real Aᶜ = 1 - P.real A := probReal_compl_eq_one_sub hAmeas
  have hpA1 : P.real A ≤ 1 := measureReal_le_one
  -- independence factorisation
  have hprod : ∀ i, ∫ ω, g i ω * h i ω ∂P = (∫ ω, g i ω ∂P) * P.real (E i) := by
    intro i
    have hI := hindep.indepFun_finset {i} (Finset.Iio i) (by simp) hmeas
    have hφ : Measurable (fun y : ({i} : Finset (Fin n)) → ℝ => max (y ⟨i, Finset.mem_singleton_self i⟩ - T) 0) :=
      (by fun_prop)
    have hψ : Measurable (fun y : (Finset.Iio i) → ℝ => (if ∀ j, y j < T then (1:ℝ) else 0)) := by
      have hs : MeasurableSet {y : (Finset.Iio i) → ℝ | ∀ j, y j < T} := by
        have : {y : (Finset.Iio i) → ℝ | ∀ j, y j < T} = ⋂ j, {y | y j < T} := by
          ext y; simp
        rw [this]
        exact MeasurableSet.iInter (fun j => measurableSet_lt (measurable_pi_apply j) measurable_const)
      exact Measurable.ite hs measurable_const measurable_const
    have hI2 := hI.comp hφ hψ
    have hgh : IndepFun (g i) (h i) P := by
      refine hI2.congr ?_ ?_
      · exact Filter.Eventually.of_forall (fun ω => rfl)
      · refine Filter.Eventually.of_forall (fun ω => ?_)
        rw [hhite]
        show (if ∀ j : (Finset.Iio i), X j ω < T then (1:ℝ) else 0) = _
        congr 1
        apply propext
        constructor
        · intro hh j hj; exact hh ⟨j, Finset.mem_Iio.mpr hj⟩
        · intro hh j; exact hh j (Finset.mem_Iio.mp j.2)
    have := hgh.integral_fun_mul_eq_mul_integral (hgmeas i).aestronglyMeasurable
      (hhmeas i).aestronglyMeasurable
    rw [this]
    congr 1
    simp only [h]
    exact integral_indicator_one (hEmeas i)
  -- integrability of the product terms
  have hgh_int : ∀ i, Integrable (fun ω => g i ω * h i ω) P := by
    intro i
    refine Integrable.mono' (hgint i) ((hgmeas i).mul (hhmeas i)).aestronglyMeasurable
      (Filter.Eventually.of_forall ?_)
    intro ω
    have h01 : 0 ≤ h i ω ∧ h i ω ≤ 1 := by
      rw [hhite]; split_ifs <;> simp
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hgnn i ω) h01.1)]
    nlinarith [hgnn i ω, h01.1, h01.2]
  have hAint : Integrable (A.indicator (fun _ => T)) P :=
    (integrable_const T).indicator hAmeas
  have hreward_eq : ∀ ω, reward P X ω = A.indicator (fun _ => T) ω + ∑ i, g i ω * h i ω := by
    intro ω
    rw [hrew, pv19b_reward_eq]
    have e1 : (if T ≤ maxX X ω then T else 0) = A.indicator (fun _ => T) ω := by
      simp [Set.indicator_apply, A]
    have e2 : ∑ i, max (X i ω - T) 0 * (if ∀ j < i, X j ω < T then (1:ℝ) else 0)
        = ∑ i, g i ω * h i ω :=
      Finset.sum_congr rfl (fun i _ => by rw [hhite])
    rw [e1, e2]
  have hint_reward : ∫ ω, reward P X ω ∂P = T * P.real A + ∑ i, (∫ ω, g i ω ∂P) * P.real (E i) := by
    have : (fun ω => reward P X ω) = fun ω => A.indicator (fun _ => T) ω + ∑ i, g i ω * h i ω :=
      funext hreward_eq
    rw [this, integral_add hAint (integrable_finsetSum _ (fun i _ => hgh_int i)),
      integral_finsetSum _ (fun i _ => hgh_int i), integral_indicator_const _ hAmeas]
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => hprod i)
  -- S ≥ T
  have hS : T ≤ ∑ i, ∫ ω, g i ω ∂P := by
    have h1 : ∫ ω, maxX X ω ∂P ≤ ∫ ω, (T + ∑ i, g i ω) ∂P :=
      integral_mono hint ((integrable_const T).add (integrable_finsetSum _ (fun i _ => hgint i)))
        (fun ω => pv19b_max_le X T ω)
    rw [integral_add (integrable_const T) (integrable_finsetSum _ (fun i _ => hgint i)),
      integral_finsetSum _ (fun i _ => hgint i)] at h1
    simp at h1
    have h2 : ∫ ω, maxX X ω ∂P = 2 * T := by rw [hT]; ring
    linarith
  have hlow : ∑ i, (∫ ω, g i ω ∂P) * (1 - P.real A) ≤ ∑ i, (∫ ω, g i ω ∂P) * P.real (E i) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (integral_nonneg (hgnn i))
    rw [← hPAc]; exact hPA i
  rw [← Finset.sum_mul] at hlow
  have : T ≤ T * P.real A + (∑ i, ∫ ω, g i ω ∂P) * (1 - P.real A) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hpA1)]
  rw [hint_reward]
  linarith
