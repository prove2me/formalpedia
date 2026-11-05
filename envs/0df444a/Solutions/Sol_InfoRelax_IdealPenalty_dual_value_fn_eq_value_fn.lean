-- Prove2me | solution 1 for InfoRelax.IdealPenalty.dual_value_fn_eq_value_fn
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:14:59.739328+00:00
-- url     : https://prove2.me/submissions/65a49425-3fcf-4e94-b6d1-76d12dc27c3a

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework
import Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel
import Definitions.Def_InfoRelax_IdealPenalty_Penalty

set_option autoImplicit false
open MeasureTheory InfoRelax.IdealPenalty



namespace IPAux

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace ι] [Countable ι]
  [MeasurableSingletonClass ι]

/-- integrability of a countable substitution of uniformly bounded measurable functions -/
lemma integrable_subst (μ : Measure Ω) [IsFiniteMeasure μ] (g : ι → Ω → ℝ)
    (hg : ∀ b, Measurable (g b)) (K : ℝ) (hK : ∀ b, ∀ᵐ ω ∂μ, |g b ω| ≤ K)
    (β : Ω → ι) (hβ : Measurable β) :
    Integrable (fun ω => g (β ω) ω) μ := by
  have hm : Measurable (fun p : Ω × ι => g p.2 p.1) :=
    measurable_from_prod_countable_left (fun b => hg b)
  have hm2 : Measurable (fun ω => g (β ω) ω) :=
    hm.comp (measurable_id.prodMk hβ)
  refine Integrable.of_bound hm2.aestronglyMeasurable K ?_
  have : ∀ᵐ ω ∂μ, ∀ b, |g b ω| ≤ K := ae_all_iff.2 hK
  filter_upwards [this] with ω hω
  simpa [Real.norm_eq_abs] using hω (β ω)

lemma measurable_subst (g : ι → Ω → ℝ)
    (hg : ∀ b, Measurable (g b)) (β : Ω → ι) (hβ : Measurable β) :
    Measurable (fun ω => g (β ω) ω) :=
  (measurable_from_prod_countable_left (f := fun p : Ω × ι => g p.2 p.1)
    (fun b => hg b)).comp (measurable_id.prodMk hβ)

/-- splitting the integral of a substitution along the fibres of `β`. -/
lemma setIntegral_subst (μ : Measure Ω) (g : ι → Ω → ℝ)
    (β : Ω → ι) (hβ : Measurable β) (s : Set Ω) (hs : MeasurableSet s)
    (hint : IntegrableOn (fun ω => g (β ω) ω) s μ) :
    ∫ ω in s, g (β ω) ω ∂μ = ∑' b, ∫ ω in s ∩ β ⁻¹' {b}, g b ω ∂μ := by
  have hU : (⋃ b, s ∩ β ⁻¹' {b}) = s := by
    ext ω; simp
  have hmeas : ∀ b, MeasurableSet (s ∩ β ⁻¹' {b}) :=
    fun b => hs.inter (hβ (measurableSet_singleton b))
  have hdisj : Pairwise (Function.onFun Disjoint fun b => s ∩ β ⁻¹' {b}) := by
    intro b b' hbb'
    refine Set.disjoint_left.2 ?_
    intro ω h1 h2
    exact hbb' (h1.2.symm.trans h2.2)
  have hint' : IntegrableOn (fun ω => g (β ω) ω) (⋃ b, s ∩ β ⁻¹' {b}) μ := by
    rw [hU]; exact hint
  have := integral_iUnion hmeas hdisj hint'
  rw [hU] at this
  rw [this]
  congr 1
  funext b
  refine setIntegral_congr_fun (hmeas b) ?_
  intro ω hω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hω
  simp [hω.2]

/-- The key substitution lemma: integrating a conditional expectation along an
`m`-measurable countable-valued selection. -/
lemma setIntegral_condExp_subst (μ : Measure Ω) [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (g : ι → Ω → ℝ) (hgi : ∀ b, Integrable (g b) μ)
    (K : ℝ) (hK : ∀ b, ∀ᵐ ω ∂μ, |g b ω| ≤ K)
    (β : Ω → ι) (hβ : Measurable[m] β) (s : Set Ω) (hs : MeasurableSet[m] s) :
    ∫ ω in s, (μ[g (β ω) | m]) ω ∂μ = ∑' b, ∫ ω in s ∩ β ⁻¹' {b}, g b ω ∂μ := by
  have hβ' : Measurable[mΩ] β := hβ.mono hm le_rfl
  have hint : Integrable (fun ω => (μ[g (β ω) | m]) ω) μ := by
    refine integrable_subst (mΩ := mΩ) μ (fun b => μ[g b | m])
      (fun b => (stronglyMeasurable_condExp.mono hm).measurable) K ?_ β hβ'
    intro b
    exact ae_bdd_abs_condExp_of_ae_bdd_abs (hK b)
  rw [setIntegral_subst (mΩ := mΩ) μ (fun b => μ[g b | m]) β hβ' s (hm s hs) hint.integrableOn]
  congr 1
  funext b
  exact setIntegral_condExp hm (hgi b) (hs.inter (hβ (measurableSet_singleton b)))

lemma setIntegral_condExp_subst' (μ : Measure Ω) [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (g : ι → Ω → ℝ) (hgm : ∀ b, Measurable[mΩ] (g b))
    (K : ℝ) (hK : ∀ b, ∀ᵐ ω ∂μ, |g b ω| ≤ K)
    (β : Ω → ι) (hβ : Measurable[m] β) (s : Set Ω) (hs : MeasurableSet[m] s) :
    ∫ ω in s, (μ[g (β ω) | m]) ω ∂μ = ∫ ω in s, g (β ω) ω ∂μ := by
  have hβ' : Measurable[mΩ] β := hβ.mono hm le_rfl
  have hgi : ∀ b, Integrable (g b) μ := fun b =>
    Integrable.of_bound (hgm b).aestronglyMeasurable K
      (by filter_upwards [hK b] with ω h; simpa [Real.norm_eq_abs] using h)
  rw [setIntegral_condExp_subst (mΩ := mΩ) μ hm g hgi K hK β hβ s hs,
    setIntegral_subst (mΩ := mΩ) μ g β hβ' s (hm s hs) (integrable_subst (mΩ := mΩ) μ g hgm K hK β hβ').integrableOn]

end IPAux



namespace IPAux

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  [DiscreteMeasurableSpace X] [Countable X] [DecidableEq X] {T : ℕ}

lemma bellman_fin (μ : Measure Ω) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (Afeas : Fin (T + 1) → (Fin (T + 1) → X) → Set X)
    (f : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (t : Fin (T + 1)) (a : Fin (T + 1) → X) :
    bellman μ 𝔾 Afeas f (t : ℕ) a = fun ω => ⨆ x : Afeas t a,
        f t (Function.update a t x.1) ω +
          μ[bellman μ 𝔾 Afeas f ((t : ℕ) + 1) (Function.update a t x.1) | 𝔾 t] ω := by
  rw [bellman, dif_pos (Nat.lt_succ_iff.mp t.isLt)]

lemma bellman_gt (μ : Measure Ω) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (Afeas : Fin (T + 1) → (Fin (T + 1) → X) → Set X)
    (f : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (t : ℕ) (ht : T < t)
    (a : Fin (T + 1) → X) :
    bellman μ 𝔾 Afeas f t a = 0 := by
  rw [bellman, dif_neg (by omega)]

section
variable (μ : Measure Ω) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (Afeas : Fin (T + 1) → (Fin (T + 1) → X) → Set X)
    (f : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ)

/-- dependence only on the past actions -/
lemma bellman_dep
    (hA : ∀ t a a', (∀ s, s < t → a s = a' s) → Afeas t a = Afeas t a')
    (hf : ∀ t a a', (∀ s, s ≤ t → a s = a' s) → f t a = f t a') :
    ∀ k t, T + 1 - t = k → ∀ a a' : Fin (T + 1) → X,
      (∀ s : Fin (T + 1), (s : ℕ) < t → a s = a' s) →
        bellman μ 𝔾 Afeas f t a = bellman μ 𝔾 Afeas f t a' := by
  intro k
  induction k with
  | zero =>
    intro t ht a a' _
    rw [bellman_gt μ 𝔾 Afeas f t (by omega), bellman_gt μ 𝔾 Afeas f t (by omega)]
  | succ k ih =>
    intro t ht a a' haa
    have htT : t < T + 1 := by omega
    have e := bellman_fin μ 𝔾 Afeas f ⟨t, htT⟩
    simp only at e
    rw [e a, e a']
    have hAe : Afeas ⟨t, htT⟩ a = Afeas ⟨t, htT⟩ a' :=
      hA _ a a' (fun s hs => haa s (by simpa [Fin.lt_def] using hs))
    have hup : ∀ x : X, ∀ s, s ≤ (⟨t, htT⟩ : Fin (T + 1)) →
        Function.update a ⟨t, htT⟩ x s = Function.update a' ⟨t, htT⟩ x s := by
      intro x s hs
      by_cases hst : s = ⟨t, htT⟩
      · subst hst; simp
      · rw [Function.update_of_ne hst, Function.update_of_ne hst]
        apply haa
        have : s ≠ ⟨t, htT⟩ := hst
        have h1 : (s : ℕ) ≤ t := by simpa [Fin.le_def] using hs
        have h2 : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
        omega
    have hf' : ∀ x : X, f ⟨t, htT⟩ (Function.update a ⟨t, htT⟩ x) =
        f ⟨t, htT⟩ (Function.update a' ⟨t, htT⟩ x) := fun x => hf _ _ _ (hup x)
    have hV : ∀ x : X, bellman μ 𝔾 Afeas f (t + 1) (Function.update a ⟨t, htT⟩ x) =
        bellman μ 𝔾 Afeas f (t + 1) (Function.update a' ⟨t, htT⟩ x) := by
      intro x
      apply ih (t + 1) (by omega)
      intro s hs
      exact hup x s (by rw [Fin.le_def]; simp; omega)
    funext ω
    simp_rw [hf', hV]
    rw [hAe]

end

section
variable (μ : Measure Ω) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (Afeas : Fin (T + 1) → (Fin (T + 1) → X) → Set X)
    (f : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ)

lemma bellman_meas_fin (hfm : ∀ t a, Measurable[𝔾 t] (f t a)) (t : Fin (T + 1))
    (a : Fin (T + 1) → X) : Measurable[𝔾 t] (bellman μ 𝔾 Afeas f (t : ℕ) a) := by
  rw [bellman_fin]
  exact Measurable.iSup (fun x => (hfm _ _).add stronglyMeasurable_condExp.measurable)

lemma bellman_meas (hfm : ∀ t a, Measurable[𝔾 t] (f t a)) (t : ℕ)
    (a : Fin (T + 1) → X) : Measurable (bellman μ 𝔾 Afeas f t a) := by
  by_cases ht : t ≤ T
  · have := bellman_meas_fin μ 𝔾 Afeas f hfm ⟨t, by omega⟩ a
    exact this.mono (𝔾.le _) le_rfl
  · rw [bellman_gt μ 𝔾 Afeas f t (by omega)]
    exact measurable_const

lemma bellman_bound (hne : ∀ t a, (Afeas t a).Nonempty) (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ t a ω, |f t a ω| ≤ C) :
    ∀ k t, T + 1 ≤ t + k → ∀ a, ∀ᵐ ω ∂μ, |bellman μ 𝔾 Afeas f t a ω| ≤ k * C := by
  intro k
  induction k with
  | zero =>
    intro t ht a
    rw [bellman_gt μ 𝔾 Afeas f t (by omega)]
    simp
  | succ k ih =>
    intro t ht a
    by_cases htT : T < t
    · rw [bellman_gt μ 𝔾 Afeas f t htT]
      filter_upwards with ω
      simp only [Pi.zero_apply, abs_zero]
      positivity
    have htT' : t < T + 1 := by omega
    have e := bellman_fin μ 𝔾 Afeas f ⟨t, htT'⟩ a
    simp only at e
    rw [e]
    have h1 : ∀ b, ∀ᵐ ω ∂μ,
        |(μ[bellman μ 𝔾 Afeas f (t + 1) b | 𝔾 ⟨t, htT'⟩]) ω| ≤ k * C := fun b =>
      ae_bdd_abs_condExp_of_ae_bdd_abs (ih (t + 1) (by omega) b)
    have h2 := ae_all_iff.2 h1
    filter_upwards [h2] with ω hω
    have hg : ∀ x : X, |f ⟨t, htT'⟩ (Function.update a ⟨t, htT'⟩ x) ω +
        (μ[bellman μ 𝔾 Afeas f (t + 1) (Function.update a ⟨t, htT'⟩ x) | 𝔾 ⟨t, htT'⟩]) ω|
          ≤ C + k * C := fun x =>
      (abs_add_le _ _).trans (add_le_add (hfb _ _ _) (hω _))
    haveI : Nonempty (Afeas ⟨t, htT'⟩ a) := (hne _ a).to_subtype
    have hbdd : BddAbove (Set.range fun x : Afeas ⟨t, htT'⟩ a =>
        f ⟨t, htT'⟩ (Function.update a ⟨t, htT'⟩ x.1) ω +
        (μ[bellman μ 𝔾 Afeas f (t + 1) (Function.update a ⟨t, htT'⟩ x.1) | 𝔾 ⟨t, htT'⟩]) ω) := by
      refine ⟨C + k * C, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact (abs_le.1 (hg x.1)).2
    rw [abs_le]
    obtain ⟨x0⟩ := (inferInstance : Nonempty (Afeas ⟨t, htT'⟩ a))
    push_cast
    constructor
    · refine le_ciSup_of_le hbdd x0 ?_
      have := (abs_le.1 (hg x0.1)).1
      linarith
    · refine ciSup_le fun x => ?_
      have := (abs_le.1 (hg x.1)).2
      linarith

lemma bellman_ge (hne : ∀ t a, (Afeas t a).Nonempty) (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ t a ω, |f t a ω| ≤ C) (t : Fin (T + 1)) (a : Fin (T + 1) → X) :
    ∀ᵐ ω ∂μ, ∀ x ∈ Afeas t a, f t (Function.update a t x) ω +
      (μ[bellman μ 𝔾 Afeas f ((t : ℕ) + 1) (Function.update a t x) | 𝔾 t]) ω ≤
        bellman μ 𝔾 Afeas f t a ω := by
  have h1 : ∀ b, ∀ᵐ ω ∂μ,
      |(μ[bellman μ 𝔾 Afeas f ((t : ℕ) + 1) b | 𝔾 t]) ω| ≤ (T + 1 : ℕ) * C := fun b =>
    ae_bdd_abs_condExp_of_ae_bdd_abs (bellman_bound μ 𝔾 Afeas f hne C hC hfb (T + 1) _
      (by omega) b)
  filter_upwards [ae_all_iff.2 h1] with ω hω
  intro x hx
  rw [bellman_fin]
  have hbdd : BddAbove (Set.range fun x : Afeas t a =>
      f t (Function.update a t x.1) ω +
      (μ[bellman μ 𝔾 Afeas f ((t : ℕ) + 1) (Function.update a t x.1) | 𝔾 t]) ω) := by
    refine ⟨C + (T + 1 : ℕ) * C, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact add_le_add (abs_le.1 (hfb _ _ _)).2 (abs_le.1 (hω _)).2
  exact le_ciSup hbdd (⟨x, hx⟩ : Afeas t a)

end

lemma tele (h : ℕ → ℝ) : ∑ t : Fin (T + 1), (h t - h ((t : ℕ) + 1)) = h 0 - h (T + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => h i - h (i + 1)), Finset.sum_range_sub']

/-- truncation of an action sequence after period `t` -/
def truncSeq (x0 : X) (t : Fin (T + 1)) (a : Fin (T + 1) → X) : Fin (T + 1) → X :=
  fun s => if s ≤ t then a s else x0

lemma truncSeq_meas (x0 : X) (𝔾 : Filtration (Fin (T + 1)) mΩ) (t : Fin (T + 1))
    (α : Ω → Fin (T + 1) → X) (hα : ∀ s, Measurable[𝔾 s] (fun ω => α ω s)) :
    Measurable[𝔾 t] (fun ω => truncSeq x0 t (α ω)) := by
  refine @measurable_pi_lambda Ω (Fin (T + 1)) (fun _ => X) (𝔾 t) _ _ (fun s => ?_)
  unfold truncSeq
  by_cases hs : s ≤ t
  · simp only [hs, if_true]
    exact (hα s).mono (𝔾.mono hs) le_rfl
  · simp only [hs, if_false]
    exact measurable_const

section DP
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T)

lemma V_dep (hM : M.Valid) (t : ℕ) (a a' : Fin (T + 1) → X)
    (h : ∀ s : Fin (T + 1), (s : ℕ) < t → a s = a' s) : valueFn M μ t a = valueFn M μ t a' :=
  bellman_dep μ M.𝔽 M.Afeas M.rt hM.2.1 hM.2.2.2.2.1 _ t rfl a a' h

lemma V_meas (hM : M.Valid) (t : ℕ) (a : Fin (T + 1) → X) : Measurable (valueFn M μ t a) :=
  bellman_meas μ M.𝔽 M.Afeas M.rt hM.2.2.2.1 t a

lemma V_meas_fin (hM : M.Valid) (t : Fin (T + 1)) (a : Fin (T + 1) → X) :
    Measurable[M.𝔽 t] (valueFn M μ t a) :=
  bellman_meas_fin μ M.𝔽 M.Afeas M.rt hM.2.2.2.1 t a

lemma rt_bound (hM : M.Valid) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t a ω, |M.rt t a ω| ≤ C := by
  obtain ⟨C, hC⟩ := hM.2.2.2.2.2
  exact ⟨max C 0, le_max_right _ _, fun t a ω => (hC t a ω).trans (le_max_left _ _)⟩

lemma V_bound (hM : M.Valid) : ∃ K : ℝ, ∀ t a, ∀ᵐ ω ∂μ, |valueFn M μ t a ω| ≤ K := by
  obtain ⟨C, hC0, hC⟩ := rt_bound M hM
  refine ⟨(T + 1 : ℕ) * C, fun t a => ?_⟩
  exact bellman_bound μ M.𝔽 M.Afeas M.rt hM.2.2.1 C hC0 hC (T + 1) t (by omega) a

lemma V_ge (hM : M.Valid) (t : Fin (T + 1)) :
    ∀ᵐ ω ∂μ, ∀ a : Fin (T + 1) → X, a t ∈ M.Afeas t a →
      M.rt t a ω + (μ[valueFn M μ ((t : ℕ) + 1) a | M.𝔽 t]) ω ≤ valueFn M μ t a ω := by
  obtain ⟨C, hC0, hC⟩ := rt_bound M hM
  have h := fun a => bellman_ge μ M.𝔽 M.Afeas M.rt hM.2.2.1 C hC0 hC t a
  filter_upwards [ae_all_iff.2 h] with ω hω
  intro a ha
  have := hω a (a t) ha
  simp only [Function.update_eq_self] at this
  exact this

lemma V_last (t : ℕ) (ht : T < t) (a : Fin (T + 1) → X) : valueFn M μ t a = 0 :=
  bellman_gt μ M.𝔽 M.Afeas M.rt t ht a

lemma int_V (hM : M.Valid) (t : ℕ) (α : Ω → Fin (T + 1) → X) (hα : Measurable α) :
    Integrable (fun ω => valueFn M μ t (α ω) ω) μ := by
  obtain ⟨K, hK⟩ := V_bound μ M hM
  exact integrable_subst μ (fun b => valueFn M μ t b) (fun b => V_meas μ M hM t b) K
    (fun b => hK t b) α hα

lemma int_rt (hM : M.Valid) (t : Fin (T + 1)) (α : Ω → Fin (T + 1) → X) (hα : Measurable α) :
    Integrable (fun ω => M.rt t (α ω) ω) μ := by
  obtain ⟨C, _, hC⟩ := rt_bound M hM
  exact integrable_subst μ (fun b => M.rt t b)
    (fun b => (hM.2.2.2.1 t b).mono (M.𝔽.le t) le_rfl) C
    (fun b => Filter.Eventually.of_forall (hC t b)) α hα

lemma int_CE (hM : M.Valid) (𝔾 : Filtration (Fin (T + 1)) mΩ) (t' : Fin (T + 1)) (t : ℕ)
    (α : Ω → Fin (T + 1) → X) (hα : Measurable α) :
    Integrable (fun ω => (μ[valueFn M μ t (α ω) | 𝔾 t']) ω) μ := by
  obtain ⟨K, hK⟩ := V_bound μ M hM
  exact integrable_subst μ (fun b => μ[valueFn M μ t b | 𝔾 t'])
    (fun b => (stronglyMeasurable_condExp.mono (𝔾.le t')).measurable) K
    (fun b => ae_bdd_abs_condExp_of_ae_bdd_abs (hK t b)) α hα

lemma integral_CE_V (hM : M.Valid) (x0 : X) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (t : Fin (T + 1)) (α : Ω → Fin (T + 1) → X)
    (hα : ∀ s, Measurable[𝔾 s] (fun ω => α ω s)) :
    ∫ ω, (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | 𝔾 t]) ω ∂μ =
      ∫ ω, valueFn M μ ((t : ℕ) + 1) (α ω) ω ∂μ := by
  have e : ∀ ω, valueFn M μ ((t : ℕ) + 1) (α ω) =
      valueFn M μ ((t : ℕ) + 1) (truncSeq x0 t (α ω)) := by
    intro ω
    apply V_dep μ M hM
    intro s hs
    have : s ≤ t := by rw [Fin.le_def]; omega
    simp [truncSeq, this]
  have e1 : (fun ω => (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | 𝔾 t]) ω) =
      fun ω => (μ[valueFn M μ ((t : ℕ) + 1) (truncSeq x0 t (α ω)) | 𝔾 t]) ω := by
    funext ω; rw [e ω]
  have e2 : (fun ω => valueFn M μ ((t : ℕ) + 1) (α ω) ω) =
      fun ω => valueFn M μ ((t : ℕ) + 1) (truncSeq x0 t (α ω)) ω := by
    funext ω; rw [e ω]
  rw [e1, e2]
  obtain ⟨K, hK⟩ := V_bound μ M hM
  have := setIntegral_condExp_subst' (mΩ := mΩ) μ (𝔾.le t)
    (fun b => valueFn M μ ((t : ℕ) + 1) b) (fun b => V_meas μ M hM _ b) K (fun b => hK _ b)
    (fun ω => truncSeq x0 t (α ω)) (truncSeq_meas x0 𝔾 t α hα) Set.univ MeasurableSet.univ
  simpa only [setIntegral_univ] using this

end DP

end IPAux



open IPAux in
theorem solution {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] [DecidableEq X] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T) (hM : M.Valid)
    (𝔾 : Filtration (Fin (T + 1)) mΩ) (h𝔾 : IsRelaxation M.𝔽 𝔾) :
    ∀ (t : ℕ) (a : Fin (T + 1) → X),
      dualValueFn M μ 𝔾 (idealGen M μ) t a =ᵐ[μ] valueFn M μ t a := by
  have key : ∀ k t, T + 1 - t = k → ∀ a : Fin (T + 1) → X,
      dualValueFn M μ 𝔾 (idealGen M μ) t a =ᵐ[μ] valueFn M μ t a := by
    intro k
    induction k with
    | zero =>
      intro t ht a
      unfold dualValueFn valueFn
      rw [bellman_gt _ _ _ _ t (by omega), bellman_gt _ _ _ _ t (by omega)]
    | succ k ih =>
      intro t ht a
      have htT : t < T + 1 := by omega
      have e1 := bellman_fin μ 𝔾 M.Afeas
        (fun t a ω => M.rt t a ω - penaltyComp μ M.𝔽 𝔾 (idealGen M μ) t a ω) ⟨t, htT⟩ a
      have e2 := bellman_fin μ M.𝔽 M.Afeas M.rt ⟨t, htT⟩ a
      simp only at e1 e2
      unfold dualValueFn valueFn
      rw [e1, e2]
      have h1 : ∀ x : X, μ[dualValueFn M μ 𝔾 (idealGen M μ) (t + 1)
            (Function.update a ⟨t, htT⟩ x) | 𝔾 ⟨t, htT⟩] =ᵐ[μ]
          μ[valueFn M μ (t + 1) (Function.update a ⟨t, htT⟩ x) | 𝔾 ⟨t, htT⟩] :=
        fun x => condExp_congr_ae (ih (t + 1) (by omega) _)
      filter_upwards [ae_all_iff.2 h1] with ω hω
      refine iSup_congr (fun x => ?_)
      have := hω x.1
      unfold dualValueFn at this
      rw [this]
      simp only [penaltyComp, idealGen, Pi.sub_apply]
      unfold valueFn
      ring
  intro t a
  by_cases ht : t ≤ T + 1
  · exact key _ t rfl a
  · unfold dualValueFn valueFn
    rw [bellman_gt _ _ _ _ t (by omega), bellman_gt _ _ _ _ t (by omega)]
